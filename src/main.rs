// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::{fs::File, io::BufReader, path::PathBuf};

use anyhow::{Result, anyhow};
use clap::Parser;
use wf_inv_auth_scanning::{Login, LoginScanner, Process};
use wf_inv_price_data::{Item, ParseContext};

use crate::settings::{Arguments, ParseArgs, PrintArgs};

mod settings;
mod table;

fn main() -> Result<()> {
    Arguments::parse().command.execute()
}

fn scan() -> Result<Login> {
    let process = Process::find_by_executable_name("Warframe.x64.exe")
        .ok_or_else(|| anyhow!("could not find a running Warframe process"))?;

    let auth = LoginScanner::from_process(&process)
        .find_auth()
        .ok_or_else(|| anyhow!("could not find a login in the running Warframe process"))?;

    Ok(auth)
}

fn fetch(login: &Login) -> Result<String> {
    Ok(reqwest::blocking::get(login.to_api_url())?.text()?)
}

fn parse(args: ParseArgs, inventory_json: impl std::io::Read) -> Result<Box<[Item]>> {
    let open = |maybe_path: Option<PathBuf>| -> std::io::Result<Option<BufReader<File>>> {
        maybe_path
            .map(|path| File::open(path).map(BufReader::new))
            .transpose()
    };
    let ctx = ParseContext::from_some_fresh(
        open(args.parser_json)?,
        open(args.price_data_json)?,
        open(args.item_list_json)?,
    )?;

    wf_inv_price_data::get_tradable_items(ctx, inventory_json)
}

fn to_table(mut args: PrintArgs, items: &[Item]) -> Result<()> {
    args.resolve_defaults(); // Ensures no argument is `None`.
    let table_column_separator = args.table_column_separator.unwrap();
    let table_header_separator = args.table_header_separator.unwrap().chars().next();

    let columns = {
        macro_rules! columns {
            [$(
                $(if $cond:expr =>)? ($type:ident, $title:expr, $values:expr $(,)?)
            ),+,] => {{
                let mut columns = Vec::new();
                $(
                    columns!(@ $((if $cond))? columns, $type, $title, $values);
                )+
                columns
            }};
            (@ (if $cond:expr) $out:expr, $type:ident, $title:expr, $values:expr) => {
                if $cond {
                    columns!(@ $out, $type, $title, $values)
                }
            };
            (@ $out:expr, $type:ident, $title:expr, $values:expr) => {
                $out.push(Box::new(table::Column::new(
                    table::ColumnType::$type,
                    $title.into(),
                    $values,
                )) as Box<dyn table::ErasedColumn>)
            };
        }

        let mut ducat_plat_ratio_vals = Vec::new();
        let mut name_vals = Vec::new();
        let mut lotus_path_vals = Vec::new();
        let mut ducats_vals = Vec::new();
        let mut category_vals = Vec::new();
        let mut subtype_vals = Vec::new();
        let mut count_vals = Vec::new();
        let mut closest_subtype_with_price_data_vals = Vec::new();
        let mut trade_volume_vals = Vec::new();
        let mut weighted_average_vals = Vec::new();
        let mut minimum_vals = Vec::new();
        let mut median_vals = Vec::new();
        let mut maximum_vals = Vec::new();

        for item in items {
            for wf_inv_price_data::UniqueItem {
                name,
                lotus_path,
                ducats,
                category,
                subtype,
                count,
                closest_subtype_with_price_data,
                closest_subtype_price_data,
            } in item.flatten()
            {
                let volume = closest_subtype_price_data.volume();
                let wa_price = closest_subtype_price_data.wa_price().0;
                let min_price = closest_subtype_price_data.min_price().0;
                let median = closest_subtype_price_data.median().0;
                let max_price = closest_subtype_price_data.max_price().0;

                let ducat_plat_ratio = {
                    #[expect(
                        clippy::cast_precision_loss,
                        reason = "not a precise calculation and \
                            it's unlikely this would be large enough to be problematic"
                    )]
                    ducats.map(|ducats| {
                        table::FixedPointDecimal::try_round_from((ducats.get() as f64) / wa_price)
                    })
                }
                .transpose()?;

                if args.ducat_valuation && ducats.is_none() {
                    continue;
                }

                ducat_plat_ratio_vals.push(table::PrintingOption::from(ducat_plat_ratio));
                name_vals.push(name);
                lotus_path_vals.push(lotus_path);
                ducats_vals.push(table::PrintingOption::from(ducats));
                category_vals.push(category);
                subtype_vals.push(subtype);
                count_vals.push(count);
                closest_subtype_with_price_data_vals.push(closest_subtype_with_price_data);
                trade_volume_vals.push(volume);
                weighted_average_vals.push(table::FixedPointDecimal::try_round_from(wa_price)?);
                minimum_vals.push(min_price);
                median_vals.push(table::FixedPointDecimal::try_round_from(median)?);
                maximum_vals.push(max_price);
            }
        }

        columns![
            if args.verbose || args.ducat_valuation => (
                Fractional,
                "ducat/plat ratio",
                ducat_plat_ratio_vals,
            ),
            (String, "name", name_vals.into_iter().map(Box::<str>::from)),
            if args.verbose => (
                String,
                "lotus path",
                lotus_path_vals.into_iter().map(Box::<str>::from),
            ),
            if args.verbose || args.ducat_valuation => (Integer, "ducats", ducats_vals),
            if args.verbose || !args.ducat_valuation => (
                String,
                "category",
                category_vals.into_iter().map(Box::<str>::from),
            ),
            if args.verbose || !args.ducat_valuation => (
                String,
                "subtype",
                subtype_vals.into_iter().map(Box::<str>::from),
            ),
            (Integer, "count", count_vals),
            if args.verbose || !args.ducat_valuation => (
                String,
                "closest subtype with price data",
                closest_subtype_with_price_data_vals
                    .into_iter()
                    .map(Box::<str>::from),
            ),
            (Integer, "trade volume", trade_volume_vals),
            (Fractional, "weighted average", weighted_average_vals),
            if args.verbose => (Integer, "minimum", minimum_vals),
            // TO-DO: why is the median fractional? That's definitely not right.
            if args.verbose => (Fractional, "median", median_vals),
            if args.verbose => (Integer, "maximum", maximum_vals),
        ]
    };

    let mut table = table::Table::new(
        columns.into(),
        args.pretty_print,
        table_column_separator,
        table_header_separator,
    );

    table.sort_descending_by_column_title(if args.ducat_valuation {
        &["ducat/plat ratio", "count"]
    } else {
        &["weighted average", "count"]
    })?;

    println!("{table}");

    Ok(())
}

fn to_tsv_summary(items: impl IntoIterator<Item = Item>) {
    println!("name\tlotus path\tcategory\tcount");

    for item in items {
        let r#type = match item.price_data() {
            wf_inv_price_data::PriceDataByType::Relic(_) => "relic",
            wf_inv_price_data::PriceDataByType::Mod(_) => "mod",
            wf_inv_price_data::PriceDataByType::Fish(_) => "fish",
            wf_inv_price_data::PriceDataByType::Riven(_) => "riven",
            wf_inv_price_data::PriceDataByType::Other(_) => "other",
        };

        println!(
            "{}\t{}\t{}\t{}",
            item.name(),
            item.lotus_path(),
            item.count(),
            r#type,
        );
    }
}
