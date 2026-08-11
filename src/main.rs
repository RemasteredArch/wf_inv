// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::{fmt::Display, fs::File, io::BufReader, num::NonZero, path::PathBuf};

use anyhow::{Result, anyhow};
use clap::Parser;
use wf_inv_auth_scanning::{Login, LoginScanner, Process};
use wf_inv_price_data::{Item, ParseContext};

use settings::{Arguments, ParseArgs, PrintArgs};
use table::ErasedColumn;

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

    let columns = columns(&args, items)?;

    let table_column_separator = args.table_column_separator.unwrap();
    let table_header_separator = args.table_header_separator.unwrap().chars().next();

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

fn columns(args: &PrintArgs, items: &[Item]) -> Result<Vec<Box<dyn ErasedColumn>>> {
    macro_rules! ty {
        ($ty:ty) => {
            ColumnBuilder<$ty>
        };
        ($ty:ty, $cond:expr) => {
            Option<ColumnBuilder<$ty>>
        };
    }

    macro_rules! columns {
        [$(
            $vec_name:ident: $value_type:ty =
                $(if $cond:expr =>)? ($column_type:ident, $title:expr $(,)?)
        ),+ ,] => {
            $(
                let mut $vec_name: ty!($value_type $(, $cond)?) =
                    columns!(@ $(if $cond =>)? ($column_type, $title));
            )+
        };
        (
            @ if $cond:expr => ($type:ident, $title:expr $(,)?)
        ) => {
            if $cond {
                Some(columns!(@ ($type, $title)))
            } else {
                None
            }
        };
        (
            @ ($type:ident, $title:expr $(,)?)
        ) => {
            ColumnBuilder::new(table::ColumnType::$type, $title)
        };
    }

    macro_rules! filtered_vec {
        [$(
            // `$($match_try_op:ident)*` is a hack that should only ever match zero elements. Its
            // sole purpose is to provide a meta-variable to match the `?` on, as every
            // meta-variable that could match it would cause other problems (e.g., `tt` would be
            // ambiguous with the following comma).
            $builder:ident $($($match_try_op:ident)* ?)?
        ),+ ,] => {{
            let mut out = Vec::new();
            $( filtered_vec!(@ $builder $($($match_try_op)* ?)? out); )+
            out
        }};
        (@ $builder:ident ? $out:expr) => {
            if let Some(builder) = $builder {
                filtered_vec!(@ builder $out);
            }
        };
        (@ $builder:ident $out:expr) => {
            $out.push($builder.into());
        };
    }

    columns![
        ducat_plat_ratio_vals: table::PrintingOption<table::FixedPointDecimal> =
            if args.verbose || args.ducat_valuation => (Fractional, "ducat/plat ratio"),
        name_vals: Box<str> =
            (String, "name"),
        lotus_path_vals: Box<str> =
            if args.verbose => (String, "lotus path"),
        ducats_vals: table::PrintingOption<NonZero<wf_inv_price_data::Ducats>> =
            if args.verbose || args.ducat_valuation => (Integer, "ducats"),
        category_vals: Box<str> =
            if args.verbose || !args.ducat_valuation => (String, "category"),
        subtype_vals: Box<str> =
            if args.verbose || !args.ducat_valuation => (String, "subtype"),
        count_vals: wf_inv_price_data::Count =
            (Integer, "count"),
        closest_subtype_with_price_data_vals: Box<str> =
            if args.verbose || !args.ducat_valuation => (String, "closest subtype with price data"),
        trade_volume_vals: wf_inv_price_data::Count =
            (Integer, "trade volume"),
        weighted_average_vals: table::FixedPointDecimal =
            (Fractional, "weighted average"),
        minimum_vals: u64 =
            if args.verbose => (Integer, "minimum"),
        // TO-DO: why is the median fractional? That's definitely not right.
        median_vals: table::FixedPointDecimal =
            if args.verbose => (Fractional, "median"),
        maximum_vals: u64 =
            if args.verbose => (Integer, "maximum"),
    ];

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

            ducat_plat_ratio_vals.push(ducat_plat_ratio.into());
            name_vals.push(name.into());
            lotus_path_vals.push(lotus_path.into());
            ducats_vals.push(ducats.into());
            category_vals.push(category.into());
            subtype_vals.push(subtype.into());
            count_vals.push(count);
            closest_subtype_with_price_data_vals.push(closest_subtype_with_price_data.into());
            trade_volume_vals.push(volume);
            weighted_average_vals.push(table::FixedPointDecimal::try_round_from(wa_price)?);
            minimum_vals.push(min_price);
            median_vals.push(table::FixedPointDecimal::try_round_from(median)?);
            maximum_vals.push(max_price);
        }
    }

    Ok(filtered_vec![
        ducat_plat_ratio_vals?,
        name_vals,
        lotus_path_vals?,
        ducats_vals?,
        category_vals?,
        subtype_vals?,
        count_vals,
        closest_subtype_with_price_data_vals?,
        trade_volume_vals,
        weighted_average_vals,
        minimum_vals?,
        median_vals?,
        maximum_vals?,
    ])
}

trait Push {
    type Value;

    fn push(&mut self, value: Self::Value);
}

struct ColumnBuilder<T> {
    ty: table::ColumnType,
    title: &'static str,
    values: Vec<T>,
}

impl<T> ColumnBuilder<T> {
    const fn new(ty: table::ColumnType, title: &'static str) -> Self {
        Self {
            ty,
            title,
            values: Vec::new(),
        }
    }
}

impl<T> Push for ColumnBuilder<T> {
    type Value = T;

    fn push(&mut self, value: Self::Value) {
        self.values.push(value);
    }
}

impl<T> Push for Option<ColumnBuilder<T>> {
    type Value = T;

    fn push(&mut self, value: Self::Value) {
        if let Some(builder) = self {
            builder.push(value);
        }
    }
}

impl<T: Display> From<ColumnBuilder<T>> for table::Column<T> {
    fn from(value: ColumnBuilder<T>) -> Self {
        Self::new(value.ty, value.title.into(), value.values)
    }
}

impl<T: Ord + Display + 'static> From<ColumnBuilder<T>> for Box<dyn table::ErasedColumn> {
    fn from(value: ColumnBuilder<T>) -> Self {
        Box::new(table::Column::<T>::from(value)) as Self
    }
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
