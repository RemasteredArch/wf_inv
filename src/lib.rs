// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::{
    fs::File,
    io::{BufReader, Read, Write},
    num::NonZero,
    path::PathBuf,
};

use anyhow::{Result, anyhow};
use wf_inv_auth_scanning::{Login, LoginScanner, Process};
use wf_inv_price_data::{Item, ParseContext};

use print::Push;
use settings::{DisplayArgs, ParseArgs, PrintArgs};
use table::ErasedColumn;

#[macro_use]
mod print;
#[cfg(feature = "unstable-gui")]
pub mod gui;
pub mod settings;
mod table;

impl settings::Command {
    #[expect(clippy::missing_errors_doc, reason = "not actually a public API")]
    pub fn execute(self) -> Result<()> {
        match self {
            Self::All {
                parse_args,
                print_args,
            } => {
                let login = scan()?;
                let inventory_json = fetch(&login)?;
                parse_and_print(parse_args, print_args, inventory_json.as_bytes())?;
            }
            Self::Scan => {
                println!("{}", scan()?.to_api_url());
            }
            Self::Parse {
                inventory_json:
                    settings::InventoryJsonArg {
                        inventory_json: maybe_json_path,
                    },
                parse_args,
                print_args,
            } => {
                let mut inventory_json = Vec::new();
                match maybe_json_path {
                    Some(path) => {
                        BufReader::new(File::open(path)?).read_to_end(&mut inventory_json)?
                    }
                    None => std::io::stdin().lock().read_to_end(&mut inventory_json)?,
                };

                parse_and_print(parse_args, print_args, &inventory_json)?;
            }
            #[cfg(feature = "unstable-gui")]
            Self::Gui(settings::GuiArgs {
                inventory_json: settings::InventoryJsonArg { inventory_json },
                parse_args,
                display_args,
            }) => {
                gui::gui(inventory_json, parse_args, display_args)?;
            }
        }

        Ok(())
    }
}

/// Protect against font-related issues from running this as an AppImage on NixOS by panicking.
///
/// # Panics
///
/// Panics if all of the following are true:
///
/// 1. The `CARGO_CRATE_NAME_SKIP_APPIMAGE_CHECK` (so, currently `WF_INV_NAME_SKIP_APPIMAGE_CHECK`)
///    environment variable is not set.
/// 2. The `APPIMAGE` environment variable is set.
/// 3. Either:
///   - The environment variable `FONTCONFIG_FILE` is defined and is a symlink to a file contained
///     in `/nix/store`.
///   - `FONTCONFIG_FILE` is not defined and one of `/etc/fonts/{local,fonts}.conf` (checked in that
///     order) exists and is a symlink to `/nix/store`.
///
/// # Errors
///
/// Any file-related errors encountered when trying to follow the above logic. That means, e.g., a
/// file not found error from `FONTCONFIG_FILE` being defined but pointing to a file that doesn't
/// exist, but does not mean, e.g., `/etc/fonts/{local,fonts}.conf` not existing.
pub fn try_panic_if_appimage_and_font_config_in_nix_store() -> std::io::Result<()> {
    #[cfg(not(target_os = "linux"))]
    return Ok(());

    let skip_check_var_name =
        concat!(env!("CARGO_CRATE_NAME"), "_SKIP_APPIMAGE_CHECK").to_uppercase();
    if std::env::var_os(&skip_check_var_name).is_none()
        && std::env::var_os("APPIMAGE").is_some()
        && is_font_config_in_nix_store()?
    {
        panic!(
            concat!(
                "running `",
                env!("CARGO_CRATE_NAME"),
                "` as an AppImage under NixOS will cause font issues, set `{}` to skip this check",
            ),
            skip_check_var_name,
        )
    }

    Ok(())
}

fn is_font_config_in_nix_store() -> std::io::Result<bool> {
    let is_store_symlink: fn(&std::path::Path) -> std::io::Result<bool> = |path| {
        std::fs::read_link(path)
            .map(|target_path| target_path.starts_with("/nix/store"))
            .or_else(|err| {
                // If the target path exists but is not a symlink.
                if err.kind() == std::io::ErrorKind::InvalidInput {
                    Ok(false)
                } else {
                    Err(err)
                }
            })
    };

    #[expect(clippy::option_if_let_else, reason = "this is better")]
    if let Some(env_path) = std::env::var_os("FONTCONFIG_FILE") {
        is_store_symlink(env_path.as_ref())
    } else {
        let map_not_found = |result: std::io::Result<bool>| -> std::io::Result<Option<bool>> {
            result.map_or_else(
                |err| {
                    if err.kind() == std::io::ErrorKind::NotFound {
                        Ok(None)
                    } else {
                        Err(err)
                    }
                },
                |value| Ok(Some(value)),
            )
        };

        match map_not_found(is_store_symlink("/etc/fonts/local.conf".as_ref()))? {
            Some(bool) => Ok(bool),
            None => map_not_found(is_store_symlink("/etc/fonts/fonts.conf".as_ref()))
                .map(|maybe_bool| maybe_bool.unwrap_or(false)),
        }
    }
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
    if login.is_fake() {
        return Err(anyhow::anyhow!(
            "tried to fetch inventory contents with fake credentials"
        ));
    }

    Ok(reqwest::blocking::Client::builder()
        .user_agent(concat!(
            env!("CARGO_PKG_NAME"),
            "/",
            env!("CARGO_PKG_VERSION"),
        ))
        .build()?
        .get(login.to_api_url())
        .send()?
        .text()?)
}

fn parse_and_print(
    parse_args: ParseArgs,
    print_args: PrintArgs,
    inventory_json: &[u8],
) -> Result<()> {
    if print_args.output_format == settings::OutputFormat::Raw {
        std::io::stdout().lock().write_all(inventory_json)?;
        return Ok(());
    }

    let items = parse(parse_args, inventory_json)?;

    let output_json = print_args.output_format;
    let table = to_table(print_args, items)?;
    print(output_json, &table)
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

fn print(output_format: settings::OutputFormat, table: &table::Table) -> Result<()> {
    match output_format {
        settings::OutputFormat::Tabular => println!("{table}"),
        settings::OutputFormat::Json => println!("{}", serde_json::to_string_pretty(&table)?),
        settings::OutputFormat::Raw => {
            return Err(anyhow::anyhow!("tried to print parsed table as raw"));
        }
    }

    Ok(())
}

fn to_table(
    print_args: PrintArgs,
    items: impl IntoIterator<Item = Item> + AsRef<[Item]>,
) -> Result<table::Table> {
    if print_args.display_args.group_subtypes {
        Ok(to_tsv_summary(print_args, items))
    } else {
        to_full_table(print_args, items.as_ref())
    }
}

fn to_full_table(mut args: PrintArgs, items: &[Item]) -> Result<table::Table> {
    args.resolve_defaults(); // Ensures no argument is `None`.

    let columns = columns(&args.display_args, items)?;

    let table_column_separator = args.table_column_separator.unwrap();
    let table_header_separator = args.table_header_separator.unwrap().chars().next();

    let mut table = table::Table::new(
        columns.into(),
        args.display_args.pretty_print,
        table_column_separator,
        table_header_separator,
    );

    table.sort_descending_by_column_title(if args.display_args.ducat_valuation {
        &["ducat/plat ratio", "count"]
    } else {
        &["weighted average", "count"]
    })?;

    Ok(table)
}

fn columns(args: &DisplayArgs, items: &[Item]) -> Result<Vec<Box<dyn ErasedColumn>>> {
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

#[must_use]
fn to_tsv_summary(mut args: PrintArgs, items: impl IntoIterator<Item = Item>) -> table::Table {
    args.resolve_defaults(); // Ensures no argument is `None`.
    let table_column_separator = args.table_column_separator.unwrap();
    let table_header_separator = args.table_header_separator.unwrap().chars().next();

    let columns = {
        columns![
            name_vals: Box<str> = (String, "name"),
            lotus_path_vals: Box<str> = if args.display_args.verbose => (String, "lotus path"),
            category_vals: &'static str = (String, "category"),
            count_vals: wf_inv_price_data::Count = (Integer, "count"),
        ];

        for item in items {
            let r#type = match item.price_data() {
                wf_inv_price_data::PriceDataByType::Relic(_) => "relic",
                wf_inv_price_data::PriceDataByType::Mod(_) => "mod",
                wf_inv_price_data::PriceDataByType::Fish(_) => "fish",
                wf_inv_price_data::PriceDataByType::Riven(_) => "riven",
                wf_inv_price_data::PriceDataByType::Other(_) => "other",
            };

            name_vals.push(item.name().into());
            lotus_path_vals.push(item.lotus_path().into());
            category_vals.push(r#type);
            count_vals.push(item.count());
        }

        filtered_vec![name_vals, lotus_path_vals?, category_vals, count_vals,]
    };

    table::Table::new(
        columns.into(),
        args.display_args.pretty_print,
        table_column_separator,
        table_header_separator,
    )
}
