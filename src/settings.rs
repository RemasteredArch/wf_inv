// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::path::PathBuf;

use clap::{Args, Parser, Subcommand};

#[derive(Parser, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[command(about, version)]
#[non_exhaustive]
pub struct Arguments {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Command {
    /// Scan for credentials, fetch the inventory data using them, parse the data, and print the
    /// data.
    ///
    /// This is also broken out into separate scanning and parsing subcommands to avoid repeated API
    /// requests.
    ///
    // TO-DO: update this text!
    /// Prints the output as tab-separated values, with the first line being a header. Does not
    /// attempt to escape newlines, quotes, tabs, etc. in the output (under the assumption that it
    /// should not appear).
    All {
        #[command(flatten)]
        parse_args: ParseArgs,
        #[command(flatten)]
        print_args: PrintArgs,
    },
    /// Scan a running Warframe process (an executable named `Warframe.x64.exe`) for API credentials
    /// and print the authenticated URL to fetch inventory data.
    ///
    /// Appends the API credentials to <https://mobile.warframe.com/api/inventory.php>. Use your
    /// favorite fetch tool (e.g., `curl`) on this URL to get your inventory data as JSON, exactly
    /// as expected by the parse command.
    Scan,
    /// Get the tradable items in the provided inventory data and their pricing data.
    ///
    /// The inventory data must be the JSON from <https://mobile.warframe.com/api/inventory.php>.
    ///
    // TO-DO: update this text!
    /// Prints the output as tab-separated values, with the first line being a header. Does not
    /// attempt to escape newlines, quotes, tabs, etc. in the output (under the assumption that it
    /// should not appear).
    Parse {
        /// The path to a JSON file containing the contents of a Warframe inventory, as would be
        /// received from <https://mobile.warframe.com/api/inventory.php>. If not provided, it will
        /// try to read this from standard input.
        #[arg(value_name = "INVENTORY_JSON_PATH")]
        inventory_json: Option<PathBuf>,
        #[command(flatten)]
        parse_args: ParseArgs,
        #[command(flatten)]
        print_args: PrintArgs,
    },
    #[cfg(feature = "unstable-gui")]
    Gui(GuiArgs),
}

/// Experimental.
#[cfg(feature = "unstable-gui")]
#[derive(Args, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
#[non_exhaustive]
pub struct GuiArgs {
    /// The path to a JSON file containing the contents of a Warframe inventory, as would be
    /// received from <https://mobile.warframe.com/api/inventory.php>.
    #[arg(value_name = "INVENTORY_JSON_PATH")]
    pub inventory_json: Option<PathBuf>,
    #[command(flatten)]
    pub parse_args: ParseArgs,
    #[command(flatten)]
    pub display_args: DisplayArgs,
}

#[expect(clippy::struct_field_names, reason = "not relevant to CLI arguments")]
#[derive(Args, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
#[non_exhaustive]
pub struct ParseArgs {
    /// The path to the JSON file containing the pricing data, as would be produced by
    /// <https://relics.run/history/price_history_2026-08-09.json>. If not provided, it will default
    /// to an embedded copy. The embedded data is guaranteed to be valid and stable, whereas the API
    /// to pull new data from may at any point disappear or change its format, but the API will
    /// provide you fresher data.
    #[arg(long, value_name = "PATH")]
    pub price_data_json: Option<PathBuf>,
    /// The path to the JSON file containing the parsing data, as would be produced by
    /// <https://relics.run/export/parser.json>. If not provided, it will default to an embedded
    /// copy. The embedded data is guaranteed to be valid and stable, whereas the API to pull new
    /// data from may at any point disappear or change its format, but the API will provide you
    /// fresher data, which would be necessary if more tradable items are added.
    #[arg(long, value_name = "PATH")]
    pub parser_json: Option<PathBuf>,
    /// The path to the JSON file containing a list of all tradable items, as would be produced by
    /// <https://api.warframe.market/v2/items>. If not provided, it will default to an embedded
    /// copy. The embedded data is guaranteed to be valid and stable, whereas the API to pull new
    /// data from may at any point disappear or change its format, but the API will provide you
    /// fresher data, which would be necessary if more tradable items are added.
    #[arg(long, value_name = "PATH")]
    pub item_list_json: Option<PathBuf>,
}

// TO-DO: allow saving the raw inventory contents or exporting to JSON.
/// The arguments that control how the output tables should be printed.
///
/// For table formatting arguments that are agnostic to output medium, see [`DisplayArgs`].
#[expect(
    clippy::struct_excessive_bools,
    reason = "not relevant to CLI arguments"
)]
#[derive(Args, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub struct PrintArgs {
    #[command(flatten)]
    pub display_args: DisplayArgs,
    /// The string to print between the entries in every row of the tabular output.
    ///
    /// Can be an empty string to avoid printing any separators.
    ///
    /// Defaults to ' | ' if `--pretty-print` is true, or a tab if it is false.
    #[arg(long)]
    pub table_column_separator: Option<Box<str>>,
    // TO-DO: change to the first _glyph_ instead of the first character.
    /// The character to print between the header and the first row of data in the table.
    ///
    /// Uses only the first character if multiple are provided. Can be an empty string to disable
    /// printing a separating row.
    ///
    /// Defaults to '-' if `--pretty-print` is true, or disabled if it is false.
    #[arg(long)]
    // This is actually used as a `char` (or, rather, a glyph), but must be a string to detect the
    // none option.
    pub table_header_separator: Option<Box<str>>,
}

impl PrintArgs {
    pub fn resolve_defaults(&mut self) {
        let pretty_print = self.display_args.pretty_print;

        self.table_column_separator
            .get_or_insert_with(|| default_table_column_separator(pretty_print).into());
        self.table_header_separator
            .get_or_insert_with(|| default_table_header_separator(pretty_print).into());
    }
}

pub const fn default_table_column_separator(pretty_print: bool) -> &'static str {
    if pretty_print { " | " } else { "\t" }
}

pub const fn default_table_header_separator(pretty_print: bool) -> &'static str {
    if pretty_print { "-" } else { "" }
}

impl Default for PrintArgs {
    // Manually mirror the default values provided to Clap. Ideally, Clap should pick _these_ values
    // up for itself, but that depends on this issue being completed:
    // <https://github.com/clap-rs/clap/issues/3116>.
    fn default() -> Self {
        Self {
            display_args: DisplayArgs::default(),
            table_column_separator: Some(" | ".into()),
            table_header_separator: Some("-".into()),
        }
    }
}

/// The arguments that control how the output tables should be display, regardless of medium.
///
/// For flags that are specific to strictly textual output, see [`DisplayArgs`].
#[derive(Args, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct DisplayArgs {
    /// Group subtypes of a given item, discarding subtype and pricing data.
    #[arg(long, num_args(0..=1), default_value_t = false)]
    pub group_subtypes: bool,
    /// Show all available data columns instead of just a curated subset.
    #[arg(long, num_args(0..=1), default_value_t = false)]
    pub verbose: bool,
    /// Show only items with Orokin Ducat values and print (and sort by) the ratio of Ducat value to
    /// Platinum value.
    #[arg(long, num_args(0..=1), default_value_t = false)]
    pub ducat_valuation: bool,
    /// Whether to print a table with padding.
    ///
    /// Also changes the column separator to be a tab and disables the header separator by default.
    #[arg(long, num_args(0..=1), default_value_t = true)]
    pub pretty_print: bool,
}

impl Default for DisplayArgs {
    // Manually mirror the default values provided to Clap. Ideally, Clap should pick _these_ values
    // up for itself, but that depends on this issue being completed:
    // <https://github.com/clap-rs/clap/issues/3116>.
    fn default() -> Self {
        Self {
            group_subtypes: false,
            verbose: false,
            ducat_valuation: false,
            pretty_print: true,
        }
    }
}
