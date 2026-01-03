use std::{fs::File, io::BufReader, path::PathBuf};

use anyhow::{Result, anyhow};
use clap::{Args, Parser, Subcommand};
use wf_inv_auth_scanning::{Login, LoginScanner, Process};
use wf_inv_price_data::{Item, ParseContext};

fn main() -> Result<()> {
    Arguments::parse().command.execute()
}

#[non_exhaustive]
#[derive(Parser, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[command(about, version)]
struct Arguments {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum Command {
    /// Scan for credentials, fetch the inventory data using them, parse the data, and print the
    /// data.
    ///
    /// This is also broken out into separate scanning and parsing subcommands to avoid repeated API
    /// requests.
    ///
    /// Prints the output as tab-separated values, with the first line being a header. Does not
    /// attempt to escape newlines, quotes, tabs, etc. in the output (under the assumption that it
    /// should not appear).
    All {
        #[command(flatten)]
        parse_args: ParseArgs,
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
    },
}

impl Command {
    fn execute(self) -> Result<()> {
        match self {
            Self::All { parse_args } => {
                let login = scan()?;
                let json = fetch(&login)?;

                let items = parse(parse_args, json.as_bytes())?;
                to_tsv(items);
            }
            Self::Scan => {
                println!("{}", scan()?.to_api_url());
            }
            Self::Parse {
                inventory_json,
                parse_args,
            } => {
                let items = match inventory_json {
                    Some(path) => parse(parse_args, BufReader::new(File::open(path)?)),
                    None => parse(parse_args, std::io::stdin()),
                }?;
                to_tsv(items);
            }
        }

        Ok(())
    }
}

#[non_exhaustive]
#[derive(Args, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct ParseArgs {
    /// The path to the JSON file containing the pricing data, as would be produced by
    /// <https://relics.run/history/price_history_2025-12-21.json>. If not provided, it will default
    /// to an embedded copy. The embedded data is guaranteed to be valid and stable, whereas the API
    /// to pull new data from may at any point disappear or change its format, but the API will
    /// provide you fresher data.
    #[arg(long, value_name = "PATH")]
    price_data_json: Option<PathBuf>,
    /// The path to the JSON file containing the parsing data, as would be produced by
    /// <https://relics.run/export/parser.json>. If not provided, it will default to an embedded
    /// copy. The embedded data is guaranteed to be valid and stable, whereas the API to pull new
    /// data from may at any point disappear or change its format, but the API will provide you
    /// fresher data, which would be necessary if more tradable items are added.
    #[arg(long, value_name = "PATH")]
    parser_json: Option<PathBuf>,
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
    let open = |path| -> Result<_> { Ok(BufReader::new(File::open(path)?)) };
    let ctx = match (args.parser_json, args.price_data_json) {
        (Some(parser), Some(price_data)) => ParseContext::new(open(parser)?, open(price_data)?)?,
        (Some(parser), None) => ParseContext::from_fresh_parser(open(parser)?)?,
        (None, Some(price_data)) => ParseContext::from_fresh_price_history(open(price_data)?)?,
        (None, None) => ParseContext::from_embedded_data(),
    };

    wf_inv_price_data::get_tradable_items(ctx, inventory_json)
}

fn to_tsv(items: Box<[Item]>) {
    println!("name\tlotus path\tcount\tcategory");

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
