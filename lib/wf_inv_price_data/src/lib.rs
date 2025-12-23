use std::{
    collections::{HashMap, HashSet},
    sync::OnceLock,
};

use anyhow::{Result, anyhow};

mod parse;

/// From <https://relics.run/export/parser.json>.
const PARSER: &str = include_str!("../data/parser.json");
/// From <https://relics.run/history/price_history_2025-12-21.json>.
const PRICE_HISTORY: &str = include_str!("../data/price_history_2025-12-21.json");
/// From <https://mobile.warframe.com/api/inventory.php>.
const INVENTORY_DATA: &str = include_str!("../data/inventory.json");

static TRADEABLE_ITEMS: OnceLock<Box<[Item]>> = OnceLock::new();

pub fn items() -> &'static [Item] {
    TRADEABLE_ITEMS.get_or_init(|| get_tradeable_items().unwrap())
}

fn get_tradeable_items() -> Result<Box<[Item]>> {
    eprintln!("1");
    let parse::Inventory {
        misc_items,
        raw_upgrades,
    } = serde_json::from_str(INVENTORY_DATA)?;

    eprintln!("2");
    let misc_items = misc_items
        .into_iter()
        .map(|misc_item| (misc_item.item_type, misc_item.item_count));
    let raw_upgrades = raw_upgrades
        .into_iter()
        .map(|raw_upgrade| (raw_upgrade.item_type, raw_upgrade.item_count));

    eprintln!("3");
    let parse::Parser { map: parser } = serde_json::from_str(PARSER)?;
    eprintln!("4");
    let parse::PriceHistory { map: history } = serde_json::from_str(PRICE_HISTORY)?;

    // Key is the name as used in the price history.
    let mut items: HashMap<String, Item> = HashMap::new();

    eprintln!("5");
    let mut ctx = ParseContext {
        items: &mut items,
        history: &history,
        parser: &parser,
    };
    for (is_mod, (lotus_path, count)) in misc_items.map(|item| (false, item)).chain(
        raw_upgrades
            .filter(|(lotus_path, _)| {
                // Skip flawed mods, as it appears warframe.market doesn't list those.
                //
                // There's also "expert" mods which would be parsed the same way. These correspond
                // to primed variants, and it appears that the parser does correctly prefix the name
                // with "primed" for every mod that has a primed variant. The parser also include
                // some "expert" mods whose names aren't prefixed with "primed", but none of these
                // appear to actually be real mods, so that shouldn't be an issue.
                !(lotus_path.contains("/Beginner/") && lotus_path.ends_with("Beginner"))
            })
            .map(|item| (true, item)),
    ) {
        add_or_update_item(&mut ctx, is_mod, lotus_path, count)?;
    }

    Ok(items.into_values().collect())
}

fn get_relic_subtype_and_maybe_strip_name(
    lotus_path: &str,
    name: &mut String,
) -> Option<RelicSubtype> {
    if !lotus_path.starts_with("Lotus/Types/Game/Projections/") {
        return None;
    }

    [
        ("Bronze", " Intact", RelicSubtype::Intact),
        ("Silver", " Exceptional", RelicSubtype::Exceptional),
        ("Gold", " Flawless", RelicSubtype::Flawless),
        ("Platinum", " Radiant", RelicSubtype::Radiant),
    ]
    .into_iter()
    .find_map(|(path_suffix, tier, subtype)| {
        if lotus_path.ends_with(path_suffix)
            && let Some(stripped_name) = name.strip_suffix(tier)
        {
            *name = stripped_name.to_string();
            Some(subtype)
        } else {
            None
        }
    })
}

fn get_fish_subtype(lotus_path: &str) -> Option<FishSubtype> {
    if !lotus_path.contains("/Fish/") || lotus_path.contains("/FishParts/") {
        return None;
    }

    [
        // For some reason, the ordering of "Item" and the size depends on the fish.
        ("ItemLarge", "LargeItem", FishSubtype::Large),
        ("ItemMedium", "MediumItem", FishSubtype::Medium),
        // For some reason, small fish aren't given a size.
        //
        // This will, unfortunately, also catch (ha!) boots, but they can't be traded so I do not
        // care. A regex hack could catch that, but I am not taking a regex dependency for a
        // non-issue.
        ("Item", "Item", FishSubtype::Small),
    ]
    .into_iter()
    .find_map(|(path_suffix_a, path_suffix_b, subtype)| {
        if lotus_path.ends_with(path_suffix_a) || lotus_path.ends_with(path_suffix_b) {
            Some(subtype)
        } else {
            None
        }
    })
}

struct ParseContext<'c> {
    pub items: &'c mut HashMap<String, Item>,
    pub history: &'c HashMap<String, Box<[parse::PriceData]>>,
    pub parser: &'c HashMap<String, String>,
}

fn add_or_update_item(
    ctx: &mut ParseContext<'_>,
    is_mod: bool,
    lotus_path: String,
    count: Count,
) -> Result<()> {
    eprintln!("{lotus_path}");

    let mut name = ctx
        .parser
        .get(&lotus_path)
        .cloned()
        .ok_or_else(|| anyhow!("item `{lotus_path}` not present in parser"))?;
    // Some entries in the parser are just another Lotus path. It isn't necessarily clear that
    // resolving them down ceaselessly is entirely correct, however, because it does appear to
    // normalize some recipes into their products.
    //
    // TO-DO: should I normalize `lotus_path` to whatever the last one is or keep it to whatever it
    // was in the inventory?
    while name.starts_with("/Lotus/") {
        name = ctx
            .parser
            .get(&name)
            .cloned()
            .ok_or_else(|| anyhow!("item `{lotus_path}` -> `{name}` not present in parser"))?;
    }

    let subtype = Subtype::detect_and_maybe_strip_name(is_mod, &lotus_path, &mut name);

    let Some(mut price_data) = ctx.history.get(&name).map(|price_data| {
        price_data
            .iter()
            .filter(|data| matches!(data.order_type, parse::OrderType::Closed))
            .peekable()
    }) else {
        return Ok(());
    };
    // Assume that there is no price data available because there just isn't enough sold to find
    // data on actually closed sales. This makes the assumption that only data from closed sales is
    // worth considering, and that items with such low sales volumes aren't even worth selling.
    //
    // The assumptions that these conditions are (A) worth ignoring and (B) the only conditions that
    // could cause a [`None`] value are not necessarily bulletproof. I could be wrong here.
    if price_data.peek().is_none() {
        return Ok(());
    }

    if let Some(item) = ctx.items.get_mut(&name) {
        increment_item_count(item, count, subtype)?;

        return Ok(());
    }

    ctx.items.insert(
        name.clone(),
        Item {
            name,
            lotus_path,
            count,
            price_data: PriceDataByVariant::new(subtype, count, price_data)?,
        },
    );

    Ok(())
}

fn increment_item_count(item: &mut Item, count: Count, subtype: Subtype) -> Result<()> {
    item.count += count;

    match (&mut item.price_data, subtype) {
        (PriceDataByVariant::Relic(relic), Subtype::Relic(relic_subtype)) => {
            relic.owned_variants.insert(relic_subtype, count);
        }
        // TO-DO: track owned variants.
        (PriceDataByVariant::Mod(r#mod), Subtype::Mod) => {
            r#mod.owned_variants.insert(ModRank::Ranked(u8::MAX));
        }
        (PriceDataByVariant::Fish(fish), Subtype::Fish(fish_subtype)) => {
            fish.owned_variants.insert(fish_subtype, count);
        }
        // TO-DO: track revealed variants.
        (PriceDataByVariant::Riven(riven), Subtype::Riven(riven_subtype)) => {
            riven.owned_variants.insert(riven_subtype, count);
        }
        (PriceDataByVariant::Other(_), Subtype::Other) => (),
        (data, subtype) => {
            return Err(anyhow!(
                "expected matching subtypes, received `{data:?}` and `{subtype:?}`",
            ));
        }
    }

    Ok(())
}

#[derive(Debug, Clone, Copy)]
enum Subtype {
    Relic(RelicSubtype),
    Fish(FishSubtype),
    Riven(RivenSubtype),
    Mod,
    Other,
}

impl Subtype {
    fn detect_and_maybe_strip_name(is_mod: bool, lotus_path: &str, name: &mut String) -> Self {
        get_relic_subtype_and_maybe_strip_name(lotus_path, name).map_or_else(
            || {
                get_fish_subtype(lotus_path).map_or_else(
                    || {
                        // A riven that has been revealed or unlocked will be prefixed with
                        // `/Lotus/Upgrades/Mods/Randomized/Lotus` (note `/Raw` versus `/Lotus`),
                        // but it appears that none appear in this section of the `inventory.json`.
                        //
                        // TO-DO: parse revealed (but not unlocked) rivens from the `upgrades`
                        // section.
                        if lotus_path.starts_with("/Lotus/Upgrades/Mods/Randomized/Raw") {
                            Self::Riven(RivenSubtype::Unrevealed)
                        } else if is_mod {
                            Self::Mod
                        } else {
                            Self::Other
                        }
                    },
                    Self::Fish,
                )
            },
            Self::Relic,
        )
    }
}

#[derive(Debug)]
pub struct Item {
    pub name: String,
    pub lotus_path: String,
    pub count: Count,
    pub price_data: PriceDataByVariant,
}

pub type RelicSubtype = parse::RelicSubtype;
pub type FishSubtype = parse::FishSubtype;
pub type RivenSubtype = parse::RivenSubtype;
pub type Count = u64;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModRank {
    Ranked(u8),
    /// Some mods don't have ranks. This includes the legendary fusion core, but also more ordinary
    /// mods like Runtime.
    Rankless,
}

#[derive(Debug)]
pub enum PriceDataByVariant {
    Relic(Relic),
    Mod(Mod),
    Fish(Fish),
    Riven(Riven),
    Other(PriceData),
}

impl PriceDataByVariant {
    fn new<'a>(
        subtype: Subtype,
        count: Count,
        price_data: impl Iterator<Item = &'a parse::PriceData>,
    ) -> Result<Self> {
        /// Check that the subtypes of the price data match and convert the data from the types
        /// provided by [`parse`].
        macro_rules! parse_matching {
            ($subtype_ident:ident ($subtype_value:ident), $subtype_lit:literal) => {{
                let price_data = price_data
                    .map(|data| {
                        let Some(parse::Subtype::$subtype_ident(matching_subtype)) = data.subtype
                        else {
                            return Err(anyhow!(concat!(
                                $subtype_lit,
                                " price data missing ",
                                $subtype_lit,
                                " subtype",
                            )));
                        };
                        Ok((matching_subtype, PriceData::from_parsed_lossy(data)))
                    })
                    .collect::<Result<_>>()?;

                Self::$subtype_ident($subtype_ident {
                    owned_variants: HashMap::from([($subtype_value, count)]),
                    price_data,
                })
            }};
        }

        let price_data = match subtype {
            Subtype::Relic(relic_subtype) => parse_matching!(Relic(relic_subtype), "relic"),
            Subtype::Fish(fish_subtype) => parse_matching!(Fish(fish_subtype), "fish"),
            Subtype::Riven(riven_subtype) => parse_matching!(Riven(riven_subtype), "riven"),
            Subtype::Mod => Self::Mod(Mod {
                owned_variants: HashSet::from([ModRank::Ranked(u8::MAX)]),
                price_data: price_data
                    .map(|data| {
                        (
                            data.mod_rank.map_or(ModRank::Rankless, ModRank::Ranked),
                            PriceData::from_parsed_lossy(data),
                        )
                    })
                    .collect(),
            }),
            Subtype::Other => Self::Other(
                price_data
                    .map(PriceData::from_parsed_lossy)
                    .next()
                    .ok_or_else(|| anyhow!("received empty price data iterator"))?,
            ),
        };

        Ok(price_data)
    }
}

#[derive(Debug)]
pub struct Relic {
    pub owned_variants: HashMap<RelicSubtype, Count>,
    pub price_data: HashMap<RelicSubtype, PriceData>,
}

#[derive(Debug)]
pub struct Mod {
    pub owned_variants: HashSet<ModRank>,
    pub price_data: HashMap<ModRank, PriceData>,
}

#[derive(Debug)]
pub struct Fish {
    pub owned_variants: HashMap<FishSubtype, Count>,
    pub price_data: HashMap<FishSubtype, PriceData>,
}

#[derive(Debug)]
pub struct Riven {
    pub owned_variants: HashMap<RivenSubtype, Count>,
    pub price_data: HashMap<RivenSubtype, PriceData>,
}

#[derive(Debug)]
pub struct PriceData {
    pub volume: u64,
    pub wa_price: f64,
    pub min_price: u64,
    pub median: f64,
    pub max_price: u64,
}

impl PriceData {
    const fn from_parsed_lossy(data: &parse::PriceData) -> Self {
        Self {
            volume: data.volume,
            #[expect(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                reason = "not expecting large or negative values"
            )]
            min_price: data.min_price.round() as u64,
            #[expect(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                reason = "not expecting large or negative values"
            )]
            max_price: data.max_price.round() as u64,
            wa_price: data.wa_price,
            median: data.median,
        }
    }
}
