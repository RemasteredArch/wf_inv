use std::{
    collections::{HashMap, HashSet},
    sync::OnceLock,
};

use anyhow::anyhow;

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

fn get_tradeable_items() -> anyhow::Result<Box<[Item]>> {
    eprintln!("1");
    let parse::Inventory {
        misc_items,
        raw_upgrades,
    } = serde_json::from_str(INVENTORY_DATA)?;

    eprintln!("2");
    let misc_items = misc_items.into_iter().map(
        |parse::MiscItem {
             item_count,
             item_type,
         }| { (item_type, item_count) },
    );
    let raw_upgrades = raw_upgrades.into_iter().map(
        |parse::RawUpgrade {
             item_count,
             item_type,
         }| { (item_type, item_count) },
    );

    eprintln!("3");
    let parse::Parser { map: parser } = serde_json::from_str(PARSER)?;
    eprintln!("4");
    let parse::PriceHistory { map: history } = serde_json::from_str(PRICE_HISTORY)?;

    // Key is the name as used in the price history.
    let mut items: HashMap<String, Item> = HashMap::new();

    eprintln!("5");
    for (is_mod, (lotus_path, count)) in misc_items
        .map(|item| (false, item))
        .chain(raw_upgrades.map(|(lotus_path, count)| {
            (
                // // Every item in the list of mods is obviously a mod (or arcane) except fusion
                // // cores. These are _technically_ mods, but break the assumptions that one would
                // // reasonably make about mods and more closely align with regular items than mods
                // // for the purposes of this library.
                // !lotus_path.starts_with("/Lotus/Upgrades/Mods/Fusers/"),
                true,
                (lotus_path, count),
            )
        }))
        .filter(|(_, (lotus_path, _))| {
            // Skip flawed mods, as it appears warframe.market doesn't list those.
            //
            // There's also "expert" mods which would be parsed the same way. These correspond to
            // primed variants, and it appears that the parser does correctly prefix the name with
            // "primed" for every mod that has a primed variant. The parser also include some
            // "expert" mods whose names aren't prefixed with "primed", but none of these appear to
            // actually be real mods, so that shouldn't be an issue.
            !(lotus_path.contains("/Beginner/") && lotus_path.ends_with("Beginner"))
        })
    {
        eprintln!("{lotus_path}");

        let mut name = parser
            .get(&lotus_path)
            .cloned()
            .ok_or_else(|| anyhow!("item `{lotus_path}` not present in parser"))?;
        // Some entries in the parser are just another Lotus path. It isn't necessarily clear that
        // resolving them down ceaselessly is entirely correct, however, because it does appear to
        // normalize some recipes into their products.
        //
        // TO-DO: should I normalize `lotus_path` to whatever the last one is or keep it to whatever
        // it was in the inventory?
        while name.starts_with("/Lotus/") {
            name = parser
                .get(&name)
                .cloned()
                .ok_or_else(|| anyhow!("item `{lotus_path}` -> `{name}` not present in parser"))?;
        }

        let relic_subtype = [
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
                name = stripped_name.to_string();
                Some(subtype)
            } else {
                None
            }
        });
        let fish_subtype = [
            // For some reason, the ordering of "Item" and the size depends on the fish.
            ("ItemLarge", "LargeItem", FishSubtype::Large),
            ("ItemMedium", "MediumItem", FishSubtype::Medium),
            // For some reason, small fish aren't given a size.
            //
            // This will, unfortunately, also catch (ha!) boots, but they can't be traded so I do
            // not care. A regex hack could catch that, but I am not taking a regex dependency for a
            // non-issue.
            ("Item", "Item", FishSubtype::Small),
        ]
        .into_iter()
        .find_map(|(path_suffix_a, path_suffix_b, subtype)| {
            if lotus_path.contains("/Fish/")
                && !lotus_path.contains("/FishParts/")
                && (lotus_path.ends_with(path_suffix_a) || lotus_path.ends_with(path_suffix_b))
            {
                Some(subtype)
            } else {
                None
            }
        });
        // A riven that has been revealed or unlocked will be prefixed with
        // `/Lotus/Upgrades/Mods/Randomized/Lotus` (note `/Raw` versus `/Lotus`), but it appears
        // that none appear in this section of the `inventory.json`.
        //
        // TO-DO: parse revealed (but not unlocked) rivens from the `upgrades` section.
        let riven_subtype = if lotus_path.starts_with("/Lotus/Upgrades/Mods/Randomized/Raw") {
            Some(RivenSubtype::Unrevealed)
        } else {
            None
        };

        let Some(price_data) = history.get(&name) else {
            continue;
        };
        let mut price_data = price_data
            .iter()
            .filter(|data| matches!(data.order_type, parse::OrderType::Closed))
            .peekable();
        // Assume that there is no price data available because there just isn't enough sold to find
        // data on actually closed sales. This makes the assumption that only data from closed sales
        // is worth considering, and that items with such low sales volumes aren't even worth
        // selling.
        //
        // The assumptions that these conditions are (A) worth ignoring and (B) the only conditions
        // that could cause a [`None`] value are not necessarily bulletproof. I could be wrong here.
        if price_data.peek().is_none() {
            continue;
        }

        if let Some(item) = items.get_mut(&name) {
            item.count += count;

            match &mut item.price_data {
                PriceDataByVariant::Relic(relic) => {
                    relic.owned_variants.insert(
                        relic_subtype
                            .ok_or_else(|| anyhow!("relics should always have subtypes"))?,
                        count,
                    );
                }
                // TO-DO: track owned variants.
                PriceDataByVariant::Mod(r#mod) => {
                    r#mod.owned_variants.insert(ModRank::Ranked(u8::MAX));
                }
                PriceDataByVariant::Fish(fish) => {
                    fish.owned_variants.insert(
                        fish_subtype.ok_or_else(|| anyhow!("fish should always have subtypes"))?,
                        count,
                    );
                }
                PriceDataByVariant::Riven(riven) => {
                    riven.owned_variants.insert(
                        riven_subtype
                            .ok_or_else(|| anyhow!("riven should always have subtypes"))?,
                        count,
                    );
                }
                PriceDataByVariant::Other(_) => (),
            }

            continue;
        }

        if let Some(relic_subtype) = relic_subtype {
            let price_data = price_data
                .map(|data| {
                    Ok((
                        match data.subtype {
                            Some(parse::Subtype::Relic(relic_subtype)) => relic_subtype,
                            _ => return Err(anyhow!("relic price data missing relic subtype")),
                        },
                        PriceData::from_parsed_lossy(data),
                    ))
                })
                .collect::<anyhow::Result<HashMap<_, _>>>()?;

            items.insert(
                name.clone(),
                Item {
                    name,
                    lotus_path,
                    count,
                    price_data: PriceDataByVariant::Relic(Relic {
                        owned_variants: HashMap::from([(relic_subtype, count)]),
                        price_data,
                    }),
                },
            );

            continue;
        }

        if let Some(fish_subtype) = fish_subtype {
            let price_data = price_data
                .map(|data| {
                    Ok((
                        match data.subtype {
                            Some(parse::Subtype::Fish(fish_subtype)) => fish_subtype,
                            _ => return Err(anyhow!("fish price data missing fish subtype")),
                        },
                        PriceData::from_parsed_lossy(data),
                    ))
                })
                .collect::<anyhow::Result<HashMap<_, _>>>()?;

            items.insert(
                name.clone(),
                Item {
                    name,
                    lotus_path,
                    count,
                    price_data: PriceDataByVariant::Fish(Fish {
                        owned_variants: HashMap::from([(fish_subtype, count)]),
                        price_data,
                    }),
                },
            );

            continue;
        }

        if let Some(riven_subtype) = riven_subtype {
            let price_data = price_data
                .map(|data| {
                    Ok((
                        match data.subtype {
                            Some(parse::Subtype::Riven(riven_subtype)) => riven_subtype,
                            _ => return Err(anyhow!("riven price data missing riven subtype")),
                        },
                        PriceData::from_parsed_lossy(data),
                    ))
                })
                .collect::<anyhow::Result<HashMap<_, _>>>()?;

            items.insert(
                name.clone(),
                Item {
                    name,
                    lotus_path,
                    count,
                    price_data: PriceDataByVariant::Riven(Riven {
                        owned_variants: HashMap::from([(riven_subtype, count)]),
                        price_data,
                    }),
                },
            );

            continue;
        }

        let price_data = if is_mod {
            PriceDataByVariant::Mod(Mod {
                owned_variants: HashSet::from([ModRank::Ranked(u8::MAX)]),
                price_data: price_data
                    .map(|data| {
                        (
                            data.mod_rank.map_or(ModRank::Rankless, ModRank::Ranked),
                            PriceData::from_parsed_lossy(data),
                        )
                    })
                    .collect(),
            })
        } else {
            PriceDataByVariant::Other(
                price_data
                    .map(PriceData::from_parsed_lossy)
                    .next()
                    .expect("already peeked previously"),
            )
        };

        items.insert(
            name.clone(),
            Item {
                name,
                lotus_path,
                count,
                price_data,
            },
        );
    }

    Ok(items.into_values().collect())
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
