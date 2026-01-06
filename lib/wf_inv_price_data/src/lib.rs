// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::{borrow::Cow, collections::HashMap};

use anyhow::{Result, anyhow};
use serde::{Deserialize, Serialize};

mod parse;

/// From <https://relics.run/export/parser.json>.
const PARSER: &str = include_str!("../data/parser.json");
/// From <https://relics.run/history/price_history_2025-12-21.json>.
const PRICE_HISTORY: &str = include_str!("../data/price_history_2025-12-21.json");

/// Get the tradable items in the provided inventory and their pricing data.
///
/// The inventory data must be the JSON from <https://mobile.warframe.com/api/inventory.php>.
///
/// # Errors
///
/// Returns an error if the data provided to this function is missing or unrecognized data.
///
/// Also returns errors if internal implementation details fail, but these are obviously considered
/// bugs (i.e., the blame is not the caller).
pub fn get_tradable_items(
    mut ctx: ParseContext,
    inventory_json: impl std::io::Read,
) -> Result<Box<[Item]>> {
    let parse::Inventory {
        misc_items,
        raw_upgrades,
        upgrades,
    } = serde_json::from_reader(inventory_json)?;

    // The `MiscItems` list does not contain mods or upgrade fingerprints.
    let misc_items = misc_items
        .into_iter()
        .map(|misc_item| (false, misc_item.item_type, misc_item.item_count, None));
    // The `RawUpgrades` list contains only mods but does not contain upgrade fingerprints.
    let raw_upgrades = raw_upgrades
        .into_iter()
        .map(|raw_upgrade| (true, raw_upgrade.item_type, raw_upgrade.item_count, None));
    // The `Upgrades` list contains only mods and their upgrade fingerprints.
    let upgrades = upgrades.into_iter().map(|upgrade| {
        (
            true,
            upgrade.item_type,
            1,
            Some(upgrade.upgrade_fingerprint),
        )
    });

    for (is_mod, lotus_path, count, upgrade_fingerprint) in
        misc_items.chain(raw_upgrades).chain(upgrades)
    {
        add_or_update_item(
            &mut ctx,
            is_mod,
            lotus_path,
            count,
            upgrade_fingerprint.as_ref(),
        )?;
    }

    Ok(ctx.items.into_values().collect())
}

/// Stores parsed items, pricing data, and translation lookups for use in
/// [parsing inventory data][`get_tradable_items`].
pub struct ParseContext {
    items: HashMap<String, Item>,
    history: HashMap<String, Box<[parse::PriceData]>>,
    parser: HashMap<String, String>,
}

impl ParseContext {
    /// Creates a [`Self`] based on the provided parser and price history data.
    ///
    /// One should prefer to use [`Self::from_embedded_data`], but this works if you need newer data
    /// than what is embedded. The embedded data is guaranteed to be valid and stable, whereas the
    /// API to pull new data from may at any point disappear or change its format.
    ///
    /// # Errors
    ///
    /// Returns an error if the parser data isn't a JSON file as produced
    /// <https://relics.run/export/parser.json> or if the price history data isn't produced in the
    /// same (JSON) format as <https://relics.run/history/price_history_2025-12-21.json>.
    pub fn new(parser: impl std::io::Read, price_history: impl std::io::Read) -> Result<Self> {
        let parse::Parser { map: parser } = serde_json::from_reader(parser)?;
        let parse::PriceHistory { map: history } = serde_json::from_reader(price_history)?;

        // Key is the name as used in the price history.
        let items: HashMap<String, Item> = HashMap::new();

        Ok(Self {
            items,
            history,
            parser,
        })
    }

    /// Creates a [`Self`] based on the provided parser.
    ///
    /// One should prefer to use [`Self::from_embedded_data`], but this works if you need newer data
    /// than what is embedded. The embedded data is guaranteed to be valid and stable, whereas the
    /// API to pull new data from may at any point disappear or change its format.
    ///
    /// See also [`Self::new`], where both the parser and pricing history are provided as arguments.
    ///
    /// # Errors
    ///
    /// Returns an error if the parser data isn't a JSON file as produced
    /// <https://relics.run/export/parser.json>.
    pub fn from_fresh_parser(parser: impl std::io::Read) -> Result<Self> {
        Self::new(parser, PRICE_HISTORY.as_bytes())
    }

    /// Creates a [`Self`] based on the provided price history data.
    ///
    /// One should prefer to use [`Self::from_embedded_data`], but this works if you need newer data
    /// than what is embedded. The embedded data is guaranteed to be valid and stable, whereas the
    /// API to pull new data from may at any point disappear or change its format.
    ///
    /// See also [`Self::new`], where both the parser and pricing history are provided as arguments.
    ///
    /// # Errors
    ///
    /// Returns an error if the price history data isn't produced in the same (JSON) format as
    /// <https://relics.run/history/price_history_2025-12-21.json>.
    pub fn from_fresh_price_history(price_history: impl std::io::Read) -> Result<Self> {
        Self::new(PARSER.as_bytes(), price_history)
    }

    /// Creates a [`Self`] based on the parser and price history data embedded within this crate.
    ///
    /// This function is reliable, but using [`Self::new`] would allow you to use newer data than
    /// what is embedded.
    #[must_use]
    pub fn from_embedded_data() -> Self {
        #[expect(
            clippy::missing_panics_doc,
            reason = "embedded data should be valid and this panic isn't public"
        )]
        Self::new(PARSER.as_bytes(), PRICE_HISTORY.as_bytes())
            .expect("only valid parser and price history data should be embedded")
    }
}

fn add_or_update_item(
    ctx: &mut ParseContext,
    is_mod: bool,
    lotus_path: String,
    count: Count,
    upgrade_fingerprint: Option<&parse::UpgradeFingerprint>,
) -> Result<()> {
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

    let subtype =
        Subtype::detect_and_maybe_strip_name(is_mod, &lotus_path, &mut name, upgrade_fingerprint);

    let Some(mut price_data) = ctx
        .history
        .get(subtype.name_to_price_history(&name).as_ref())
        .map(|price_data| {
            price_data
                .iter()
                .filter(|data| matches!(data.order_type, parse::OrderType::Closed))
                .peekable()
        })
    else {
        return Ok(());
    };
    // Assume that there is no price data available because there just isn't enough sold to find
    // data on actually closed sales. This makes the assumption that only data from closed sales is
    // worth considering, and that items with such low sales volumes aren't even worth selling.
    //
    // The assumptions that these conditions are (A) worth ignoring and (B) the only conditions that
    // could cause a [`None`] value are not necessarily bulletproof. I could be wrong here.
    //
    // TO-DO: are "closed" listings those which have been sold, or those which have been silently
    // taken off the market? Is this genuinely good data?
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
            price_data: PriceDataByType::new(subtype, count, price_data)?,
        },
    );

    Ok(())
}

fn increment_item_count(item: &mut Item, count: Count, subtype: Subtype) -> Result<()> {
    fn insert_mod_rank(r#mod: &mut Mod, count: Count, rank: ModRank) {
        if let Some(owned_count) = r#mod.owned_ranks.get_mut(&rank) {
            *owned_count += count;
        } else {
            r#mod.owned_ranks.insert(rank, count);
        }
    }

    item.count += count;

    match (&mut item.price_data, subtype) {
        (PriceDataByType::Relic(relic), Subtype::Relic(relic_subtype)) => {
            relic.owned_subtypes.insert(relic_subtype, count);
        }
        // Does not attempt to match [`ModRank`]s. That is, inserting a ranked subtype into an
        // unranked mod's owned subtypes will insert it despite the obvious conflict.
        (PriceDataByType::Mod(r#mod), Subtype::Mod(Some(mod_rank))) => {
            insert_mod_rank(r#mod, count, mod_rank);
        }
        (PriceDataByType::Mod(r#mod), Subtype::Mod(None)) => {
            // No need to insert anything for a rankless mod, all that's needed is the count
            // increase already performed.
            if !r#mod
                .owned_ranks
                .keys()
                .any(|mod_rank| matches!(mod_rank, ModRank::Rankless))
            {
                // Assumes that any mod that isn't rankless but which doesn't have a listed rank
                // will be rank zero.
                insert_mod_rank(r#mod, count, ModRank::Ranked(0));
            }
        }
        (PriceDataByType::Fish(fish), Subtype::Fish(fish_subtype)) => {
            fish.owned_subtypes.insert(fish_subtype, count);
        }
        (PriceDataByType::Riven(riven), Subtype::Riven(riven_subtype)) => {
            riven.owned_subtypes.insert(riven_subtype, count);
        }
        (PriceDataByType::Other(_), Subtype::Other) => (),
        (data, subtype) => {
            return Err(anyhow!(
                "expected matching subtypes, received `{data:?}` and `{subtype:?}`",
            ));
        }
    }

    Ok(())
}

#[derive(Debug, Clone, Copy, Deserialize, Serialize)]
enum Subtype {
    Relic(RelicSubtype),
    Fish(FishSubtype),
    Riven(RivenSubtype),
    Mod(Option<ModRank>),
    // TO-DO: what about [`parse::Subtype::Crafted`]?
    Other,
}

impl Subtype {
    fn detect_and_maybe_strip_name(
        is_mod: bool,
        lotus_path: &str,
        name: &mut String,
        upgrade_fingerprint: Option<&parse::UpgradeFingerprint>,
    ) -> Self {
        if let Some(relic_subtype) =
            RelicSubtype::try_from_inventory_and_maybe_strip_name(lotus_path, name)
        {
            return Self::Relic(relic_subtype);
        }

        if let Some(fish_subtype) = FishSubtype::try_from_inventory(lotus_path) {
            return Self::Fish(fish_subtype);
        }

        if let Some(riven_subtype) =
            RivenSubtype::try_from_inventory(lotus_path, upgrade_fingerprint)
        {
            return Self::Riven(riven_subtype);
        }

        if let Some(parse::UpgradeFingerprint::Mod(parse::Mod { lvl })) = upgrade_fingerprint {
            return Self::Mod(Some(ModRank::Ranked(*lvl)));
        }

        if is_mod {
            return Self::Mod(None);
        }

        Self::Other
    }

    fn name_to_price_history(self, name: &str) -> Cow<'_, str> {
        match self {
            Self::Riven(riven_subtype) if riven_subtype.is_veiled() => {
                format!("{name} (Veiled)").into()
            }
            _ => Cow::Borrowed(name),
        }
    }
}

/// An [`Item`] flattened into a consistent and easily printable format.
pub struct UniqueItem<'i> {
    /// The English display name of this item.
    ///
    /// For relics, this is stripped of tier names, e.g., `Meso T1 Relic` instead of
    /// `Meso T1 Relic Intact`.
    pub name: &'i str,
    /// The internal path to this item used by Warframe.
    ///
    /// For example, `/Lotus/Characters/Tenno/Accessory/Scarves/U17IntermScarf/U17IntermScarfItem`
    /// for the Udyat Syandana.
    pub lotus_path: &'i str,
    /// The type of this item, e.g., "relic" for a Void Relic.
    pub category: &'static str,
    /// The subtype of this item, e.g., "radiant" for a Radiant-tier Void Relic.
    pub subtype: &'static str,
    /// The number of copies of this item owned in total.
    pub count: Count,
    /// Indicates the other subtype of this [`Item`] used to represent this subtype's pricing data
    /// in lieu of pricing data specific to this subtype for [`Self::closest_subtype_price_data`].
    pub closest_subtype_with_price_data: &'static str,
    /// When the pricing data associated with an [`Item`] does not include data for this subtype, it
    /// will use pricing data from another subtype, the one considered closest. The subtype used is
    /// indicated by [`Self::closest_subtype_with_price_data`].
    ///
    /// For example, a [`Self`] that is a mod of rank ten, whose pricing data only includes the same
    /// mod of ranks zero, six, and eight will choose the rank eight data to represent the rank ten
    /// item owned. If there are both rank eight and twelve items, then it will choose whichever one
    /// has the largest trade volume (making the assumption that larger volumes are correlated with
    /// more reliable data).
    pub closest_subtype_price_data: &'i PriceData,
}

/// An item in Warframe and its recent [pricing data][`PriceDataByType`].
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
pub struct Item {
    name: String,
    lotus_path: String,
    count: Count,
    price_data: PriceDataByType,
}

impl Item {
    /// Get the English display name of this item.
    ///
    /// For relics, this is stripped of tier names, e.g., `Meso T1 Relic` instead of
    /// `Meso T1 Relic Intact`.
    #[must_use]
    pub const fn name(&self) -> &str {
        self.name.as_str()
    }

    /// Get Warframe's internal path to this item.
    ///
    /// For example, `/Lotus/Characters/Tenno/Accessory/Scarves/U17IntermScarf/U17IntermScarfItem`
    /// for the Udyat Syandana.
    #[must_use]
    pub const fn lotus_path(&self) -> &str {
        self.lotus_path.as_str()
    }

    /// Get the number of copies of this item owned in total.
    #[must_use]
    pub const fn count(&self) -> Count {
        self.count
    }

    /// Get the value of this item.
    #[must_use]
    pub const fn price_data(&self) -> &PriceDataByType {
        &self.price_data
    }

    #[must_use]
    pub fn flatten(&self) -> Box<[UniqueItem<'_>]> {
        let name = self.name();
        let lotus_path = self.lotus_path();

        match self.price_data() {
            PriceDataByType::Relic(relic) => relic
                .owned_subtypes()
                .iter()
                .map(|(subtype, &count)| {
                    let (closest_subtype_with_price_data, closest_subtype_price_data) =
                        closest_subtype_price_data(subtype, relic.price_data());

                    UniqueItem {
                        name,
                        lotus_path,
                        category: RelicSubtype::category(),
                        subtype: subtype.subtype(),
                        count,
                        closest_subtype_with_price_data,
                        closest_subtype_price_data,
                    }
                })
                .collect(),
            PriceDataByType::Mod(r#mod) => r#mod
                .owned_ranks()
                .iter()
                .map(|(rank, &count)| {
                    let (closest_subtype_with_price_data, closest_subtype_price_data) =
                        closest_subtype_price_data(rank, r#mod.price_data());
                    UniqueItem {
                        name,
                        lotus_path,
                        category: ModRank::category(),
                        subtype: rank.subtype(),
                        count,
                        closest_subtype_with_price_data,
                        closest_subtype_price_data,
                    }
                })
                .collect(),
            PriceDataByType::Fish(fish) => fish
                .owned_subtypes()
                .iter()
                .map(|(subtype, &count)| {
                    let (closest_subtype_with_price_data, closest_subtype_price_data) =
                        closest_subtype_price_data(subtype, fish.price_data());
                    UniqueItem {
                        name,
                        lotus_path,
                        category: FishSubtype::category(),
                        subtype: subtype.subtype(),
                        count,
                        closest_subtype_with_price_data,
                        closest_subtype_price_data,
                    }
                })
                .collect(),
            PriceDataByType::Riven(riven) => riven
                .owned_subtypes()
                .iter()
                .map(|(subtype, &count)| {
                    let (closest_subtype_with_price_data, closest_subtype_price_data) =
                        closest_subtype_price_data(subtype, riven.price_data());
                    UniqueItem {
                        name,
                        lotus_path,
                        category: RivenSubtype::category(),
                        subtype: subtype.subtype(),
                        count,
                        closest_subtype_with_price_data,
                        closest_subtype_price_data,
                    }
                })
                .collect(),
            PriceDataByType::Other(data) => [UniqueItem {
                name,
                lotus_path,
                category: "other",
                subtype: "other",
                count: self.count(),
                closest_subtype_with_price_data: "other",
                closest_subtype_price_data: data,
            }]
            .into(),
        }
    }
}

trait Flatten {
    /// A somewhat arbitrary valuing of the subtype of [`Self`], used in [`Self::subtype_distance`].
    /// Generally, lower values are the less desirable and less expensive subtypes.
    fn subtype_value(&self) -> u8;

    /// The distance between given subtypes, used to determine which other subtype's data should be
    /// used for a subtype when it does not have any pricing data of its own. Closer distances
    /// (smaller values) represent more alike subtypes.
    fn subtype_distance(&self, other: &Self) -> u8 {
        self.subtype_value().abs_diff(other.subtype_value())
    }

    /// The type or category of an item, e.g., "mod," as opposed to "fish."
    fn category() -> &'static str;

    /// The subtype of an item, e.g., "small," as opposed to "medium."
    fn subtype(&self) -> &'static str;
}

/// Panics if given an empty iterator.
fn closest_subtype_price_data<'i, F: std::hash::Hash + Eq + Flatten + 'i>(
    subtype: &'i F,
    price_data: &'i HashMap<F, PriceData>,
) -> (&'static str, &'i PriceData) {
    let (closest_subtype, data) = price_data.get(subtype).map_or_else(
        || {
            price_data
                .iter()
                .reduce(|(acc_subtype, acc_data), (data_subtype, price_data)| {
                    let acc_distance = subtype.subtype_distance(acc_subtype);
                    let data_distance = subtype.subtype_distance(data_subtype);

                    // Lower distances or equal distances with higher volumes (making the assumption that
                    // higher volumes are correlated with more certain pricing data) are better.
                    if acc_distance < data_distance
                        || (acc_distance == data_distance && acc_data.volume >= price_data.volume)
                    {
                        (acc_subtype, acc_data)
                    } else {
                        (data_subtype, price_data)
                    }
                })
                .expect("expected a non-empty iterator")
        },
        |price_data| (subtype, price_data),
    );

    (closest_subtype.subtype(), data)
}

/// The level of refinement of a [Void Relic][`Relic`].
///
/// See <https://wiki.warframe.com/w/Void_Relic#Refinement>.
#[derive(Debug, Copy, Clone, Deserialize, Serialize, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
pub enum RelicSubtype {
    Intact,
    Exceptional,
    Flawless,
    Radiant,
}

impl RelicSubtype {
    fn try_from_inventory_and_maybe_strip_name(
        lotus_path: &str,
        name: &mut String,
    ) -> Option<Self> {
        if !lotus_path.starts_with("/Lotus/Types/Game/Projections/") {
            return None;
        }

        [
            ("Bronze", " Intact", Self::Intact),
            ("Silver", " Exceptional", Self::Exceptional),
            ("Gold", " Flawless", Self::Flawless),
            ("Platinum", " Radiant", Self::Radiant),
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
}

impl Flatten for RelicSubtype {
    fn subtype_value(&self) -> u8 {
        match self {
            Self::Intact => 0,
            Self::Exceptional => 1,
            Self::Flawless => 2,
            Self::Radiant => 3,
        }
    }

    fn category() -> &'static str {
        "relic"
    }

    fn subtype(&self) -> &'static str {
        match self {
            Self::Intact => "intact",
            Self::Exceptional => "exceptional",
            Self::Flawless => "flawless",
            Self::Radiant => "radiant",
        }
    }
}

/// The size (for fleshy fish) or quality (for robotic or hybrid fish) of a [fish][`Fish`].
///
/// See <https://wiki.warframe.com/w/Fishing#Products>.
#[derive(Debug, Copy, Clone, Deserialize, Serialize, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
pub enum FishSubtype {
    Small,
    Medium,
    Large,
    // I could separate out these types from fleshy fish, but I do not care enough.
    /// The equivalent to [`Self::Small`] for robotic or hybrid fish.
    Basic,
    /// The equivalent to [`Self::Medium`] for robotic or hybrid fish.
    Adorned,
    /// The equivalent to [`Self::Large`] for robotic or hybrid fish.
    Magnificent,
}

impl FishSubtype {
    fn try_from_inventory(lotus_path: &str) -> Option<Self> {
        if !lotus_path.contains("/Fish/") || lotus_path.contains("/FishParts/") {
            return None;
        }

        [
            // For some reason, the ordering of "Item" and the size depends on the fish.
            ("ItemLarge", "LargeItem", Self::Large),
            ("ItemMedium", "MediumItem", Self::Medium),
            // For some reason, small fish aren't given a size.
            //
            // This will, unfortunately, also catch (ha!) boots, but they can't be traded so I do
            // not care. A regex hack could catch that, but I am not taking a regex dependency for a
            // non-issue.
            ("Item", "Item", Self::Small),
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
}

impl Flatten for FishSubtype {
    fn subtype_value(&self) -> u8 {
        match self {
            Self::Small | Self::Basic => 0,
            Self::Medium | Self::Adorned => 1,
            Self::Large | Self::Magnificent => 2,
        }
    }

    fn category() -> &'static str {
        "fish"
    }

    fn subtype(&self) -> &'static str {
        match self {
            Self::Small => "small",
            Self::Medium => "medium",
            Self::Large => "large",
            Self::Basic => "basic",
            Self::Adorned => "adorned",
            Self::Magnificent => "magnificent",
        }
    }
}

/// The state of a [Riven Mod][`Riven`].
///
/// A Riven Mod whose challenge has been revealed (a "veiled" Riven Mod) or completed (an "unveiled"
/// Riven Mod) is considered "revealed" ([`Self::Revealed`]), otherwise it is considered
/// "unrevealed" ([`Self::Unrevealed`], also a "veiled" Riven Mod). It is very important to note
/// that "(un)revealed" and "(un)veiled" are _not the same thing._ To match on either of those,
/// prefer to use [`Self::is_revealed`] or [`Self::is_veiled`] instead of `match`ing.
///
/// This does not represented unveiled Riven Mods. They are never present in the data (their unique
/// nature makes them auction items, not items with consistent and matchable prices), so there is no
/// purpose in making that state possible to represent.
///
/// See <https://wiki.warframe.com/w/Riven_Mods#States>.
#[derive(Debug, Copy, Clone, Deserialize, Serialize, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
pub enum RivenSubtype {
    /// A Riven Mod whose challenge has not been revealed or completed.
    ///
    /// This is considered a "veiled" and "unrevealed" Riven Mod.
    Unrevealed,
    /// A Riven Mod whose challenge has been revealed but not yet completed.
    ///
    /// This is considered a "veiled" and "revealed" Riven Mod. This is not an unveiled Riven Mod,
    /// that state is not represented.
    Revealed,
}

impl RivenSubtype {
    /// Whether or not this Riven Mod has had its challenge completed.
    ///
    /// This is _not_ the same thing as whether the challenge has been revealed or not, use
    /// [`Self::is_revealed`] for that.
    ///
    /// This currently always returns `true` (because [`Self`] does not currently represent unveiled
    /// Riven Mods), but this method is more semantically meaningful and resistant to breaking
    /// changes.
    #[must_use]
    pub const fn is_veiled(self) -> bool {
        true
    }

    /// Whether or not this Riven Mod has had its challenge revealed.
    ///
    /// This is _not_ the same thing as whether the Riven Mod has been unveiled (its challenge
    /// completed), use [`Self::is_veiled`] for that.
    #[must_use]
    pub const fn is_revealed(self) -> bool {
        match self {
            Self::Unrevealed => false,
            Self::Revealed => true,
        }
    }

    fn try_from_inventory(
        lotus_path: &str,
        upgrade_fingerprint: Option<&parse::UpgradeFingerprint>,
    ) -> Option<Self> {
        // The unrevealed Riven Mods are only present in the `RawUpgrades` section of the inventory,
        // but it's much easier to just use the same function for both.
        if lotus_path.starts_with("/Lotus/Upgrades/Mods/Randomized/Raw") {
            return Some(Self::Unrevealed);
        }

        // Notice the difference the last segment of the path --- unrevealed Riven Mods include
        // `Raw`, revealed (and unveiled) Riven Mods include `Lotus`.
        //
        // The revealed and unveiled Riven Mods are only present in the `Upgrades` section of the
        // inventory, but it's much easier to just use the same function for both.
        if lotus_path.starts_with("/Lotus/Upgrades/Mods/Randomized/Lotus")
            // Unveiled Riven Mods are not be present in the pricing data, so there is no point in
            // parsing for them.
            && matches!(
                upgrade_fingerprint?,
                parse::UpgradeFingerprint::RevealedRiven(_)
            )
        {
            return Some(Self::Revealed);
        }

        None
    }
}

impl Flatten for RivenSubtype {
    fn subtype_value(&self) -> u8 {
        match self {
            Self::Unrevealed => 1,
            Self::Revealed => 0,
        }
    }

    fn category() -> &'static str {
        "riven"
    }

    fn subtype(&self) -> &'static str {
        match self {
            Self::Unrevealed => "unrevealed",
            Self::Revealed => "revealed",
        }
    }
}

/// The rank of a [mod][`Mod`].
///
/// See <https://wiki.warframe.com/w/Mod#Attributes>.
#[derive(Debug, Copy, Clone, Deserialize, Serialize, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModRank {
    /// The rank of a mod that can be upgraded. The maximum value depends on the mod.
    Ranked(u8),
    /// A mod that doesn't have ranks and cannot be upgraded.
    ///
    /// This includes the legendary fusion core, but also more ordinary mods like Runtime.
    Rankless,
}

impl ModRank {
    // What `'static` will do to a codebase.
    const RANK_STRINGS: [&str; u8::MAX as usize + 1] = [
        "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11", "r12", "r13",
        "r14", "r15", "r16", "r17", "r18", "r19", "r20", "r21", "r22", "r23", "r24", "r25", "r26",
        "r27", "r28", "r29", "r30", "r31", "r32", "r33", "r34", "r35", "r36", "r37", "r38", "r39",
        "r40", "r41", "r42", "r43", "r44", "r45", "r46", "r47", "r48", "r49", "r50", "r51", "r52",
        "r53", "r54", "r55", "r56", "r57", "r58", "r59", "r60", "r61", "r62", "r63", "r64", "r65",
        "r66", "r67", "r68", "r69", "r70", "r71", "r72", "r73", "r74", "r75", "r76", "r77", "r78",
        "r79", "r80", "r81", "r82", "r83", "r84", "r85", "r86", "r87", "r88", "r89", "r90", "r91",
        "r92", "r93", "r94", "r95", "r96", "r97", "r98", "r99", "r100", "r101", "r102", "r103",
        "r104", "r105", "r106", "r107", "r108", "r109", "r110", "r111", "r112", "r113", "r114",
        "r115", "r116", "r117", "r118", "r119", "r120", "r121", "r122", "r123", "r124", "r125",
        "r126", "r127", "r128", "r129", "r130", "r131", "r132", "r133", "r134", "r135", "r136",
        "r137", "r138", "r139", "r140", "r141", "r142", "r143", "r144", "r145", "r146", "r147",
        "r148", "r149", "r150", "r151", "r152", "r153", "r154", "r155", "r156", "r157", "r158",
        "r159", "r160", "r161", "r162", "r163", "r164", "r165", "r166", "r167", "r168", "r169",
        "r170", "r171", "r172", "r173", "r174", "r175", "r176", "r177", "r178", "r179", "r180",
        "r181", "r182", "r183", "r184", "r185", "r186", "r187", "r188", "r189", "r190", "r191",
        "r192", "r193", "r194", "r195", "r196", "r197", "r198", "r199", "r200", "r201", "r202",
        "r203", "r204", "r205", "r206", "r207", "r208", "r209", "r210", "r211", "r212", "r213",
        "r214", "r215", "r216", "r217", "r218", "r219", "r220", "r221", "r222", "r223", "r224",
        "r225", "r226", "r227", "r228", "r229", "r230", "r231", "r232", "r233", "r234", "r235",
        "r236", "r237", "r238", "r239", "r240", "r241", "r242", "r243", "r244", "r245", "r246",
        "r247", "r248", "r249", "r250", "r251", "r252", "r253", "r254", "r255",
    ];
}

impl Flatten for ModRank {
    fn subtype_value(&self) -> u8 {
        match self {
            Self::Ranked(rank) => *rank,
            Self::Rankless => 0,
        }
    }

    fn category() -> &'static str {
        "mod"
    }

    fn subtype(&self) -> &'static str {
        match self {
            Self::Ranked(rank) => Self::RANK_STRINGS[*rank as usize],
            Self::Rankless => "rankless",
        }
    }
}

/// A quantity of copies of a particular item or item subtype.
///
/// E.g., the quantity sold on a given day, the quantity owned by a given player, etc.
pub type Count = u64;

/// Represents the price data of a given [item][`Item`].
///
/// Enumerated because some types of items have multiple subtypes that are priced differently.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
pub enum PriceDataByType {
    Relic(Relic),
    Mod(Mod),
    Fish(Fish),
    Riven(Riven),
    Other(PriceData),
}

impl PriceDataByType {
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
                    owned_subtypes: HashMap::from([($subtype_value, count)]),
                    price_data,
                })
            }};
        }

        let price_data = match subtype {
            Subtype::Relic(relic_subtype) => parse_matching!(Relic(relic_subtype), "relic"),
            Subtype::Fish(fish_subtype) => parse_matching!(Fish(fish_subtype), "fish"),
            Subtype::Riven(riven_subtype) => parse_matching!(Riven(riven_subtype), "riven"),
            Subtype::Mod(mod_rank) => {
                let price_data: HashMap<ModRank, PriceData> = price_data
                    .map(|data| {
                        (
                            data.mod_rank.map_or(ModRank::Rankless, ModRank::Ranked),
                            PriceData::from_parsed_lossy(data),
                        )
                    })
                    .collect();

                // The inventory data doesn't include ranks in the `RawUpgrade` list (which only
                // includes rankless or rank zero mods), so we have to extract whether an entry is
                // rankless or rank zero from the price data.
                let mod_rank = match mod_rank {
                    Some(mod_rank) => mod_rank,
                    None if price_data
                        .keys()
                        .any(|mod_rank| matches!(mod_rank, ModRank::Rankless)) =>
                    {
                        ModRank::Rankless
                    }
                    // Assumes that any mod that isn't rankless but which doesn't have a listed rank
                    // will be rank zero.
                    None => ModRank::Ranked(0),
                };

                Self::Mod(Mod {
                    owned_ranks: HashMap::from([(mod_rank, count)]),
                    price_data,
                })
            }
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

/// A [Void Relic](https://wiki.warframe.com/w/Void_Relic).
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
pub struct Relic {
    owned_subtypes: HashMap<RelicSubtype, Count>,
    price_data: HashMap<RelicSubtype, PriceData>,
}

impl Relic {
    /// Get the quantity of each subtype owned (i.e., present in the inventory data).
    #[must_use]
    pub const fn owned_subtypes(&self) -> &HashMap<RelicSubtype, Count> {
        &self.owned_subtypes
    }

    /// Get the pricing data available for each subtype of an item.
    ///
    /// Only includes those subtypes which actually have pricing data available.
    #[must_use]
    pub const fn price_data(&self) -> &HashMap<RelicSubtype, PriceData> {
        &self.price_data
    }
}

/// A [mod](https://wiki.warframe.com/w/Mod#Attributes).
///
/// This includes ordinary mods, e.g., [Fast Hands](https://wiki.warframe.com/w/Fast_Hands), but
/// also more exotic mods like [Fusion Cores](https://wiki.warframe.com/w/Fusion_Core). This does
/// not, however, include Riven Mods (despite them also being Mods), because those are already
/// covered by the [`Riven`] type.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
pub struct Mod {
    owned_ranks: HashMap<ModRank, Count>,
    price_data: HashMap<ModRank, PriceData>,
}

impl Mod {
    /// Get the quantity of each rank owned (i.e., present in the inventory data).
    #[must_use]
    pub const fn owned_rank(&self) -> &HashMap<ModRank, Count> {
        &self.owned_ranks
    }

    /// Get the pricing data available for each subtype of an item.
    ///
    /// Only includes those subtypes which actually have pricing data available.
    #[must_use]
    pub const fn price_data(&self) -> &HashMap<ModRank, PriceData> {
        &self.price_data
    }
}

/// A [fish](https://wiki.warframe.com/w/Fishing).
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
pub struct Fish {
    owned_subtypes: HashMap<FishSubtype, Count>,
    price_data: HashMap<FishSubtype, PriceData>,
}

impl Fish {
    /// Get the quantity of each subtype owned (i.e., present in the inventory data).
    #[must_use]
    pub const fn owned_subtypes(&self) -> &HashMap<FishSubtype, Count> {
        &self.owned_subtypes
    }

    /// Get the pricing data available for each subtype of an item.
    ///
    /// Only includes those subtypes which actually have pricing data available.
    #[must_use]
    pub const fn price_data(&self) -> &HashMap<FishSubtype, PriceData> {
        &self.price_data
    }
}

/// A [Riven Mod](https://wiki.warframe.com/w/Riven_Mods).
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq)]
pub struct Riven {
    owned_subtypes: HashMap<RivenSubtype, Count>,
    price_data: HashMap<RivenSubtype, PriceData>,
}

impl Riven {
    /// Get the quantity of each subtype owned (i.e., present in the inventory data).
    #[must_use]
    pub const fn owned_subtypes(&self) -> &HashMap<RivenSubtype, Count> {
        &self.owned_subtypes
    }

    /// Get the pricing data available for each subtype of an item.
    ///
    /// Only includes those subtypes which actually have pricing data available.
    #[must_use]
    pub const fn price_data(&self) -> &HashMap<RivenSubtype, PriceData> {
        &self.price_data
    }
}

/// Indicates that the given type is measuring[^1] in units of
/// [Platinum](https://wiki.warframe.com/w/Platinum).
///
/// [^1]: This is intended to be used with numeric types.
#[derive(Debug, Copy, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[repr(transparent)]
pub struct Platinum<T>(pub T);

/// Stores data about closed sales of some [item][`Item`] over the time period analyzed.
#[derive(Debug, Copy, Clone, Deserialize, Serialize, PartialEq)]
pub struct PriceData {
    volume: Count,
    wa_price: Platinum<f64>,
    min_price: Platinum<u64>,
    median: Platinum<f64>,
    max_price: Platinum<u64>,
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
            min_price: Platinum(data.min_price.round() as u64),
            #[expect(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                reason = "not expecting large or negative values"
            )]
            max_price: Platinum(data.max_price.round() as u64),
            wa_price: Platinum(data.wa_price),
            median: Platinum(data.median),
        }
    }

    // TO-DO: is it actually the quantity sold, or is it the number of closed transactions?
    /// Get the quantity of copies of this item sold over the time period analyzed.
    #[must_use]
    pub const fn volume(&self) -> Count {
        self.volume
    }

    // TO-DO: is this actually the unit price, or is it also artificially inflated by selling
    // multiple copies of an item per transaction?
    /// Get the weighted average unit price of closed sales of this item over the time period
    /// analyzed.
    #[must_use]
    pub const fn wa_price(&self) -> Platinum<f64> {
        self.wa_price
    }

    // TO-DO: is this actually the unit price, or is it also artificially inflated by selling
    // multiple copies of an item per transaction?
    /// Get the lowest unit price of any closed sale of this item over the time period analyzed.
    #[must_use]
    pub const fn min_price(&self) -> Platinum<u64> {
        self.min_price
    }

    // TO-DO: is this actually the unit price, or is it also artificially inflated by selling
    // multiple copies of an item per transaction?
    /// Get the median unit price of all closed sales of this item over the time period analyzed.
    #[must_use]
    pub const fn median(&self) -> Platinum<f64> {
        self.median
    }

    // TO-DO: is this actually the unit price, or is it also artificially inflated by selling
    // multiple copies of an item per transaction?
    /// Get the highest unit price of any closed sale of this item over the time period analyzed.
    #[must_use]
    pub const fn max_price(&self) -> Platinum<u64> {
        self.max_price
    }
}
