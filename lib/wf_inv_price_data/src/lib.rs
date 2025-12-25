use std::{borrow::Cow, collections::HashMap};

use anyhow::{Result, anyhow};
use serde::{Deserialize, Serialize};

mod parse;

/// From <https://relics.run/export/parser.json>.
const PARSER: &str = include_str!("../data/parser.json");
/// From <https://relics.run/history/price_history_2025-12-21.json>.
const PRICE_HISTORY: &str = include_str!("../data/price_history_2025-12-21.json");

// TO-DO: this doesn't actually seem to be returning any relics.
/// Given the tradable items in the provided inventory and their pricing data.
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
    } = serde_json::from_reader(inventory_json)?;

    let misc_items = misc_items
        .into_iter()
        .map(|misc_item| (misc_item.item_type, misc_item.item_count));
    let raw_upgrades = raw_upgrades
        .into_iter()
        .map(|raw_upgrade| (raw_upgrade.item_type, raw_upgrade.item_count));

    for (is_mod, (lotus_path, count)) in misc_items.map(|item| (false, item)).chain(
        raw_upgrades
            .filter(|(lotus_path, _)| {
                // Skip flawed mods, as it appears warframe.market doesn't list those.
                //
                // There's also "expert" mods which would be parsed the same way. These correspond
                // to primed variants, and it appears that the parser does correctly prefix the name
                // with "primed" for every mod that has a primed variant. The parser also include
                // some "expert" mods whose names aren't prefixed with "primed," but none of these
                // appear to actually be real mods, so that shouldn't be an issue.
                !(lotus_path.contains("/Beginner/") && lotus_path.ends_with("Beginner"))
            })
            .map(|item| (true, item)),
    ) {
        add_or_update_item(&mut ctx, is_mod, lotus_path, count)?;
    }

    Ok(ctx.items.into_values().collect())
}

fn get_relic_subtype_and_maybe_strip_name(
    lotus_path: &str,
    name: &mut String,
) -> Option<RelicSubtype> {
    if !lotus_path.starts_with("/Lotus/Types/Game/Projections/") {
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

    let subtype = Subtype::detect_and_maybe_strip_name(is_mod, &lotus_path, &mut name);

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
    item.count += count;

    match (&mut item.price_data, subtype) {
        (PriceDataByType::Relic(relic), Subtype::Relic(relic_subtype)) => {
            relic.owned_subtypes.insert(relic_subtype, count);
        }
        // TO-DO: track owned variants.
        (PriceDataByType::Mod(r#mod), Subtype::Mod) => {
            r#mod.owned_ranks.insert(ModRank::Ranked(u8::MAX), count);
        }
        (PriceDataByType::Fish(fish), Subtype::Fish(fish_subtype)) => {
            fish.owned_subtypes.insert(fish_subtype, count);
        }
        // TO-DO: track revealed variants.
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
    Mod,
    // TO-DO: what about [`parse::Subtype::Crafted`]?
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
                        // section. Alternatively, do consider parsing unveiled rivens as well.
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

    fn name_to_price_history(self, name: &str) -> Cow<'_, str> {
        match self {
            Self::Riven(riven_subtype) if riven_subtype.is_veiled() => {
                format!("{name} (Veiled)").into()
            }
            _ => Cow::Borrowed(name),
        }
    }
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

/// The size (for fleshy fish) or quality (for robotic or hybrid fish) of a [fish][`Fish`].
///
/// See <https://wiki.warframe.com/w/Fishing#Products>.
#[derive(Debug, Copy, Clone, Deserialize, Serialize, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
pub enum FishSubtype {
    Small,
    Medium,
    Large,
    // I could separate out these types, but I do not care enough.
    /// The equivalent to [`Self::Small`] for robotic or hybrid fish.
    Basic,
    /// The equivalent to [`Self::Medium`] for robotic or hybrid fish.
    Adorned,
    /// The equivalent to [`Self::Large`] for robotic or hybrid fish.
    Magnificent,
}

/// The state of a [Riven Mod][`Riven`].
///
/// A Riven Mod whose challenge has been revealed (a "veiled" Riven Mod) or completed (an "unveiled"
/// Riven Mod) is considered "revealed" ([`Self::Revealed`] or [`Self::Unveiled`]), otherwise it is
/// considered "unrevealed" ([`Self::Unrevealed`], also a "veiled" Riven Mod). It is very important
/// to note that "(un)revealed" and "(un)veiled" are _not the same thing._ To match on either of
/// those, prefer to use [`Self::is_revealed`] or [`Self::is_veiled`] instead of `match`ing.
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
    /// This is considered a "veiled" and "revealed" Riven Mod. While both [`Self::Revealed`] and
    /// [`Self::Unveiled`] are considered "revealed," breaking out [`Self::Unveiled`] allows this
    /// one enum to represent both revealing and veiling. Prefer to use [`Self::is_revealed`] and
    /// [`Self::is_veiled`] for those purposes.
    Revealed,
    /// A Riven Mod whose challenge has completed.
    ///
    /// This is considered a "unveiled" and "revealed" Riven Mod. While both [`Self::Unveiled`] and
    /// [`Self::Revealed`] are considered "revealed," breaking out [`Self::Unveiled`] allows this
    /// one enum to represent both revealing and veiling. Prefer to use [`Self::is_revealed`] and
    /// [`Self::is_veiled`] for those purposes.
    Unveiled,
}

impl RivenSubtype {
    /// Whether or not this Riven Mod has had its challenge completed.
    ///
    /// This is _not_ the same thing as whether the challenge has been revealed or not, use
    /// [`Self::is_revealed`] for that.
    #[must_use]
    pub const fn is_veiled(self) -> bool {
        match self {
            Self::Unrevealed | Self::Revealed => true,
            Self::Unveiled => false,
        }
    }

    /// Whether or not this Riven Mod has had its challenge revealed.
    ///
    /// This is _not_ the same thing as whether the Riven Mod has been unveiled (its challenge
    /// completed), use [`Self::is_veiled`] for that.
    #[must_use]
    pub const fn is_revealed(self) -> bool {
        match self {
            Self::Unrevealed => false,
            Self::Revealed | Self::Unveiled => true,
        }
    }
}

/// A quantity of copies of a particular item or item subtype.
///
/// E.g., the quantity sold on a given day, the quantity owned by a given player, etc.
pub type Count = u64;

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
            Subtype::Mod => Self::Mod(Mod {
                owned_ranks: HashMap::from([(ModRank::Ranked(u8::MAX), count)]),
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
