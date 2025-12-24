use std::collections::HashMap;

use serde::Deserialize;

use crate::Count;

/// For example:
///
/// ```json
/// {
///     "Secura Dual Cestra": [
///         {
///             "datetime": "2025-08-20T00:00:00.000+00:00",
///             "volume": 9,
///             "min_price": 25,
///             "max_price": 35,
///             "open_price": 30,
///             "closed_price": 26,
///             "avg_price": 30.0,
///             "wa_price": 30.0,
///             "median": 30,
///             "moving_avg": 32.3,
///             "donch_top": 50,
///             "donch_bot": 20,
///             "id": "68a6618013a27d0015137b04",
///             "item_id": "54aae292e7798909064f1575",
///             "order_type": "closed"
///         },
///         {
///             "datetime": "2025-08-20T00:00:00.000+00:00",
///             "volume": 88,
///             "min_price": 8,
///             "max_price": 20,
///             "avg_price": 14.0,
///             "wa_price": 12.205,
///             "median": 15,
///             "order_type": "buy",
///             "moving_avg": 24.8,
///             "id": "68a6618013a27d0015137b09",
///             "item_id": "54aae292e7798909064f1575"
///         },
///         {
///             "datetime": "2025-08-20T00:00:00.000+00:00",
///             "volume": 111,
///             "min_price": 20,
///             "max_price": 65,
///             "avg_price": 42.5,
///             "wa_price": 36.423,
///             "median": 36.0,
///             "order_type": "sell",
///             "moving_avg": 30.3,
///             "id": "68a6618013a27d0015137b08",
///             "item_id": "54aae292e7798909064f1575"
///         }
///     ]
/// }
/// ```
#[derive(Deserialize, Debug, Clone)]
#[serde(transparent)]
pub struct PriceHistory {
    pub map: HashMap<String, Box<[PriceData]>>,
}

/// For example:
///
/// ```json
/// [
///     {
///         "datetime": "2025-08-20T00:00:00.000+00:00",
///         "volume": 9,
///         "min_price": 25,
///         "max_price": 35,
///         "open_price": 30,
///         "closed_price": 26,
///         "avg_price": 30.0,
///         "wa_price": 30.0,
///         "median": 30,
///         "moving_avg": 32.3,
///         "donch_top": 50,
///         "donch_bot": 20,
///         "id": "68a6618013a27d0015137b04",
///         "item_id": "54aae292e7798909064f1575",
///         "order_type": "closed"
///     },
///     {
///         "datetime": "2025-08-20T00:00:00.000+00:00",
///         "volume": 88,
///         "min_price": 8,
///         "max_price": 20,
///         "avg_price": 14.0,
///         "wa_price": 12.205,
///         "median": 15,
///         "order_type": "buy",
///         "moving_avg": 24.8,
///         "id": "68a6618013a27d0015137b09",
///         "item_id": "54aae292e7798909064f1575"
///     },
///     {
///         "datetime": "2025-08-20T00:00:00.000+00:00",
///         "volume": 111,
///         "min_price": 20,
///         "max_price": 65,
///         "avg_price": 42.5,
///         "wa_price": 36.423,
///         "median": 36.0,
///         "order_type": "sell",
///         "moving_avg": 30.3,
///         "id": "68a6618013a27d0015137b08",
///         "item_id": "54aae292e7798909064f1575"
///     }
/// ]
/// ```
#[derive(Deserialize, Debug, Clone)]
pub struct PriceData {
    // An extra field:
    //
    // ```rust
    // pub datetime: String,
    // ```
    pub volume: Count,
    /// This isn't actually a floating-point number. I have not observed any decimal portion other
    /// than `.0`, and it would not be reasonable for this data to not be an integer anyways. This
    /// is probably an artifact of the API being implemented in something float-based like
    /// JavaScript.
    pub min_price: f64,
    /// This isn't actually a floating-point number. I have not observed any decimal portion other
    /// than `.0`, and it would not be reasonable for this data to not be an integer anyways. This
    /// is probably an artifact of the API being implemented in something float-based like
    /// JavaScript.
    pub max_price: f64,
    // Some extra fields:
    //
    // ```rust
    // pub open_price: Option<u64>,
    // pub closed_price: Option<u64>,
    // pub avg_price: f64,
    // ```
    pub wa_price: f64,
    pub median: f64,
    // Some extra fields:
    //
    // ```rust
    // pub moving_avg: Option<f64>,
    // pub donch_top: Option<u64>,
    // pub donch_bot: Option<u64>,
    // pub id: String,
    // pub item_id: String,
    // ```
    pub order_type: OrderType,
    pub mod_rank: Option<u8>,
    pub subtype: Option<Subtype>,
}

#[derive(Deserialize, Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
pub enum OrderType {
    Closed,
    Buy,
    Sell,
}

#[derive(Deserialize, Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
#[serde(untagged)]
pub enum Subtype {
    Fish(crate::FishSubtype),
    Relic(crate::RelicSubtype),
    Craftable(CraftableSubtype),
    Riven(crate::RivenSubtype),
}

#[derive(Deserialize, Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "lowercase")]
pub enum CraftableSubtype {
    Blueprint,
    Crafted,
}

/// A parser struct for `../data/parser.json`. For example:
///
/// ```json
/// {
///     "/Lotus/Characters/Tenno/Accessory/Scarves/GrnBannerScarf/GrnBannerScarfItem": "Vanquished Banner",
///     "/Lotus/Characters/Tenno/Accessory/Scarves/PrimeScarfD/Cloth/PrimeScarfDItem": "Cycuta Prime Syandana",
///     "/Lotus/Characters/Tenno/Accessory/Scarves/U17IntermScarf/IridosUdyatSkin/UdyatPrimeGamingSyandana": "Udyat Iridos Syandana",
///     "/Lotus/Characters/Tenno/Accessory/Scarves/U17IntermScarf/U17IntermScarfItem": "Udyat Syandana"
/// }
/// ```
///
/// `parser.json` also contains map nodes, some of which have objects for values instead of strings.
/// This just outright skips over them, as map nodes are not relevant to this crate. This does not,
/// however, skip over map nodes whose values are strings.
#[derive(Debug, Clone)]
pub struct Parser {
    pub map: HashMap<String, String>,
}

impl<'de> Deserialize<'de> for Parser {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self {
            map: serde_json::Map::deserialize(deserializer)?
                .into_iter()
                .filter_map(|(k, v)| {
                    Some(Ok((
                        k,
                        match v {
                            serde_json::Value::String(s) => s,
                            // Assume that these are map nodes and move along.
                            serde_json::Value::Object(_) => return None,
                            _ => {
                                return Some(Err(serde::de::Error::custom(format!(
                                    "expected string, received `{v}`"
                                ))));
                            }
                        },
                    )))
                })
                .collect::<Result<HashMap<_, _>, _>>()?,
        })
    }
}

#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "PascalCase")]
pub struct Inventory {
    pub misc_items: Box<[MiscItem]>,
    pub raw_upgrades: Box<[RawUpgrade]>,
    // There are a great many fields which I am choosing to ignore.
}

/// For example:
///
/// ```json
/// {
///     "ItemCount": 257238,
///     "ItemType": "/Lotus/Types/Items/MiscItems/Rubedo"
/// }
/// ```
#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "PascalCase")]
pub struct MiscItem {
    pub item_count: Count,
    pub item_type: String,
}

/// For example:
///
/// ```json
/// {
///     "ItemCount": 150,
///     "LastAdded": {
///         "$oid": "6912e7e6c68feb3cfa09480f"
///     },
///     "ItemType": "/Lotus/Upgrades/Mods/Warframe/AvatarShieldMaxMod"
/// }
/// ```
#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "PascalCase")]
pub struct RawUpgrade {
    // `u64` is probably excessive, but that's fine.
    pub item_count: Count,
    pub item_type: String,
    // There's also a `LastAdded` field (containing just an object ID) which I am choosing to
    // ignore.
}
