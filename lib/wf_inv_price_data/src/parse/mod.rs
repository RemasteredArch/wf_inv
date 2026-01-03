// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::{collections::HashMap, marker::PhantomData};

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

#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq)]
#[serde(rename_all = "PascalCase")]
pub struct Inventory {
    pub misc_items: Box<[MiscItem]>,
    pub raw_upgrades: Box<[RawUpgrade]>,
    pub upgrades: Box<[Upgrade]>,
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

/// For example:
///
/// ```json
/// {
///     "UpgradeFingerprint": "{\"compat\":\"/Lotus/Weapons/Ostron/Melee/ModularMelee01/Tip/TipOne\",\"lim\":150972995,\"lvlReq\":11,\"pol\":\"AP_ATTACK\",\"buffs\":[{\"Tag\":\"WeaponMeleeRangeIncMod\",\"Value\":188159691},{\"Tag\":\"WeaponSlashDamageMod\",\"Value\":116638843}]}",
///     "ItemType": "/Lotus/Upgrades/Mods/Randomized/LotusModularMeleeRandomModRare",
///     "ItemId": {
///         "$oid": "642218d830953d4aec075daa"
///     }
/// }
/// ```
#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq)]
#[serde(rename_all = "PascalCase")]
pub struct Upgrade {
    #[serde(deserialize_with = "deserialize_json_str")]
    pub upgrade_fingerprint: UpgradeFingerprint,
    pub item_type: String,
    // There's also a `LastAdded` field (containing just an object ID) which I am choosing to
    // ignore.
}

fn deserialize_json_str<'de, D, T>(deserializer: D) -> Result<T, D::Error>
where
    D: serde::Deserializer<'de>,
    T: serde::de::DeserializeOwned,
{
    struct Visitor<T>(PhantomData<T>);

    impl<T: serde::de::DeserializeOwned> serde::de::Visitor<'_> for Visitor<T> {
        type Value = T;

        fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
            formatter.write_str("a string containing JSON")
        }

        fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
        where
            E: serde::de::Error,
        {
            serde_json::from_str(v).map_err(serde::de::Error::custom)
        }
    }

    deserializer.deserialize_str(Visitor(PhantomData::<T>))
}

#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq)]
#[serde(untagged)]
pub enum UpgradeFingerprint {
    /// A veiled and revealed Riven Mod. That is, a Riven Mod whose challenge is visible but not yet
    /// completed
    RevealedRiven(RevealedRiven),
    /// An unveiled Riven Mod. That is, a Riven Mod whose challenge has been completed and its stats
    /// are available.
    UnveiledRiven(UnveiledRiven),
    /// Any other kind of mod.
    Mod(Mod),
}

#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(rename_all = "camelCase")]
pub struct Mod {
    pub lvl: u8,
}

#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct RevealedRiven {
    // This is a well-formed structure, I could map it out, but I do not feel like doing that.
    pub challenge: serde_json::Value,
}

#[derive(Deserialize, Debug, Clone, Hash, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct UnveiledRiven {
    pub compat: String,
    pub lim: u64,
    pub lvl_req: u32,
    // Assume that the `rerolls` key being absent means that it just hasn't been rerolled yet.
    #[serde(default)]
    pub rerolls: u64,
    pub pol: String,
    // This is a well-formed structure, I could map it out, but I do not feel like doing that.
    pub buffs: Box<[serde_json::Value]>,
    // Assume that the `lvl` key being absent means that it just hasn't been ranked up yet.
    #[serde(default)]
    pub lvl: u32,
}
