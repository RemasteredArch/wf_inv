// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::io::BufRead;

use crate::handle::PlatformHandle;

use super::Region;

pub(super) struct Regions {
    regions: std::vec::IntoIter<Region>,
}

impl Regions {
    pub fn new(handle: PlatformHandle) -> Self {
        let regions = parse_memory_mappings(handle)
            .unwrap()
            .into_iter()
            .map(Result::unwrap)
            .filter_map(
                |MemoryMapping {
                     addrs: std::range::Range { start, end },
                     readable,
                     ..
                 }| {
                    readable.then_some(Region {
                        addr: start,
                        size: end - start,
                        handle,
                    })
                },
            );
        Self {
            regions: regions.collect::<Vec<_>>().into_iter(),
        }
    }
}

impl Iterator for Regions {
    type Item = Region;

    fn next(&mut self) -> Option<Self::Item> {
        self.regions.next()
    }
}

pub(super) fn parse_memory_mappings(
    handle: PlatformHandle,
) -> std::io::Result<impl IntoIterator<Item = std::io::Result<MemoryMapping>>> {
    fn parse_line(line: String) -> std::io::Result<MemoryMapping> {
        fn invalid_data(message: String) -> std::io::Error {
            std::io::Error::new(std::io::ErrorKind::InvalidData, message)
        }

        fn split_mapping(line: &str, pat: char) -> Result<(&str, &str), std::io::Error> {
            line.split_once(pat).ok_or_else(move || {
                invalid_data(
                    format!(
                        "expected mapping line in format `START_ADDR-END_ADDR PERMISSIONS ...`, got: {line}",
                    ),
                )
            })
        }
        let (start_addr, rest) = split_mapping(&line, '-')?;
        let (end_addr, rest) = split_mapping(rest, ' ')?;
        let (permissions, _) = split_mapping(rest, ' ')?;

        let permission_error = || {
            invalid_data(format!(
                "expected permissions string in the format `rwx_`, where `rwx` may each be `-` and `_` is `p` or `s`, got {permissions}",
            ))
        };
        let check_permission = |idx: usize, char: u8| {
            permissions
                // Well-formed permission will always be ASCII, so using `as_bytes` is just fine.
                .as_bytes()
                .get(idx)
                .filter(|&&byte| byte == char || byte == b'-')
                .map(|&byte| byte == char)
                .ok_or_else(permission_error)
        };
        let readable = check_permission(0, b'r')?;
        let writable = check_permission(1, b'w')?;
        let executable = check_permission(2, b'x')?;
        // Wait to error out until checking that it's not private.
        let shared = check_permission(3, b's').unwrap_or(false);
        let private = !shared && check_permission(3, b'p')?;
        let change_visibility = if shared {
            MemoryMappingChangeVisibility::Shared
        } else if private {
            MemoryMappingChangeVisibility::Private
        } else {
            return Err(permission_error());
        };

        let parse_hex_addr = |addr| {
            usize::from_str_radix(addr, 16)
                .map_err(|_| invalid_data(format!("expected hexadecimal address, got {addr}")))
        };
        let start_addr = parse_hex_addr(start_addr)?;
        let end_addr = parse_hex_addr(end_addr)?;

        Ok(MemoryMapping {
            addrs: std::range::Range {
                start: start_addr,
                end: end_addr,
            },
            readable,
            writable,
            executable,
            change_visibility,
            line,
        })
    }

    Ok(
        std::io::BufReader::new(std::fs::File::open(format!("/proc/{}/maps", handle.0))?)
            .lines()
            .map(|r| r.and_then(parse_line)),
    )
}

pub(super) struct MemoryMapping {
    pub addrs: std::range::Range<usize>,
    pub readable: bool,
    pub writable: bool,
    pub executable: bool,
    pub change_visibility: MemoryMappingChangeVisibility,
    pub line: String,
}

pub(super) enum MemoryMappingChangeVisibility {
    /// Mappings whose changes are visible to everyone.
    Shared,
    /// Mappings that copy on write to hide changes from everyone else.
    Private,
}
