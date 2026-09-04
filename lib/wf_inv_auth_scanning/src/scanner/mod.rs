// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

#[cfg(windows)]
mod windows;

use std::{collections::HashMap, fmt::Debug};

use crate::{
    Login,
    handle::{Handle, PlatformHandle},
};

#[cfg(windows)]
use windows::Regions as PlatformRegions;

pub struct LoginScanner {
    handle: PlatformHandle,
}

impl LoginScanner {
    /// Construct a [`Self`] targeting a Warframe [process][`crate::Process`].
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let Some(process) = Process::find_by_executable_name("Warframe.x64.exe") else {
    ///     panic!("Could not find Warframe's process!");
    /// };
    ///
    /// let auth = LoginScanner::from_process(&process)
    ///     .find_auth()
    ///     .expect("no login found!");
    ///
    /// println!("{}", auth.to_api_url());
    /// ```
    #[must_use]
    pub const fn from_process(process: &crate::Process) -> Self {
        Self {
            handle: process.handle(),
        }
    }

    /// Scan the Warframe process's memory for a [`Login`].
    #[must_use]
    pub fn find_auth(&self) -> Option<Login> {
        const ACCOUNT_ID_PREFIX: [u8; 11] = *b"?accountId=";
        const TOKEN_PREFIX: [u8; 7] = *b"&nonce=";

        println!("Starting search");

        let regions = PlatformRegions::new(self.handle);
        let mut candidates = HashMap::<Login, usize>::new();

        for region in regions {
            let Some(mut addr) = region.scan(&ACCOUNT_ID_PREFIX) else {
                continue;
            };

            // TO-DO: is this check even necessary? Consider either removing or making it an actual
            // error instead of a panic. It's notable that it can also fail for reasons other than
            // incorrect code from this crate --- if that region of memory were to change between
            // scanning and reading it again, this could actually fail. It's unlikely, but possible.
            // Doing this check doesn't really protect against that, though, because that problem
            // could occur between this check and future reads (just like it can occur between the
            // scan and this check).
            #[expect(clippy::missing_panics_doc, reason = "just a sanity check")]
            {
                // Sanity check that the scan _did_ match on the correct string.
                assert_eq!(
                    region.read(addr),
                    Some(ACCOUNT_ID_PREFIX),
                    "the address returned by a scanner should contain the pattern scanned for",
                );
            }
            // Skip past the matched string.
            addr += ACCOUNT_ID_PREFIX.len();

            // Check that the account ID prefix and account ID are followed by the token prefix.
            let token_prefix: [u8; TOKEN_PREFIX.len()] =
                region.read(addr + Login::ACCOUNT_ID_LEN).unwrap();
            if token_prefix != TOKEN_PREFIX {
                println!("real {token_prefix:?} != expected {TOKEN_PREFIX:?}, skipping");
                continue;
            }

            // Actually read the account ID.
            let account_id: [u8; Login::ACCOUNT_ID_LEN] = region.read(addr).unwrap();
            addr += Login::ACCOUNT_ID_LEN + TOKEN_PREFIX.len();

            // Actually read the token.
            let mut token = Vec::new();
            loop {
                let char: u8 = region.read(addr).unwrap();
                addr += 1;

                // TO-DO: arbitrary memory can occasionally just have bytes that correspond to ASCII
                // digits, so this is fragile. Consider investigating whether tokens are fixed
                // length and could be parsed like the account ID.
                if !char.is_ascii_digit() {
                    break;
                }

                token.push(char);
            }

            let login = Login {
                account_id: crate::ArrayStr::new(account_id).unwrap(),
                token: str::from_utf8(token.as_slice())
                    .expect("`token` should only have ascii numerics")
                    .into(),
            };

            // If this login has shown up twice already, assume it's the correct one and return it.
            if let Some(count) = candidates.get_mut(&login) {
                if *count == 2 {
                    return Some(login);
                }

                *count += 1;
            } else {
                candidates.insert(login, 1);
            }
        }

        None
    }
}

#[derive(Debug)]
struct Region {
    addr: usize,
    size: usize,
    handle: PlatformHandle,
}

impl Region {
    #[must_use]
    pub const fn to_range(&self) -> std::ops::Range<usize> {
        self.addr..(self.addr + self.size)
    }

    #[must_use]
    pub fn read<T: Sized>(&self, addr: usize) -> Option<T> {
        let range = self.to_range();
        if !range.contains(&addr) || !range.contains(&(addr + size_of::<T>())) {
            return None;
        }

        unsafe {
            let mut data: T = std::mem::zeroed();

            self.handle
                .raw_read(addr, (&raw mut data).cast(), size_of::<T>())
                .ok()
                .map(|()| data)
        }
    }

    #[must_use]
    pub fn buffer(&self) -> Vec<u8> {
        // Buffer must be under the impression that it's of the correct size, so we initialize it
        // with zeros before even filling it with the correct data.
        let mut buffer = vec![0; self.size];
        unsafe {
            self.handle
                .raw_read(self.addr, buffer.as_mut_ptr(), self.size)
                .unwrap_or_else(|error| {
                    panic!("Reading region {self:?} failed: {error}");
                });
        }

        buffer
    }

    #[must_use]
    pub fn scan(&self, pattern: &[u8]) -> Option<usize> {
        let buffer = self.buffer();

        for buffer_addr in 0..buffer.len() {
            let Some(subslice) = buffer.get(buffer_addr..(buffer_addr + pattern.len())) else {
                break;
            };

            if subslice == pattern {
                return Some(self.addr + buffer_addr);
            }
        }

        None
    }
}

// Sanity check that the required methods are present and have the correct signature.
const _: fn(&crate::Process) -> LoginScanner = LoginScanner::from_process;
const _: fn(&LoginScanner) -> Option<crate::Login> = LoginScanner::find_auth;
const _: fn(&mut PlatformRegions) -> Option<Region> = <PlatformRegions as Iterator>::next;
