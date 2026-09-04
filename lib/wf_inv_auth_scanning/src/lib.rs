// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2025-2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

#![cfg(windows)]

use std::{collections::HashMap, ffi, fmt::Display, ops::Range, str::Utf8Error, sync::LazyLock};

use windows::Win32::{
    Foundation,
    System::{Diagnostics::Debug, Memory},
};

mod process;
mod scanner;

pub use process::Process;

fn panic_on_last_error() {
    let error = unsafe { windows::Win32::Foundation::GetLastError() };
    panic!("{error:?}");
}

/// A [`Sized`] and stack-allocated equivalent to [`str`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ArrayStr<const LEN: usize>([u8; LEN]);

impl<const LEN: usize> ArrayStr<LEN> {
    pub const fn new(str: [u8; LEN]) -> Result<Self, Utf8Error> {
        match str::from_utf8(&str) {
            Ok(_) => Ok(Self(str)),
            Err(e) => Err(e),
        }
    }
}

impl<const LEN: usize> AsRef<str> for ArrayStr<LEN> {
    fn as_ref(&self) -> &str {
        // Safety: [`Self::new`] checks that [`Self::0`] is valid UTF-8.
        unsafe { str::from_utf8_unchecked(&self.0) }
    }
}

impl<const LEN: usize> Display for ArrayStr<LEN> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Login {
    account_id: ArrayStr<{ Self::ACCOUNT_ID_LEN }>,
    token: Box<str>,
}

impl Login {
    const ACCOUNT_ID_LEN: usize = 24;

    /// Returns a fake set of credentials for use in testing and demos. Do not ever actually try to
    /// make an inventory request with these!
    #[must_use]
    pub fn fake() -> Self {
        const FAKE_ID: ArrayStr<{ Login::ACCOUNT_ID_LEN }> = {
            match ArrayStr::new(*b"wf_inv_test_id__________") {
                Ok(id) => id,
                Err(_) => panic!("test ID is invalid"),
            }
        };
        const FAKE_TOKEN: &str = "wf_inv_test_token";

        Self {
            account_id: FAKE_ID,
            token: FAKE_TOKEN.into(),
        }
    }

    /// Returns the account ID.
    #[must_use]
    pub fn account_id(&self) -> &str {
        self.account_id.as_ref()
    }

    /// Returns the authentication token (or "nonce") of the account.
    ///
    /// This is comprised of only [ASCII digits].
    ///
    /// [ASCII digits]: `char::is_ascii_digit`
    #[must_use]
    pub fn token(&self) -> &str {
        self.token.as_ref()
    }

    /// Formats [`Self`] as the authenticated URL to fetch the inventory data from
    /// <https://mobile.warframe.com/api/inventory.php>.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let query = login.to_api_url();
    /// assert!(
    ///     query.starts_with("https://mobile.warframe.com/api/inventory.php?accountId=")
    ///         && query.contains("&nonce="),
    /// );
    /// let inventory_json = your_request_fn(url)?;
    /// ```
    #[must_use]
    pub fn to_api_url(&self) -> String {
        format!(
            "https://mobile.warframe.com/api/inventory.php?accountId={}&nonce={}",
            self.account_id(),
            self.token(),
        )
    }

    /// Checks whether the [`Self`] is from [`Self::fake`].
    ///
    /// Can be used to avoid performing real operations with fake credentials.
    #[must_use]
    pub fn is_fake(&self) -> bool {
        static FAKE_LOGIN: LazyLock<Login> = LazyLock::new(Login::fake);

        self == &*FAKE_LOGIN
    }
}
