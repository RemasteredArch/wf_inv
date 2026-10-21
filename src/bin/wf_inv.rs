// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use clap::Parser;

fn main() -> anyhow::Result<()> {
    env_logger::init();

    wf_inv::try_panic_if_appimage_and_font_config_in_nix_store()?;

    wf_inv::settings::Arguments::parse().command.execute()
}
