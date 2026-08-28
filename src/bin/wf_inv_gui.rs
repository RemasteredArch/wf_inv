// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

#![windows_subsystem = "windows"]

use clap::Parser;
use wf_inv::settings::GuiArgs;

fn main() -> anyhow::Result<()> {
    let Arguments {
        args:
            GuiArgs {
                inventory_json,
                parse_args,
                display_args,
                ..
            },
    } = Arguments::parse(); // TO-DO: use `try_parse` and raise the error in a pop-up.

    wf_inv::gui::gui(inventory_json, parse_args, display_args)
}

#[derive(Parser, Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[command(about, version)]
#[non_exhaustive]
pub struct Arguments {
    #[command(flatten)]
    args: GuiArgs,
}
