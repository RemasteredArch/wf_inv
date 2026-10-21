# SPDX-License-Identifier: MPL-2.0
#
# Copyright © 2026 RemasteredArch
#
# This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
# copy of the Mozilla Public License was not distributed with this file, You can obtain one at
# <https://mozilla.org/MPL/2.0/>.
#
# First modified from
# <https://github.com/ipetkov/crane/blob/a1a1116/examples/quick-start-workspace/flake.nix>
# Copyright © 2022-2026 Ivan Petkov and crane contributors, MIT license.

{
    description = "Program to scan a Warframe process to analyze inventory data";

    inputs = {
        nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
        crane.url = "github:ipetkov/crane";
        flake-utils.url = "github:numtide/flake-utils";
        nix-appimage = {
            url = "github:ralismark/nix-appimage";
            inputs.nixpkgs.follows = "nixpkgs";
        };
    };

    outputs =
        {
            self,
            nixpkgs,
            crane,
            flake-utils,
            nix-appimage,
            ...
        }:
        flake-utils.lib.eachSystem [ "x86_64-linux" ] (
            system:
            let
                debug = false;

                pkgs = nixpkgs.legacyPackages.${system};
                inherit (pkgs) lib;
                craneLib = crane.mkLib pkgs;

                fileSetForCrate =
                    crate: extras:
                    lib.fileset.toSource {
                        root = ./.;
                        fileset = lib.fileset.unions (
                            [
                                ./Cargo.toml
                                ./Cargo.lock
                                (craneLib.fileset.commonCargoSources crate)

                                ./lib/wf_inv_price_data/data/items.json
                                ./lib/wf_inv_price_data/data/parser.json
                                ./lib/wf_inv_price_data/data/price_history.json
                                ./build/net.remasteredarch.wf_inv.png
                            ]
                            ++ extras
                        );
                    };

                # File set for the root of the workspace, such that it would cover `cargo clippy`
                # and friends run from the root.
                #
                # If a new crate output were to be added, it would use a more minimal file set.
                # Having a more minimal file set means that less rebuilds would be triggered by the
                # editing of unrelated files.
                src = fileSetForCrate ./. [ ];

                commonArgs =
                    let
                        runtimeDependencies = with pkgs; [
                            dbus.lib
                            libgcc
                            libxkbcommon

                            vulkan-loader
                            libGL

                            wayland

                            # X11-specific libraries.
                            libxi
                            libxcursor
                            libx11
                        ];
                    in
                    {
                        inherit src;
                        strictDeps = true;

                        buildInputs = [
                        ]
                        ++ runtimeDependencies;

                        nativeBuildInputs = with pkgs; [
                            pkg-config
                            autoPatchelfHook
                        ];

                        inherit runtimeDependencies;

                        CARGO_PROFILE = if debug then "" else null;
                    };

                # Build the workspace's dependencies to make building top-level crates faster with
                # caching.
                #
                # Would be made more effective by unifying dependency features using
                # [`cargo-hakari`](https://crates.io/crates/cargo-hakari).
                cargoArtifacts = craneLib.buildDepsOnly commonArgs;

                individualCrateArgs = commonArgs // {
                    inherit cargoArtifacts;
                    inherit (craneLib.crateNameFromCargoToml { inherit src; }) version;
                };

                # Anywhere this gets used would be joined by other crates if this workspace had more
                # than one non-rlib crate.
                wf_inv = craneLib.buildPackage (
                    individualCrateArgs
                    // {
                        pname = "wf_inv";
                        cargoExtraArgs = lib.strings.join " " (
                            let
                                features = [ "unstable-gui" ] ++ (lib.lists.optional debug "unstable-gui-debug");
                            in
                            [
                                "--package wf_inv"
                                ("--features " + lib.strings.join "," features)
                            ]
                        );

                        # TO-DO: make this the `install` step of a wrapper derivation to avoid
                        # having to rebuild the crate.
                        postInstall = ''
                            install -Dm755 \
                                ${./build/net.remasteredarch.wf_inv.desktop} \
                                ./build/net.remasteredarch.wf_inv.desktop
                            patch -p1 < ${./build/desktop_exec_path_nix.diff}
                            chmod 555 ./build/net.remasteredarch.wf_inv.desktop

                            install -Dm444 \
                                ./build/net.remasteredarch.wf_inv.png \
                                $out/share/icons/hicolor/128x128/apps/net.remasteredarch.wf_inv.png

                            mkdir -p $out/share/applications
                            substitute \
                                ./build/net.remasteredarch.wf_inv.desktop \
                                $out/share/applications/net.remasteredarch.wf_inv.desktop \
                                --subst-var out \
                                --subst-var APPIMAGE_VERSION \
                                --subst-var APPIMAGE_ARCH
                        '';

                        APPIMAGE_VERSION = individualCrateArgs.version;
                        # The QEMU architecture names aren't a perfect match for AppImageKit's
                        # expected architecture names (and it's not clear that's the list of
                        # architecture names to expect --- I really wish they documented this at
                        # all), but it does match on AArch64 and x86_64, which are the most
                        # important architectures for me to target.
                        APPIMAGE_ARCH = pkgs.stdenv.targetPlatform.qemuArch;
                    }
                );
            in
            {
                # Having the checks be different derivations makes it possible for users to build
                # the main output even if some checks fail.
                checks = {
                    # Just building the crates.
                    inherit wf_inv;

                    clippy = craneLib.cargoClippy (
                        commonArgs
                        // {
                            inherit cargoArtifacts;
                            cargoClippyExtraArgs = "--all-targets -- --deny warnings";
                        }
                    );

                    doc = craneLib.cargoDoc (
                        commonArgs
                        // {
                            inherit cargoArtifacts;
                            env.RUSTDOCFLAGS = "--deny warnings";
                        }
                    );

                    rust-formatting = craneLib.cargoFmt {
                        inherit src;
                    };
                };

                packages = {
                    inherit wf_inv;
                };

                apps = {
                    wf_inv =
                        flake-utils.lib.mkApp {
                            drv = wf_inv;
                        }
                        // {
                            meta.description = "Run the `wf_inv` CLI";
                        };

                    wf_inv_gui =
                        flake-utils.lib.mkApp {
                            drv = wf_inv;
                            name = "wf_inv_gui";
                        }
                        // {
                            meta.description = "Run the `wf_inv` GUI";
                        };
                };

                # E.g., `nix bundle --bundler .#toAppImage .#wf_inv`.
                bundlers = {
                    # TO-DO: the AppImage contains `systemd-minimal`. What in the world?
                    toAppImage = nix-appimage.bundlers.${system}.default;
                };

                # TO-DO: switch to [devshell](https://numtide.github.io/devshell/) over `nix-shell`?
                devShells.default = craneLib.devShell {
                    # Inherit inputs from checks --- allegedly.
                    checks = self.checks.${system};

                    # Extra developer tools, e.g., `pkgs.cargo-hakari`.
                    #
                    # Cargo and rustc are provided by default.
                    packages = [ ];
                };
            }
        );
}
