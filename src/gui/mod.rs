// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::fmt::Display;
use std::sync::{Arc, OnceLock};

use anyhow::Context;
use iced::{
    Center, Element, Task,
    widget::{
        button, center_x, center_y, checkbox, column, container, pick_list, row, scrollable, text,
        toggler,
    },
};

mod thread;

macro_rules! bc {
    ($content:expr) => {
        container($content).style(|theme| container::bordered_box(theme))
    };
}

type ActionResult<T> = Result<T, Arc<anyhow::Error>>;

pub fn gui(
    inventory_json: Option<std::path::PathBuf>,
    parse_args: crate::settings::ParseArgs,
    print_args: crate::settings::PrintArgs,
) -> anyhow::Result<()> {
    static CLI_SETTINGS: OnceLock<(
        Option<std::path::PathBuf>,
        crate::settings::ParseArgs,
        crate::settings::PrintArgs,
    )> = OnceLock::new();

    if CLI_SETTINGS
        .set((inventory_json, parse_args, print_args))
        .is_err()
    {
        eprintln!(
            "warning: tried to set global CLI settings more than once (ignoring new settings)"
        );
    }

    iced::application(
        || {
            let (
                inventory_json,
                crate::settings::ParseArgs {
                    price_data_json,
                    parser_json,
                    item_list_json,
                },
                print_settings,
            ) = CLI_SETTINGS.get().unwrap();

            let into_handle = |maybe_path: &Option<std::path::PathBuf>| -> Option<rfd::FileHandle> {
                maybe_path.as_ref().map(|path| path.clone().into())
            };

            (
                Gui::default(),
                Task::batch(
                    [
                        Message::PrintSettingsChanged(print_settings.clone()),
                        Message::FileChanged(File::InventoryJson, into_handle(inventory_json)),
                        Message::FileChanged(File::PriceDataJson, into_handle(price_data_json)),
                        Message::FileChanged(File::ParserJson, into_handle(parser_json)),
                        Message::FileChanged(File::ItemListJson, into_handle(item_list_json)),
                    ]
                    .map(Task::done),
                ),
            )
        },
        Gui::update,
        Gui::view,
    )
    .title(env!("CARGO_CRATE_NAME"))
    .run()?;

    Ok(())
}

#[derive(Default)]
struct Gui {
    action: Action,
    is_action_pending: bool,
    inventory_json: DialogSelectable<rfd::FileHandle>,
    parse_result: Option<Result<crate::table::Table, Box<str>>>,
    is_parse_result_stale: bool,
    // TO-DO: store results for `Action::Parse` and `Action::All` separately.
    parse_result_source: Action,
    scan_result: Option<Result<wf_inv_auth_scanning::Login, Box<str>>>,
    is_scan_result_stale: bool,
    print_args: crate::settings::PrintArgs,
    price_data_json: DialogSelectable<rfd::FileHandle>,
    parser_json: DialogSelectable<rfd::FileHandle>,
    item_list_json: DialogSelectable<rfd::FileHandle>,
}

impl Gui {
    fn update(&mut self, message: Message) -> Task<Message> {
        match message {
            Message::FileChanged(_, _)
            | Message::OpenFile(_)
            | Message::PrintSettingsChanged(_) => self.is_parse_result_stale = true,
            _ => (),
        }

        match message {
            Message::ActionChanged(action) => self.action = action,
            Message::OpenFile(file) => return file.launch_dialog(self),
            Message::FileChanged(file, maybe_handle) => {
                *self.get_file_mut(file) = maybe_handle.into();
            }
            Message::PrintSettingsChanged(settings) => {
                self.print_args = settings;
            }
            Message::CopyToClipboard(text) => return iced::clipboard::write(text.into()),
            Message::Parse(handle) => {
                let reader = match std::fs::File::open(handle.path()) {
                    Ok(v) => std::io::BufReader::new(v),
                    Err(err) => {
                        return Task::done(Message::FinishedParsing(Err(Arc::new(
                            anyhow::Error::from(err)
                                .context("failed to open provided inventory JSON file"),
                        ))));
                    }
                };
                return self.parse_inventory_in_thread(reader);
            }
            Message::FinishedParsing(result) => {
                self.parse_result = Some(result.map_err(|err| format!("Error: {err}").into()));
                self.is_action_pending = false;
            }
            Message::Scan => return self.scan_in_thread(),
            Message::FinishedScanning(result) => {
                self.scan_result =
                    Some(result.clone().map_err(|err| format!("Error: {err}").into()));

                if self.is_action_pending {
                    if matches!(self.action, Action::All) {
                        match result {
                            Ok(login) => return thread::fetch_in_thread(login),
                            Err(err) => return Task::done(Message::FinishedFetching(Err(err))),
                        }
                    }

                    self.is_action_pending = false;
                }
            }
            Message::ScanAndParse => {
                self.is_action_pending = true;
                return Task::done(Message::Scan);
            }
            Message::FinishedFetching(result) => {
                let inventory_json = match result {
                    Ok(inventory_json) => inventory_json,
                    Err(err) => return Task::done(Message::FinishedParsing(Err(err))),
                };

                return self.parse_inventory_in_thread(std::io::Cursor::new(inventory_json));
            }
        }

        Task::none()
    }

    fn view(&self) -> Element<'_, Message> {
        let choose_inventory_json = if matches!(self.action, Action::Parse) {
            Some(bc!(self
                .inventory_json
                .to_labeled_button(
                    "Choose the inventory JSON file to parse",
                    |handle| text(handle.file_name()),
                    button::primary,
                    if self.is_action_pending {
                        None
                    } else {
                        Some(Message::OpenFile(File::InventoryJson))
                    },
                )
                .spacing(10)
                .padding(10)))
        } else {
            None
        };

        let content = column![
            self.action_selector(),
            choose_inventory_json,
            self.settings(),
            self.action_bar(),
            self.action_result(),
        ]
        .spacing(10)
        .padding(50);

        center_y(center_x(content)).into()
    }

    fn action_selector(&self) -> container::Container<'_, Message> {
        bc!(column![
            text("Action:"),
            pick_list(
                if self.is_action_pending {
                    match self.action {
                        Action::All => &[Action::All][..],
                        Action::Scan => &[Action::Scan][..],
                        Action::Parse => &[Action::Parse][..],
                    }
                } else {
                    &[Action::All, Action::Scan, Action::Parse][..]
                },
                Some(&self.action),
                Message::ActionChanged,
            )
        ]
        .spacing(10)
        .padding(10))
    }

    fn action_bar(&self) -> container::Container<'_, Message> {
        bc!(row![
            self.action_button(),
            self.copy_result_button(),
            self.stale_result_warning()
        ]
        .spacing(10)
        .height(iced::Length::Shrink))
        .padding(10)
    }

    fn action_button(&self) -> button::Button<'_, Message> {
        let button = button(self.action.short_name()).style(button::primary);

        if self.is_action_pending {
            button
        } else {
            match self.action {
                Action::Parse
                    if let DialogSelectable::Selected(handle) = self.inventory_json.as_ref() =>
                {
                    button.on_press_with(|| Message::Parse(handle.clone()))
                }
                Action::Parse => button,
                Action::Scan => button.on_press(Message::Scan),
                Action::All => button.on_press(Message::ScanAndParse),
            }
        }
        .padding(10)
    }

    fn copy_result_button(&self) -> Option<button::Button<'_, Message>> {
        if matches!(self.action, Action::Scan)
            && let Some(Ok(result)) = &self.scan_result
        {
            Some(
                button(center_y("\u{1F5CF} Copy result"))
                    .style(button::secondary)
                    .on_press(Message::CopyToClipboard(result.to_api_url().into()))
                    .padding(iced::Padding::default().vertical(5.0).horizontal(8.0))
                    .height(iced::Length::Fill),
            )
        } else {
            None
        }
    }

    fn stale_result_warning(&self) -> Option<container::Container<'_, Message>> {
        if !(self.parse_result.is_some()
            && self.is_parse_result_stale
            && self.parse_result_source == self.action)
        {
            return None;
        }

        Some(
            // The first Unicode character is the "circled information source."
            container("\u{1F6C8} Your settings have changed since this result was generated")
                .style(|theme: &iced::Theme| {
                    let warning = theme.extended_palette().warning;
                    let mut style = container::bordered_box(theme)
                        .color(warning.base.text)
                        .background(iced::Background::Color(warning.base.color));
                    style.border = style.border.color(warning.strong.color);
                    style
                })
                .padding(iced::Padding::default().vertical(5.0).horizontal(8.0))
                .height(iced::Length::Fill)
                .align_y(Center),
        )
    }

    fn settings(&self) -> Option<container::Container<'_, Message>> {
        if !matches!(self.action, Action::All | Action::Parse) {
            return None;
        }

        let bool_button = |name: &'static str,
                           is_checked: bool,
                           is_enabled: bool,
                           change: fn(&mut crate::settings::PrintArgs)| {
            let button = checkbox(is_checked);
            row![
                if is_enabled {
                    button.on_toggle(move |_| {
                        let mut new = self.print_args.clone();
                        change(&mut new);
                        Message::PrintSettingsChanged(new)
                    })
                } else {
                    button
                },
                name,
            ]
            .align_y(Center)
            .spacing(10)
        };

        macro_rules! bool {
            ($name:expr, $field:ident) => {
                bool_button(
                    $name,
                    self.print_args.$field,
                    !self.is_action_pending,
                    |print_args| print_args.$field ^= true,
                )
            };
        }

        macro_rules! file {
            ($name:literal, $field:ident, $file:ident) => {
                self.$field
                    .to_labeled_button(
                        concat!("Choose fresher ", $name, " JSON file (optional)"),
                        |handle| text(handle.file_name()),
                        button::secondary,
                        if self.is_action_pending {
                            None
                        } else {
                            Some(Message::OpenFile(File::$file))
                        },
                    )
                    .spacing(10)
            };
        }

        Some(bc!(column![
            "Display settings:",
            bool!("Group items by subtype", group_subtypes),
            bool!("Show all fields", verbose),
            bool!("Show Ducat valuation", ducat_valuation),
            "Parsing settings:",
            file!("price data", price_data_json, PriceDataJson),
            file!("parser", parser_json, ParserJson),
            file!("item list", item_list_json, ItemListJson),
        ]
        .spacing(10)
        .padding(10)))
    }

    fn action_result(&self) -> Option<container::Container<'_, Message>> {
        match self.action {
            _ if self.is_action_pending => Some(iced_aw::Spinner::new().into()),
            Action::Parse | Action::All => {
                if self.parse_result_source == self.action {
                    self.parse_result.as_ref().map(|result| match result {
                        Ok(table) => table.to_element(),
                        Err(e) => text!("Error: {e}").into(),
                    })
                } else {
                    None
                }
            }
            Action::Scan => self.scan_result.as_ref().map(|result| match result {
                Ok(login) => text(login.to_api_url()).font(iced::Font::MONOSPACE).into(),
                Err(e) => text!("Error: {e}").into(),
            }),
        }
        .map(|result| bc!(result).padding(10))
    }

    const fn get_file_mut(&mut self, file: File) -> &mut DialogSelectable<rfd::FileHandle> {
        match file {
            File::InventoryJson => &mut self.inventory_json,
            File::PriceDataJson => &mut self.price_data_json,
            File::ParserJson => &mut self.parser_json,
            File::ItemListJson => &mut self.item_list_json,
        }
    }

    fn parse_inventory_in_thread(
        &mut self,
        inventory_json: impl std::io::Read + Send + 'static,
    ) -> Task<Message> {
        // Already being in the midst of an action means this is last step of `Action::All`, not an
        // independent parse.
        self.parse_result_source = if self.is_action_pending {
            Action::All
        } else {
            Action::Parse
        };

        self.parse_result = None;
        self.is_parse_result_stale = false;
        self.is_action_pending = true;

        let try_get_path =
            |dialog: &DialogSelectable<rfd::FileHandle>| dialog.as_ref().selected().map(Into::into);
        let parse_args = crate::settings::ParseArgs {
            price_data_json: try_get_path(&self.price_data_json),
            parser_json: try_get_path(&self.parser_json),
            item_list_json: try_get_path(&self.item_list_json),
        };

        thread::parse_inventory_in_thread(self.print_args.clone(), parse_args, inventory_json)
    }

    fn scan_in_thread(&mut self) -> Task<Message> {
        self.scan_result = None;
        self.is_scan_result_stale = false;
        self.is_action_pending = true;

        thread::scan_in_thread()
    }
}

#[derive(Debug, Clone)]
enum Message {
    ActionChanged(Action),
    OpenFile(File),
    FileChanged(File, Option<rfd::FileHandle>),
    PrintSettingsChanged(crate::settings::PrintArgs),
    CopyToClipboard(Box<str>),
    Parse(rfd::FileHandle),
    FinishedParsing(ActionResult<crate::table::Table>),
    Scan,
    FinishedScanning(ActionResult<wf_inv_auth_scanning::Login>),
    /// This gets no 'finished' message, because it uses the 'finished' messages of the three steps
    /// (scan, fetch, parse) it comprises.
    ScanAndParse,
    /// Fetching is only done by [`Self::ScanAndParse`], so it has no independent start message.
    FinishedFetching(ActionResult<String>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
enum Action {
    // TO-DO: allow saving the inventory.json out to a file.
    #[default]
    All,
    Scan,
    Parse,
}

impl Action {
    const fn short_name(self) -> &'static str {
        match self {
            Self::All => "Scan, fetch, and parse",
            Self::Scan => "Scan for credentials",
            Self::Parse => "Parse inventory JSON",
        }
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.short_name())
    }
}

#[expect(
    clippy::enum_variant_names,
    reason = "it's only all JSON by chance, something else could be added in the future"
)]
#[derive(Debug, Copy, Clone)]
enum File {
    InventoryJson,
    PriceDataJson,
    ParserJson,
    ItemListJson,
}

impl File {
    fn launch_dialog(self, state: &mut Gui) -> Task<Message> {
        let (filter_name, extension) = self.filter_name_and_extensions();

        *state.get_file_mut(self) = DialogSelectable::Selecting;

        Task::future(
            rfd::AsyncFileDialog::new()
                .set_file_name(self.filename())
                .add_filter(filter_name, extension)
                .pick_file(),
        )
        .map(move |maybe_handle| Message::FileChanged(self, maybe_handle))
    }

    const fn filename(self) -> &'static str {
        match self {
            Self::InventoryJson => "inventory.json",
            Self::PriceDataJson => "price_history.json",
            Self::ParserJson => "parser.json",
            Self::ItemListJson => "items.json",
        }
    }

    const fn filter_name_and_extensions(self) -> (&'static str, &'static [&'static str]) {
        match self {
            Self::InventoryJson | Self::PriceDataJson | Self::ParserJson | Self::ItemListJson => {
                ("JSON", &["json"])
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
enum DialogSelectable<T> {
    Selected(T),
    #[default]
    Unselected,
    Selecting,
}

impl<T> DialogSelectable<T> {
    const fn as_ref(&self) -> DialogSelectable<&T> {
        match self {
            Self::Selected(v) => DialogSelectable::Selected(v),
            Self::Unselected => DialogSelectable::Unselected,
            Self::Selecting => DialogSelectable::Selecting,
        }
    }

    fn selected(self) -> Option<T> {
        match self {
            Self::Selected(v) => Some(v),
            _ => None,
        }
    }

    fn to_labeled_button<'m, C, F, L, M>(
        &'m self,
        content: C,
        mut to_label: F,
        style: impl Fn(&iced::Theme, button::Status) -> button::Style + 'm,
        message: Option<M>,
    ) -> iced::widget::Row<'m, M>
    where
        C: Into<Element<'m, M>>,
        F: FnMut(&'m T) -> L,
        L: Into<Element<'m, M>>,
        M: Clone + 'm,
    {
        let mut row = row![button(content).style(style).on_press_maybe(match self {
            Self::Selecting => None,
            _ => message,
        })]
        .align_y(Center);
        if let DialogSelectable::Selected(v) = self.as_ref() {
            row = row.push(to_label(v));
        }
        row
    }
}

impl<T: Clone> DialogSelectable<T> {
    fn cloned(&self) -> Self {
        match self {
            Self::Selected(v) => Self::Selected(v.clone()),
            Self::Unselected => Self::Unselected,
            Self::Selecting => Self::Selecting,
        }
    }
}

impl<T> From<Option<T>> for DialogSelectable<T> {
    fn from(value: Option<T>) -> Self {
        value.map_or_else(|| Self::Unselected, Self::Selected)
    }
}
