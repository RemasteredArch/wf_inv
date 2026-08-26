// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::borrow::Cow;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, OnceLock};

use anyhow::Context;
use iced::widget::{radio, stack, text_input};
use iced::{
    Center, Element, Task,
    widget::{
        button, center, center_x, center_y, checkbox, column, container, pick_list, row,
        scrollable, text, toggler,
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
    display_args: crate::settings::DisplayArgs,
) -> anyhow::Result<()> {
    static CLI_SETTINGS: OnceLock<(
        Option<std::path::PathBuf>,
        crate::settings::ParseArgs,
        crate::settings::DisplayArgs,
    )> = OnceLock::new();

    if CLI_SETTINGS
        .set((inventory_json, parse_args, display_args))
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
                display_settings,
            ) = CLI_SETTINGS.get().unwrap();

            let into_handle = |maybe_path: &Option<std::path::PathBuf>| -> Option<rfd::FileHandle> {
                maybe_path.as_ref().map(|path| path.clone().into())
            };

            (
                Gui::default(),
                Task::batch(
                    [
                        Message::DisplaySettingsChanged(display_settings.clone()),
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
    all_parse_result: Option<ParseResult>,
    pure_parse_result: Option<ParseResult>,
    scan_result: Option<Result<wf_inv_auth_scanning::Login, Box<str>>>,
    display_settings: crate::settings::DisplayArgs,
    price_data_json: DialogSelectable<rfd::FileHandle>,
    parser_json: DialogSelectable<rfd::FileHandle>,
    item_list_json: DialogSelectable<rfd::FileHandle>,
}

impl Gui {
    fn update(&mut self, message: Message) -> Task<Message> {
        match message {
            Message::ActionChanged(action) => self.action = action,
            Message::OpenFile(file) => return file.launch_dialog(self),
            Message::FileChanged(file, maybe_handle) => {
                *self.get_file_mut(file) = maybe_handle.into();
            }
            Message::DisplaySettingsChanged(settings) => {
                self.display_settings = settings;
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
                let result = ParseResult {
                    result: result.map_err(|err| format!("Error: {err}").into()),
                    settings_hash: self.current_settings().default_hash(),
                };
                match self.action {
                    Action::All => self.all_parse_result = Some(result),
                    Action::Parse => self.pure_parse_result = Some(result),
                    _ => {
                        panic!("received `FinishedParsing` when the pending action does not parse");
                    }
                }

                self.is_action_pending = false;
            }
            Message::Scan => return self.scan_in_thread(),
            Message::FinishedScanning(result) => {
                self.scan_result =
                    Some(result.clone().map_err(|err| format!("Error: {err}").into()));

                if matches!(self.action, Action::All) {
                    match result {
                        Ok(login) => return thread::fetch_in_thread(login),
                        Err(err) => return Task::done(Message::FinishedFetching(Err(err))),
                    }
                }
                self.is_action_pending = false;
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

    fn current_settings(&self) -> SettingsRef<'_> {
        SettingsRef {
            display_settings: &self.display_settings,
            price_data_json: self
                .price_data_json
                .as_ref()
                .selected()
                .map(rfd::FileHandle::path),
            parser_json: self
                .parser_json
                .as_ref()
                .selected()
                .map(rfd::FileHandle::path),
            item_list_json: self
                .item_list_json
                .as_ref()
                .selected()
                .map(rfd::FileHandle::path),
        }
    }

    fn is_current_action_result_stale(&self) -> bool {
        match self.action {
            Action::Scan => false,
            _ => match self.action {
                Action::All => self.all_parse_result.as_ref(),
                Action::Parse => self.pure_parse_result.as_ref(),
                _ => unreachable!(),
            }
            .is_some_and(|result| result.is_stale(self.current_settings())),
        }
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
            self.stale_result_warning(),
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
        if !self.is_current_action_result_stale() {
            return None;
        }

        let warning: fn(_) -> _ = |message| {
            container(message)
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
                .align_y(Center)
        };

        Some(warning(
            // The first Unicode character is the "circled information source."
            "\u{1F6C8} Your settings have changed since this result was generated",
        ))
    }

    fn settings(&self) -> Option<container::Container<'_, Message>> {
        if !matches!(self.action, Action::All | Action::Parse) {
            return None;
        }

        let bool_button =
            |name: &'static str,
             is_checked: bool,
             is_enabled: bool,
             change: fn(&mut crate::settings::DisplayArgs)| {
                let button = checkbox(is_checked);
                row![
                    if is_enabled {
                        button.on_toggle(move |_| {
                            let mut new = self.display_settings.clone();
                            change(&mut new);
                            Message::DisplaySettingsChanged(new)
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
                    self.display_settings.$field,
                    !self.is_action_pending,
                    |display_settings| display_settings.$field ^= true,
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
                match self.action {
                    Action::Parse => &self.pure_parse_result,
                    Action::All => &self.all_parse_result,
                    _ => unreachable!(),
                }
                .as_ref()
                .map(|result| match &result.result {
                    Ok(table) => table.to_element(),
                    Err(e) => text!("Error: {e}").into(),
                })
                //
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
        if self.is_action_pending && matches!(self.action, Action::All) {
            self.all_parse_result = None;
        } else {
            self.pure_parse_result = None;
        };

        self.is_action_pending = true;

        let try_get_path =
            |dialog: &DialogSelectable<rfd::FileHandle>| dialog.as_ref().selected().map(Into::into);
        let parse_args = crate::settings::ParseArgs {
            price_data_json: try_get_path(&self.price_data_json),
            parser_json: try_get_path(&self.parser_json),
            item_list_json: try_get_path(&self.item_list_json),
        };

        thread::parse_inventory_in_thread(self.display_settings.clone(), parse_args, inventory_json)
    }

    fn scan_in_thread(&mut self) -> Task<Message> {
        self.scan_result = None;
        self.is_action_pending = true;

        thread::scan_in_thread()
    }
}

#[derive(Debug, Clone)]
enum Message {
    ActionChanged(Action),
    OpenFile(File),
    FileChanged(File, Option<rfd::FileHandle>),
    DisplaySettingsChanged(crate::settings::DisplayArgs),
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

struct ParseResult {
    result: Result<crate::table::Table, Box<str>>,
    settings_hash: u64,
}

impl ParseResult {
    fn is_stale(&self, current_settings: SettingsRef<'_>) -> bool {
        self.settings_hash != current_settings.default_hash()
    }
}

#[derive(Hash, Copy, Clone)]
struct SettingsRef<'g> {
    display_settings: &'g crate::settings::DisplayArgs,
    price_data_json: Option<&'g std::path::Path>,
    parser_json: Option<&'g std::path::Path>,
    item_list_json: Option<&'g std::path::Path>,
}

impl SettingsRef<'_> {
    fn default_hash(&self) -> u64 {
        let mut hasher = std::hash::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
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
