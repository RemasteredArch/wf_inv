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

// TO-DO: this doesn't support keyboard navigation.
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
    export_modal: ExportModal,
    save_raw_modal: SaveRawModal,
}

impl Gui {
    fn update(&mut self, message: Message) -> Task<Message> {
        match message {
            Message::ActionChanged(action) => {
                // Ignore requests to change action that are submitted before the action selector
                // stops showing other options while the current action is being executed.
                if !self.is_action_pending {
                    self.action = action;
                }
            }
            Message::OpenFile(file) => return file.launch_dialog(self),
            Message::FileChanged(file, maybe_handle) => {
                *self.get_file_mut(file) = maybe_handle.into();
            }
            Message::DisplaySettingsChanged(settings) => {
                self.display_settings = settings;
            }
            Message::CopyToClipboard(text) => return iced::clipboard::write(text.into()),
            Message::ExportModalMessage(message) => {
                return self
                    .export_modal
                    .update(message)
                    .map(Message::ExportModalMessage);
            }
            Message::SaveRawModalMessage(message) => {
                return self
                    .save_raw_modal
                    .update(message)
                    .map(Message::SaveRawModalMessage);
            }
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
                    result: result.map_err(|err| format!("{err:#}").into()),
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
                self.scan_result = Some(result.clone().map_err(|err| format!("{err:#}").into()));

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

                self.save_raw_modal.fetch_result = Some(inventory_json.clone().into());

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

        let base = center(content);
        let (content, message): (Element<'_, Message>, Message) =
            if let Some(export_modal) = self.export_modal.view() {
                (
                    Element::from(export_modal).map(Message::ExportModalMessage),
                    Message::ExportModalMessage(ExportModalMessage::Hide),
                )
            } else if let Some(save_raw_modal) = self.save_raw_modal.view() {
                (
                    Element::from(save_raw_modal).map(Message::SaveRawModalMessage),
                    Message::SaveRawModalMessage(SaveRawModalMessage::Hide),
                )
            } else {
                return base.into();
            };

        modal(base, content, message)
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
            self.save_fetch_result_button(),
            self.export_result_button(),
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

    fn save_fetch_result_button(&self) -> Option<button::Button<'_, Message>> {
        self.save_raw_modal.fetch_result.is_some().then(|| {
            button(center_y("\u{1F5CF} Save raw inventory data"))
                .style(button::secondary)
                .on_press_with(|| Message::SaveRawModalMessage(SaveRawModalMessage::Show))
                .padding(iced::Padding::default().vertical(5.0).horizontal(8.0))
                .height(iced::Length::Fill)
        })
    }

    fn export_result_button(&self) -> Option<button::Button<'_, Message>> {
        match self.action {
            Action::All => self.all_parse_result.as_ref(),
            Action::Parse => self.pure_parse_result.as_ref(),
            Action::Scan => None,
        }
        .and_then(|result| result.result.as_ref().ok())
        .map(|table| {
            button(center_y("\u{1F5CF} Export parsed result"))
                .style(button::secondary)
                .on_press_with(|| {
                    Message::ExportModalMessage(ExportModalMessage::Show(table.clone()))
                })
                .padding(iced::Padding::default().vertical(5.0).horizontal(8.0))
                .height(iced::Length::Fill)
        })
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
    ExportModalMessage(ExportModalMessage),
    SaveRawModalMessage(SaveRawModalMessage),
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

#[derive(Default)]
struct ExportModal {
    is_exporting: bool,
    finished_exporting: bool,
    export_error: Option<Arc<anyhow::Error>>,
    table: Option<crate::table::Table>,
    format: ExportFormat,
    pretty_print: bool,
    table_column_separator: Box<str>,
    table_header_separator: Box<str>,
    output: DialogSelectable<rfd::FileHandle>,
}

impl ExportModal {
    fn update(&mut self, message: ExportModalMessage) -> Task<ExportModalMessage> {
        self.finished_exporting = false;
        self.export_error = None;

        match message {
            ExportModalMessage::Show(table) => {
                self.is_exporting = false;
                self.table = Some(table);
            }
            ExportModalMessage::Hide => {
                if !self.is_exporting {
                    self.table = None;
                }
            }
            ExportModalMessage::PrettyPrintChanged(is_enabled) => {
                self.pretty_print = is_enabled;
            }
            ExportModalMessage::TableColumnSeparatorChanged(str) => {
                self.table_column_separator = str;
            }
            ExportModalMessage::TableHeaderSeparatorChanged(str) => {
                self.table_header_separator = str;
            }
            ExportModalMessage::FormatChanged(format) => self.format = format,
            ExportModalMessage::OpenOutputFile => {
                return Task::future(
                    rfd::AsyncFileDialog::new()
                        .set_file_name(self.format.example_filename())
                        .pick_file(),
                )
                .map(ExportModalMessage::OutputFileChanged);
            }
            ExportModalMessage::OutputFileChanged(file_handle) => self.output = file_handle.into(),
            ExportModalMessage::Export(path) => return self.export(path),
            ExportModalMessage::FinishedExporting(result) => {
                self.is_exporting = false;
                self.finished_exporting = true;
                if let Err(err) = result {
                    self.export_error = Some(err);
                }
            }
        }

        Task::none()
    }

    fn view(&self) -> Option<iced::widget::Column<'_, ExportModalMessage>> {
        if !self.is_open() {
            return None;
        }

        let input = |label: &'static str,
                     default_from_pretty_print: fn(bool) -> &'static str,
                     current_value: &str,
                     message: fn(Box<str>) -> ExportModalMessage| {
            row![
                label,
                text_input(default_from_pretty_print(self.pretty_print), current_value)
                    .on_input(move |str| message(str.into()))
                    // TO-DO: replace with `Length::Shrink` + `min_width` when iced 0.15.0 releases.
                    // Needs <https://github.com/iced-rs/iced/pull/3367>.
                    .width(iced::Length::Fixed(75.0))
            ]
            .align_y(Center)
            .spacing(5)
        };

        let content = column![
            self.output
                .to_labeled_button(
                    "Choose file to overwrite",
                    |handle| text(handle.file_name()),
                    button::primary,
                    Some(ExportModalMessage::OpenOutputFile),
                )
                .spacing(10),
            bc!(column![
                "Format:",
                radio(
                    "Table",
                    ExportFormat::Table,
                    Some(self.format),
                    ExportModalMessage::FormatChanged,
                ),
                radio(
                    "JSON",
                    ExportFormat::Json,
                    Some(self.format),
                    ExportModalMessage::FormatChanged,
                ),
            ]
            .spacing(10)
            .padding(10)),
            (self.format == ExportFormat::Table).then(|| {
                bc!(column![
                    "Format options:",
                    row![
                        checkbox(self.pretty_print).on_toggle_maybe(
                            (!self.is_exporting).then_some(ExportModalMessage::PrettyPrintChanged)
                        ),
                        "Pretty print",
                    ]
                    .align_y(Center)
                    .spacing(10),
                    input(
                        "Table column seperator: ",
                        crate::settings::default_table_column_separator,
                        &self.table_column_separator,
                        ExportModalMessage::TableColumnSeparatorChanged,
                    ),
                    input(
                        "Table header seperator: ",
                        crate::settings::default_table_header_separator,
                        &self.table_header_separator,
                        ExportModalMessage::TableHeaderSeparatorChanged,
                    ),
                ]
                .spacing(10)
                .padding(10))
            }),
            row![
                button("Export to file")
                    .style(button::primary)
                    .on_press_maybe(
                        self.output
                            .as_ref()
                            .selected()
                            .filter(|_| !self.is_exporting)
                            .map(|handle| ExportModalMessage::Export(handle.path().into()))
                    ),
                if self.finished_exporting {
                    Some(self.export_error.as_deref().map_or_else(
                        || Element::from("\u{2705}"),
                        |err| text!("\u{274C} {err}").style(text::danger).into(),
                    ))
                } else if self.is_exporting {
                    Some(iced_aw::Spinner::new().into())
                } else {
                    None
                },
            ]
            .align_y(Center)
            .spacing(10)
        ]
        .spacing(10);

        Some(content)
    }

    const fn is_open(&self) -> bool {
        self.table.is_some() || self.is_exporting
    }

    fn export(&mut self, to: std::path::PathBuf) -> Task<ExportModalMessage> {
        self.is_exporting = true;

        // TO-DO: raise an error if `Hide` arrives before `Export` does, triggering this to fail
        // unexpectedly.
        let mut table = self
            .table
            .clone()
            .expect("the export button should only be visible if the modal has its table");

        macro_rules! tri {
            ($result:expr $(,)?) => {
                match $result {
                    Ok(v) => v,
                    Err(err) => {
                        return Task::done(ExportModalMessage::FinishedExporting(Err(Arc::new(
                            err,
                        ))));
                    }
                }
            };
        }

        *table.column_separator_mut() = tri!(self.resolve_table_column_separator());
        *table.header_separator_mut() = tri!(self.resolve_table_header_separator());

        thread::export_in_thread(self.format, table, to)
    }

    fn resolve_table_column_separator(&self) -> anyhow::Result<Box<str>> {
        if self.table_column_separator.is_empty() {
            return Ok(crate::settings::default_table_column_separator(self.pretty_print).into());
        }

        unescape(Cow::Borrowed(&self.table_column_separator))
            .map(Box::from)
            .context("failed to unescape table column separator")
    }

    fn resolve_table_header_separator(&self) -> anyhow::Result<Option<char>> {
        if self.table_header_separator.is_empty() {
            return Ok(
                crate::settings::default_table_header_separator(self.pretty_print)
                    .chars()
                    .next(),
            );
        }

        unescape(Cow::Borrowed(&self.table_header_separator))
            // TO-DO: special casing on the null byte is a terrible way to allow the user to disable
            // the header separator.
            .map(|str| str.chars().next().filter(|&char| char != '\0'))
            .context("failed to unescape table header separator")
    }
}

#[derive(Debug, Copy, Clone, Default, PartialEq, Eq)]
enum ExportFormat {
    #[default]
    Table,
    Json,
}

impl ExportFormat {
    const fn example_filename(self) -> &'static str {
        match self {
            Self::Table => "wf_inv_export.txt",
            Self::Json => "wf_inv_export.json",
        }
    }
}

#[derive(Debug, Clone)]
enum ExportModalMessage {
    Show(crate::table::Table),
    Hide,
    FormatChanged(ExportFormat),
    PrettyPrintChanged(bool),
    TableColumnSeparatorChanged(Box<str>),
    TableHeaderSeparatorChanged(Box<str>),
    OpenOutputFile,
    OutputFileChanged(Option<rfd::FileHandle>),
    Export(std::path::PathBuf),
    FinishedExporting(ActionResult<()>),
}

#[derive(Default)]
struct SaveRawModal {
    is_open: bool,
    is_saving: bool,
    finished_saving: bool,
    save_error: Option<Arc<anyhow::Error>>,
    fetch_result: Option<Box<str>>,
    output: DialogSelectable<rfd::FileHandle>,
}

impl SaveRawModal {
    fn update(&mut self, message: SaveRawModalMessage) -> Task<SaveRawModalMessage> {
        self.finished_saving = false;
        self.save_error = None;

        match message {
            SaveRawModalMessage::Show => {
                if self.fetch_result.is_some() {
                    self.is_open = true;
                }
            }
            SaveRawModalMessage::Hide => {
                if !self.is_saving {
                    self.is_open = false;
                }
            }
            SaveRawModalMessage::OpenOutputFile => {
                let (filter_name, filter_extensions) =
                    File::InventoryJson.filter_name_and_extensions();

                return Task::future(
                    rfd::AsyncFileDialog::new()
                        .set_file_name(File::InventoryJson.filename())
                        .add_filter(filter_name, filter_extensions)
                        .pick_file(),
                )
                .map(SaveRawModalMessage::OutputFileChanged);
            }
            SaveRawModalMessage::OutputFileChanged(file_handle) => self.output = file_handle.into(),
            SaveRawModalMessage::Save(path) => return self.save(path),
            SaveRawModalMessage::FinishedSaving(result) => {
                self.is_saving = false;
                self.finished_saving = true;
                if let Err(err) = result {
                    self.save_error = Some(err);
                }
            }
        }

        Task::none()
    }

    fn view(&self) -> Option<iced::widget::Column<'_, SaveRawModalMessage>> {
        if !self.is_open {
            return None;
        }

        let content = column![
            self.output
                .to_labeled_button(
                    "Choose file to overwrite",
                    |handle| text(handle.file_name()),
                    button::primary,
                    Some(SaveRawModalMessage::OpenOutputFile),
                )
                .spacing(10),
            row![
                button("Save to file")
                    .style(button::primary)
                    .on_press_maybe(
                        self.output
                            .as_ref()
                            .selected()
                            .filter(|_| !self.is_saving)
                            .map(|handle| SaveRawModalMessage::Save(handle.path().into()))
                    ),
                if self.finished_saving {
                    Some(self.save_error.as_deref().map_or_else(
                        || Element::from("\u{2705}"),
                        |err| text!("\u{274C} {err}").style(text::danger).into(),
                    ))
                } else if self.is_saving {
                    Some(iced_aw::Spinner::new().into())
                } else {
                    None
                },
            ]
            .align_y(Center)
            .spacing(10)
        ]
        .spacing(10);

        Some(content)
    }

    fn save(&mut self, to: std::path::PathBuf) -> Task<SaveRawModalMessage> {
        self.is_saving = true;

        // TO-DO: raise an error if `Hide` arrives before `Save` does, triggering this to fail
        // unexpectedly.
        let contents = self
            .fetch_result
            .clone()
            .expect("the export button should only be visible if the modal has its table");

        thread::save_raw_in_thread(contents, to)
    }
}

#[derive(Debug, Clone)]
enum SaveRawModalMessage {
    Show,
    Hide,
    OpenOutputFile,
    OutputFileChanged(Option<rfd::FileHandle>),
    Save(std::path::PathBuf),
    FinishedSaving(ActionResult<()>),
}

fn modal<'e, B, C>(base: B, content: C, hide_message: Message) -> Element<'e, Message>
where
    B: Into<Element<'e, Message>>,
    C: Into<Element<'e, Message>>,
{
    use iced::widget::{mouse_area, opaque};

    const ZERO: iced::Size<iced::Length> = iced::Size {
        width: iced::Length::Fixed(0.0),
        height: iced::Length::Fixed(0.0),
    };

    let content: Element<'e, Message> = content.into();

    if iced::advanced::Widget::size(content.as_widget()) == ZERO {
        return base.into();
    }

    let modal = bc!(container(content).padding(25)).style(|theme| {
        let palette = theme.extended_palette();

        container::Style {
            background: Some(palette.background.base.color.into()),
            text_color: Some(palette.background.base.text),
            border: iced::Border {
                width: 1.0,
                radius: 5.0.into(),
                color: palette.background.strong.color,
            },
            ..container::Style::default()
        }
    });
    let overlay = opaque(
        mouse_area(
            center(opaque(modal))
                .style(|_| {
                    container::Style::default().background(iced::Color::BLACK.scale_alpha(0.8))
                })
                .width(iced::Length::Fill)
                .height(iced::Length::Fill),
        )
        .on_press(hide_message),
    );

    stack![base.into(), overlay].into()
}

/// Unescapes the following sequences:
///
/// - `\0` into `U+0000` (null byte, Unicode `NUL`)
/// - `\t` into `U+0009` (tab, Unicode `HT`)
/// - `\n` into `U+000A` (newline, Unicode `LF`)
/// - `\r` into `U+000D` (carriage return, Unicode `CR`)
/// - `\\` into `U+005C` (backslash, Unicode `REVERSE SOLIDUS`)
/// - `\u{*}`, where `*` is a sequence of hexadecimal characters (of any capitalization) and
///   underscores (`U+005F LOW LINE`), into the Unicode value encoded by the numeric value of those
///   hexadecimal characters (ignoring the underscores).
fn unescape(str: Cow<str>) -> anyhow::Result<Cow<str>> {
    macro_rules! throw {
        ($($content:tt),+ $(,)?) => {
            return Err(anyhow::anyhow!($( $content ),+))
        };
    }

    enum EscapeState {
        UnicodeU,
        UnicodeOpenBrace,
        UnicodeHex(String),
        Simple,
        None,
    }

    let push_hex: fn(&mut String, String, char) -> anyhow::Result<EscapeState> =
        |out, mut hex_str, char| {
            if char.is_ascii_hexdigit() {
                hex_str.push(char);
                Ok(EscapeState::UnicodeHex(hex_str))
            } else if char == '}' {
                let char = u32::from_str_radix(&hex_str, 16).expect(
                    "a string of hexadecimal characters should never fail `from_str_radix(16)`",
                );
                let Some(char) = char::from_u32(char) else {
                    throw!(
                        "received hexadecimal value `{char}` in a Unicode escape, which is not a valid Unicode character",
                    );
                };
                out.push(char);

                Ok(EscapeState::None)
            } else if char == '_' {
                Ok(EscapeState::UnicodeHex(hex_str)) // Do nothing.
            } else {
                throw!(
                    "expected hexadecimal digit or underscore in Unicode escape, received `{char}`"
                );
            }
        };

    // Assume that most strings won't contain escaped characters and eat the `O(n)` up front.
    if !str.contains('\\') {
        return Ok(str);
    }

    // This be shorter than `str`, but likely not by enough to make the oversized allocation cost
    // more than the extra allocations from resizing.
    let mut out = String::with_capacity(str.len());

    let mut prev_state = EscapeState::None;
    for char in str.chars() {
        prev_state = match prev_state {
            EscapeState::UnicodeU => {
                if char != '{' {
                    throw!("expected `{{` after `\\u`, received `{char}`");
                }
                EscapeState::UnicodeOpenBrace
            }
            EscapeState::UnicodeOpenBrace => push_hex(&mut out, String::new(), char)?,
            EscapeState::UnicodeHex(str) => push_hex(&mut out, str, char)?,
            EscapeState::Simple => {
                if char == 'u' {
                    EscapeState::UnicodeU
                } else {
                    out.push(match char {
                        '0' => '\0',
                        't' => '\t',
                        'n' => '\n',
                        'r' => '\r',
                        '\\' => '\\',
                        _ => throw!(
                            "received invalid escape sequence `\\{char}`, expected one of: `\\0`, `\\t`, `\\n`, `\\r`, `\\\\`",
                        ),
                    });
                    EscapeState::None
                }
            }
            EscapeState::None => {
                if char == '\\' {
                    EscapeState::Simple
                } else {
                    out.push(char);
                    EscapeState::None
                }
            }
        }
    }
    if !matches!(prev_state, EscapeState::None) {
        throw!("finished unescaping string with unfinished escape sequence");
    }

    Ok(out.into())
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

#[cfg(test)]
mod test {
    use std::borrow::Cow;

    #[test]
    fn test_str_unescape() {
        for (input, expected_output, should_output_be_borrowed) in [
            // Simple strings without escape sequences.
            ("", Some(""), true),
            ("foo", Some("foo"), true),
            // Strings with trailing escape sequences.
            ("foo\\0", Some("foo\0"), false),
            ("foo\\0", Some("foo\0"), false),
            ("foo\\t", Some("foo\t"), false),
            ("foo\\n", Some("foo\n"), false),
            ("foo\\r", Some("foo\r"), false),
            ("foo\\\\", Some("foo\\"), false),
            ("foo\\u{2b}", Some("foo+"), false),
            ("foo\\u{002B}", Some("foo+"), false),
            // Strings with invalid trailing escape sequences.
            ("foo\\a", None, false),
            ("foo\\\0", None, false),
            // Strings with special characters, but without escape sequences.
            ("foo\0", Some("foo\0"), true),
            ("foo\t", Some("foo\t"), true),
            ("foo\n", Some("foo\n"), true),
            ("foo\r", Some("foo\r"), true),
            // Strings with unfinished escape sequences.
            ("foo\\", None, false),
            ("foo\\u", None, false),
            ("foo\\u{", None, false),
            ("foo\\u{00", None, false),
            // Strings with non-trailing escape sequences.
            ("foo\\0bar", Some("foo\0bar"), false),
            ("foo\\0bar", Some("foo\0bar"), false),
            ("foo\\tbar", Some("foo\tbar"), false),
            ("foo\\nbar", Some("foo\nbar"), false),
            ("foo\\rbar", Some("foo\rbar"), false),
            ("foo\\\\bar", Some("foo\\bar"), false),
            ("foo\\u{2b}bar", Some("foo+bar"), false),
            ("foo\\u{002B}bar", Some("foo+bar"), false),
            // Strings with invalid non-trailing escape sequences.
            ("foo\\abar", None, false),
            ("foo\\\0bar", None, false),
        ] {
            let result = super::unescape(Cow::Borrowed(input)).ok();
            assert_eq!(expected_output, result.as_deref());

            if let Some(cow) = result {
                let is_borrowed = matches!(cow, Cow::Borrowed(_));
                assert_eq!(should_output_be_borrowed, is_borrowed);
            }
        }
    }
}
