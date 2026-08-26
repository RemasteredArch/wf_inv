// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::{collections::HashMap, fmt::Display};

pub use column::{Column, ColumnType, ErasedColumn};
use serde::ser::SerializeSeq;

mod column;

#[derive(Debug)]
pub struct Table {
    columns: Box<[Box<dyn ErasedColumn>]>,
    rows: usize,
    pretty_print: bool,
    column_separator: Box<str>,
    header_separator: Option<char>,
}

impl Table {
    pub fn new(
        columns: Box<[Box<dyn ErasedColumn>]>,
        pretty_print: bool,
        column_separator: Box<str>,
        header_separator: Option<char>,
    ) -> Self {
        Self {
            // TO-DO: this never actually ensures that they're the same length?
            rows: columns.iter().map(|c| c.len()).max().unwrap_or(0),
            columns,
            pretty_print,
            column_separator,
            header_separator,
        }
    }

    pub fn sort_descending_by_column_title(&mut self, columns: &[&str]) -> anyhow::Result<()> {
        let columns: Vec<usize> = columns
            .iter()
            .map(|&sort_title| {
                self.columns
                    .iter()
                    .enumerate()
                    .find_map(|(idx, column)| {
                        if column.title() == sort_title {
                            Some(idx)
                        } else {
                            None
                        }
                    })
                    .ok_or_else(|| {
                        let valid_titles = self.columns.iter().map(|c| c.title()).fold(
                            String::new(),
                            |mut acc, title| {
                                if !acc.is_empty() {
                                    acc.push_str(", ");
                                }
                                acc.push('\'');
                                acc.push_str(title);
                                acc.push('\'');
                                acc
                            },
                        );

                        anyhow::anyhow!("no column titled '{sort_title}' found (expected one of: {valid_titles})")
                    })
            })
        .collect::<Result<_, _>>()?;

        self.sort_descending_by_column_idx(&columns);

        Ok(())
    }

    pub fn sort_descending_by_column_idx(&mut self, columns: &[usize]) {
        let compare = |table: &Self, idx_a: usize, idx_b: usize| -> std::cmp::Ordering {
            for &column in columns {
                let ordering = table.columns[column].cmp(idx_a, idx_b).unwrap();
                if ordering != std::cmp::Ordering::Equal {
                    return ordering;
                }
            }
            std::cmp::Ordering::Equal
        };

        let mut i: usize = 1;
        while i < self.rows {
            let mut j: usize = i;
            while j > 0 && compare(self, j - 1, j) == std::cmp::Ordering::Less {
                self.swap(j, j - 1);
                j -= 1;
            }
            i += 1;
        }
    }

    fn swap(&mut self, idx_a: usize, idx_b: usize) {
        for column in &mut self.columns {
            column.swap(idx_a, idx_b);
        }
    }

    fn row_width(&self) -> usize {
        let entries_width = self.columns.iter().map(|c| c.max_width()).sum::<usize>();
        let separators_width = self.columns.len().saturating_sub(1) * self.column_separator.len();

        entries_width + separators_width
    }

    #[cfg(feature = "unstable-gui")]
    pub fn to_element<'a, Message: 'a>(&'a self) -> iced::Element<'a, Message> {
        use iced::widget::{scrollable, table, text};

        let element = {
            let bold: iced::Font = {
                let mut f = iced::Font::DEFAULT;
                f.weight = iced::font::Weight::Bold;
                f
            };

            table(
                self.columns.iter().map(|column| {
                    let title = text(column.title()).font(bold);
                    let view = |idx| {
                        text(column.get_padded_value_width(idx).unwrap().to_string())
                            .font(iced::Font::MONOSPACE)
                    };

                    table::column(title, view)
                        .align_x(iced::Alignment::from(column.alignment()))
                        .align_y(iced::Alignment::Center)
                }),
                0..self.rows,
            )
            .separator(2)
            .padding_x(10)
            .padding_y(6)
        };

        scrollable::Scrollable::with_direction(
            element,
            scrollable::Direction::Both {
                vertical: scrollable::Scrollbar::default(),
                horizontal: scrollable::Scrollbar::default(),
            },
        )
        .into()
    }

    pub const fn column_separator_mut(&mut self) -> &mut Box<str> {
        &mut self.column_separator
    }

    pub fn header_separator_mut(&mut self) -> &mut Option<char> {
        &mut self.header_separator
    }
}

impl Display for Table {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn write_row(
            f: &mut std::fmt::Formatter<'_>,
            table: &Table,
            mut mapping: impl FnMut(&dyn ErasedColumn) -> Box<str>,
        ) -> std::fmt::Result {
            if table.columns.is_empty() {
                return Ok(());
            }

            // Print only the first without proceeding whitespace.
            write!(f, "{}", mapping(table.columns.first().unwrap().as_ref()))?;

            for i in 1..table.columns.len() {
                write!(
                    f,
                    "{}{}",
                    table.column_separator,
                    mapping(table.columns[i].as_ref()),
                )?;
            }

            writeln!(f)
        }

        let get_title: fn(&dyn ErasedColumn) -> Box<str> = if self.pretty_print {
            |column| column.title_padded()
        } else {
            |column| column.title().into()
        };

        // Print table headings.
        write_row(f, self, get_title)?;

        if let Some(header_separator) = self.header_separator {
            writeln!(
                f,
                "{}",
                header_separator.to_string().repeat(self.row_width()),
            )?;
        }

        let get_value_at_row_idx: fn(&dyn ErasedColumn, usize) -> Box<str> = if self.pretty_print {
            |column, row_idx| {
                column
                    .get_padded(row_idx)
                    .expect("all columns in a table should be `rows` long")
            }
        } else {
            |column, row_idx| {
                column
                    .get(row_idx)
                    .expect("all columns in a table should be `rows` long")
                    .into()
            }
        };

        // Print table values.
        for row_idx in 0..self.rows {
            write_row(f, self, |column| get_value_at_row_idx(column, row_idx))?;
        }

        Ok(())
    }
}

impl Clone for Table {
    fn clone(&self) -> Self {
        Self {
            columns: self.columns.iter().map(|c| c.clone_boxed()).collect(),
            rows: self.rows,
            pretty_print: self.pretty_print,
            column_separator: self.column_separator.clone(),
            header_separator: self.header_separator,
        }
    }
}

impl serde::Serialize for Table {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut s = serializer.serialize_seq(Some(self.rows))?;

        macro_rules! conv_err {
            ($type:literal, $value:expr) => {
                |err| {
                    serde::ser::Error::custom(format!(
                        concat!(
                            "could not parse ",
                            $type,
                            " value from its string representation '{}': {}",
                        ),
                        $value, err,
                    ))
                }
            };
        }

        // Stores the key-value pairs for each row of the table. Never cleared because it's assumed
        // that the titles of columns will never change.
        let mut row: HashMap<&str, serde_json::Value> = HashMap::with_capacity(self.columns.len());

        for row_idx in 0..self.rows {
            for column in &self.columns {
                let as_str = column
                    .get(row_idx)
                    .expect("all columns in a table should be `rows` long");

                // TO-DO: implement optional types more concretely, so that strings that are
                // legitimately just hyphens don't get chopped.
                let value = if as_str == PrintingOption::<()>::NONE {
                    serde_json::Value::Null
                } else {
                    match column.ty() {
                        ColumnType::Integer => {
                            let as_i128 = as_str.parse().map_err(conv_err!("integer", as_str))?;
                            serde_json::Number::from_i128(as_i128)
                                .ok_or_else(|| {
                                    serde::ser::Error::custom(format!(
                                        // TO-DO: this would be false negative for formats with arbitrary
                                        // precision.
                                        "integer value {as_i128} out of representable range",
                                    ))
                                })?
                                .into()
                        }
                        ColumnType::Fractional => {
                            let as_f64 = as_str.parse().map_err(conv_err!("fractional", as_str))?;
                            serde_json::Number::from_f64(as_f64)
                                .ok_or_else(|| {
                                    serde::ser::Error::custom(format!(
                                        // TO-DO: this would be false negative for formats with arbitrary
                                        // precision.
                                        "fractional value {as_f64} not a finite value",
                                    ))
                                })?
                                .into()
                        }
                        ColumnType::String | ColumnType::Other => as_str.into(),
                    }
                };

                row.insert(column.title(), value);
            }

            s.serialize_element(&row)?;
        }

        s.end()
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
#[repr(transparent)]
pub struct PrintingOption<T>(Option<T>);

impl<T> PrintingOption<T> {
    const NONE: &'static str = "-";
}

impl<T: Display> Display for PrintingOption<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Some(v) => v.fmt(f),
            None => Self::NONE.fmt(f),
        }
    }
}

impl<T> From<Option<T>> for PrintingOption<T> {
    fn from(value: Option<T>) -> Self {
        Self(value)
    }
}

impl<T> From<PrintingOption<T>> for Option<T> {
    fn from(value: PrintingOption<T>) -> Self {
        value.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FixedPointDecimal {
    integral: i64,
    fractional: u8,
}

impl FixedPointDecimal {
    pub fn try_round_from<F: num_traits::Float + num_traits::FromPrimitive + Display>(
        float: F,
    ) -> anyhow::Result<Self> {
        let one_hundred = <F as num_traits::FromPrimitive>::from_f64(100.0).unwrap();

        // TO-DO: `round_ties_even` would probably be better, but it looks like the PR to add this
        // has simply stalled: <https://github.com/rust-num/num-traits/pull/350>.
        let integral = float.round().to_i64().ok_or_else(|| {
            anyhow::anyhow!(
                "floating-point value {float} could not have its integral portion represented by an `i64`",
            )
        })?;

        let fractional = ((float * one_hundred) % one_hundred).round().abs();
        let fractional = fractional.to_u8().ok_or_else(|| {
            assert!(
                !fractional.is_finite(),
                "any finite (n * 100) % 100 should always fit within a `u8`",
            );
            anyhow::anyhow!(
                "floating-point ({float} * 100) % 100 = {fractional} couldn't be represented as a `u8`",
            )
        })?;
        assert!(fractional < 100);

        Ok(Self {
            integral,
            fractional,
        })
    }
}

impl Display for FixedPointDecimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{:02}", self.integral, self.fractional)
    }
}

#[cfg(test)]
mod test {
    // Sanity check that `Option` does sort things as I would expect.
    #[test]
    fn optional_cmp() {
        let one_hundred: super::PrintingOption<usize> = Some(100).into();
        let fifty: super::PrintingOption<usize> = Some(50).into();
        let none: super::PrintingOption<usize> = None.into();
        assert!(fifty < one_hundred);
        assert_eq!(fifty, fifty);
        assert!(none < fifty);
        assert_eq!(none, none);
    }

    #[test]
    fn table_to_json() {
        let str = serde_json::to_string(&super::Table::new(
            [
                Box::new(super::Column::new(
                    super::ColumnType::Integer,
                    "foo".into(),
                    [1, 2, 3],
                )) as _,
                Box::new(super::Column::new(
                    super::ColumnType::String,
                    "bar".into(),
                    ["quux", "qux", "quuux"],
                )) as _,
                Box::new(super::Column::new(
                    super::ColumnType::Fractional,
                    "baz".into(),
                    // All types get squashed into strings eventually, so not using a proper numeric
                    // type here is fine.
                    ["1.00", "1.01", "5000.000001"],
                )) as _,
            ]
            .into(),
            true,
            "".into(),
            None,
        ))
        .unwrap();

        let expected = serde_json::json!([
            {
                "foo": 1,
                "bar": "quux",
                "baz": 1.0
            },
            {
                "foo": 2,
                "bar": "qux",
                "baz": 1.01
            },
            {
                "foo": 3,
                "bar": "quuux",
                "baz": 5000.000001
            }
        ]);

        let as_value = serde_json::from_str::<serde_json::Value>(&str).unwrap();
        assert_eq!(expected, as_value);
    }
}
