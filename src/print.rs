// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::fmt::Display;

use crate::table;

macro_rules! columns {
    [$(
        $vec_name:ident: $value_type:ty =
            $(if $cond:expr =>)? ($column_type:ident, $title:expr $(,)?)
    ),+ ,] => {
        $(
            let mut $vec_name: columns!(@ty $value_type $(, $cond)?) =
                columns!(@ $(if $cond =>)? ($column_type, $title));
        )+
    };
    (
        @ if $cond:expr => ($type:ident, $title:expr $(,)?)
    ) => {
        if $cond {
            Some(columns!(@ ($type, $title)))
        } else {
            None
        }
    };
    (
        @ ($type:ident, $title:expr $(,)?)
    ) => {
        $crate::print::ColumnBuilder::new($crate::table::ColumnType::$type, $title)
    };
    (@ty $ty:ty) => {
        $crate::print::ColumnBuilder<$ty>
    };
    (@ty $ty:ty, $cond:expr) => {
        Option<$crate::print::ColumnBuilder<$ty>>
    };
}

macro_rules! filtered_vec {
    [$(
        // `$($match_try_op:ident)*` is a hack that should only ever match zero elements. Its sole
        // purpose is to provide a meta-variable to match the `?` on, as every meta-variable that
        // could match it would cause other problems (e.g., `tt` would be ambiguous with the
        // following comma).
        $builder:ident $($($match_try_op:ident)* ?)?
    ),+ ,] => {{
        let mut out = Vec::new();
        $( filtered_vec!(@ $builder $($($match_try_op)* ?)? out); )+
        out
    }};
    (@ $builder:ident ? $out:expr) => {
        if let Some(builder) = $builder {
            filtered_vec!(@ builder $out);
        }
    };
    (@ $builder:ident $out:expr) => {
        $out.push($builder.into());
    };
}

pub trait Push {
    type Value;

    fn push(&mut self, value: Self::Value);
}

pub struct ColumnBuilder<T> {
    ty: table::ColumnType,
    title: &'static str,
    values: Vec<T>,
}

impl<T> ColumnBuilder<T> {
    pub const fn new(ty: table::ColumnType, title: &'static str) -> Self {
        Self {
            ty,
            title,
            values: Vec::new(),
        }
    }
}

impl<T> Push for ColumnBuilder<T> {
    type Value = T;

    fn push(&mut self, value: Self::Value) {
        self.values.push(value);
    }
}

impl<T> Push for Option<ColumnBuilder<T>> {
    type Value = T;

    fn push(&mut self, value: Self::Value) {
        if let Some(builder) = self {
            builder.push(value);
        }
    }
}

impl<T: Display> From<ColumnBuilder<T>> for table::Column<T> {
    fn from(value: ColumnBuilder<T>) -> Self {
        Self::new(value.ty, value.title.into(), value.values)
    }
}

impl<T: Ord + Display + 'static> From<ColumnBuilder<T>> for Box<dyn table::ErasedColumn> {
    fn from(value: ColumnBuilder<T>) -> Self {
        Box::new(table::Column::<T>::from(value)) as Self
    }
}
