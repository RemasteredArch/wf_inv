use std::fmt::Display;

// Caries the bare minimum of functions useful to outside observers to keep more things private.
#[expect(private_bounds, reason = "intentional to seal trait")]
pub trait ErasedColumn: ErasedColumnSealed {
    fn title(&self) -> &str;
}

pub(super) trait ErasedColumnSealed {
    fn title_padded(&self) -> Box<str>;
    fn len(&self) -> usize;
    /// The width in bytes of the title or the widest stringified value, whichever is greater.
    fn max_width(&self) -> usize;
    fn get(&self, idx: usize) -> Option<&str>;
    fn get_padded(&self, idx: usize) -> Option<Box<str>>;
    fn cmp(&self, idx_a: usize, idx_b: usize) -> Option<std::cmp::Ordering>;
    fn swap(&mut self, idx_a: usize, idx_b: usize);
}

pub struct Column<T> {
    ty: ColumnTypeValued,
    title: Box<str>,
    widest_value: usize,
    values: Values<T>,
}

impl<T: Display> Column<T> {
    pub fn new(ty: ColumnType, title: Box<str>, values: impl IntoIterator<Item = T>) -> Self {
        // TO-DO: this will be calculated with `str::len`, which is absolutely NOT CORRECT!
        let mut widest_value = 0;

        let mut ty = ty.into();
        let values = match &mut ty {
            ColumnTypeValued::Fractional {
                widest_fractional_portion,
            } => {
                *widest_fractional_portion = 0;

                Values::Other(
                    values
                        .into_iter()
                        .map(|value| {
                            let as_str = value.to_string().into_boxed_str();
                            widest_value = widest_value.max(as_str.len());

                            *widest_fractional_portion =
                                (*widest_fractional_portion).max(fractional_portion_width(&as_str));

                            (value, as_str)
                        })
                        .collect(),
                )
            }
            ColumnTypeValued::String => Values::String(
                values
                    .into_iter()
                    .map(|value| {
                        let as_str = value.to_string().into_boxed_str();
                        assert!(!as_str.ends_with(' '));
                        widest_value = widest_value.max(as_str.len());

                        as_str
                    })
                    .collect(),
            ),
            ColumnTypeValued::Integer | ColumnTypeValued::Other => Values::Other(
                values
                    .into_iter()
                    .map(|value| {
                        let as_str = value.to_string().into_boxed_str();
                        widest_value = widest_value.max(as_str.len());

                        (value, as_str)
                    })
                    .collect(),
            ),
        };

        Self {
            ty,
            title,
            widest_value,
            values,
        }
    }
}

impl<T: Ord> ErasedColumn for Column<T> {
    fn title(&self) -> &str {
        &self.title
    }
}

impl<T: Ord> ErasedColumnSealed for Column<T> {
    fn title_padded(&self) -> Box<str> {
        let mut out: String = self.title.clone().into_string();

        let padding = " ".repeat(self.max_width() - self.title.len());
        out.push_str(&padding);

        out.into_boxed_str()
    }

    fn len(&self) -> usize {
        match &self.values {
            Values::String(items) => items.len(),
            Values::Other(items) => items.len(),
        }
    }

    fn max_width(&self) -> usize {
        self.widest_value.max(self.title.len())
    }

    fn get(&self, idx: usize) -> Option<&str> {
        match &self.values {
            Values::String(items) => items.get(idx).map(|s| -> &str { s }),
            Values::Other(items) => items.get(idx).map(|(_, s)| -> &str { s }),
        }
    }

    fn get_padded(&self, idx: usize) -> Option<Box<str>> {
        let as_str = self.get(idx)?;
        let width_delta = self.max_width() - as_str.len();

        let mut lhs = String::new();
        let mut rhs = String::new();
        match self.ty {
            ColumnTypeValued::Integer => lhs = " ".repeat(width_delta),
            ColumnTypeValued::Fractional {
                widest_fractional_portion,
            } => {
                let frac_width_delta = widest_fractional_portion - fractional_portion_width(as_str);
                let leftover_width = width_delta - frac_width_delta;

                lhs = " ".repeat(leftover_width);
                rhs = " ".repeat(frac_width_delta);
            }
            ColumnTypeValued::String | ColumnTypeValued::Other => rhs = " ".repeat(width_delta),
        }

        let mut out = lhs;
        out.push_str(as_str);
        out.push_str(&rhs);

        Some(out.into_boxed_str())
    }

    fn cmp(&self, idx_a: usize, idx_b: usize) -> Option<std::cmp::Ordering> {
        Some(match &self.values {
            Values::String(items) => items.get(idx_a)?.cmp(items.get(idx_b)?),
            Values::Other(items) => items.get(idx_a)?.0.cmp(&items.get(idx_b)?.0),
        })
    }

    fn swap(&mut self, idx_a: usize, idx_b: usize) {
        match &mut self.values {
            Values::String(items) => items.swap(idx_a, idx_b),
            Values::Other(items) => items.swap(idx_a, idx_b),
        }
    }
}

fn fractional_portion_width(stringified_float: &str) -> usize {
    // ```
    //    idx = 3
    //    |  len = 6
    //    v  v
    // 100.03
    //     ^^ frac_width = 6 - 3 - 1 = 2
    // ```
    (stringified_float.len() - stringified_float.find('.').unwrap_or(0)).saturating_sub(1)
}

pub enum ColumnType {
    Integer,
    Fractional,
    String,
    Other,
}

enum ColumnTypeValued {
    Integer,
    Fractional { widest_fractional_portion: usize },
    String,
    Other,
}

impl From<ColumnType> for ColumnTypeValued {
    fn from(value: ColumnType) -> Self {
        match value {
            ColumnType::Integer => Self::Integer,
            ColumnType::Fractional => Self::Fractional {
                widest_fractional_portion: 0,
            },
            ColumnType::String => Self::String,
            ColumnType::Other => Self::Other,
        }
    }
}

enum Values<T> {
    String(Box<[Box<str>]>),
    Other(Box<[(T, Box<str>)]>),
}
