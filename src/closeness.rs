use std::{cmp::Ordering, f32};

pub trait Closeness {
    /// Tells which one among two objects is closer to the current object.
    /// Returns `Less` if the first object is closer, `Greater` if the second object is closer, and `Equal` if they are
    /// equally close.
    fn closeness(&self, other_1: &Self, other_2: &Self) -> Ordering;
}

pub trait Distance {
    type Output;
    fn distance(&self, other: &Self) -> Self::Output;
}

impl<R, D> Closeness for R where R: Distance<Output = D>, D: Ord {
    fn closeness(&self, other_1: &Self, other_2: &Self) -> Ordering {
        self.distance(other_1).cmp(&self.distance(other_2))
    }
}

macro_rules! impl_distance_by_abs_diff {
    ($($t:ident),*$(,)?) => {
        $(impl Distance for $t {
            type Output = $t;
            fn distance(&self, other: &Self) -> Self::Output {
                self.abs_diff(*other)
            }
        })*
    };
}

macro_rules! impl_distance_by_sub {
    ($($t:ident),*$(,)?) => {
        $(impl Distance for $t {
            type Output = $t;
            fn distance(&self, other: &Self) -> Self::Output {
                (self - other).abs()
            }
        })*
    };
}

impl_distance_by_abs_diff!(u8, u16, u32, u64, u128, usize);
impl_distance_by_sub!(i8, i16, i32, i64, i128, isize, f32, f64);