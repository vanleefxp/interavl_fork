mod owned_iter;
mod pruners;
mod pruning_iter;
mod ref_iter;

use std::ops::Range;

pub(crate) use owned_iter::*;
pub(crate) use pruners::*;
pub(crate) use pruning_iter::*;
pub(crate) use ref_iter::*;

use crate::Node;

pub trait IntervalTreeIterator<'a, R: 'a, V: 'a>: Iterator<Item = &'a Box<Node<R, V>>> + Sized {
    fn ranges(self) -> impl Iterator<Item = &'a Range<R>> {
        self.map(|node| node.range())
    }

    fn values(self) -> impl Iterator<Item = &'a V> {
        self.map(|node| &node.value)
    }

    fn tuples(self) -> impl Iterator<Item = (&'a Range<R>, &'a V)> {
        self.map(|node| (node.range(), &node.value))
    }
}

impl <'a, R: 'a, V: 'a, T: Iterator<Item = &'a Box<Node<R, V>>> + Sized> IntervalTreeIterator<'a, R, V> for T {}