// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use num::traits::ops::wrapping::{WrappingAdd, WrappingMul, WrappingSub};
use num::{PrimInt, Signed};
use std::convert::{From, TryFrom};
use std::fmt::Debug;
use std::marker::PhantomData;

/// The ring of signed integers modulo `2^n` whose elements are stored in a
/// primitive signed integer type. The ring operations on these sets wrap
/// around. This structure is equivalent to the quotient ring of the set of
/// integers modulo `2^n`, but its implementation is more efficient.
#[derive(Clone, Debug, Default)]
pub struct ModularInts<E>
where
    E: PrimInt
        + Signed
        + WrappingAdd
        + WrappingMul
        + WrappingSub
        + Debug
        + From<i8>
        + TryFrom<isize>,
{
    phantom: PhantomData<E>,
}

impl<E> Domain for ModularInts<E>
where
    E: PrimInt
        + Signed
        + WrappingAdd
        + WrappingMul
        + WrappingSub
        + Debug
        + From<i8>
        + TryFrom<isize>,
{
    type Elem = E;

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

impl<E> AdditiveGroup for ModularInts<E>
where
    E: PrimInt
        + Signed
        + WrappingAdd
        + WrappingMul
        + WrappingSub
        + Debug
        + From<i8>
        + TryFrom<isize>,
{
    fn zero(&self) -> Self::Elem {
        0.into()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        *elem == 0.into()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.zero().wrapping_sub(elem)
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.wrapping_add(elem2)
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.wrapping_sub(elem2)
    }
}

impl<E> UnitaryRing for ModularInts<E>
where
    E: PrimInt
        + Signed
        + WrappingAdd
        + WrappingMul
        + WrappingSub
        + Debug
        + From<i8>
        + TryFrom<isize>,
{
    fn one(&self) -> Self::Elem {
        1.into()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        *elem == 1.into()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.wrapping_mul(elem2)
    }
}
