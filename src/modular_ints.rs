// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::{Domain, UnitaryRing};
use num::traits::ops::wrapping::{WrappingAdd, WrappingMul, WrappingSub};
use num::{PrimInt, Signed};
use std::convert::From;
use std::fmt::Debug;
use std::marker::PhantomData;

/// The ring of signed integers modulo `2^n` whose elements are stored in a
/// primitive signed integer type. The ring operations on these sets wrap
/// around. This structure is equivalent to the quotient ring of the set of
/// integers modulo `2^n`, but its implementation is more efficient.
pub struct ModularInts<E>
where
    E: PrimInt + Signed + WrappingAdd + WrappingMul + WrappingSub + Debug + From<i8>,
{
    phantom: PhantomData<E>,
}

impl<E> Domain for ModularInts<E>
where
    E: PrimInt + Signed + WrappingAdd + WrappingMul + WrappingSub + Debug + From<i8>,
{
    type Elem = E;
}

impl<E> UnitaryRing for ModularInts<E>
where
    E: PrimInt + Signed + WrappingAdd + WrappingMul + WrappingSub + Debug + From<i8>,
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
