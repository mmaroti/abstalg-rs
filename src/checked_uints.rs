// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use num::{PrimInt, Unsigned};
use std::convert::{From, TryFrom};
use std::fmt::Debug;
use std::marker::PhantomData;

/// The semiring of natural numbers with `u8` primitive values and checked
/// operations.
pub const U8: CheckedUints<u8> = CheckedUints {
    phantom: PhantomData,
};

/// The semiring of natural numbers with `u16` primitive values and checked
/// operations.
pub const U16: CheckedUints<u16> = CheckedUints {
    phantom: PhantomData,
};

/// The semiring of natural numbers with `u32` primitive values and checked
/// operations.
pub const U32: CheckedUints<u32> = CheckedUints {
    phantom: PhantomData,
};

/// The semiring of natural numbers with `u64` primitive values and checked
/// operations.
pub const U64: CheckedUints<u64> = CheckedUints {
    phantom: PhantomData,
};

/// The set of natural numbers whose elements are stored in a primitive
/// unsigned integer type. This structure is functionally equivalent to the
/// set of all natural numbers, but some operations are going to panic if the
/// mathematical result cannot be represented in the primitive type. The
/// lattice order is the normal total order, which is not upper bounded.
#[derive(Clone, Debug)]
pub struct CheckedUints<E>
where
    E: PrimInt + Unsigned + Debug + From<u8> + TryFrom<usize>,
{
    phantom: PhantomData<E>,
}

impl<E> Domain for CheckedUints<E>
where
    E: PrimInt + Unsigned + Debug + From<u8> + TryFrom<usize>,
{
    type Elem = E;

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

impl<E> Semigroup for CheckedUints<E>
where
    E: PrimInt + Unsigned + Debug + From<u8> + TryFrom<usize>,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.checked_mul(elem2).unwrap()
    }
}

impl<E> Monoid for CheckedUints<E>
where
    E: PrimInt + Unsigned + Debug + From<u8> + TryFrom<usize>,
{
    fn one(&self) -> Self::Elem {
        1.into()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        *elem == 1.into()
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if *elem == 1.into() {
            Some(1.into())
        } else {
            None
        }
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        *elem == 1.into()
    }
}

impl<E> CommuntativeMonoid for CheckedUints<E>
where
    E: PrimInt + Unsigned + Debug + From<u8> + TryFrom<usize>,
{
    fn zero(&self) -> Self::Elem {
        0.into()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        elem.is_zero()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.checked_add(elem2).unwrap()
    }
}

impl<E> PartialOrder for CheckedUints<E>
where
    E: PrimInt + Unsigned + Debug + From<u8> + TryFrom<usize>,
{
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 <= *elem2
    }
}

impl<E> Lattice for CheckedUints<E>
where
    E: PrimInt + Unsigned + Debug + From<u8> + TryFrom<usize>,
{
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1.min(elem2)
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1.max(elem2)
    }
}

impl<E> DistributiveLattice for CheckedUints<E> where
    E: PrimInt + Unsigned + Debug + From<u8> + TryFrom<usize>
{
}
