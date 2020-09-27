// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

//! A module that contains the basic sets on which various algebraic structures
//! are implemented.

use num::{BigInt, PrimInt};
use std::fmt::Debug;

/// An arbitrary set of elements where not all representable elements are
/// members of the set, but every member is uniquely represented, thus they
/// can be compered using the `==` operator.
pub trait Domain {
    /// The type of the elements of this domain.
    type Elem: Clone + PartialEq + Debug;

    /// Checks if the given element is a member of the domain. Not all
    /// possible objects need to be elements of the set.
    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }
}

/// The set of integers whose elements are
/// [BigInt](../../num/struct.BigInt.html) objects. The ring operations are the
/// normal ones.
#[derive(Clone, Debug, Default)]
pub struct Integers();

impl Domain for Integers {
    type Elem = BigInt;
}

/// Marker trait for subsets of the integers whose elements are stored in a
/// primitive signed integer type. The ring operations on these sets are
/// checked, that is, they will panic if the result cannot be represented in
/// the primitive type.
pub trait PartialInts: Domain
where
    Self::Elem: PrimInt,
{
}

/// The set of integers whose elements are stored in `i32` values.
pub struct PartialInt32();

impl Domain for PartialInt32 {
    type Elem = i32;
}

impl PartialInts for PartialInt32 {}

/// The set of integers whose elements are stored in `i32` values.
pub struct PartialInt64();

impl Domain for PartialInt64 {
    type Elem = i64;
}

impl PartialInts for PartialInt64 {}
