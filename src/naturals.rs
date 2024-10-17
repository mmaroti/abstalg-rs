// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use num::{BigUint, One, Zero};

/// The commutative monoid of natural numbers (including zero) with arbitrary
/// large values.
pub const NN: Naturals = Naturals();

/// The set of natural numbers (including zero) whose elements are
/// [BigUint](../num/struct.BigUint.html) objects. The semilattice and
/// commutative semilattice operations are the normal ones while the
/// lattice order is the normal total order.
#[derive(Clone, Debug)]
pub struct Naturals();

impl Domain for Naturals {
    type Elem = BigUint;

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

impl Semigroup for Naturals {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 * elem2
    }
}

impl Monoid for Naturals {
    fn one(&self) -> Self::Elem {
        One::one()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        elem.is_one()
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if elem.is_one() {
            Some(One::one())
        } else {
            None
        }
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        elem.is_one()
    }
}

impl CommuntativeMonoid for Naturals {
    fn zero(&self) -> Self::Elem {
        Zero::zero()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        elem.is_zero()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 + elem2
    }

    fn double(&self, elem: &mut Self::Elem) {
        *elem *= 2u32;
    }

    fn times(&self, num: usize, elem: &Self::Elem) -> Self::Elem {
        num * elem
    }
}

impl PartialOrder for Naturals {
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 <= elem2
    }
}

impl Lattice for Naturals {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.min(elem2).clone()
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.max(elem2).clone()
    }
}

impl DistributiveLattice for Naturals {}
