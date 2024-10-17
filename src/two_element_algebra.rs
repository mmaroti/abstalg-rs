// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The two-element boolean algebra and field with `bool` elements.
pub const BB: TwoElementAlgebra = TwoElementAlgebra();

#[derive(Clone, Debug)]
pub struct TwoElementAlgebra();

impl Domain for TwoElementAlgebra {
    type Elem = bool;

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 == *elem2
    }
}

impl Semigroup for TwoElementAlgebra {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1 && *elem2
    }

    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        *elem1 &= *elem2
    }

    fn square(&self, _elem: &mut Self::Elem) {}
}

impl Monoid for TwoElementAlgebra {
    fn one(&self) -> Self::Elem {
        true
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        *elem
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if *elem {
            Some(true)
        } else {
            None
        }
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        *elem
    }
}

impl CommuntativeMonoid for TwoElementAlgebra {
    fn zero(&self) -> Self::Elem {
        false
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        !*elem
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1 ^ *elem2
    }

    fn add_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        *elem1 ^= *elem2;
    }

    fn double(&self, elem: &mut Self::Elem) {
        *elem = false
    }
}

impl AbelianGroup for TwoElementAlgebra {
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        *elem
    }

    fn neg_assign(&self, _elem: &mut Self::Elem) {}

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1 ^ *elem2
    }

    fn sub_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        *elem1 ^= *elem2;
    }

    fn times(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        *elem && (num % 2 != 0)
    }
}

impl UnitaryRing for TwoElementAlgebra {}

impl Field for TwoElementAlgebra {
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(*elem);
        true
    }

    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(*elem2);
        *elem1
    }

    fn power(&self, _num: isize, elem: &Self::Elem) -> Self::Elem {
        *elem
    }
}

impl PartialOrder for TwoElementAlgebra {
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 <= *elem2
    }

    fn less_than(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        !(*elem1) && *elem2
    }

    fn comparable(&self, _elem1: &Self::Elem, _elem2: &Self::Elem) -> bool {
        true
    }
}

impl BoundedOrder for TwoElementAlgebra {
    fn max(&self) -> Self::Elem {
        true
    }

    fn min(&self) -> Self::Elem {
        false
    }
}

impl Lattice for TwoElementAlgebra {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1 && *elem2
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1 || *elem2
    }
}

impl DistributiveLattice for TwoElementAlgebra {}

impl BooleanAlgebra for TwoElementAlgebra {
    fn not(&self, elem: &Self::Elem) -> Self::Elem {
        !*elem
    }
}
