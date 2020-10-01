// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::{
    BoundedOrder, DistributiveLattice, Domain, EuclideanDomain, IntegralDomain, Lattice,
    PartialOrder,
};

/// The bounded distributive lattice of divisibility on the set of non-negative
/// integers.
pub const ZD: DivisibilityOrder<crate::Integers> = DivisibilityOrder { base: crate::Z };

/// The bounded partial order of divisibility on the set of polynomials over
/// the integers.
pub const ZXD: DivisibilityOrder<crate::Integers> = DivisibilityOrder { base: crate::Z };

/// The divisibility partial order of an integral domain where the elements are
/// the unique representatives of associate classes, the largest element is
/// zero, the smallest element is one. If the domain is Euclidean, this is a
/// bounded distributive lattice where the meet is the greatest common divisor,
/// the join is the least common multiple.
#[derive(Clone, Debug, Default)]
pub struct DivisibilityOrder<R: IntegralDomain> {
    base: R,
}

impl<R: IntegralDomain> DivisibilityOrder<R> {
    /// Creates a lattice from the given Euclidean domain.
    pub fn new(base: R) -> Self {
        DivisibilityOrder { base }
    }

    /// Returns the base ring from which this lattice was constructed.
    pub fn base(&self) -> &R {
        &self.base
    }
}

impl<R: IntegralDomain> Domain for DivisibilityOrder<R> {
    type Elem = R::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        let m = self.base.associate_repr(elem).1;
        self.base.is_one(&m)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1, elem2)
    }
}

impl<R: IntegralDomain> PartialOrder for DivisibilityOrder<R> {
    fn less_or_equal(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.is_multiple_of(elem2, elem1)
    }
}

impl<R: IntegralDomain> BoundedOrder for DivisibilityOrder<R> {
    fn max(&self) -> Self::Elem {
        self.base.zero()
    }

    fn min(&self) -> Self::Elem {
        self.base.one()
    }
}

impl<R: EuclideanDomain> Lattice for DivisibilityOrder<R> {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = self.base.gcd(elem1, elem2);
        self.base.associate_repr(&elem).0
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = self.base.lcm(elem1, elem2);
        self.base.associate_repr(&elem).0
    }
}

impl<R: EuclideanDomain> DistributiveLattice for DivisibilityOrder<R> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CheckedInts;

    #[test]
    fn order() {
        let ring: CheckedInts<i32> = Default::default();
        let lat = DivisibilityOrder::new(ring);

        for a in -50..50 {
            if a < 0 {
                assert!(!lat.contains(&a));
                continue;
            }

            for b in 0..50 {
                let c = lat.meet(&a, &b);
                assert!(lat.contains(&c));
                assert!(lat.less_or_equal(&c, &a));
                assert!(lat.less_or_equal(&c, &b));

                let d = lat.join(&a, &b);
                assert!(lat.contains(&d));
                assert!(lat.less_or_equal(&a, &d));
                assert!(lat.less_or_equal(&a, &d));

                if lat.less_or_equal(&a, &b) {
                    assert!(c == a);
                    assert!(d == b);
                }
            }
        }
    }
}
