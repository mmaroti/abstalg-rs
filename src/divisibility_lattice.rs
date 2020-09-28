// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::{BoundedLattice, DistributiveLattice, Domain, EuclideanDomain, Lattice};

/// The lattice of divisibility of an Euclidean domain where the elements are
/// the unique representative of associate classes, the meet is the greatest
/// common divisor, the join is the least common multiple, the largest element
/// is zero and the least element is one.
#[derive(Clone, Debug, Default)]
pub struct DivisibilityLattice<R: EuclideanDomain> {
    base: R,
}

impl<R: EuclideanDomain> DivisibilityLattice<R> {
    /// Creates a lattice from the given Euclidean domain.
    pub fn new(base: R) -> Self {
        DivisibilityLattice { base }
    }

    /// Returns the base ring from which this lattice was constructed.
    pub fn base(&self) -> &R {
        &self.base
    }
}

impl<R: EuclideanDomain> Domain for DivisibilityLattice<R> {
    type Elem = R::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        let m = self.base.associate_repr(elem).1;
        self.base.is_one(&m)
    }
}

impl<R: EuclideanDomain> Lattice for DivisibilityLattice<R> {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = self.base.gcd(elem1, elem2);
        self.base.associate_repr(&elem).0
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = self.base.lcm(elem1, elem2);
        self.base.associate_repr(&elem).0
    }

    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.is_multiple_of(elem2, elem1)
    }
}

impl<R: EuclideanDomain> DistributiveLattice for DivisibilityLattice<R> {}

impl<R: EuclideanDomain> BoundedLattice for DivisibilityLattice<R> {
    fn max(&self) -> Self::Elem {
        self.base.zero()
    }

    fn min(&self) -> Self::Elem {
        self.base.one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CheckedInts;

    #[test]
    fn order() {
        let ring: CheckedInts<i32> = Default::default();
        let lat = DivisibilityLattice::new(ring);

        for a in -50..50 {
            if a < 0 {
                assert!(!lat.contains(&a));
                continue;
            }

            for b in 0..50 {
                let c = lat.meet(&a, &b);
                assert!(lat.contains(&c));
                assert!(lat.leq(&c, &a));
                assert!(lat.leq(&c, &b));

                let d = lat.join(&a, &b);
                assert!(lat.contains(&d));
                assert!(lat.leq(&a, &d));
                assert!(lat.leq(&a, &d));

                if lat.leq(&a, &b) {
                    assert!(c == a);
                    assert!(d == b);
                }
            }
        }
    }
}
