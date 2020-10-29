// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The divisibility partial order of an integral domain where the elements are
/// the unique representatives of associate classes, the largest element is
/// zero, the smallest element is one. If the domain is Euclidean, this is a
/// bounded distributive lattice where the meet is the greatest common divisor,
/// the join is the least common multiple.
#[derive(Clone, Debug)]
pub struct DivisibilityOrder<A>(pub A)
where
    A: IntegralDomain;

impl<A: IntegralDomain> DivisibilityOrder<A> {
    /// Returns the base ring from which this lattice was constructed.
    pub fn base(&self) -> &A {
        &self.0
    }
}

impl<A: IntegralDomain> Domain for DivisibilityOrder<A> {
    type Elem = A::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.0.is_zero(elem) || self.0.is_one(&self.0.associate_coef(elem))
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.0.equals(elem1, elem2)
    }
}

impl<A: IntegralDomain> PartialOrder for DivisibilityOrder<A> {
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.0.divisible(elem2, elem1)
    }
}

impl<A: IntegralDomain> BoundedOrder for DivisibilityOrder<A> {
    fn max(&self) -> Self::Elem {
        self.0.zero()
    }

    fn min(&self) -> Self::Elem {
        self.0.one()
    }
}

impl<A: EuclideanDomain> Lattice for DivisibilityOrder<A> {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = self.0.gcd(elem1, elem2);
        self.0.associate_repr(&elem)
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = self.0.lcm(elem1, elem2);
        self.0.associate_repr(&elem)
    }
}

impl<A: EuclideanDomain> DistributiveLattice for DivisibilityOrder<A> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn order() {
        let lat = DivisibilityOrder(I32);

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
