// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The divisibility partial order of an integral domain where the elements
/// are the unique representatives of associate classes. The largest element
/// is zero, and the smallest element is one. If the domain is Euclidean, this is
/// a bounded distributive lattice where the meet is the greatest common
/// divisor and the join is the least common multiple.
#[derive(Clone, Debug)]
pub struct DivisibilityOrder<A>
where
    A: IntegralDomain,
{
    base: A,
}

impl<A: IntegralDomain> DivisibilityOrder<A> {
    /// Creates a new divisibility order from the given base.
    pub fn new(base: A) -> Self {
        Self { base }
    }

    /// Returns the base ring from which this order was constructed.
    pub fn base(&self) -> &A {
        &self.base
    }
}

impl<A: IntegralDomain> Domain for DivisibilityOrder<A> {
    type Elem = A::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.contains(elem)
            && (self.base.is_zero(elem) || self.base.is_one(&self.base.associate_coef(elem)))
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1, elem2)
    }
}

impl<A: IntegralDomain> PartialOrder for DivisibilityOrder<A> {
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.divisible(elem2, elem1)
    }
}

impl<A: IntegralDomain> BoundedOrder for DivisibilityOrder<A> {
    fn max(&self) -> Self::Elem {
        self.base.zero()
    }

    fn min(&self) -> Self::Elem {
        self.base.one()
    }
}

impl<A: EuclideanDomain> Lattice for DivisibilityOrder<A> {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = self.base.gcd(elem1, elem2);
        self.base.associate_repr(&elem)
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = self.base.lcm(elem1, elem2);
        self.base.associate_repr(&elem)
    }
}

impl<A: EuclideanDomain> DistributiveLattice for DivisibilityOrder<A> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contains() {
        let lat = DivisibilityOrder::new(PolynomialAlgebra::new(ZZ));
        assert!(lat.contains(&vec![]));
        assert!(lat.contains(&vec![ZZ.one()]));
        assert!(!lat.contains(&vec![ZZ.zero()]));
        assert!(!lat.contains(&vec![ZZ.one(), ZZ.zero()]));
        assert!(!lat.contains(&vec![ZZ.int(-1)]));
    }

    #[test]
    fn order() {
        let lat = DivisibilityOrder::new(I32);

        fn divides(a: i32, b: i32) -> bool {
            if a == 0 {
                b == 0
            } else {
                b % a == 0
            }
        }

        for a in -50..=50 {
            assert_eq!(lat.contains(&a), a >= 0);
        }
        for a in 0..=50 {
            for b in 0..=50 {
                assert_eq!(lat.leq(&a, &b), divides(a, b));
                let meet = lat.meet(&a, &b);
                let join = lat.join(&a, &b);
                assert!(lat.contains(&meet));
                assert!(lat.contains(&join));
                assert!(divides(meet, a) && divides(meet, b));
                assert!(divides(a, join) && divides(b, join));
                assert_eq!(meet, lat.meet(&b, &a));
                assert_eq!(join, lat.join(&b, &a));

                // Includes every possible GCD and LCM of these inputs.
                // Zero is the greatest element in the divisibility order.
                for c in 0..=2500 {
                    if divides(c, a) && divides(c, b) {
                        assert!(divides(c, meet), "meet: a={}, b={}, c={}", a, b, c);
                    }
                    if divides(a, c) && divides(b, c) {
                        assert!(divides(join, c), "join: a={}, b={}, c={}", a, b, c);
                    }
                }
            }
        }
    }
}
