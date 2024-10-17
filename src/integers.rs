// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use num::{BigInt, Integer, One, Signed, Zero};

/// The Euclidean ring of integers with arbitrary large values.
pub const ZZ: Integers = Integers();

/// The set of integers whose elements are
/// [BigInt](../num/struct.BigInt.html) objects. The ring operations are the
/// normal ones. The lattice order is the normal total order.
#[derive(Clone, Debug)]
pub struct Integers();

impl Domain for Integers {
    type Elem = BigInt;

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

impl Semigroup for Integers {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 * elem2
    }
}

impl Monoid for Integers {
    fn one(&self) -> Self::Elem {
        One::one()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        elem.is_one()
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if self.invertible(elem) {
            Some(elem.clone())
        } else {
            None
        }
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        elem.is_one() || (-elem).is_one()
    }
}

impl CommuntativeMonoid for Integers {
    fn zero(&self) -> Self::Elem {
        Zero::zero()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        elem.is_zero()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 + elem2
    }
}

impl AbelianGroup for Integers {
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        -elem
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 - elem2
    }

    fn times(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        num * elem
    }
}

impl UnitaryRing for Integers {}

impl IntegralDomain for Integers {
    fn try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem> {
        assert!(!elem2.is_zero());

        let (quo, rem) = elem1.div_rem(elem2);
        if rem.is_zero() {
            Some(quo)
        } else {
            None
        }
    }

    fn divisible(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if elem2.is_zero() {
            elem1.is_zero()
        } else {
            elem1.is_multiple_of(elem2)
        }
    }

    fn associate_repr(&self, elem: &Self::Elem) -> Self::Elem {
        if elem.is_negative() {
            self.neg(elem)
        } else {
            elem.clone()
        }
    }

    fn associate_coef(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(!elem.is_zero());
        if elem.is_negative() {
            self.neg(&One::one())
        } else {
            One::one()
        }
    }
}

impl EuclideanDomain for Integers {
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        assert!(!elem2.is_zero());

        let (quo, rem) = elem1.div_rem(elem2);
        if rem.is_negative() {
            if elem2.is_negative() {
                (quo + 1, rem - elem2)
            } else {
                (quo - 1, rem + elem2)
            }
        } else {
            (quo, rem)
        }
    }

    fn reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if elem2.is_zero() {
            true
        } else {
            !elem1.is_negative() && *elem1 < elem2.abs()
        }
    }
}

impl PartialOrder for Integers {
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 <= elem2
    }
}

impl Lattice for Integers {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.min(elem2).clone()
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.max(elem2).clone()
    }
}

impl DistributiveLattice for Integers {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quo_rem() {
        let ring = Integers();

        for n in -40..40 {
            let n: BigInt = n.into();
            for m in -40..40 {
                if m == 0 {
                    continue;
                }
                let m: BigInt = m.into();
                let (q, r) = ring.quo_rem(&n, &m);
                println!("n={}, m={}, q={}, r={}", n, m, q, r);
                assert_eq!(n, &m * &q + &r);
                assert!(ring.zero() <= r && r < m.abs());

                assert_eq!(q, ring.quo(&n, &m));
                assert_eq!(r, ring.rem(&n, &m));
                assert_eq!(ring.is_zero(&r), ring.divisible(&n, &m));
                assert_eq!(ring.is_zero(&q), ring.reduced(&n, &m));
            }
        }

        assert_eq!(ring.rem(&0.into(), &2.into()), 0.into());
        assert_eq!(ring.rem(&1.into(), &2.into()), 1.into());

        assert_eq!(ring.rem(&0.into(), &3.into()), 0.into());
        assert_eq!(ring.rem(&1.into(), &3.into()), 1.into());
        assert_eq!(ring.rem(&2.into(), &3.into()), 2.into());

        assert_eq!(ring.rem(&0.into(), &(-2).into()), 0.into());
        assert_eq!(ring.rem(&1.into(), &(-2).into()), 1.into());
    }
}
