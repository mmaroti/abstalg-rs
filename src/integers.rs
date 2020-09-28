// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::{Domain, EuclideanDomain, Lattice, DistributiveLattice, UnitaryRing};
use num::{BigInt, Integer, One, Signed, Zero};

/// The set of integers whose elements are
/// [BigInt](../num/struct.BigInt.html) objects. The ring operations are the
/// normal ones. The lattice order is the normal total order.
#[derive(Clone, Debug, Default)]
pub struct Integers();

impl Domain for Integers {
    type Elem = BigInt;
}

impl UnitaryRing for Integers {
    fn zero(&self) -> Self::Elem {
        Zero::zero()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        -elem
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 + elem2
    }

    fn one(&self) -> Self::Elem {
        One::one()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 * elem2
    }
}

impl EuclideanDomain for Integers {
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if elem2.is_zero() {
            (BigInt::zero(), elem1.clone())
        } else {
            let (quo, rem) = elem1.div_rem(elem2);

            if elem1.is_positive() && elem2.is_positive() {
                let tmp = elem2 - &rem;
                if rem > tmp {
                    return (quo + 1, -tmp);
                }
            } else if !elem1.is_positive() && !elem2.is_positive() {
                let tmp = elem2 - &rem;
                if rem <= tmp {
                    return (quo + 1, -tmp);
                }
            } else if elem1.is_positive() && !elem2.is_positive() {
                let tmp = elem2 + &rem;
                if -&rem < tmp {
                    return (quo - 1, tmp);
                }
            } else if !elem1.is_positive() && elem2.is_positive() {
                let tmp = elem2 + &rem;
                if -&rem >= tmp {
                    return (quo - 1, tmp);
                }
            }

            (quo, rem)
        }
    }

    fn is_multiple_of(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if elem2.is_zero() {
            elem1.is_zero()
        } else {
            elem1.is_multiple_of(elem2)
        }
    }

    fn is_reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if elem2.is_zero() {
            true
        } else {
            let elem1 = elem1 + elem1;
            let elem2 = elem2.abs();
            -&elem2 < elem1 && elem1 <= elem2
        }
    }

    fn associate_repr(&self, elem: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if *elem < 0.into() {
            (self.neg(elem), (-1).into())
        } else {
            (elem.clone(), 1.into())
        }
    }
}

impl Lattice for Integers {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.min(elem2).clone()
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.max(elem2).clone()
    }

    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 <= elem2
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
                let m: BigInt = m.into();
                let (q, r) = ring.quo_rem(&n, &m);
                println!("n={}, m={}, q={}, r={}", n, m, q, r);
                assert_eq!(n, &m * &q + &r);
                assert!(r.abs() <= (&r + &m).abs());
                assert!(r.abs() <= (&r - &m).abs());

                assert!(m.is_zero() || &r + &r <= m.abs());
                assert!(m.is_zero() || &r + &r > -m.abs());

                assert_eq!(q, ring.quo(&n, &m));
                assert_eq!(r, ring.rem(&n, &m));
                assert_eq!(ring.is_zero(&r), ring.is_multiple_of(&n, &m));
                assert_eq!(ring.is_zero(&q), ring.is_reduced(&n, &m));
            }
        }

        assert_eq!(ring.rem(&0.into(), &2.into()), 0.into());
        assert_eq!(ring.rem(&1.into(), &2.into()), 1.into());

        assert_eq!(ring.rem(&0.into(), &3.into()), 0.into());
        assert_eq!(ring.rem(&1.into(), &3.into()), 1.into());
        assert_eq!(ring.rem(&2.into(), &3.into()), (-1).into());

        assert_eq!(ring.rem(&0.into(), &4.into()), 0.into());
        assert_eq!(ring.rem(&1.into(), &4.into()), 1.into());
        assert_eq!(ring.rem(&2.into(), &4.into()), 2.into());
        assert_eq!(ring.rem(&3.into(), &4.into()), (-1).into());

        assert_eq!(ring.rem(&0.into(), &(-2).into()), 0.into());
        assert_eq!(ring.rem(&1.into(), &(-2).into()), 1.into());
    }
}
