// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use num::{PrimInt, Signed};
use std::convert::{From, TryFrom, TryInto};
use std::fmt::Debug;
use std::marker::PhantomData;

/// The Euclidean ring of integers with `i8` primitive values and checked
/// operations.
pub const I8: CheckedInts<i8> = CheckedInts {
    phantom: PhantomData,
};

/// The Euclidean ring of integers with `i16` primitive values and checked
/// operations.
pub const I16: CheckedInts<i16> = CheckedInts {
    phantom: PhantomData,
};

/// The Euclidean ring of integers with `i32` primitive values and checked
/// operations.
pub const I32: CheckedInts<i32> = CheckedInts {
    phantom: PhantomData,
};

/// The Euclidean ring of integers with `i64` primitive values and checked
/// operations.
pub const I64: CheckedInts<i64> = CheckedInts {
    phantom: PhantomData,
};

/// The set of integers whose elements are stored in a primitive signed
/// integer type. This structure is functionally equivalent to the set
/// of all integers, but some operations are going to panic if the
/// mathematical result cannot be represented in the primitive type.
/// The lattice order is the normal total order, which is not bounded.
#[derive(Clone, Debug, Default)]
pub struct CheckedInts<E>
where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>,
{
    phantom: PhantomData<E>,
}

impl<E> Domain for CheckedInts<E>
where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>,
{
    type Elem = E;

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

impl<E> AdditiveGroup for CheckedInts<E>
where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>,
{
    fn zero(&self) -> Self::Elem {
        0.into()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        elem.is_zero()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.zero().checked_sub(elem).unwrap()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.checked_add(elem2).unwrap()
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.checked_sub(elem2).unwrap()
    }

    fn multiple(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let num: Option<Self::Elem> = num.try_into().ok();
        elem.checked_mul(&num.expect("too large value")).unwrap()
    }
}

impl<E> UnitaryRing for CheckedInts<E>
where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>,
{
    fn one(&self) -> Self::Elem {
        1.into()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        *elem == 1.into()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.checked_mul(elem2).unwrap()
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if *elem == 1.into() || *elem == (-1).into() {
            Some(*elem)
        } else {
            None
        }
    }
}

impl<E> IntegralDomain for CheckedInts<E>
where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>,
{
    fn try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem> {
        self.auto_try_div(elem1, elem2)
    }

    fn associate_repr(&self, elem: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if *elem < 0.into() {
            (self.neg(elem), (-1).into())
        } else {
            (*elem, 1.into())
        }
    }
}

impl<E> EuclideanDomain for CheckedInts<E>
where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>,
{
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if *elem2 == 0.into() {
            (0.into(), *elem1)
        } else {
            let quo = elem1.checked_div(elem2).unwrap();
            let rem = *elem1 - quo * *elem2;

            if *elem1 >= 0.into() && *elem2 >= 0.into() {
                let tmp = *elem2 - rem;
                if rem > tmp {
                    return (quo + 1.into(), -tmp);
                }
            } else if *elem1 < 0.into() && *elem2 < 0.into() {
                let tmp = *elem2 - rem;
                if rem <= tmp {
                    return (quo + 1.into(), -tmp);
                }
            } else if *elem1 >= 0.into() && *elem2 < 0.into() {
                let tmp = *elem2 + rem;
                if -rem < tmp {
                    return (quo - 1.into(), tmp);
                }
            } else if *elem1 < 0.into() && *elem2 >= 0.into() {
                let tmp = *elem2 + rem;
                if -rem >= tmp {
                    return (quo - 1.into(), tmp);
                }
            }

            (quo, rem)
        }
    }

    fn is_reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if *elem2 == 0.into() {
            true
        } else {
            let elem2 = if *elem2 < 0.into() { *elem2 } else { -*elem2 };
            (elem2 + 1.into()) / 2.into() <= *elem1 && *elem1 <= -(elem2 / 2.into())
        }
    }
}

impl<E> PartialOrder for CheckedInts<E>
where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>,
{
    fn less_or_equal(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 <= *elem2
    }
}

impl<E> Lattice for CheckedInts<E>
where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>,
{
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1.min(elem2)
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        *elem1.max(elem2)
    }
}

impl<E> DistributiveLattice for CheckedInts<E> where
    E: PrimInt + Signed + Debug + From<i8> + TryFrom<isize>
{
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::BigInt;

    #[test]
    fn quo_rem() {
        let ring1: CheckedInts<i32> = Default::default();
        let ring2 = Integers();

        let mut elems: Vec<i32> = Default::default();
        for i in 0..10 {
            elems.push(i);
            if i > 0 {
                elems.push(-i);
            }
            elems.push(i32::MIN + i);
            elems.push(i32::MAX - i);
        }

        let min2: BigInt = i32::MIN.into();
        let max2: BigInt = i32::MAX.into();

        for &n1 in elems.iter() {
            let n2: BigInt = n1.into();
            for &m1 in elems.iter() {
                let m2: BigInt = m1.into();

                let (q2, r2) = ring2.quo_rem(&n2, &m2);
                if min2 <= q2 && q2 <= max2 && min2 <= r2 && r2 <= max2 {
                    let (q1, r1) = ring1.quo_rem(&n1, &m1);
                    println!(
                        "n1={}, m1={}, q1={}, r1={}, q2={}, r2={}",
                        n1, m1, q1, r1, q2, r2
                    );

                    assert_eq!(q2, q1.into());
                    assert_eq!(r2, r1.into());

                    assert_eq!(
                        ring1.is_multiple_of(&n1, &m1),
                        ring2.is_multiple_of(&n2, &m2)
                    );
                    assert_eq!(ring1.is_reduced(&n1, &m1), ring2.is_reduced(&n2, &m2));
                } else {
                    let result = std::panic::catch_unwind(|| {
                        ring1.quo_rem(&n1, &m1);
                    });
                    assert!(result.is_err());
                }
            }
        }
    }

    #[test]
    fn extended_gcd() {
        let ring: CheckedInts<i32> = Default::default();

        for a in -10..10 {
            for b in -10..10 {
                let (g, x, y) = ring.extended_gcd(&a, &b);
                println!("a:{}, b:{}, g:{}, x:{}, y:{}", a, b, g, x, y);
                assert_eq!(g, a * x + b * y);
                assert_eq!(g, ring.gcd(&a, &b));
                assert!(ring.is_multiple_of(&a, &g));
                assert!(ring.is_multiple_of(&b, &g));
            }
        }
    }
}
