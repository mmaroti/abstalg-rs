// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_traits::Zero;

/// An arbitrary set of elements.
pub trait Domain {
    /// The type of the elements of this domain.
    type Elem: Clone;

    /// Checks if the given element is a member of the domain.
    fn contains(&self, elem: &Self::Elem) -> bool;

    /// Checks if the given elements represent the same value in the domain.
    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool;
}

/// The ring of integers whose elements are [BigInt](::num_bigint::bigint::BigInt)
/// objects.
#[derive(Clone, Debug, Default)]
pub struct BigIntegers();

impl Domain for BigIntegers {
    type Elem = BigInt;

    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

/// The ring of integers whose elements are represented with 32-bit integers.
/// Some operations will panic if the result cannot be represented in 32 bits.
#[derive(Clone, Debug, Default)]
pub struct Integers32();

impl Domain for Integers32 {
    type Elem = i32;

    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

/// The ring of integers whose elements are represented with 64-bit integers.
/// Some operations will panic if the result cannot be represented in 64 bits.
#[derive(Clone, Debug, Default)]
pub struct Integers64();

impl Domain for Integers64 {
    type Elem = i64;

    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

/// A ring with an identity element (not necessarily commutative). Typical
/// examples are the rings of rectangular matrices, integers and polynomials.
/// Some operations may panic (for example, the underlying type cannot
/// represent the real result).
pub trait RingWithIdentity: Domain {
    /// The additive identity element of the ring.
    fn zero(&self) -> Self::Elem;

    /// Checks if the given element is the additive identity of the ring.
    fn is_zero(&self, elem: &Self::Elem) -> bool {
        self.equals(elem, &self.zero())
    }

    /// The additive inverse of the given element.
    fn neg(&self, elem: &Self::Elem) -> Self::Elem;

    /// The additive sum of the given elements
    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;

    /// The multiplicative identity element of the ring.
    fn one(&self) -> Self::Elem;

    /// Checks if the given element is the multiplicative identity of the ring.
    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.equals(elem, &self.one())
    }

    /// The multiplicative product of the given elements.
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;
}

impl RingWithIdentity for BigIntegers {
    fn zero(&self) -> Self::Elem {
        0.into()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        -elem
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 + elem2
    }

    fn one(&self) -> Self::Elem {
        1.into()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 * elem2
    }
}

impl RingWithIdentity for Integers32 {
    fn zero(&self) -> Self::Elem {
        0
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        i32::checked_neg(*elem).unwrap()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i32::checked_add(*elem1, *elem2).unwrap()
    }

    fn one(&self) -> Self::Elem {
        1
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i32::checked_mul(*elem1, *elem2).unwrap()
    }
}

impl RingWithIdentity for Integers64 {
    fn zero(&self) -> Self::Elem {
        0
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        i64::checked_neg(*elem).unwrap()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i64::checked_add(*elem1, *elem2).unwrap()
    }

    fn one(&self) -> Self::Elem {
        1
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i64::checked_mul(*elem1, *elem2).unwrap()
    }
}

/// An Euclidean domain is an integral domain where the Euclidean algorithm
/// can be implemented. Typical examples are the rings of integers and
/// polynomials.
pub trait EuclideanDomain: RingWithIdentity {
    /// Performs the euclidean division algorithm dividing the first elem
    /// with the second one and returning the quotient and the remainder.
    /// The remainder should be the one with the least norm among all possible
    /// ones so that the Euclidean algorithm runs fast. The second element
    /// may be zero, in which case the quotient shall be zero and the
    /// remainder be the first element.
    fn div_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem);

    /// Performs the division just like the [div_rem](EuclideanDomain::div_rem)
    /// method would do and returns the quotient.
    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.div_rem(elem1, elem2).0
    }

    /// Performs the division just like the [div_rem](EuclideanDomain::div_rem)
    /// method would do and returns the remainder
    fn rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.div_rem(elem1, elem2).1
    }

    /// Returns true if the first element is a multiple of the second one.
    fn is_multiple_of(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        let rem = self.rem(elem1, elem2);
        self.is_zero(&rem)
    }

    /// Returns true if the two elements are associated (divide each other)
    fn are_associated(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_multiple_of(elem1, elem2) && self.is_multiple_of(elem2, elem1)
    }
}

impl EuclideanDomain for Integers32 {
    fn div_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        let rem = self.rem(elem1, elem2);
        let elem1 = i32::checked_sub(*elem1, rem).unwrap();
        let div = elem1 / *elem2;
        (rem, div)
    }

    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 + elem2
    }

    fn rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(*elem2 != 0);
        let elem2 = i32::checked_abs(*elem2).unwrap();

        let elem1 = *elem1 % elem2;
        if elem1 < 0 && elem1 + elem2 > 0 {
            elem1 + elem2
        } else if elem1 > 0 && elem1 - elem2 < 0 {
            elem1 - elem2
        } else {
            elem1
        }
    }

    fn is_multiple_of(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if *elem2 == 0 {
            *elem1 == 0
        } else if *elem2 == -1 {
            true
        } else {
            *elem1 % *elem2 == 0
        }
    }
}

impl EuclideanDomain for BigIntegers {
    fn div_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        let sign2 = elem2.sign();
        if sign2 == Sign::NoSign {
            (BigInt::zero(), elem1.clone())
        } else {
            let sign1 = elem1.sign();
            let (div, rem) = elem1.div_rem(elem2);

            if sign1 == sign2 {
                if (&rem + &rem - elem2).sign() == sign1 {
                    return (div + 1i32, rem - elem2);
                }
            } else {
                if (&rem + &rem + elem2).sign() == sign1 {
                    return (div - 1i32, rem + elem2);
                }
            }
            (div, rem)
        }
    }

    fn rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let sign2 = elem2.sign();
        if sign2 == Sign::NoSign {
            elem1.clone()
        } else {
            let sign1 = elem1.sign();
            let rem = elem1 % elem2;

            if sign1 == sign2 {
                if (&rem + &rem - elem2).sign() == sign1 {
                    return rem - elem2;
                }
            } else {
                if (&rem + &rem + elem2).sign() == sign1 {
                    return rem + elem2;
                }
            }
            rem
        }
    }

    fn is_multiple_of(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if elem2.is_zero() {
            elem1.is_zero()
        } else {
            elem1.is_multiple_of(elem2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::sign::Signed;

    #[test]
    fn div_rem_bigint() {
        let ring = BigIntegers();

        for n in -20..20 {
            let n: BigInt = n.into();
            for m in -20..20 {
                let m: BigInt = m.into();
                let (q, r) = ring.div_rem(&n, &m);
                println!("n={}, m={}, q={}, r={}", n, m, q, r);
                assert_eq!(n, &m * &q + &r);
                assert!(r.abs() <= (&r + &m).abs());
                assert!(r.abs() <= (&r - &m).abs());

                assert_eq!(q, ring.div(&n, &m));
                assert_eq!(r, ring.rem(&n, &m));
                assert_eq!(ring.is_zero(&r), ring.is_multiple_of(&n, &m));
            }
        }
    }
}
