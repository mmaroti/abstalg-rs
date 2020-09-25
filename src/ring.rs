// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

//! A module that contains ring like structures.

use num::{BigInt, Integer, Signed, Zero};
use std::fmt::Display;

/// An arbitrary set of elements.
pub trait Domain {
    /// The type of the elements of this domain.
    type Elem: Clone + Display;

    /// Checks if the given element is a member of the domain.
    fn contains(&self, elem: &Self::Elem) -> bool;

    /// Checks if the given elements represent the same value in the domain.
    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool;
}

/// The ring of integers whose elements are
/// [BigInt](../../num_bigint/struct.BigInt.html) objects.
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

    /// The difference of the given elements.
    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.add(elem1, &self.neg(elem2))
    }

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
        self.is_zero(&self.rem(elem1, elem2))
    }

    /// Returns true if the first element is its own remainder when the
    /// divided by the second one (so the quotient is zero).
    fn is_reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(&self.div(elem1, elem2))
    }

    /// Returns true if the two elements are associated (divide each other)
    fn are_associated(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_multiple_of(elem1, elem2) && self.is_multiple_of(elem2, elem1)
    }

    /// Returns true if the given element has a multiplicative inverse,
    /// that is, it is a divisor of the identity element.
    fn is_unit(&self, elem: &Self::Elem) -> bool {
        self.is_multiple_of(elem, &self.one())
    }

    /// Calculates the greatest common divisor of two elements using the
    /// Euclidean algorithm.
    fn gcd(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let mut elem1 = elem1.clone();
        let mut elem2 = elem2.clone();
        while !self.is_zero(&elem2) {
            let rem = self.rem(&elem1, &elem2);
            elem1 = elem2;
            elem2 = rem;
        }
        elem1
    }

    /// Performs the extended Euclidean algorithm which returns the greatest
    /// common divisor, and two elements that multiplied with the inputs gives
    /// the greatest common divisor.
    fn extended_gcd(
        &self,
        elem1: &Self::Elem,
        elem2: &Self::Elem,
    ) -> (Self::Elem, Self::Elem, Self::Elem) {
        if self.is_zero(elem2) {
            (elem1.clone(), self.one(), self.zero())
        } else {
            let (div, rem) = self.div_rem(elem1, elem2);
            let (gcd, x, y) = self.extended_gcd(elem2, &rem);
            let z = self.sub(&x, &self.mul(&y, &div));
            (gcd, y, z)
        }
    }

    /// Checks if the given two elements are relative prime.
    fn are_relative_prime(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        let gcd = self.gcd(elem1, elem2);
        self.is_unit(&gcd)
    }

    /// Among all the associates of the given elem if there is a well defined
    /// unique one (non-negative for integers, zero or monoic for polynomials),
    /// then this method returns quotient of that unique element and the input
    /// one. In general, this method returns one.
    fn normalizer(&self, _elem: &Self::Elem) -> Self::Elem {
        self.one()
    }
}

impl EuclideanDomain for BigIntegers {
    fn div_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if elem2.is_zero() {
            (BigInt::zero(), elem1.clone())
        } else {
            let (div, rem) = elem1.div_rem(elem2);

            if elem1.is_positive() && elem2.is_positive() {
                let tmp = elem2 - &rem;
                if rem > tmp {
                    return (div + 1, -tmp);
                }
            } else if !elem1.is_positive() && !elem2.is_positive() {
                let tmp = elem2 - &rem;
                if rem <= tmp {
                    return (div + 1, -tmp);
                }
            } else if elem1.is_positive() && !elem2.is_positive() {
                let tmp = elem2 + &rem;
                if -&rem < tmp {
                    return (div - 1, tmp);
                }
            } else if !elem1.is_positive() && elem2.is_positive() {
                let tmp = elem2 + &rem;
                if -&rem >= tmp {
                    return (div - 1, tmp);
                }
            }

            (div, rem)
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

    fn normalizer(&self, elem: &Self::Elem) -> Self::Elem {
        if elem.is_negative() {
            (-1).into()
        } else {
            1.into()
        }
    }
}

impl EuclideanDomain for Integers32 {
    fn div_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if *elem2 == 0 {
            (0, *elem1)
        } else {
            let div = i32::checked_div(*elem1, *elem2).unwrap();
            let rem = *elem1 - div * elem2;

            if *elem1 >= 0 && *elem2 >= 0 {
                let tmp = *elem2 - rem;
                if rem > tmp {
                    return (div + 1, -tmp);
                }
            } else if *elem1 < 0 && *elem2 < 0 {
                let tmp = *elem2 - rem;
                if rem <= tmp {
                    return (div + 1, -tmp);
                }
            } else if *elem1 >= 0 && *elem2 < 0 {
                let tmp = elem2 + rem;
                if -rem < tmp {
                    return (div - 1, tmp);
                }
            } else if *elem1 < 0 && *elem2 >= 0 {
                let tmp = elem2 + rem;
                if -rem >= tmp {
                    return (div - 1, tmp);
                }
            }

            (div, rem)
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

    fn is_reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if *elem2 == 0 {
            true
        } else {
            let elem2 = if *elem2 < 0 { *elem2 } else { -elem2 };
            (elem2 + 1) / 2 <= *elem1 && *elem1 <= -(elem2 / 2)
        }
    }

    fn normalizer(&self, elem: &Self::Elem) -> Self::Elem {
        if *elem == i32::MIN {
            panic!();
        } else if *elem < 0 {
            -1
        } else {
            0
        }
    }
}

impl EuclideanDomain for Integers64 {
    fn div_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if *elem2 == 0 {
            (0, *elem1)
        } else {
            let div = i64::checked_div(*elem1, *elem2).unwrap();
            let rem = *elem1 - div * elem2;

            if *elem1 >= 0 && *elem2 >= 0 {
                let tmp = *elem2 - rem;
                if rem > tmp {
                    return (div + 1, -tmp);
                }
            } else if *elem1 < 0 && *elem2 < 0 {
                let tmp = *elem2 - rem;
                if rem <= tmp {
                    return (div + 1, -tmp);
                }
            } else if *elem1 >= 0 && *elem2 < 0 {
                let tmp = elem2 + rem;
                if -rem < tmp {
                    return (div - 1, tmp);
                }
            } else if *elem1 < 0 && *elem2 >= 0 {
                let tmp = elem2 + rem;
                if -rem >= tmp {
                    return (div - 1, tmp);
                }
            }

            (div, rem)
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

    fn is_reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if *elem2 == 0 {
            true
        } else {
            let elem2 = if *elem2 < 0 { *elem2 } else { -elem2 };
            (elem2 + 1) / 2 <= *elem1 && *elem1 <= -(elem2 / 2)
        }
    }

    fn normalizer(&self, elem: &Self::Elem) -> Self::Elem {
        if *elem == i64::MIN {
            panic!();
        } else if *elem < 0 {
            -1
        } else {
            0
        }
    }
}

/// A quotient ring over an Euclidean domain by a principal ideal.
#[derive(Clone, Debug, Default)]
pub struct QuotientRing<RING: EuclideanDomain> {
    base: RING,
    modulo: RING::Elem,
    one: RING::Elem,
}

impl<RING: EuclideanDomain> QuotientRing<RING> {
    /// Creates a new quotient ring from the given Euclidean domain and
    /// one of its element.
    pub fn new(base: RING, modulo: RING::Elem) -> Self {
        assert!(base.contains(&modulo));
        // if the quotient is trivial, then the identity element becomes zero.
        let one = base.div(&base.one(), &modulo);
        QuotientRing { base, modulo, one }
    }

    /// Returns the base ring from which this ring was constructed.
    pub fn base(&self) -> &RING {
        &self.base
    }

    /// Returns the modulo element from which this ring was constructed.
    pub fn modulo(&self) -> &RING::Elem {
        &self.modulo
    }
}

impl<RING: EuclideanDomain> Domain for QuotientRing<RING> {
    type Elem = RING::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.is_reduced(elem, &self.modulo)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1, elem2)
    }
}

impl<RING: EuclideanDomain> RingWithIdentity for QuotientRing<RING> {
    fn zero(&self) -> Self::Elem {
        self.base.zero()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.neg(elem), &self.modulo)
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.add(elem1, elem2), &self.modulo)
    }

    fn one(&self) -> Self::Elem {
        self.one.clone()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.mul(elem1, elem2), &self.modulo)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn div_rem_bigint() {
        let ring = BigIntegers();

        for n in -40..40 {
            let n: BigInt = n.into();
            for m in -40..40 {
                let m: BigInt = m.into();
                let (q, r) = ring.div_rem(&n, &m);
                println!("n={}, m={}, q={}, r={}", n, m, q, r);
                assert_eq!(n, &m * &q + &r);
                assert!(r.abs() <= (&r + &m).abs());
                assert!(r.abs() <= (&r - &m).abs());

                assert!(m.is_zero() || &r + &r <= m.abs());
                assert!(m.is_zero() || &r + &r > -m.abs());

                assert_eq!(q, ring.div(&n, &m));
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

    #[test]
    fn div_rem_int32() {
        let ring1 = Integers32();
        let ring2 = BigIntegers();

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

                let (q2, r2) = ring2.div_rem(&n2, &m2);
                if min2 <= q2 && q2 <= max2 && min2 <= r2 && r2 <= max2 {
                    let (q1, r1) = ring1.div_rem(&n1, &m1);
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
                        ring1.div_rem(&n1, &m1);
                    });
                    assert!(result.is_err());
                }
            }
        }
    }

    #[test]
    fn extended_gcd() {
        let ring = Integers32();

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
