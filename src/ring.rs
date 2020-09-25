// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

//! A module that contains ring like structures.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Signed;
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

    /// Checks if the given two elements are relative prime.
    fn are_relative_prime(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        let gcd = self.gcd(elem1, elem2);
        self.is_unit(&gcd)
    }

    /// Among all the associates of the given elem if there is a well defined
    /// unique one (non-negative for integers, zero or monoic for polynomials),
    /// then this method returns that one. In general this method returns the
    /// given element.
    fn normalize(&self, elem: &Self::Elem) -> Self::Elem {
        elem.clone()
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

    fn normalize(&self, elem: &Self::Elem) -> Self::Elem {
        elem.abs()
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

    fn normalize(&self, elem: &Self::Elem) -> Self::Elem {
        i32::checked_abs(*elem).unwrap()
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

    fn normalize(&self, elem: &Self::Elem) -> Self::Elem {
        i64::checked_abs(*elem).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::sign::Signed;

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
                } else {
                    let result = std::panic::catch_unwind(|| {
                        ring1.div_rem(&n1, &m1);
                    });
                    assert!(result.is_err());
                }
            }
        }
    }
}
