// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

//! A module that contains ring like structures.

use crate::{Domain, Integers, PartialInts};
use num::{
    BigInt, BigRational, CheckedAdd, CheckedDiv, CheckedMul, CheckedSub, Integer, One, PrimInt,
    Signed, Zero,
};
use std::ops::Mul;

/// The ring of integers modulo 2^32 whose elements are represented with
/// signed 32-bit integers. All operations will wrap around.
pub struct ModularInt32();

impl Domain for ModularInt32 {
    type Elem = i32;

    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }
}

/// The ring of integers modulo 2^64 whose elements are represented with
/// signed 64-bit integers. All operations will wrap around.
pub struct ModularInt64();

impl Domain for ModularInt64 {
    type Elem = i64;

    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }
}

/// The field of fractions of an Euclidean ring. All elements are
/// represented in their normal form where the denominator is non-zero
/// the numerator and denominator are relative prime, and the
pub struct Fractions<R: EuclideanRing> {
    base: R,
}

impl<R: EuclideanRing> Fractions<R> {
    /// Creates a new field of fractions from the give Euclidean ring.
    pub fn new(base: R) -> Self {
        Fractions { base }
    }

    /// Returns the base from which this field of created from.
    pub fn base(&self) -> &R {
        &self.base
    }
}

//impl<R: EuclideanRing> Domain for Fractions<R> {
//    type Elem = Ratio<R::Elem>;
//
//    fn contains(&self, elem: &Self::Elem) -> bool {
//        !self.base.is_zero(elem.denom())
//            && self.base.are_relative_primes(elem.numer(), elem.denom())
//    }
//}

/// The field of rational numbers whose elements are
/// [BigRational](../../num/type.BigRational.html) objects.
#[derive(Clone, Debug, Default)]
pub struct Rationals();

impl Domain for Rationals {
    type Elem = BigRational;

    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }
}

/// The field of real numbers approximated by 32-bit floating point
/// values. NaN and infinity values are not considered as members,
/// so all operations resulting one of these will panic.
pub struct ApproxFloat32();

impl Domain for ApproxFloat32 {
    type Elem = f32;

    fn contains(&self, elem: &Self::Elem) -> bool {
        elem.is_finite()
    }
}

/// The field of real numbers approximated by 64-bit floating point
/// values. NaN and infinity values are not considered as members,
/// so all operations resulting one of these will panic.
pub struct ApproxFloat64();

impl Domain for ApproxFloat64 {
    type Elem = f64;

    fn contains(&self, elem: &Self::Elem) -> bool {
        elem.is_finite()
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
        elem == &self.zero()
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
        elem == &self.one()
    }

    /// The multiplicative product of the given elements.
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;
}

impl RingWithIdentity for Integers {
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

impl<R> RingWithIdentity for R
where
    R: PartialInts,
    R::Elem: PrimInt + Zero + One + CheckedAdd + CheckedSub + CheckedMul,
{
    fn zero(&self) -> Self::Elem {
        Zero::zero()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        let z: Self::Elem = Zero::zero();
        z.checked_sub(elem).unwrap()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.checked_add(elem2).unwrap()
    }

    fn one(&self) -> Self::Elem {
        One::one()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.checked_mul(elem2).unwrap()
    }
}

impl RingWithIdentity for ModularInt32 {
    fn zero(&self) -> Self::Elem {
        0
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        i32::wrapping_neg(*elem)
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i32::wrapping_add(*elem1, *elem2)
    }

    fn one(&self) -> Self::Elem {
        1
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i32::wrapping_mul(*elem1, *elem2)
    }
}

impl RingWithIdentity for ModularInt64 {
    fn zero(&self) -> Self::Elem {
        0
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        i64::wrapping_neg(*elem)
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i64::wrapping_add(*elem1, *elem2)
    }

    fn one(&self) -> Self::Elem {
        1
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i64::wrapping_mul(*elem1, *elem2)
    }
}

impl RingWithIdentity for Rationals {
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

impl RingWithIdentity for ApproxFloat32 {
    fn zero(&self) -> Self::Elem {
        0.0
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        let r = -elem;
        assert!(r.is_finite());
        r
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = elem1 + elem2;
        assert!(r.is_finite());
        r
    }

    fn one(&self) -> Self::Elem {
        1.0
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = elem1 * elem2;
        assert!(r.is_finite());
        r
    }
}

impl RingWithIdentity for ApproxFloat64 {
    fn zero(&self) -> Self::Elem {
        0.0
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        let r = -elem;
        assert!(r.is_finite());
        r
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = elem1 + elem2;
        assert!(r.is_finite());
        r
    }

    fn one(&self) -> Self::Elem {
        1.0
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = elem1 * elem2;
        assert!(r.is_finite());
        r
    }
}

/// An Euclidean ring is an integral domain where the Euclidean algorithm
/// can be implemented. Typical examples are the rings of integers and
/// polynomials.
pub trait EuclideanRing: RingWithIdentity {
    /// Performs the euclidean division algorithm dividing the first elem
    /// with the second one and returning the quotient and the remainder.
    /// The remainder should be the one with the least norm among all possible
    /// ones so that the Euclidean algorithm runs fast. The second element
    /// may be zero, in which case the quotient shall be zero and the
    /// remainder be the first element.
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem);

    /// Performs the division just like the [quo_rem](EuclideanRing::quo_rem)
    /// method would do and returns the quotient.
    fn quo(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.quo_rem(elem1, elem2).0
    }

    /// Performs the division just like the [quo_rem](EuclideanRing::quo_rem)
    /// method would do and returns the remainder
    fn rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.quo_rem(elem1, elem2).1
    }

    /// Returns true if the first element is a multiple of the second one.
    fn is_multiple_of(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(&self.rem(elem1, elem2))
    }

    /// Returns true if the first element is its own remainder when the
    /// divided by the second one (so the quotient is zero).
    fn is_reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(&self.quo(elem1, elem2))
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
            let (quo, rem) = self.quo_rem(elem1, elem2);
            let (gcd, x, y) = self.extended_gcd(elem2, &rem);
            let z = self.sub(&x, &self.mul(&y, &quo));
            (gcd, y, z)
        }
    }

    /// Checks if the given two elements are relative prime.
    fn are_relative_primes(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
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

impl EuclideanRing for Integers {
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

    fn normalizer(&self, elem: &Self::Elem) -> Self::Elem {
        if elem.is_negative() {
            (-1).into()
        } else {
            1.into()
        }
    }
}

#[doc(hidden)]
pub trait EuclideanRingImpl<K>: RingWithIdentity {
    fn auto_quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem);
}

impl<R, K> EuclideanRing for R
where
    R: EuclideanRingKind<Kind = K>,
    R: EuclideanRingImpl<K>,
{
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        self.auto_quo_rem(elem1, elem2)
    }
}

#[doc(hidden)]
pub trait EuclideanRingKind {
    type Kind;
}

#[doc(hidden)]
pub struct EuclideanRingKind1;

impl<R> EuclideanRingKind for R
where
    R: PartialInts,
    R::Elem: PrimInt,
{
    type Kind = EuclideanRingKind1;
}

impl<R> EuclideanRingImpl<EuclideanRingKind1> for R
where
    R: RingWithIdentity,
    R::Elem: PrimInt + CheckedDiv + Mul + Signed,
{
    fn auto_quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if self.is_zero(elem2) {
            (self.zero(), *elem1)
        } else {
            let quo = elem1.checked_div(elem2).unwrap();
            let rem = *elem1 - self.mul(&quo, elem2);

            if !elem1.is_negative() && !elem2.is_negative() {
                let tmp = *elem2 - rem;
                if rem > tmp {
                    return (quo + self.one(), -tmp);
                }
            } else if elem1.is_negative() && elem2.is_negative() {
                let tmp = *elem2 - rem;
                if rem <= tmp {
                    return (quo + self.one(), -tmp);
                }
            } else if !elem1.is_negative() && elem2.is_negative() {
                let tmp = *elem2 + rem;
                if -rem < tmp {
                    return (quo - self.one(), tmp);
                }
            } else if elem1.is_negative() && !elem2.is_negative() {
                let tmp = *elem2 + rem;
                if -rem >= tmp {
                    return (quo - self.one(), tmp);
                }
            }

            (quo, rem)
        }
    }
}

/*
impl EuclideanRing for PartialInt32 {
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if *elem2 == 0 {
            (0, *elem1)
        } else {
            let quo = i32::checked_div(*elem1, *elem2).unwrap();
            let rem = *elem1 - quo * elem2;

            if *elem1 >= 0 && *elem2 >= 0 {
                let tmp = *elem2 - rem;
                if rem > tmp {
                    return (quo + 1, -tmp);
                }
            } else if *elem1 < 0 && *elem2 < 0 {
                let tmp = *elem2 - rem;
                if rem <= tmp {
                    return (quo + 1, -tmp);
                }
            } else if *elem1 >= 0 && *elem2 < 0 {
                let tmp = elem2 + rem;
                if -rem < tmp {
                    return (quo - 1, tmp);
                }
            } else if *elem1 < 0 && *elem2 >= 0 {
                let tmp = elem2 + rem;
                if -rem >= tmp {
                    return (quo - 1, tmp);
                }
            }

            (quo, rem)
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

impl EuclideanRing for PartialInt64 {
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if *elem2 == 0 {
            (0, *elem1)
        } else {
            let quo = i64::checked_div(*elem1, *elem2).unwrap();
            let rem = *elem1 - quo * elem2;

            if *elem1 >= 0 && *elem2 >= 0 {
                let tmp = *elem2 - rem;
                if rem > tmp {
                    return (quo + 1, -tmp);
                }
            } else if *elem1 < 0 && *elem2 < 0 {
                let tmp = *elem2 - rem;
                if rem <= tmp {
                    return (quo + 1, -tmp);
                }
            } else if *elem1 >= 0 && *elem2 < 0 {
                let tmp = elem2 + rem;
                if -rem < tmp {
                    return (quo - 1, tmp);
                }
            } else if *elem1 < 0 && *elem2 >= 0 {
                let tmp = elem2 + rem;
                if -rem >= tmp {
                    return (quo - 1, tmp);
                }
            }

            (quo, rem)
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
*/
/// A quotient ring of an Euclidean ring by a principal ideal.
#[derive(Clone, Debug, Default)]
pub struct QuotientRing<R: EuclideanRing> {
    base: R,
    modulo: R::Elem,
    one: R::Elem,
}

impl<R: EuclideanRing> QuotientRing<R> {
    /// Creates a new quotient ring from the given Euclidean ring and
    /// one of its element.
    pub fn new(base: R, modulo: R::Elem) -> Self {
        assert!(base.contains(&modulo));
        // if the quotient is trivial, then the identity element becomes zero.
        let one = base.quo(&base.one(), &modulo);
        QuotientRing { base, modulo, one }
    }

    /// Returns the base ring from which this ring was constructed.
    pub fn base(&self) -> &R {
        &self.base
    }

    /// Returns the modulo element from which this ring was constructed.
    pub fn modulo(&self) -> &R::Elem {
        &self.modulo
    }
}

impl<R: EuclideanRing> Domain for QuotientRing<R> {
    type Elem = R::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.is_reduced(elem, &self.modulo)
    }
}

impl<R: EuclideanRing> RingWithIdentity for QuotientRing<R> {
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

/// A quotient field of an Euclidean ring by a principal ideal
/// generated by an irreducible (prime) element.
#[derive(Clone, Debug, Default)]
pub struct QuotientField<R: EuclideanRing> {
    base: R,
    modulo: R::Elem,
}

impl<R: EuclideanRing> QuotientField<R> {
    /// Creates a field from the given Euclidean ring and one of
    /// its irreducible (prime) element. This method does not check
    /// that the modulo is indeed irreducible. If this fails, then
    /// calculating the multiplicative inverse of some elements
    /// may panic.
    pub fn new(base: R, modulo: R::Elem) -> Self {
        assert!(base.contains(&modulo));
        let one = base.one();
        assert!(base.is_zero(&base.rem(&one, &one)));
        QuotientField { base, modulo }
    }

    /// Returns the base ring from which this field was constructed.
    pub fn base(&self) -> &R {
        &self.base
    }

    /// Returns the modulo element from which this field was constructed.
    pub fn modulo(&self) -> &R::Elem {
        &self.modulo
    }
}

impl<R: EuclideanRing> Domain for QuotientField<R> {
    type Elem = R::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.is_reduced(elem, &self.modulo)
    }
}

impl<R: EuclideanRing> RingWithIdentity for QuotientField<R> {
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
        self.base.one()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.mul(elem1, elem2), &self.modulo)
    }
}

/// A field is a commutative ring with identity where each non-zero element
/// has a multiplicative inverse. Typical examples are the real, complex and
/// rational numbers, and finite fields constructed from an Euclidean ring
/// and one of its irreducible elements. All fields are Euclidean rings
/// themselves, which will be automatically derived.
pub trait Field: RingWithIdentity {
    /// Returns the multiplicative inverse of the given non-zero element.
    /// This method panics for the zero element.
    fn inv(&self, elem: &Self::Elem) -> Self::Elem;

    /// Returns the quotient of the two elements in the field. This method
    /// panics if the second element is zero.
    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.mul(elem1, &self.inv(elem2))
    }
}

#[doc(hidden)]
pub struct EuclideanRingKind2;

impl<F: Field> EuclideanRingImpl<EuclideanRingKind2> for F {
    fn auto_quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if self.is_zero(elem2) {
            (self.zero(), elem1.clone())
        } else {
            (self.div(elem1, elem2), self.zero())
        }
    }
}

/*
impl<F: Field> EuclideanRing for F {
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if self.is_zero(elem2) {
            (self.zero(), elem1.clone())
        } else {
            (self.div(elem1, elem2), self.zero())
        }
    }

    fn quo(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem2) {
            self.zero()
        } else {
            self.div(elem1, elem2)
        }
    }

    fn rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem2) {
            elem1.clone()
        } else {
            self.zero()
        }
    }

    fn is_multiple_of(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(elem1) || !self.is_zero(elem2)
    }

    fn is_reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(elem1) || self.is_zero(elem2)
    }

    fn are_associated(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(elem1) == self.is_zero(elem2)
    }

    fn is_unit(&self, elem: &Self::Elem) -> bool {
        !self.is_zero(elem)
    }

    fn gcd(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem1) && self.is_zero(elem2) {
            self.zero()
        } else {
            self.one()
        }
    }

    fn extended_gcd(
        &self,
        elem1: &Self::Elem,
        elem2: &Self::Elem,
    ) -> (Self::Elem, Self::Elem, Self::Elem) {
        if !self.is_zero(elem1) {
            (self.one(), self.inv(elem1), self.zero())
        } else if !self.is_zero(elem2) {
            (self.one(), self.zero(), self.inv(elem2))
        } else {
            (self.zero(), self.zero(), self.zero())
        }
    }

    fn are_relative_primes(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        !self.is_zero(elem1) && !self.is_zero(elem2)
    }

    fn normalizer(&self, elem: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem) {
            self.zero()
        } else {
            self.one()
        }
    }
}
*/
impl<R: EuclideanRing> Field for QuotientField<R> {
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        let (g, _, mut r) = self.base.extended_gcd(&self.modulo, elem);
        if !self.base.is_one(&g) {
            let (a, b) = self.base.quo_rem(&self.base.one(), &g);
            assert!(self.base.is_zero(&b), "modulo was not irreducible");
            r = self.base.mul(&r, &a);
        }
        let r = self.base.rem(&r, &self.modulo);
        r
    }
}

impl<R: EuclideanRing> EuclideanRingKind for QuotientField<R> {
    type Kind = EuclideanRingKind2;
}

impl Field for Rationals {
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        elem.recip()
    }

    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 / elem2
    }
}

impl Field for ApproxFloat32 {
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        let r = 1.0 / elem;
        assert!(r.is_finite());
        r
    }

    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = elem1 / elem2;
        assert!(r.is_finite());
        r
    }
}

impl Field for ApproxFloat64 {
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        let r = 1.0 / elem;
        assert!(r.is_finite());
        r
    }

    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = elem1 / elem2;
        assert!(r.is_finite());
        r
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PartialInt32;

    #[test]
    fn quo_rem_bigint() {
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

    #[test]
    fn quo_rem_int32() {
        let ring1 = PartialInt32();
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
        let ring = PartialInt32();

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

    #[test]
    fn field_1721() {
        let field = QuotientField::new(PartialInt32(), 1721);

        for a in -860..860 {
            assert!(field.contains(&a));
            if a != 0 {
                let b = field.inv(&a);
                assert!(field.contains(&b));
                println!("{} {}", a, b);
                assert!(field.is_one(&field.mul(&a, &b)));
            }
        }
    }
}
