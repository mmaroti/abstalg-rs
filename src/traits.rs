// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

//! A module that contains the basic sets on which various algebraic structures
//! are implemented.

use crate::*;
use std::fmt::Debug;

/// An arbitrary set of elements where not all representable objects are
/// members of the set. The same element can be represented by different
/// objects, thus the `equals` method shall be used in place of `==`.
pub trait Domain: Clone {
    /// The type of the elements of this domain.
    type Elem: Clone + Debug;

    /// Checks if the given object is a member of the domain.
    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }

    /// Checks if the given objects represent the same element of the set.
    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool;
}

/// An arbitrary (multiplicative) semigroup, which is set with an associative binary operation.
pub trait Semigroup: Domain {
    /// The multiplicative product of the given elements.
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;

    /// The first element is multiplied with the second one in place.
    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        *elem1 = self.mul(elem1, elem2);
    }

    /// Squares the given element in place.
    fn square(&self, elem: &mut Self::Elem) {
        *elem = self.mul(elem, elem);
    }
}

/// An arbitrary (multiplicative) monoid, which is a semigroup with an identity element.
/// Typical examples are the multiplicative monoid of unitary rings.
pub trait Monoid: Semigroup {
    /// The multiplicative identity element of the ring.
    fn one(&self) -> Self::Elem;

    /// Checks if the given element is the multiplicative identity.
    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.equals(elem, &self.one())
    }

    /// Calculates the multiplicative inverse of the given element if it exists.
    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem>;

    /// Returns true if the given element has a multiplicative inverse.
    fn invertible(&self, elem: &Self::Elem) -> bool {
        self.try_inv(elem).is_some()
    }
}

/// An arbitrary (multiplicative) group, which is a monoid where every element has an inverse.
/// Typical examples are the multiplicative and additive group of rings.
pub trait Group: Monoid {
    /// Returns the inverse of the given element element.
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        self.try_inv(elem).unwrap()
    }

    /// Returns the power of the given element using the square and multiply method.
    fn power(&self, mut num: isize, elem: &Self::Elem) -> Self::Elem {
        let mut elem = if num < 0 {
            num = -num;
            self.inv(elem)
        } else {
            elem.clone()
        };

        let mut res = self.one();
        while num > 0 {
            if num % 2 != 0 {
                self.mul_assign(&mut res, &elem);
            }
            num /= 2;
            self.square(&mut elem);
        }
        res
    }
}

/// A commutative group written in additive notation. Typical examples
/// are the additive structures of rings, fields and vector spaces.
pub trait AbelianGroup: Domain {
    /// The additive identity element of the ring.
    fn zero(&self) -> Self::Elem;

    /// Checks if the given element is the additive identity of the ring.
    fn is_zero(&self, elem: &Self::Elem) -> bool {
        self.equals(elem, &self.zero())
    }

    /// The additive inverse of the given element.
    fn neg(&self, elem: &Self::Elem) -> Self::Elem;

    /// The element is changed to its additive inverse.
    fn neg_assign(&self, elem: &mut Self::Elem) {
        *elem = self.neg(elem);
    }

    /// The additive sum of the given elements
    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;

    /// The second element is added to the first one.
    fn add_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        *elem1 = self.add(elem1, elem2);
    }

    /// Doubles the given element in place.
    fn double(&self, elem: &mut Self::Elem) {
        *elem = self.add(elem, elem);
    }

    /// The difference of the given elements.
    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let mut elem = self.neg(elem2);
        self.add_assign(&mut elem, elem1);
        elem
    }

    /// The second element is subtracted from the first one.
    fn sub_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        self.add_assign(elem1, &self.neg(elem2));
    }

    /// Returns an integer multiple of the given element.
    fn times(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let group = AdditiveGroup(self.clone());
        group.power(num, elem)
    }
}

/// A ring with an identity element (not necessarily commutative). Typical
/// examples are the rings of rectangular matrices, integers and polynomials.
pub trait UnitaryRing: AbelianGroup + Monoid {
    /// Returns the integer multiple of the one element in the ring.
    fn integer(&self, elem: isize) -> Self::Elem {
        self.times(elem, &self.one())
    }
}

/// An integral domain is a commutative unitary ring in which the product of
/// non-zero elements are non-zero. This trait not add any new operations,
/// just marks the properties of the ring. A typical examples are the
/// integers, and the ring of polynomials with integer coefficients, which is
/// not an Euclidean domain.
pub trait IntegralDomain: UnitaryRing {
    /// Checks if the second element divides the first one and returns the
    /// unique quotient if it exists. This method panics if the second element
    /// is zero (because there would be no unique solution).
    fn try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem>;

    /// Checks if the first element is a multiple of (or divisible by) the
    /// second one.
    fn divisible(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if self.is_zero(elem2) {
            self.is_zero(elem1)
        } else {
            self.try_div(elem1, elem2).is_some()
        }
    }

    /// Returns true if the two elements are associates (divide each other)
    fn associates(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.divisible(elem1, elem2) && self.divisible(elem2, elem1)
    }

    /// We assume, that among all associates of the given elem there is a
    /// well defined unique one (non-negative for integers, zero or monic
    /// for polynomials). This method returns that representative element.
    fn associate_repr(&self, elem: &Self::Elem) -> Self::Elem;

    /// Returns the unique invertible element which is the quotient of the
    /// associate representative and the given element. This method panics
    /// if the element is zero.
    fn associate_coef(&self, elem: &Self::Elem) -> Self::Elem;
}

/// An Euclidean domain is an integral domain where the Euclidean algorithm
/// can be implemented. Typical examples are the rings of integers and
/// polynomials.
pub trait EuclideanDomain: IntegralDomain {
    /// Performs the euclidean division algorithm dividing the first elem
    /// with the second one and returning the quotient and the remainder.
    /// The remainder should be the one with the least norm among all possible
    /// ones so that the Euclidean algorithm runs fast. This method panics
    /// if the second element is zero (because there is no unique solution)
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem);

    /// Performs the division just like the [quo_rem](EuclideanDomain::quo_rem)
    /// method would do and returns the quotient. This method panics if the
    /// second element is zero.
    fn quo(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.quo_rem(elem1, elem2).0
    }

    /// Performs the division just like the [quo_rem](EuclideanDomain::quo_rem)
    /// method would do and returns the remainder. This method panics if the
    /// second element is zero.
    fn rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.quo_rem(elem1, elem2).1
    }

    /// Returns true if the second element is zero or the first element
    /// has zero quotient by the second one. These are the representative
    /// elements of the factor ring by the principal ideal generated by
    /// the second element.
    fn reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(elem2) || self.is_zero(&self.quo(elem1, elem2))
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

    /// Calculates the lest common divisor of the two elements.
    fn lcm(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let gcd = self.gcd(elem1, elem2);
        if self.is_zero(&gcd) {
            gcd
        } else {
            self.mul(&self.quo(elem1, &gcd), elem2)
        }
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
    fn relative_primes(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        let gcd = self.gcd(elem1, elem2);
        self.invertible(&gcd)
    }

    #[doc(hidden)]
    /// Default implementation of the integral domain `try_div` method.
    fn auto_try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem> {
        let (quo, rem) = self.quo_rem(elem1, elem2);
        if self.is_zero(&rem) {
            Some(quo)
        } else {
            None
        }
    }
}

/// A field is a commutative ring with identity where each non-zero element
/// has a multiplicative inverse. Typical examples are the real, complex and
/// rational numbers, and finite fields constructed from an Euclidean domain
/// and one of its irreducible elements. All fields are Euclidean domains
/// themselves, with a rather trivial structure.
pub trait Field: EuclideanDomain {
    /// Returns the multiplicative inverse of the given non-zero element.
    /// This method panics for the zero element.
    fn inv(&self, elem: &Self::Elem) -> Self::Elem;

    /// Returns the quotient of the two elements in the field. This method
    /// panics if the second element is zero.
    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.mul(elem1, &self.inv(elem2))
    }

    /// Returns an integer power of the given element.
    fn power(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem) {
            self.zero()
        } else {
            let group = MultiplicativeGroup(self.clone());
            group.power(num, elem)
        }
    }

    #[doc(hidden)]
    /// Default implementation of the Euclidean domain `quo_rem` method.
    fn auto_quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        assert!(!self.is_zero(elem2));
        (self.div(elem1, elem2), self.zero())
    }

    #[doc(hidden)]
    /// Default implementation of the integral domain `associate_repr` method.
    fn auto_associate_repr(&self, elem: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem) {
            self.zero()
        } else {
            self.one()
        }
    }

    #[doc(hidden)]
    /// Default implementation of the integral domain `associate_coef` method.
    fn auto_associate_coef(&self, elem: &Self::Elem) -> Self::Elem {
        self.inv(elem)
    }
}

/// A set with a reflexive, transitive and antisymmetric relation.
/// Typical examples are the lattices and the divisibility relation of
/// integral domains (which might not be a lattice).
pub trait PartialOrder: Domain {
    /// Returns true if the first element is less than or equal to the
    /// second one in the lattice order.
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool;

    /// Returns true if the first element is strictly less than the
    /// second one.
    fn less_than(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        !self.equals(elem1, elem2) && self.leq(elem1, elem2)
    }

    /// Returns true if one of the elements is less than or equal to
    /// the other.
    fn comparable(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.leq(elem1, elem2) || self.leq(elem2, elem1)
    }
}

/// A set where the join and meet of elements can be calculated. Typical
/// examples are the total orders of integers or the divisibility relation
/// on the associate classes of an Euclidean domain.
pub trait Lattice: PartialOrder {
    /// Returns the largest element that is less than or equal to both given
    /// elements.
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;

    /// Returns the smallest element that is greater than or equal to both
    /// given elements.
    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;
}

/// A partial order that has a largest and smallest element. Typical
/// examples are bounded lattices.
pub trait BoundedOrder: PartialOrder {
    /// Returns the largest element of the lattice.
    fn max(&self) -> Self::Elem;

    /// Returns the smallest element of the lattice.
    fn min(&self) -> Self::Elem;
}

/// A lattice that is distributive. No new methods are added.
pub trait DistributiveLattice: Lattice {}
