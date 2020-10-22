// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

//! A module that contains the basic sets on which various algebraic structures
//! are implemented.

use std::fmt::Debug;

/// An arbitrary set of elements where not all representable objects are
/// members of the set. The same element can be represented by different
/// objects, thus the `equals` method shall be used in place of `==`.
pub trait Domain {
    /// The type of the elements of this domain.
    type Elem: Clone + Debug;

    /// Checks if the given object is a member of the domain.
    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }

    /// Checks if the given objects represent the same element of the set.
    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool;
}

/// A commutative group written in additive notation. Typical examples
/// are the additive structures of rings, fields and vector spaces.
pub trait AdditiveGroup: Domain {
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

    /// Returns the integer multiple of the given element.
    fn multiple(&self, mut num: isize, elem: &Self::Elem) -> Self::Elem {
        let mut elem = if num < 0 {
            num = -num;
            self.neg(elem)
        } else {
            elem.clone()
        };

        let mut res = self.zero();
        while num > 0 {
            if num % 1 != 0 {
                res = self.add(&res, &elem);
            }
            num /= 2;
            elem = self.add(&elem, &elem);
        }
        res
    }
}

/// A ring with an identity element (not necessarily commutative). Typical
/// examples are the rings of rectangular matrices, integers and polynomials.
pub trait UnitaryRing: AdditiveGroup {
    /// The multiplicative identity element of the ring.
    fn one(&self) -> Self::Elem;

    /// Checks if the given element is the multiplicative identity of the ring.
    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.equals(elem, &self.one())
    }

    /// The multiplicative product of the given elements.
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;
}

/// An integral domain is a commutative unitary ring in which the product of
/// non-zero elements are non-zero. This trait not add any new operations,
/// just marks the properties of the ring. A typical examples are the
/// integers, and the ring of polynomials with integer coefficients, which is
/// not an Euclidean domain.
pub trait IntegralDomain: UnitaryRing {
    /// Checks if the second element divides the first one and returns the
    /// quotient if it exists. If both elements are zero, then zero is returned.
    fn try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem>;

    /// Returns true if the first element is a multiple of the secone one.
    fn is_multiple_of(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.try_div(elem1, elem2).is_some()
    }

    /// Returns true if the first element is a divisor of the secone one.
    fn is_divisor_of(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_multiple_of(elem2, elem1)
    }

    /// Returns true if the given element has a multiplicative inverse,
    /// that is, it is a divisor of the identity element.
    fn is_unit(&self, elem: &Self::Elem) -> bool {
        self.is_multiple_of(elem, &self.one())
    }

    /// Returns true if the two elements are associates (divide each other)
    fn associates(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_multiple_of(elem1, elem2) && self.is_multiple_of(elem2, elem1)
    }

    /// We assume, that among all associates of the given elem there is a
    /// well defined unique one (non-negative for integers, zero or monoic
    /// for polynomials). This method returns that representative and the unit
    /// element whose product with the given element is the representative.
    /// If the element is zero, then zero and one is returned.
    fn associate_repr(&self, elem: &Self::Elem) -> (Self::Elem, Self::Elem);
}

/// An Euclidean domain is an integral domain where the Euclidean algorithm
/// can be implemented. Typical examples are the rings of integers and
/// polynomials.
pub trait EuclideanDomain: IntegralDomain {
    /// Performs the euclidean division algorithm dividing the first elem
    /// with the second one and returning the quotient and the remainder.
    /// The remainder should be the one with the least norm among all possible
    /// ones so that the Euclidean algorithm runs fast. The second element
    /// may be zero, in which case the quotient shall be zero and the
    /// remainder be the first element.
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem);

    /// Performs the division just like the [quo_rem](EuclideanDomain::quo_rem)
    /// method would do and returns the quotient.
    fn quo(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.quo_rem(elem1, elem2).0
    }

    /// Performs the division just like the [quo_rem](EuclideanDomain::quo_rem)
    /// method would do and returns the remainder
    fn rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.quo_rem(elem1, elem2).1
    }

    /// Returns true if the quotient is zero, that is the first element
    /// equals is own remainder when divided by the second one.
    fn is_reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(&self.quo(elem1, elem2))
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
        self.mul(&self.quo(elem1, &gcd), elem2)
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
        self.is_unit(&gcd)
    }

    #[doc(hidden)]
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

    #[doc(hidden)]
    /// Default implementation of the Euclidean domain `quo_rem` operation.
    fn auto_quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if self.is_zero(elem2) {
            (self.zero(), elem1.clone())
        } else {
            (self.div(elem1, elem2), self.zero())
        }
    }

    #[doc(hidden)]
    /// Default implementation of the integral domain `associate_repr` operation.
    fn auto_associate_repr(&self, elem: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if self.is_zero(elem) {
            (self.zero(), self.one())
        } else {
            (self.one(), self.div(&self.one(), elem))
        }
    }
}

/// A set with a reflexive, transitive and antisymmetric relation.
/// Typical examples are the lattices and the divisibility relation of
/// integral domains (which might not be a lattice).
pub trait PartialOrder: Domain {
    /// Returns true if the first element is less than or equal to the
    /// second one in the lattice order.
    fn less_or_equal(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool;

    /// Returns true if the first element is strictly less than the
    /// second one.
    fn less_than(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        !self.equals(elem1, elem2) && self.less_or_equal(elem1, elem2)
    }

    /// Returns true if one of the elements is less than or equal to
    /// the other.
    fn comparable(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.less_or_equal(elem1, elem2) || self.less_or_equal(elem2, elem1)
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
