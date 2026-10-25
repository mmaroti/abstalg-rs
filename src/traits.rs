// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

//! A module that contains the basic sets on which various algebraic
//! structures are implemented.

use crate::*;
use std::fmt::Debug;

/// An arbitrary set of elements where not all representable objects are
/// members of the set. The same element can be represented by different
/// objects, so the `equals` method should be used in place of `==`.
pub trait Domain: Clone {
    /// The type of the elements of this domain.
    type Elem: Clone + Debug;

    /// Checks membership for any `Self::Elem`, returning false for invalid
    /// representations.
    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }

    /// Checks if the given objects represent the same element of the set.
    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool;
}

/// An arbitrary (multiplicative) semigroup, which is a set with an associative
/// binary operation.
pub trait Semigroup: Domain {
    /// The multiplicative product of the given elements.
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;

    /// Multiplies the first element by the second one in place.
    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        *elem1 = self.mul(elem1, elem2);
    }

    /// Squares the given element in place.
    fn square(&self, elem: &mut Self::Elem) {
        *elem = self.mul(elem, elem);
    }
}

/// An arbitrary multiplicative monoid, which is a semigroup with an identity
/// element. Typical examples are the multiplicative monoids of unitary rings.
pub trait Monoid: Semigroup {
    /// The multiplicative identity element of the monoid.
    fn one(&self) -> Self::Elem;

    /// Checks if the given element is the multiplicative identity.
    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.equals(elem, &self.one())
    }

    /// Calculates the multiplicative inverse of the given element if it
    /// exists.
    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem>;

    /// Returns true if the given element has a multiplicative inverse.
    fn invertible(&self, elem: &Self::Elem) -> bool {
        self.try_inv(elem).is_some()
    }
}

/// An arbitrary commutative (additive) monoid. A typical example is the set
/// of natural numbers including zero with addition.
pub trait CommutativeMonoid: Domain {
    /// The additive identity element of the commutative monoid.
    fn zero(&self) -> Self::Elem;

    /// Checks if the given element is the additive identity of the monoid.
    fn is_zero(&self, elem: &Self::Elem) -> bool {
        self.equals(elem, &self.zero())
    }

    /// The additive sum of the given elements.
    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;

    /// The second element is added to the first one.
    fn add_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        *elem1 = self.add(elem1, elem2);
    }

    /// Doubles the given element in place.
    fn double(&self, elem: &mut Self::Elem) {
        *elem = self.add(elem, elem);
    }

    /// Returns an integer multiple of the given element.
    fn times(&self, mut num: usize, elem: &Self::Elem) -> Self::Elem {
        let mut elem = elem.clone();
        let mut res = self.zero();
        while num > 0 {
            if num % 2 != 0 {
                self.add_assign(&mut res, &elem);
            }
            num /= 2;
            if num > 0 {
                self.double(&mut elem);
            }
        }
        res
    }
}

/// Compatibility alias for the original spelling of [`CommutativeMonoid`].
pub use CommutativeMonoid as CommuntativeMonoid;

/// An arbitrary (multiplicative) group, which is a monoid where every element
/// has an inverse. Typical examples are the additive groups of rings and the
/// multiplicative groups of their invertible elements.
pub trait Group: Monoid {
    /// Returns the inverse of the given element.
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        self.try_inv(elem).unwrap()
    }

    /// Returns the power of the given element using the square-and-multiply
    /// method.
    fn power(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let mut elem = if num < 0 {
            self.inv(elem)
        } else {
            elem.clone()
        };
        let mut num = num.unsigned_abs();

        let mut res = self.one();
        while num > 0 {
            if num % 2 != 0 {
                self.mul_assign(&mut res, &elem);
            }
            num /= 2;
            if num > 0 {
                self.square(&mut elem);
            }
        }
        res
    }
}

/// A commutative group written in additive notation. Typical examples
/// are the additive structures of rings, fields, and vector spaces.
pub trait AbelianGroup: CommutativeMonoid {
    /// The additive inverse of the given element.
    fn neg(&self, elem: &Self::Elem) -> Self::Elem;

    /// The element is changed to its additive inverse.
    fn neg_assign(&self, elem: &mut Self::Elem) {
        *elem = self.neg(elem);
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
        let group = AdditiveGroup::new(self.clone());
        group.power(num, elem)
    }
}

/// A (not necessarily commutative) semiring. A typical example is the set
/// of natural numbers with addition and multiplication.
pub trait SemiRing: CommutativeMonoid + Monoid {}

/// A ring with an identity element (not necessarily commutative). Typical
/// examples are the rings of square matrices, integers, and polynomials.
pub trait UnitaryRing: SemiRing + AbelianGroup {
    /// Returns the given integer multiple of the multiplicative identity
    /// of the ring.
    fn int(&self, elem: isize) -> Self::Elem {
        AbelianGroup::times(self, elem, &self.one())
    }
}

/// An integral domain is a commutative unitary ring in which the product of
/// non-zero elements is non-zero. This trait adds operations for divisibility
/// and associates. Typical examples are the integers and the ring of
/// polynomials with integer coefficients; the latter is not a Euclidean domain.
pub trait IntegralDomain: UnitaryRing {
    /// Checks if the second element divides the first one and returns the
    /// unique quotient if it exists. This method panics if the second element
    /// is zero (because then there would be no unique solution).
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

    /// Returns true if the two elements are associates (divide each other).
    fn associates(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.divisible(elem1, elem2) && self.divisible(elem2, elem1)
    }

    /// We assume that among all associates of the given element there is a
    /// unique, well-defined representative (non-negative for integers, zero
    /// or monic for polynomials). This method returns that representative element.
    fn associate_repr(&self, elem: &Self::Elem) -> Self::Elem;

    /// Returns the unique invertible element obtained by dividing the
    /// associate representative by the given element. This method panics
    /// if the element is zero.
    fn associate_coef(&self, elem: &Self::Elem) -> Self::Elem;
}

/// A Euclidean domain is an integral domain where the Euclidean algorithm
/// can be implemented. Typical examples are the rings of integers and
/// polynomials.
pub trait EuclideanDomain: IntegralDomain {
    /// Performs Euclidean division, dividing the first element by the second
    /// one and returning the quotient and the remainder.
    /// This method panics if the second element is zero (because there is
    /// no unique solution).
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem);

    /// Performs division as in [quo_rem](EuclideanDomain::quo_rem) and returns
    /// the quotient. This method panics if the second element is zero.
    fn quo(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.quo_rem(elem1, elem2).0
    }

    /// Performs division as in [quo_rem](EuclideanDomain::quo_rem) and returns
    /// the remainder. This method panics if the second element is zero.
    fn rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.quo_rem(elem1, elem2).1
    }

    /// Returns true if the second element is zero or the first element
    /// has a zero quotient when divided by the second one. These are the
    /// representative elements of the factor ring by the principal ideal
    /// generated by the second element.
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

    /// Calculates the least common multiple of the two elements.
    fn lcm(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let gcd = self.gcd(elem1, elem2);
        if self.is_zero(&gcd) {
            gcd
        } else {
            self.mul(&self.quo(elem1, &gcd), elem2)
        }
    }

    /// Performs the extended Euclidean algorithm, returning the greatest
    /// common divisor and two coefficients whose products with the respective
    /// inputs sum to the greatest common divisor.
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

    /// Checks if the two given elements are relatively prime.
    fn relative_primes(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        let gcd = self.gcd(elem1, elem2);
        self.invertible(&gcd)
    }
}

/// A field is a commutative ring with identity where each non-zero element
/// has a multiplicative inverse. Typical examples are the real, complex, and
/// rational numbers, and finite fields constructed from a Euclidean domain
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
            let group = MultiplicativeGroup::new(self.clone());
            group.power(num, elem)
        }
    }
}

impl<A: Field> IntegralDomain for A {
    fn try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem> {
        Some(self.div(elem1, elem2))
    }

    fn associate_repr(&self, elem: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem) {
            self.zero()
        } else {
            self.one()
        }
    }

    fn associate_coef(&self, elem: &Self::Elem) -> Self::Elem {
        self.inv(elem)
    }
}

impl<A: Field> EuclideanDomain for A {
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        assert!(!self.is_zero(elem2));
        (self.div(elem1, elem2), self.zero())
    }

    fn quo(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(!self.is_zero(elem2));
        self.div(elem1, elem2)
    }

    fn rem(&self, _elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(!self.is_zero(elem2));
        self.zero()
    }

    fn reduced(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.is_zero(elem1) || self.is_zero(elem2)
    }

    fn gcd(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem1) && self.is_zero(elem2) {
            self.zero()
        } else {
            self.one()
        }
    }

    fn lcm(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        if self.is_zero(elem1) || self.is_zero(elem2) {
            self.zero()
        } else {
            self.one()
        }
    }
}

/// A set with a reflexive, transitive, and antisymmetric relation.
/// Typical examples are lattices and the divisibility order on associate
/// classes of integral domains (which need not be a lattice).
pub trait PartialOrder: Domain {
    /// Returns true if the first element is less than or equal to the
    /// second one in the partial order.
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

/// A partial order that has a largest and a smallest element. Typical
/// examples are bounded lattices.
pub trait BoundedOrder: PartialOrder {
    /// Returns the largest element of the order.
    fn max(&self) -> Self::Elem;

    /// Returns the smallest element of the order.
    fn min(&self) -> Self::Elem;
}

/// A set where the join and meet of elements can be calculated. Typical
/// examples are the total orders of integers or the divisibility relation
/// on the associate classes of a Euclidean domain.
pub trait Lattice: PartialOrder {
    /// Returns the largest element that is less than or equal to both given
    /// elements.
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;

    /// Returns the smallest element that is greater than or equal to both
    /// given elements.
    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem;
}

/// A lattice that is distributive. No new methods are added.
pub trait DistributiveLattice: Lattice {}

/// A Boolean algebra, which is a complemented bounded distributive lattice.
/// Typical examples are the two-element Boolean algebra and power sets.
pub trait BooleanAlgebra: DistributiveLattice + BoundedOrder {
    /// Returns the complement (logical negation) of the given element.
    fn not(&self, elem: &Self::Elem) -> Self::Elem;
}
