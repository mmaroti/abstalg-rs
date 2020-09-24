// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use num_bigint::BigInt;

/// An arbitrary set of elements.
pub trait Domain {
    /// The type of the elements of this domain.
    type Elem;

    /// Checks if the given element is a member of the domain.
    fn contains(&self, elem: &Self::Elem) -> bool;

    /// Checks if the given elements represent the same value in the domain.
    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool;
}

/// The ring of integers whose elements are [BigInt](num_bigint::BigInt)
/// objects.
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
pub struct SmallIntegers();

impl Domain for SmallIntegers {
    type Elem = i32;

    fn contains(&self, _elem: &Self::Elem) -> bool {
        true
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

/// A ring with an identity element (not necessarily commutative). Typical
/// examples are the rings of rectangular matrices, integers and polynomials.
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
    fn unit(&self) -> Self::Elem;

    /// Checks if the given element is the multiplicative identity of the ring.
    fn is_unit(&self, elem: &Self::Elem) -> bool {
        self.equals(elem, &self.unit())
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

    fn unit(&self) -> Self::Elem {
        1.into()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1 * elem2
    }
}

impl RingWithIdentity for SmallIntegers {
    fn zero(&self) -> Self::Elem {
        0
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        i32::checked_neg(*elem).unwrap()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i32::checked_add(*elem1, *elem2).unwrap()
    }

    fn unit(&self) -> Self::Elem {
        1
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        i32::checked_mul(*elem1, *elem2).unwrap()
    }
}

/// An Euclidean domain is an integral domain where the Euclidean algorithm
/// can be implemented. Typical examples are the rings of integers and
/// polynomials.
pub trait EuclideanDomain: RingWithIdentity {
    /// Performs the euclidean division algorithm dividing the first elem
    /// with the second one and returning the quotient and the remainder.
    /// The remainder should be the one with the least norm so that
    /// the Euclidean algorithm runs fast.
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
}
