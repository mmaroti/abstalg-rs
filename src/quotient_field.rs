// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::{Domain, EuclideanDomain, Field, IntegralDomain, UnitaryRing};

/// A quotient field of an Euclidean domain by a principal ideal
/// generated by an irreducible (prime) element.
#[derive(Clone, Debug, Default)]
pub struct QuotientField<R: EuclideanDomain> {
    base: R,
    modulo: R::Elem,
}

impl<R: EuclideanDomain> QuotientField<R> {
    /// Creates a field from the given Euclidean domain and one of
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

impl<R: EuclideanDomain> Domain for QuotientField<R> {
    type Elem = R::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.is_reduced(elem, &self.modulo)
    }
}

impl<R: EuclideanDomain> UnitaryRing for QuotientField<R> {
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

impl<R: EuclideanDomain> IntegralDomain for QuotientField<R> {}

impl<R: EuclideanDomain> EuclideanDomain for QuotientField<R> {
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if self.is_zero(elem2) {
            (self.zero(), elem1.clone())
        } else {
            (self.div(elem1, elem2), self.zero())
        }
    }

    fn associate_repr(&self, elem: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if self.is_zero(elem) {
            (self.zero(), self.one())
        } else {
            (self.one(), self.div(&self.one(), elem))
        }
    }
}

impl<R: EuclideanDomain> Field for QuotientField<R> {
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        let (g, _, mut r) = self.base.extended_gcd(&self.modulo, elem);
        if !self.base.is_one(&g) {
            let (a, b) = self.base.quo_rem(&self.base.one(), &g);
            assert!(self.base.is_zero(&b), "modulo was not irreducible");
            r = self.base.mul(&r, &a);
        }
        self.base.rem(&r, &self.modulo)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CheckedInts;

    #[test]
    fn field_1721() {
        let ring: CheckedInts<i32> = Default::default();
        let field = QuotientField::new(ring, 1721);

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
