// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// A quotient ring of an Euclidean domain by a principal ideal.
#[derive(Clone, Debug, Default)]
pub struct QuotientRing<R>
where
    R: EuclideanDomain,
{
    base: R,
    modulo: R::Elem,
}

impl<R> QuotientRing<R>
where
    R: EuclideanDomain,
{
    /// Creates a new quotient ring from the given Euclidean domain and
    /// one of its element.
    pub fn new(base: R, modulo: R::Elem) -> Self {
        assert!(base.contains(&modulo));
        QuotientRing { base, modulo }
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

impl<R> Domain for QuotientRing<R>
where
    R: EuclideanDomain,
{
    type Elem = R::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.reduced(elem, &self.modulo)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1, elem2)
    }
}

impl<R> Semigroup for QuotientRing<R>
where
    R: EuclideanDomain,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.mul(elem1, elem2), &self.modulo)
    }
}

impl<R> Monoid for QuotientRing<R>
where
    R: EuclideanDomain,
{
    fn one(&self) -> Self::Elem {
        self.base.one()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.base.is_one(elem)
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        let (g, _, r) = self.base.extended_gcd(&self.modulo, elem);
        self.base.try_inv(&g).map(|a| self.mul(&a, &r))
    }
}

impl<R> AbelianGroup for QuotientRing<R>
where
    R: EuclideanDomain,
{
    fn zero(&self) -> Self::Elem {
        self.base.zero()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.neg(elem), &self.modulo)
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.add(elem1, elem2), &self.modulo)
    }
}

impl<R> UnitaryRing for QuotientRing<R> where R: EuclideanDomain {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zstar_1584() {
        let ring = QuotientRing::new(I32, 1584); // 16 * 9 *11

        let mut count = 0;
        for a in 0..1584 {
            assert!(ring.contains(&a));
            if a != 0 {
                if let Some(b) = ring.try_inv(&a) {
                    assert!(ring.contains(&b));
                    assert!(ring.is_one(&ring.mul(&a, &b)));
                    count += 1;
                }
            }
        }
        assert_eq!(count, 8 * 6 * 10);
    }
}
