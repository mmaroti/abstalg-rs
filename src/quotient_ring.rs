// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// A quotient ring of an Euclidean domain by a principal ideal.
#[derive(Clone, Debug)]
pub struct QuotientRing<A>
where
    A: EuclideanDomain,
{
    base: A,
    modulo: A::Elem,
}

impl<A> QuotientRing<A>
where
    A: EuclideanDomain,
{
    /// Creates a new quotient ring from the given Euclidean domain and
    /// one of its element.
    pub fn new(base: A, modulo: A::Elem) -> Self {
        assert!(base.contains(&modulo));
        QuotientRing { base, modulo }
    }

    /// Returns the base ring from which this ring was constructed.
    pub fn base(&self) -> &A {
        &self.base
    }

    /// Returns the modulo element from which this ring was constructed.
    pub fn modulo(&self) -> &A::Elem {
        &self.modulo
    }
}

impl<A> Domain for QuotientRing<A>
where
    A: EuclideanDomain,
{
    type Elem = A::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.reduced(elem, &self.modulo)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1, elem2)
    }
}

impl<A> Semigroup for QuotientRing<A>
where
    A: EuclideanDomain,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.mul(elem1, elem2), &self.modulo)
    }
}

impl<A> Monoid for QuotientRing<A>
where
    A: EuclideanDomain,
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

impl<A> CommuntativeMonoid for QuotientRing<A>
where
    A: EuclideanDomain,
{
    fn zero(&self) -> Self::Elem {
        self.base.zero()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.add(elem1, elem2), &self.modulo)
    }
}

impl<A> AbelianGroup for QuotientRing<A>
where
    A: EuclideanDomain,
{
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.neg(elem), &self.modulo)
    }
}

impl<A> UnitaryRing for QuotientRing<A> where A: EuclideanDomain {}

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
