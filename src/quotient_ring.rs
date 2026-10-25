// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// A quotient ring of a Euclidean domain by a principal ideal.
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
    /// one of its elements.
    pub fn new(base: A, modulo: A::Elem) -> Self {
        assert!(base.contains(&modulo));
        QuotientRing { base, modulo }
    }

    /// Returns the base ring from which this ring was constructed.
    pub fn base(&self) -> &A {
        &self.base
    }

    /// Returns the modulus from which this ring was constructed.
    pub fn modulo(&self) -> &A::Elem {
        &self.modulo
    }

    fn reduce(&self, elem: A::Elem) -> A::Elem {
        if self.base.is_zero(&self.modulo) {
            elem
        } else {
            self.base.rem(&elem, &self.modulo)
        }
    }
}

impl<A> Domain for QuotientRing<A>
where
    A: EuclideanDomain,
{
    type Elem = A::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.contains(elem) && self.base.reduced(elem, &self.modulo)
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
        self.reduce(self.base.mul(elem1, elem2))
    }
}

impl<A> Monoid for QuotientRing<A>
where
    A: EuclideanDomain,
{
    fn one(&self) -> Self::Elem {
        self.reduce(self.base.one())
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if self.base.is_zero(&self.modulo) {
            return self.base.try_inv(elem);
        }
        let (g, _, r) = self.base.extended_gcd(&self.modulo, elem);
        self.base.try_inv(&g).map(|a| self.mul(&a, &r))
    }
}

impl<A> CommutativeMonoid for QuotientRing<A>
where
    A: EuclideanDomain,
{
    fn zero(&self) -> Self::Elem {
        self.base.zero()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.reduce(self.base.add(elem1, elem2))
    }
}

impl<A> AbelianGroup for QuotientRing<A>
where
    A: EuclideanDomain,
{
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.reduce(self.base.neg(elem))
    }
}

impl<A> SemiRing for QuotientRing<A> where A: EuclideanDomain {}

impl<A> UnitaryRing for QuotientRing<A> where A: EuclideanDomain {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_modulus() {
        let ring = QuotientRing::new(I32, 0);
        assert_eq!(ring.one(), 1);
        assert!(ring.is_one(&1));
        assert!(!ring.is_one(&0));

        for a in -5..=5 {
            assert!(ring.contains(&a));
            assert_eq!(ring.int(a as isize), a);
            assert_eq!(ring.neg(&a), -a);
            assert_eq!(ring.try_inv(&a), I32.try_inv(&a));
            for b in -5..=5 {
                assert_eq!(ring.add(&a, &b), a + b);
                assert_eq!(ring.sub(&a, &b), a - b);
                assert_eq!(ring.mul(&a, &b), a * b);
            }
        }
    }

    #[test]
    fn zero_polynomial_modulus() {
        let ring = QuotientRing::new(PolynomialAlgebra::new(GF2), vec![]);
        let elem = vec![0, 1];
        assert!(ring.contains(&elem));
        assert!(!ring.contains(&vec![0]));
        assert_eq!(ring.one(), vec![1]);
        assert_eq!(ring.add(&elem, &elem), vec![]);
        assert_eq!(ring.mul(&elem, &elem), vec![0, 0, 1]);
        assert_eq!(ring.neg(&elem), elem);
        assert_eq!(ring.try_inv(&elem), None);
        assert_eq!(ring.try_inv(&vec![1]), Some(vec![1]));
    }

    #[test]
    fn unit_modulus() {
        for modulo in [-1, 1] {
            let ring = QuotientRing::new(I32, modulo);
            assert_eq!(ring.one(), 0);
            assert!(ring.contains(&ring.one()));
            assert!(!ring.contains(&1));
            assert!(ring.is_one(&ring.zero()));
            assert_eq!(ring.int(-3), 0);
            assert_eq!(ring.add(&0, &0), 0);
            assert_eq!(ring.mul(&0, &0), 0);
            assert_eq!(ring.neg(&0), 0);
            assert_eq!(ring.try_inv(&0), Some(0));
        }
    }

    #[test]
    fn contains() {
        let ring = QuotientRing::new(PolynomialAlgebra::new(GF2), vec![1, 1, 1]);
        assert!(ring.contains(&vec![]));
        assert!(ring.contains(&vec![0, 1]));
        assert!(!ring.contains(&vec![0]));
        assert!(!ring.contains(&vec![1, 0]));
        assert!(!ring.contains(&vec![2]));
        assert!(!ring.contains(&vec![1, 1, 1]));
    }

    #[test]
    fn zstar_1584() {
        let ring = QuotientRing::new(I32, 1584); // 16 * 9 * 11

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
