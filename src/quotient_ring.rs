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
}

impl<A> InvertibleMonoid for QuotientRing<A>
where
    A: EuclideanDomain,
{
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
    fn integer_quotient_nilpotent_counts() {
        // https://oeis.org/A003557, moduli 1..32, including the zero element.
        let expected = [
            1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 8,
            1, 3, 1, 2, 1, 1, 1, 4, 5, 1, 9, 2, 1, 1, 1, 16,
        ];
        for n in 1..=32i32 {
            for modulo in [n, -n] {
                let ring = QuotientRing::new(I32, modulo);
                let mut count = 0;
                for a in 0..n {
                    let mut power = ring.one();
                    let mut reference = 1 % n;
                    let mut nilpotent = false;
                    // A nilpotent element in an n-element ring reaches zero
                    // within n positive powers; otherwise a nonzero power repeats.
                    for exponent in 1..=n {
                        power = ring.mul(&power, &a);
                        reference = (reference * a) % n;
                        assert_eq!(power, reference);
                        assert!(ring.contains(&power));
                        assert_eq!(ring.power(exponent as usize, &a), reference);
                        nilpotent |= reference == 0;
                    }
                    if nilpotent {
                        count += 1;
                    }
                }
                assert_eq!(count, expected[n as usize - 1]);
            }
        }
    }

    #[test]
    fn integer_quotient_rings_exhaustive() {
        // https://oeis.org/A000010, phi(n) for n = 1..32.
        let totients = [
            1, 1, 2, 2, 4, 2, 6, 4, 6, 4, 10, 4, 12, 6, 8, 8,
            16, 6, 18, 8, 12, 10, 22, 8, 20, 12, 18, 12, 28, 8, 30, 16,
        ];
        for n in 1..=32i32 {
            for modulo in [n, -n] {
                let ring = QuotientRing::new(I32, modulo);
                assert_eq!(ring.zero(), 0);
                assert_eq!(ring.one(), 1 % n);
                for a in -2 * n..=2 * n {
                    assert_eq!(ring.contains(&a), (0..n).contains(&a));
                    assert_eq!(ring.int(a as isize), a.rem_euclid(n));
                }
                let mut units = 0;
                for a in 0..n {
                    assert_eq!(ring.is_zero(&a), a == 0);
                    assert_eq!(ring.is_one(&a), a == 1 % n);
                    assert_eq!(ring.neg(&a), (-a).rem_euclid(n));
                    let expected_inv = (0..n).find(|&b| (a * b) % n == 1 % n);
                    assert_eq!(ring.try_inv(&a), expected_inv);
                    assert_eq!(ring.invertible(&a), expected_inv.is_some());
                    if let Some(inv) = expected_inv {
                        units += 1;
                        assert!(ring.contains(&inv));
                        assert_eq!(ring.mul(&a, &inv), ring.one());
                        assert_eq!(ring.power(totients[n as usize - 1], &a), ring.one());
                    }
                    let mut expected_power = 1 % n;
                    for exponent in 0..=12 {
                        assert_eq!(ring.power(exponent, &a), expected_power);
                        expected_power = (expected_power * a) % n;
                    }
                    for b in 0..n {
                        assert_eq!(ring.add(&a, &b), (a + b) % n);
                        assert_eq!(ring.sub(&a, &b), (a - b).rem_euclid(n));
                        assert_eq!(ring.mul(&a, &b), (a * b) % n);
                        for c in 0..n {
                            assert_eq!(
                                ring.add(&ring.add(&a, &b), &c),
                                ring.add(&a, &ring.add(&b, &c))
                            );
                            assert_eq!(
                                ring.mul(&ring.mul(&a, &b), &c),
                                ring.mul(&a, &ring.mul(&b, &c))
                            );
                            assert_eq!(
                                ring.mul(&a, &ring.add(&b, &c)),
                                ring.add(&ring.mul(&a, &b), &ring.mul(&a, &c))
                            );
                        }
                    }
                }
                assert_eq!(units, totients[n as usize - 1]);
            }
        }
    }
}
