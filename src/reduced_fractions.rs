// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use num::rational::Ratio;

/// The field of rational numbers with arbitrary large values.
pub const QQ: ReducedFractions<Integers> = ReducedFractions { base: Integers() };

/// The field of fractions over the elements of an Euclidean domain. The
/// elements are ratios where the numerator and denominator are relative
/// primes and the denominator is normalized with respect to its associate
/// class.
#[derive(Clone, Debug)]
pub struct ReducedFractions<A>
where
    A: EuclideanDomain,
{
    base: A,
}

impl<A> ReducedFractions<A>
where
    A: EuclideanDomain,
{
    /// Creates a new field of fractions over the given ring. The ring cannot
    /// be trivial, that is one must be different from zero.
    pub fn new(base: A) -> Self {
        assert!(!base.is_zero(&base.one()));
        Self { base }
    }

    /// Returns the base ring from which this field was created.
    pub fn base(&self) -> &A {
        &self.base
    }

    /// Takes an arbitrary ratio of elements and turns it into its normal form.
    pub fn reduce(&self, elem: &Ratio<A::Elem>) -> Ratio<A::Elem> {
        assert!(!self.base.is_zero(elem.denom()));
        let gcd = self.base.gcd(elem.numer(), elem.denom());
        let numer = self.base.quo(elem.numer(), &gcd);
        let denom = self.base.quo(elem.denom(), &gcd);
        let coef = self.base.associate_coef(&denom);
        let (numer, denom) = if !self.base.is_one(&coef) {
            (self.base.mul(&numer, &coef), self.base.mul(&denom, &coef))
        } else {
            (numer, denom)
        };
        Ratio::new_raw(numer, denom)
    }
}

impl<A> Domain for ReducedFractions<A>
where
    A: EuclideanDomain,
{
    type Elem = Ratio<A::Elem>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.relative_primes(elem.numer(), elem.denom())
            && self.base.is_one(&self.base.associate_coef(elem.denom()))
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1.numer(), elem2.numer())
            && self.base.equals(elem1.denom(), elem2.denom())
    }
}

impl<A> Semigroup for ReducedFractions<A>
where
    A: EuclideanDomain,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = Self::Elem::new_raw(
            self.base.mul(elem1.numer(), elem2.numer()),
            self.base.mul(elem1.denom(), elem2.denom()),
        );
        self.reduce(&elem)
    }
}

impl<A> Monoid for ReducedFractions<A>
where
    A: EuclideanDomain,
{
    fn one(&self) -> Self::Elem {
        Self::Elem::new_raw(self.base.one(), self.base.one())
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.base.is_one(elem.numer()) && self.base.is_one(elem.denom())
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if self.invertible(elem) {
            let elem = Self::Elem::new_raw(elem.denom().clone(), elem.numer().clone());
            Some(self.reduce(&elem))
        } else {
            None
        }
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        !self.base.is_zero(elem.numer())
    }
}

impl<A> CommuntativeMonoid for ReducedFractions<A>
where
    A: EuclideanDomain,
{
    fn zero(&self) -> Self::Elem {
        Self::Elem::new_raw(self.base.zero(), self.base.one())
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = if self.base.equals(elem1.denom(), elem2.denom()) {
            Self::Elem::new_raw(
                self.base.add(elem1.numer(), elem2.numer()),
                elem1.denom().clone(),
            )
        } else {
            Self::Elem::new_raw(
                self.base.add(
                    &self.base.mul(elem1.numer(), elem2.denom()),
                    &self.base.mul(elem1.denom(), elem2.numer()),
                ),
                self.base.mul(elem1.denom(), elem2.denom()),
            )
        };
        self.reduce(&elem)
    }
}

impl<A> AbelianGroup for ReducedFractions<A>
where
    A: EuclideanDomain,
{
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        Self::Elem::new_raw(self.base.neg(elem.numer()), elem.denom().clone())
    }

    fn times(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let elem = Self::Elem::new_raw(self.base.times(num, elem.numer()), elem.denom().clone());
        self.reduce(&elem)
    }
}

impl<A> UnitaryRing for ReducedFractions<A> where A: EuclideanDomain {}

impl<A> Field for ReducedFractions<A>
where
    A: EuclideanDomain,
{
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(!self.base.is_zero(elem.numer()));
        let numer = elem.denom();
        let denom = elem.numer();
        let coef = self.base.associate_coef(denom);
        let (numer, denom) = if !self.base.is_one(&coef) {
            (self.base.mul(numer, &coef), self.base.mul(denom, &coef))
        } else {
            (numer.clone(), denom.clone())
        };
        Ratio::new_raw(numer, denom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ops() {
        let field = ReducedFractions::new(I32);
        for numer in -20..20 {
            for denom in -20..20 {
                if denom == 0 {
                    continue;
                }
                let elem1 = Ratio::<i32>::new_raw(numer, denom);
                assert_eq!(*elem1.numer(), numer);
                assert_eq!(*elem1.denom(), denom);

                let elem1 = field.reduce(&elem1);
                let elem2 = Ratio::<i32>::new(numer, denom);
                assert_eq!(elem1, elem2);

                let elem2 = Ratio::<i32>::new(-2, 3);
                assert_eq!(elem1 + elem2, field.add(&elem1, &elem2));
                assert_eq!(elem1 * elem2, field.mul(&elem1, &elem2));
                assert_eq!(elem1 / elem2, field.div(&elem1, &elem2));
                if numer != 0 {
                    assert_eq!(elem2 / elem1, field.div(&elem2, &elem1));
                }

                let elem2 = Ratio::<i32>::new(7, 5);
                assert_eq!(elem1 + elem2, field.add(&elem1, &elem2));
                assert_eq!(elem1 * elem2, field.mul(&elem1, &elem2));
                assert_eq!(elem1 / elem2, field.div(&elem1, &elem2));
                if numer != 0 {
                    assert_eq!(elem2 / elem1, field.div(&elem2, &elem1));
                }
            }
        }
    }
}
