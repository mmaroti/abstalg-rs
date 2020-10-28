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
#[derive(Clone, Debug, Default)]
pub struct ReducedFractions<R>
where
    R: EuclideanDomain,
{
    base: R,
}

impl<R> ReducedFractions<R>
where
    R: EuclideanDomain,
{
    /// Creates a new field of fractions over the given ring. The ring cannot
    /// be trivial, that is one must be different from zero.
    pub fn new(base: R) -> Self {
        assert!(!base.is_zero(&base.one()));
        Self { base }
    }

    /// Returns the base ring from which this field was created.
    pub fn base(&self) -> &R {
        &self.base
    }

    /// Takes an arbitrary ratio of elements and turns it into its normal form.
    pub fn reduce(&self, elem: &Ratio<R::Elem>) -> Ratio<R::Elem> {
        assert!(!self.base.is_zero(elem.denom()));
        let gcd = self.base.gcd(elem.numer(), elem.denom());
        let denom = self.base.quo(elem.denom(), &gcd);
        let (denom, mult) = self.base.associate_repr(&denom);
        let numer = self.base.quo(elem.numer(), &gcd);
        let numer = self.base.mul(&numer, &mult);
        Ratio::<R::Elem>::new_raw(numer, denom)
    }
}

impl<R> Domain for ReducedFractions<R>
where
    R: EuclideanDomain,
{
    type Elem = Ratio<R::Elem>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.relative_primes(elem.numer(), elem.denom())
            && self
                .base
                .equals(&self.base.associate_repr(elem.denom()).0, elem.denom())
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1.numer(), elem2.numer())
            && self.base.equals(elem1.denom(), elem2.denom())
    }
}

impl<R> Semigroup for ReducedFractions<R>
where
    R: EuclideanDomain,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = Self::Elem::new_raw(
            self.base.mul(elem1.numer(), elem2.numer()),
            self.base.mul(elem1.denom(), elem2.denom()),
        );
        self.reduce(&elem)
    }
}

impl<R> Monoid for ReducedFractions<R>
where
    R: EuclideanDomain,
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

impl<R> AbelianGroup for ReducedFractions<R>
where
    R: EuclideanDomain,
{
    fn zero(&self) -> Self::Elem {
        Self::Elem::new_raw(self.base.zero(), self.base.one())
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        Self::Elem::new_raw(self.base.neg(elem.numer()), elem.denom().clone())
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

    fn times(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let elem = Self::Elem::new_raw(self.base.times(num, elem.numer()), elem.denom().clone());
        self.reduce(&elem)
    }
}

impl<R> UnitaryRing for ReducedFractions<R> where R: EuclideanDomain {}

impl<R> IntegralDomain for ReducedFractions<R>
where
    R: EuclideanDomain,
{
    fn associate_repr(&self, elem: &Self::Elem) -> (Self::Elem, Self::Elem) {
        self.auto_associate_repr(elem)
    }

    fn try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem> {
        Some(self.div(elem1, elem2))
    }
}

impl<R> EuclideanDomain for ReducedFractions<R>
where
    R: EuclideanDomain,
{
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        self.auto_quo_rem(elem1, elem2)
    }
}

impl<R> Field for ReducedFractions<R>
where
    R: EuclideanDomain,
{
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(!self.base.is_zero(elem.numer()));
        let (denom, mult) = self.base.associate_repr(elem.numer());
        let numer = self.base.mul(elem.denom(), &mult);
        Self::Elem::new_raw(numer, denom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ops() {
        let field = ReducedFractions::<CheckedInts<i32>>::new(I32);
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
