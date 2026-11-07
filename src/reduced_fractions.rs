// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use num::rational::Ratio;

/// The field of rational numbers with arbitrarily large values.
pub const QQ: ReducedFractions<Integers> = ReducedFractions { base: Integers() };

/// The field of fractions over the elements of a Euclidean domain. The
/// elements are ratios where the numerator and denominator are relatively
/// prime and the denominator is normalized with respect to its associate
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
    /// be trivial; that is, one must be different from zero.
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
        self.base.contains(elem.numer())
            && self.base.contains(elem.denom())
            && !self.base.is_zero(elem.denom())
            && self.base.is_one(&self.base.associate_coef(elem.denom()))
            && self.base.relative_primes(elem.numer(), elem.denom())
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
}

impl<A> InvertibleMonoid for ReducedFractions<A>
where
    A: EuclideanDomain,
{
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

impl<A> CommutativeMonoid for ReducedFractions<A>
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

    fn times_signed(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let elem = Self::Elem::new_raw(
            self.base.times_signed(num, elem.numer()),
            elem.denom().clone(),
        );
        self.reduce(&elem)
    }
}

impl<A> SemiRing for ReducedFractions<A> where A: EuclideanDomain {}

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
    fn contains() {
        let field = ReducedFractions::new(I8);
        assert!(field.contains(&Ratio::new_raw(1, 2)));
        assert!(field.contains(&Ratio::new_raw(i8::MIN, 1)));
        assert!(!field.contains(&Ratio::new_raw(1, 0)));
        assert!(!field.contains(&Ratio::new_raw(i8::MIN, -1)));
        assert!(!field.contains(&Ratio::new_raw(2, 4)));
        assert!(!field.contains(&Ratio::new_raw(1, -2)));

        let field = ReducedFractions::new(PolynomialAlgebra::new(GF2));
        assert!(field.contains(&Ratio::new_raw(vec![0, 1], vec![1])));
        assert!(!field.contains(&Ratio::new_raw(vec![0], vec![1])));
        assert!(!field.contains(&Ratio::new_raw(vec![1], vec![1, 0])));
    }

    #[test]
    fn farey_fraction_counts() {
        use std::collections::BTreeSet;

        // https://oeis.org/A005728, orders 1..20 (the order-zero term is omitted).
        let expected = [
            2, 3, 5, 7, 11, 13, 19, 23, 29, 33,
            43, 47, 59, 65, 73, 81, 97, 103, 121, 129,
        ];
        let field = ReducedFractions::new(I32);
        for n in 1..=20i32 {
            let mut fractions = BTreeSet::new();
            let mut reference = Vec::new();
            for b in 1..=n {
                for a in 0..=b {
                    let fraction = field.reduce(&Ratio::new_raw(a, b));
                    assert!(field.contains(&fraction));
                    let numer = *fraction.numer();
                    let denom = *fraction.denom();
                    assert!(denom > 0 && denom <= n);
                    assert!(numer >= 0 && numer <= denom);
                    assert_eq!(numer * b, a * denom);
                    assert_eq!(field.reduce(&fraction), fraction);
                    for scale in [-3, -2, -1, 1, 2, 3] {
                        assert_eq!(
                            field.reduce(&Ratio::new_raw(a * scale, b * scale)),
                            fraction
                        );
                    }
                    fractions.insert((numer, denom));
                    // Discover equivalence classes without reducing fractions.
                    if !reference.iter().any(|&(c, d)| a * d == c * b) {
                        reference.push((a, b));
                    }
                }
            }
            assert_eq!(fractions.len(), expected[n as usize - 1]);
            assert_eq!(fractions.len(), reference.len());
            let mut sorted: Vec<_> = fractions.into_iter().collect();
            sorted.sort_by(|&(a, b), &(c, d)| (a * d).cmp(&(c * b)));
            assert_eq!(sorted.first(), Some(&(0, 1)));
            assert_eq!(sorted.last(), Some(&(1, 1)));
            for pair in sorted.windows(2) {
                let (a, b) = pair[0];
                let (c, d) = pair[1];
                assert_eq!(b * c - a * d, 1);
                assert!(b + d > n);
            }
        }
    }

    #[test]
    fn ops() {
        // Cross multiplication and native integer GCD provide a reference
        // independent of ReducedFractions and num::Ratio arithmetic.
        fn check(value: &Ratio<i32>, numer: i64, denom: i64) {
            assert_ne!(denom, 0);
            assert!(value.denom() > &0);
            assert_eq!(num::integer::gcd(*value.numer(), *value.denom()), 1);
            assert_eq!(
                i64::from(*value.numer()) * denom,
                numer * i64::from(*value.denom())
            );
        }

        let field = ReducedFractions::new(I32);
        let mut elems = Vec::new();
        for numer in -20..=20 {
            for denom in -20..=20 {
                if denom == 0 {
                    continue;
                }
                let raw = Ratio::new_raw(numer, denom);
                let elem = field.reduce(&raw);
                check(&elem, i64::from(numer), i64::from(denom));
                assert!(field.contains(&elem));
                assert_eq!(field.reduce(&elem), elem);
                for scale in [-3, -2, -1, 1, 2, 3] {
                    assert_eq!(
                        field.reduce(&Ratio::new_raw(numer * scale, denom * scale)),
                        elem
                    );
                }
                elems.push(elem);
            }
        }
        elems.sort();
        elems.dedup();

        for a in &elems {
            let an = i64::from(*a.numer());
            let ad = i64::from(*a.denom());
            check(&field.neg(a), -an, ad);
            match field.try_inv(a) {
                Some(inv) => {
                    assert_ne!(an, 0);
                    check(&inv, ad, an);
                    assert_eq!(field.mul(a, &inv), field.one());
                }
                None => assert_eq!(an, 0),
            }
            for b in &elems {
                let bn = i64::from(*b.numer());
                let bd = i64::from(*b.denom());
                check(&field.add(a, b), an * bd + bn * ad, ad * bd);
                check(&field.sub(a, b), an * bd - bn * ad, ad * bd);
                check(&field.mul(a, b), an * bn, ad * bd);
                if bn != 0 {
                    check(&field.div(a, b), an * bd, ad * bn);
                }
            }
        }
    }
}
