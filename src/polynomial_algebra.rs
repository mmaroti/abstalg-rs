// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The ring of polynomials over a base ring or field where each element
/// is represented as a vector whose last element, the leading coefficient (if
/// any) must be non-zero. This means that the empty vector is the zero
/// element, and every polynomial has a unique representation. Polynomials
/// can be defined over any abelian group, though only the group operations
/// will be available.
#[derive(Clone, Debug)]
pub struct PolynomialAlgebra<A>(pub A)
where
    A: AbelianGroup;

impl<A> PolynomialAlgebra<A>
where
    A: AbelianGroup,
{
    /// Returns the base ring from which this ring was created.
    pub fn base(&self) -> &A {
        &self.0
    }

    /// Returns the degree of the given polynomial. The zero polynomial has
    /// no degree.
    #[allow(clippy::ptr_arg)]
    pub fn degree(&self, elem: &Vec<A::Elem>) -> Option<usize> {
        if elem.is_empty() {
            None
        } else {
            Some(elem.len() - 1)
        }
    }

    /// Returns the leading coefficient of the given polynomial. The zero
    /// polynomial has no leading coefficient.
    #[allow(clippy::ptr_arg)]
    pub fn leading_coef(&self, elem: &Vec<A::Elem>) -> Option<A::Elem> {
        if elem.is_empty() {
            None
        } else {
            Some(elem[elem.len() - 1].clone())
        }
    }
}

impl<A> Domain for PolynomialAlgebra<A>
where
    A: AbelianGroup,
{
    type Elem = Vec<A::Elem>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        if elem.is_empty() {
            true
        } else {
            for a in elem.iter() {
                if !self.0.contains(a) {
                    return false;
                }
            }
            !self.0.is_zero(&elem[elem.len() - 1])
        }
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        if elem1.len() != elem2.len() {
            false
        } else {
            elem1
                .iter()
                .zip(elem2.iter())
                .all(|(x, y)| self.0.equals(x, y))
        }
    }
}

impl<A> Semigroup for PolynomialAlgebra<A>
where
    A: AbelianGroup + Semigroup,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        if elem1.is_empty() || elem2.is_empty() {
            Vec::new()
        } else {
            let mut elem3 = Vec::with_capacity(elem1.len() + elem2.len() - 1);
            elem3.resize(elem1.len() + elem2.len() - 1, self.0.zero());
            for i in 0..elem1.len() {
                for j in 0..elem2.len() {
                    let a = self.0.mul(&elem1[i], &elem2[j]);
                    elem3[i + j] = self.0.add(&elem3[i + j], &a);
                }
            }
            elem3
        }
    }
}

impl<A> Monoid for PolynomialAlgebra<A>
where
    A: AbelianGroup + Monoid,
{
    fn one(&self) -> Self::Elem {
        assert!(!self.0.is_zero(&self.0.one()));
        vec![self.0.one()]
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        elem.len() == 1 && self.0.is_one(&elem[0])
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if elem.len() == 1 {
            if let Some(elem) = self.0.try_inv(&elem[0]) {
                return Some(vec![elem]);
            }
        }
        None
    }
}

impl<A> AbelianGroup for PolynomialAlgebra<A>
where
    A: AbelianGroup,
{
    fn zero(&self) -> Self::Elem {
        Vec::new()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        elem.is_empty()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        elem.iter().map(|a| self.0.neg(a)).collect()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        if elem1.len() != elem2.len() {
            let (elem1, elem2) = if elem1.len() > elem2.len() {
                (elem1, elem2)
            } else {
                (elem2, elem1)
            };
            let mut elem3 = elem1.clone();
            for i in 0..elem2.len() {
                elem3[i] = self.0.add(&elem3[i], &elem2[i]);
            }
            elem3
        } else {
            let mut elem3 = Vec::new();
            for i in 0..elem1.len() {
                let a = self.0.add(&elem1[i], &elem2[i]);
                if !self.0.is_zero(&a) {
                    elem3.resize(i + 1, self.0.zero());
                    elem3[i] = a;
                }
            }
            elem3
        }
    }

    fn times(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let mut elem: Self::Elem = elem.iter().map(|a| self.0.times(num, a)).collect();
        for i in (0..elem.len()).rev() {
            if !self.0.is_zero(&elem[i]) {
                elem.resize(i + 1, self.0.zero());
                return elem;
            }
        }
        self.zero()
    }
}

impl<A> UnitaryRing for PolynomialAlgebra<A> where A: UnitaryRing {}

impl<A> IntegralDomain for PolynomialAlgebra<A>
where
    A: IntegralDomain,
{
    fn try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem> {
        assert!(!self.is_zero(elem2));
        if elem1.len() < elem2.len() {
            if elem1.is_empty() {
                Some(self.zero())
            } else {
                None
            }
        } else {
            let mut quo = Vec::with_capacity(elem1.len() + elem2.len() - 1);
            quo.resize(elem1.len() - elem2.len() + 1, self.0.zero());
            let mut rem = elem1.clone();

            let a = &elem2[elem2.len() - 1];
            assert!(!self.0.is_zero(a));

            for i in (0..quo.len()).rev() {
                quo[i] = self.0.try_div(&rem[i + elem2.len() - 1], a)?;
                let b = self.0.neg(&quo[i]);
                for j in 0..(elem2.len() - 1) {
                    let c = self.0.mul(&elem2[j], &b);
                    self.0.add_assign(&mut rem[i + j], &c);
                }
            }

            for d in rem.iter().take(elem2.len() - 1) {
                if !self.0.is_zero(d) {
                    return None;
                }
            }
            Some(quo)
        }
    }

    fn associate_repr(&self, elem: &Self::Elem) -> Self::Elem {
        if elem.is_empty() {
            self.zero()
        } else {
            let coef = self.0.associate_coef(&elem[elem.len() - 1]);
            elem.iter().map(|x| self.0.mul(x, &coef)).collect()
        }
    }

    fn associate_coef(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(!elem.is_empty());
        let elem = &elem[elem.len() - 1];
        let elem = self.0.associate_coef(elem);
        vec![elem]
    }
}

impl<F> EuclideanDomain for PolynomialAlgebra<F>
where
    F: Field,
{
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        assert!(!elem2.is_empty());
        if elem1.len() < elem2.len() {
            return (self.zero(), elem1.clone());
        }

        let mut quo = Vec::with_capacity(elem1.len() - elem2.len() + 1);
        quo.resize(elem1.len() - elem2.len() + 1, self.0.zero());
        let mut rem = elem1.clone();

        let a = &elem2[elem2.len() - 1];
        assert!(!self.0.is_zero(a));

        for i in (0..quo.len()).rev() {
            quo[i] = self.0.div(&rem[i + elem2.len() - 1], a);
            let b = self.0.neg(&quo[i]);
            for j in 0..(elem2.len() - 1) {
                let c = self.0.mul(&elem2[j], &b);
                rem[i + j] = self.0.add(&rem[i + j], &c);
            }
        }

        let mut i = elem2.len() - 1;
        while i > 0 && self.0.is_zero(&rem[i - 1]) {
            i -= 1;
        }
        rem.truncate(i);

        (quo, rem)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_256() {
        let field1 = QuotientField::new(I32, 2);
        let ring2 = PolynomialAlgebra(field1);

        // the irreducible polynomial 1 + x + x^3 + x^4 + x^8
        let poly = vec![1, 1, 0, 1, 1, 0, 0, 0, 1];
        assert!(ring2.contains(&poly));
        assert_eq!(ring2.degree(&poly), Some(8));
        let field2 = QuotientField::new(ring2, poly);

        // 1 + x, primitive element, generate all 256 elements
        let gen = vec![1, 1];
        let mut elems = Vec::new();
        elems.push(field2.zero());
        elems.push(field2.one());
        let mut elem = gen.clone();
        while !field2.is_one(&elem) {
            elems.push(elem.clone());
            elem = field2.mul(&elem, &gen);
        }
        assert_eq!(elems.len(), 256);

        for a in elems {
            if !field2.is_zero(&a) {
                let b = field2.inv(&a);
                assert_eq!(field2.mul(&a, &b), field2.one())
            }
        }
    }
}
