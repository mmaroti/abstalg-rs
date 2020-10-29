// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The ring of rectangular matrices of a fixed size over a field.
/// The elements are plain vectors of entries.
#[derive(Clone, Debug)]
pub struct MatrixRing<A>(pub A, pub usize)
where
    A: Field;

impl<A> MatrixRing<A>
where
    A: Field,
{
    /// Returns the base algebra from which this vector algebra was created.
    pub fn base(&self) -> &A {
        &self.0
    }

    /// Returns the common number of columns and rows of the elements of this
    /// algebra.
    pub fn size(&self) -> usize {
        self.1
    }

    /// Returns the number of elements in the matrix, which is the square of
    /// the size.
    pub fn len(&self) -> usize {
        self.size() * self.size()
    }

    /// Returns the transpose of the given matrix.
    pub fn transpose(&self, elem: &Vec<A::Elem>) -> Vec<A::Elem> {
        assert!(elem.len() == self.len());
        let mut res = Vec::with_capacity(self.len());
        for row in 0..self.size() {
            for col in 0..self.size() {
                res.push(elem[col * self.size() + row].clone())
            }
        }
        res
    }
}

impl<A> Domain for MatrixRing<A>
where
    A: Field,
{
    type Elem = Vec<A::Elem>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        if elem.len() != self.len() {
            false
        } else {
            elem.iter().all(|a| self.base().contains(&a))
        }
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        assert!(elem1.len() == self.len() && elem2.len() == elem1.len());
        elem1
            .iter()
            .zip(elem2.iter())
            .all(|(x, y)| self.base().equals(x, y))
    }
}

impl<A> Semigroup for MatrixRing<A>
where
    A: Field,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.len());
        let elem2 = self.transpose(elem2);
        let mut res = Vec::with_capacity(self.len());
        for row in 0..self.size() {
            for col in 0..self.size() {
                let mut sum = self.base().zero();
                for tmp in 0..self.size() {
                    let val1 = &elem1[row * self.size() + tmp];
                    let val2 = &elem2[col * self.size() + tmp];
                    self.base()
                        .add_assign(&mut sum, &self.base().mul(val1, val2));
                }
                res.push(sum)
            }
        }
        res
    }
}

impl<A> AbelianGroup for MatrixRing<A>
where
    A: Field,
{
    fn zero(&self) -> Self::Elem {
        VectorAlgebra(self.base().clone(), self.len()).zero()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        VectorAlgebra(self.base().clone(), self.len()).is_zero(elem)
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        VectorAlgebra(self.base().clone(), self.len()).neg(elem)
    }

    fn neg_assign(&self, elem: &mut Self::Elem) {
        VectorAlgebra(self.base().clone(), self.len()).neg_assign(elem)
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        VectorAlgebra(self.base().clone(), self.len()).add(elem1, elem2)
    }

    fn add_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        VectorAlgebra(self.base().clone(), self.len()).add_assign(elem1, elem2);
    }

    fn double(&self, elem: &mut Self::Elem) {
        VectorAlgebra(self.base().clone(), self.len()).double(elem);
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        VectorAlgebra(self.base().clone(), self.len()).sub(elem1, elem2)
    }

    fn sub_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        VectorAlgebra(self.base().clone(), self.len()).sub_assign(elem1, elem2);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_matmul() {
        let ring = MatrixRing(QQ, 2);

        let elem1 = vec![QQ.int(1), QQ.int(2), QQ.int(3), QQ.int(4)];
        let elem2 = vec![QQ.int(5), QQ.int(6), QQ.int(7), QQ.int(8)];
        let elem3 = ring.mul(&elem1, &elem2);
        assert_eq!(elem3, vec![QQ.int(19), QQ.int(22), QQ.int(43), QQ.int(50)]);
    }
}
