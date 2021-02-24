// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The ring of rectangular matrices of a fixed size over a field.
/// The matrices are plain vectors of field elements.
#[derive(Clone, Debug)]
pub struct MatrixRing<A>
where
    A: Field,
{
    valg: VectorAlgebra<A>,
    size: usize,
}

#[allow(clippy::len_without_is_empty)]
impl<A> MatrixRing<A>
where
    A: Field,
{
    /// Creates a new matrix ring for the given base and size.
    pub fn new(base: A, size: usize) -> Self {
        let valg = VectorAlgebra::new(base, size.checked_mul(size).unwrap());
        Self { valg, size }
    }

    /// Returns the base algebra from which this vector algebra was created.
    pub fn base(&self) -> &A {
        self.valg.base()
    }

    /// Returns the common number of columns and rows of the elements of this
    /// algebra.
    pub fn size(&self) -> usize {
        self.size
    }

    /// Returns the number of elements in the matrix, which is the square of
    /// the size.
    pub fn len(&self) -> usize {
        self.size * self.size
    }

    /// Returns the transpose of the given matrix.
    #[allow(clippy::ptr_arg)]
    pub fn transpose(&self, elem: &Vec<A::Elem>) -> Vec<A::Elem> {
        assert!(elem.len() == self.len());
        let mut res = Vec::with_capacity(self.len());
        for row in 0..self.size {
            for col in 0..self.size {
                res.push(elem[col * self.size + row].clone())
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
        for row in 0..self.size {
            for col in 0..self.size {
                let mut sum = self.base().zero();
                for tmp in 0..self.size {
                    let val1 = &elem1[row * self.size + tmp];
                    let val2 = &elem2[col * self.size + tmp];
                    self.base()
                        .add_assign(&mut sum, &self.base().mul(val1, val2));
                }
                res.push(sum)
            }
        }
        res
    }
}

impl<A> Monoid for MatrixRing<A>
where
    A: Field,
{
    fn one(&self) -> Self::Elem {
        self.int(1)
    }

    // TODO: properly implement matrix inverses
    fn try_inv(&self, _elem: &Self::Elem) -> Option<Self::Elem> {
        None
    }
}

impl<A> AbelianGroup for MatrixRing<A>
where
    A: Field,
{
    fn zero(&self) -> Self::Elem {
        self.valg.zero()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        self.valg.is_zero(elem)
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.valg.neg(elem)
    }

    fn neg_assign(&self, elem: &mut Self::Elem) {
        self.valg.neg_assign(elem)
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.valg.add(elem1, elem2)
    }

    fn add_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        self.valg.add_assign(elem1, elem2);
    }

    fn double(&self, elem: &mut Self::Elem) {
        self.valg.double(elem);
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.valg.sub(elem1, elem2)
    }

    fn sub_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        self.valg.sub_assign(elem1, elem2);
    }
}

impl<A> UnitaryRing for MatrixRing<A>
where
    A: Field,
{
    fn int(&self, elem: isize) -> Self::Elem {
        let elem = self.base().int(elem);
        let mut mat = self.zero();
        for i in 0..self.size {
            mat[i * (self.size + 1)] = elem.clone();
        }
        mat
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matrix_mul() {
        let ring = MatrixRing::new(QQ, 2);

        let elem1 = vec![QQ.int(1), QQ.int(2), QQ.int(3), QQ.int(4)];
        let elem2 = vec![QQ.int(5), QQ.int(6), QQ.int(7), QQ.int(8)];
        let elem3 = ring.mul(&elem1, &elem2);
        assert_eq!(elem3, vec![QQ.int(19), QQ.int(22), QQ.int(43), QQ.int(50)]);

        assert_eq!(ring.mul(&elem1, &ring.one()), elem1);
        assert_eq!(ring.mul(&ring.one(), &elem1), elem1);
    }
}
