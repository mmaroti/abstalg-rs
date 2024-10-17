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

    /// Returns the base algebra from which this matrix ring was created.
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
    pub fn transpose(&self, elem: &<Self as Domain>::Elem) -> <Self as Domain>::Elem {
        assert!(elem.len() == self.len());
        let mut res = Vec::with_capacity(self.len());
        for row in 0..self.size {
            for col in 0..self.size {
                res.push(elem[col * self.size + row].clone())
            }
        }
        res
    }

    /// Multiplies the given row of the elem matrix with the given coefficient.
    fn mul_row(&self, elem: &mut <Self as Domain>::Elem, row: usize, coef: &A::Elem) {
        let row = row * self.size();
        for val in &mut elem[row..row + self.size] {
            self.base().mul_assign(val, coef);
        }
    }

    /// Adds the first row, multiplied by the given coefficient, to the second
    /// row of the matrix.
    fn add_rows(
        &self,
        elem: &mut <Self as Domain>::Elem,
        row1: usize,
        row2: usize,
        coef: &A::Elem,
    ) {
        let row1 = row1 * self.size();
        let row2 = row2 * self.size();
        for col in 0..self.size {
            let val = self.base().mul(&elem[row1 + col], coef);
            self.base().add_assign(&mut elem[row2 + col], &val);
        }
    }

    /// Swaps the given rows of the matrix.
    fn swap_rows(&self, elem: &mut <Self as Domain>::Elem, row1: usize, row2: usize) {
        let row1 = row1 * self.size();
        let row2 = row2 * self.size();
        for col in 0..self.size {
            elem.swap(row1 + col, row2 + col);
        }
    }

    /// Helper function for Gauss-Jordan elimination, finds the next row.
    fn find_row(&self, elem: &<Self as Domain>::Elem, col: usize) -> Option<usize> {
        (col..self.size()).find(|&row| !self.base().is_zero(&elem[row * self.size() + col]))
    }

    /// Returns the determinant of the given matrix.
    #[allow(clippy::ptr_arg)]
    pub fn determinant(&self, elem: &<Self as Domain>::Elem) -> A::Elem {
        let mut elem = elem.clone();
        let mut det = self.base().one();

        for col in 0..self.size {
            if let Some(row) = self.find_row(&elem, col) {
                if row != col {
                    self.swap_rows(&mut elem, col, row);
                }
                let coef = &elem[col * self.size + col];
                self.base().mul_assign(&mut det, coef);
                let coef = self.base().inv(coef);
                self.mul_row(&mut elem, col, &coef);
                for row in col + 1..self.size {
                    let coef = &elem[row * self.size() + col];
                    if self.base().is_zero(coef) {
                        continue;
                    }
                    let coef = self.base().neg(coef);
                    self.add_rows(&mut elem, col, row, &coef);
                }
            } else {
                return self.base().zero();
            }
        }

        det
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
            elem.iter().all(|a| self.base().contains(a))
        }
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        assert!(elem1.len() == self.len() && elem2.len() == self.len());
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
        assert!(elem1.len() == self.len() && elem2.len() == self.len());
        let elem2 = self.transpose(elem2);
        let mut res = Vec::with_capacity(self.len());
        for row in 0..self.size {
            for col in 0..self.size {
                let mut sum = self.base().zero();
                for idx in 0..self.size {
                    let val1 = &elem1[row * self.size + idx];
                    let val2 = &elem2[col * self.size + idx];
                    let val3 = self.base().mul(val1, val2);
                    self.base().add_assign(&mut sum, &val3);
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

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        let mut elem = elem.clone();
        let mut invs = self.one();

        for col in 0..self.size {
            if let Some(row) = self.find_row(&elem, col) {
                if row != col {
                    self.swap_rows(&mut elem, col, row);
                    self.swap_rows(&mut invs, col, row);
                }
                let coef = self.base().inv(&elem[col * self.size + col]);
                self.mul_row(&mut elem, col, &coef);
                self.mul_row(&mut invs, col, &coef);
                for row in 0..self.size {
                    if row == col {
                        continue;
                    }
                    let coef = &elem[row * self.size() + col];
                    if self.base().is_zero(coef) {
                        continue;
                    }
                    let coef = self.base().neg(coef);
                    self.add_rows(&mut elem, col, row, &coef);
                    self.add_rows(&mut invs, col, row, &coef);
                }
            } else {
                return None;
            }
        }

        debug_assert!(self.is_one(&elem));
        Some(invs)
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        !self.base().is_zero(&self.determinant(elem))
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

    #[test]
    fn matrix_inv_gl23() {
        let q = 3;
        let field = QuotientField::new(I32, q);
        let ring = MatrixRing::new(field.clone(), 2);

        let mut elem = vec![0; ring.len()];
        let mut gl23_count = 0;
        let mut sl23_count = 0;

        fn next(elem: &mut Vec<i32>, q: i32) -> bool {
            for i in 0..elem.len() {
                elem[i] += 1;
                if elem[i] >= q {
                    elem[i] = 0;
                } else {
                    return false;
                }
            }
            true
        }

        loop {
            let det = ring.determinant(&elem);
            if ring.invertible(&elem) {
                let invs = ring.try_inv(&elem).expect("not invertible");
                let prod = ring.mul(&elem, &invs);
                assert!(ring.is_one(&prod));
                gl23_count += 1;

                assert!(!field.is_zero(&det));
                if field.is_one(&det) {
                    sl23_count += 1;
                }
            } else {
                assert!(field.is_zero(&det));
            }
            if next(&mut elem, q) {
                break;
            }
        }

        assert_eq!(gl23_count, 48);
        assert_eq!(sl23_count, 24);
    }
}
