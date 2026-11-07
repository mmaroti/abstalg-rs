// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The ring of square matrices of a fixed size over a unitary ring.
/// The matrices are plain vectors of base ring elements.
/// Determinants, inverses, and reduced row echelon forms are available only
/// when the base is a field.
#[derive(Clone, Debug)]
pub struct MatrixRing<A>
where
    A: UnitaryRing,
{
    valg: VectorAlgebra<A>,
    size: usize,
}

#[allow(clippy::len_without_is_empty)]
impl<A> MatrixRing<A>
where
    A: UnitaryRing,
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
}

impl<A> MatrixRing<A>
where
    A: Field,
{
    /// Multiplies the given row of the matrix by the given coefficient.
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

    /// Finds the next pivot row for Gauss-Jordan elimination.
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
                    self.base().neg_assign(&mut det);
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

    /// Returns the reduced row echelon form using Gauss-Jordan elimination.
    /// The matrix keeps its shape, including any zero rows at the bottom.
    pub fn reduced_row_echelon(&self, elem: &<Self as Domain>::Elem) -> <Self as Domain>::Elem {
        assert!(elem.len() == self.len());
        let mut elem = elem.clone();
        let mut pivot_row = 0;
        for col in 0..self.size {
            let row = (pivot_row..self.size)
                .find(|&row| !self.base().is_zero(&elem[row * self.size + col]));
            if let Some(row) = row {
                self.swap_rows(&mut elem, row, pivot_row);
                let coef = self.base().inv(&elem[pivot_row * self.size + col]);
                self.mul_row(&mut elem, pivot_row, &coef);
                for row in 0..self.size {
                    if row == pivot_row {
                        continue;
                    }
                    let coef = &elem[row * self.size + col];
                    if !self.base().is_zero(coef) {
                        let coef = self.base().neg(coef);
                        self.add_rows(&mut elem, pivot_row, row, &coef);
                    }
                }
                pivot_row += 1;
            }
        }
        elem
    }
}

impl<A> Domain for MatrixRing<A>
where
    A: UnitaryRing,
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
    A: UnitaryRing,
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
    A: UnitaryRing,
{
    fn one(&self) -> Self::Elem {
        self.int(1)
    }
}

impl<A> InvertibleMonoid for MatrixRing<A>
where
    A: Field,
{
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

impl<A> CommutativeMonoid for MatrixRing<A>
where
    A: UnitaryRing,
{
    fn zero(&self) -> Self::Elem {
        self.valg.zero()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        self.valg.is_zero(elem)
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
}

impl<A> AbelianGroup for MatrixRing<A>
where
    A: UnitaryRing,
{
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.valg.neg(elem)
    }

    fn neg_assign(&self, elem: &mut Self::Elem) {
        self.valg.neg_assign(elem)
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.valg.sub(elem1, elem2)
    }

    fn sub_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        self.valg.sub_assign(elem1, elem2);
    }
}

impl<A> SemiRing for MatrixRing<A> where A: UnitaryRing {}

impl<A> UnitaryRing for MatrixRing<A>
where
    A: UnitaryRing,
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

    fn binary_matrix(bits: u32, size: usize) -> Vec<i8> {
        (0..size * size).map(|i| ((bits >> i) & 1) as i8).collect()
    }

    // Encode the span as a set of binary vectors, without matrix operations.
    fn binary_row_space(matrix: &[i8], size: usize) -> u32 {
        let mut space = 0;
        for coefficients in 0..1usize << size {
            let mut vector = 0;
            for row in 0..size {
                if coefficients & (1 << row) != 0 {
                    for col in 0..size {
                        vector ^= u32::from(matrix[row * size + col] != 0) << col;
                    }
                }
            }
            space |= 1 << vector;
        }
        space
    }

    #[test]
    fn binary_row_space_counts() {
        use std::collections::{BTreeMap, BTreeSet};

        // https://oeis.org/A006116, dimensions 0..4.
        let expected = [1, 2, 5, 16, 67];
        for size in 0..=4 {
            let ring = MatrixRing::new(GF2, size);
            let mut spaces = BTreeMap::new();
            let mut reduced_forms = BTreeSet::new();
            for bits in 0..1u32 << (size * size) {
                let matrix = binary_matrix(bits, size);
                let reduced = ring.reduced_row_echelon(&matrix);
                assert!(ring.contains(&reduced));
                assert_eq!(ring.reduced_row_echelon(&reduced), reduced);
                let space = binary_row_space(&matrix, size);
                assert_eq!(binary_row_space(&reduced, size), space);

                let mut previous_pivot = None;
                let mut zero_row_seen = false;
                for row in 0..size {
                    let pivot = (0..size).find(|&col| reduced[row * size + col] != 0);
                    if let Some(col) = pivot {
                        assert!(!zero_row_seen);
                        assert!(previous_pivot.map_or(true, |previous| previous < col));
                        assert_eq!(reduced[row * size + col], 1);
                        for other_row in 0..size {
                            if other_row != row {
                                assert_eq!(reduced[other_row * size + col], 0);
                            }
                        }
                        previous_pivot = Some(col);
                    } else {
                        zero_row_seen = true;
                    }
                }
                if let Some(previous) = spaces.insert(space, reduced.clone()) {
                    assert_eq!(previous, reduced);
                }
                reduced_forms.insert(reduced);
            }
            assert_eq!(spaces.len(), expected[size]);
            assert_eq!(reduced_forms.len(), expected[size]);
        }
    }

    #[test]
    fn binary_nilpotency_index_counts() {
        // Independent multiplication of row-major bit encodings over GF(2).
        fn multiply(a: u32, b: u32, size: usize) -> u32 {
            let mut product = 0;
            for row in 0..size {
                for col in 0..size {
                    let mut entry = 0;
                    for k in 0..size {
                        entry ^= ((a >> (row * size + k)) & 1)
                            & ((b >> (k * size + col)) & 1);
                    }
                    product |= entry << (row * size + col);
                }
            }
            product
        }

        // https://oeis.org/A346214, rows for dimensions 1..4.
        // Their sums agree with https://oeis.org/A053763.
        let expected: &[&[usize]] = &[&[1], &[1, 3], &[1, 21, 42], &[1, 315, 1260, 2520]];
        for size in 1..=4 {
            let ring = MatrixRing::new(GF2, size);
            let mut counts = vec![0; size];
            for bits in 0..1u32 << (size * size) {
                let matrix = binary_matrix(bits, size);
                let mut power = ring.one();
                let mut reference = 0;
                for i in 0..size {
                    reference |= 1 << (i * size + i);
                }
                let mut index = None;
                for exponent in 1..=size {
                    power = ring.mul(&power, &matrix);
                    reference = multiply(reference, bits, size);
                    assert_eq!(power, binary_matrix(reference, size));
                    assert_eq!(ring.power(exponent, &matrix), power);
                    if reference == 0 && index.is_none() {
                        index = Some(exponent);
                    }
                }
                if let Some(index) = index {
                    counts[index - 1] += 1;
                }
            }
            assert_eq!(counts, expected[size - 1]);
            assert_eq!(counts.iter().sum::<usize>(), 1 << (size * (size - 1)));
        }
    }

    #[test]
    fn reduced_row_echelon_finite_field() {
        let ring = MatrixRing::new(QuotientField::new(I32, 5), 3);
        let elem = vec![0, 2, 1, 0, 4, 2, 0, 0, 0];
        assert_eq!(
            ring.reduced_row_echelon(&elem),
            vec![0, 1, 3, 0, 0, 0, 0, 0, 0]
        );
    }

    #[test]
    fn matrices_over_polynomials() {
        let ring = MatrixRing::new(PolynomialAlgebra::new(ZZ), 2);
        let x = vec![ZZ.int(0), ZZ.int(1)];
        let one = ring.base().one();
        let zero = ring.base().zero();
        let elem = vec![x.clone(), one.clone(), zero.clone(), x.clone()];

        assert!(ring.contains(&elem));
        assert_eq!(ring.transpose(&elem), vec![x.clone(), zero, one, x]);
        assert_eq!(ring.mul(&elem, &ring.one()), elem);
        assert_eq!(ring.mul(&ring.one(), &elem), elem);
        assert_eq!(
            ring.mul(&elem, &elem),
            vec![
                vec![ZZ.int(0), ZZ.int(0), ZZ.int(1)],
                vec![ZZ.int(0), ZZ.int(2)],
                vec![],
                vec![ZZ.int(0), ZZ.int(0), ZZ.int(1)],
            ]
        );
        assert_eq!(ring.add(&elem, &ring.neg(&elem)), ring.zero());
        assert_eq!(ring.sub(&elem, &elem), ring.zero());
        assert_eq!(ring.int(2), ring.add(&ring.one(), &ring.one()));
    }

    #[test]
    fn matrix_det() {
        let ring = MatrixRing::new(QQ, 2);

        let elem = vec![QQ.int(0), QQ.int(1), QQ.int(1), QQ.int(0)];
        assert_eq!(ring.determinant(&elem), QQ.int(-1));

        let elem = vec![QQ.int(0), QQ.int(2), QQ.int(3), QQ.int(4)];
        assert_eq!(ring.determinant(&elem), QQ.int(-6));

        let elem = vec![QQ.int(1), QQ.int(2), QQ.int(3), QQ.int(4)];
        assert_eq!(ring.determinant(&elem), QQ.int(-2));

        let ring = MatrixRing::new(QQ, 3);
        let elem = vec![
            QQ.int(0),
            QQ.int(2),
            QQ.int(0),
            QQ.int(0),
            QQ.int(0),
            QQ.int(3),
            QQ.int(5),
            QQ.int(0),
            QQ.int(0),
        ];
        assert_eq!(ring.determinant(&elem), QQ.int(30));
    }

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
