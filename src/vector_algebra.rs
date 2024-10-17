// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The direct power of the given algebra where the elements are fixed sized
/// vectors. The algebraic operations are always acting coordinate-wise.
#[derive(Clone, Debug)]
pub struct VectorAlgebra<A>
where
    A: Domain,
{
    base: A,
    len: usize,
}

#[allow(clippy::len_without_is_empty)]
impl<A> VectorAlgebra<A>
where
    A: Domain,
{
    /// Creates a new vector algebra for the given base and length.
    pub fn new(base: A, len: usize) -> Self {
        Self { base, len }
    }

    /// Returns the base algebra from which this vector algebra was created.
    pub fn base(&self) -> &A {
        &self.base
    }

    /// Returns the common length of vectors that are the elements of this
    /// algebra (the exponent of the power algebra).
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the constant vector containing the given element.
    pub fn diagonal(&self, elem: A::Elem) -> Vec<A::Elem> {
        vec![elem; self.len]
    }
}

impl<A> Domain for VectorAlgebra<A>
where
    A: Domain,
{
    type Elem = Vec<A::Elem>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        if elem.len() != self.len {
            false
        } else {
            elem.iter().all(|a| self.base.contains(a))
        }
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter()
            .zip(elem2.iter())
            .all(|(x, y)| self.base.equals(x, y))
    }
}

impl<A> Semigroup for VectorAlgebra<A>
where
    A: Semigroup,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.base.mul(x, y))
            .collect()
    }

    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter_mut()
            .zip(elem2.iter())
            .for_each(|(x, y)| self.base.mul_assign(x, y));
    }

    fn square(&self, elem: &mut Self::Elem) {
        assert!(elem.len() == self.len);
        elem.iter_mut().for_each(|x| self.base.square(x));
    }
}

impl<A> Monoid for VectorAlgebra<A>
where
    A: Monoid,
{
    fn one(&self) -> Self::Elem {
        self.diagonal(self.base.one())
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        assert!(elem.len() == self.len);
        elem.iter().all(|x| self.base.is_one(x))
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        assert!(elem.len() == self.len);
        let mut v = Vec::with_capacity(self.len);
        for x in elem.iter() {
            if let Some(y) = self.base.try_inv(x) {
                v.push(y)
            } else {
                return None;
            }
        }
        Some(v)
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        assert!(elem.len() == self.len);
        elem.iter().all(|x| self.base.invertible(x))
    }
}

impl<A> Group for VectorAlgebra<A>
where
    A: Group,
{
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(elem.len() == self.len);
        elem.iter().map(|x| self.base.inv(x)).collect()
    }
}

impl<A> CommuntativeMonoid for VectorAlgebra<A>
where
    A: CommuntativeMonoid,
{
    fn zero(&self) -> Self::Elem {
        self.diagonal(self.base.zero())
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        assert!(elem.len() == self.len);
        elem.iter().all(|x| self.base.is_zero(x))
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.base.add(x, y))
            .collect()
    }

    fn add_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter_mut()
            .zip(elem2.iter())
            .for_each(|(x, y)| self.base.add_assign(x, y));
    }

    fn double(&self, elem: &mut Self::Elem) {
        assert!(elem.len() == self.len);
        elem.iter_mut().for_each(|x| self.base.double(x))
    }
}

impl<A> AbelianGroup for VectorAlgebra<A>
where
    A: AbelianGroup,
{
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(elem.len() == self.len);
        elem.iter().map(|x| self.base.neg(x)).collect()
    }

    fn neg_assign(&self, elem: &mut Self::Elem) {
        assert!(elem.len() == self.len);
        elem.iter_mut().for_each(|x| self.base.neg_assign(x))
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.base.sub(x, y))
            .collect()
    }

    fn sub_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter_mut()
            .zip(elem2.iter())
            .for_each(|(x, y)| self.base.sub_assign(x, y));
    }
}

impl<A> SemiRing for VectorAlgebra<A> where A: SemiRing {}

impl<A> UnitaryRing for VectorAlgebra<A>
where
    A: UnitaryRing,
{
    fn int(&self, elem: isize) -> Self::Elem {
        self.diagonal(self.base.int(elem))
    }
}

impl<A> PartialOrder for VectorAlgebra<A>
where
    A: PartialOrder,
{
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter()
            .zip(elem2.iter())
            .all(|(x, y)| self.base.leq(x, y))
    }
}

impl<A> BoundedOrder for VectorAlgebra<A>
where
    A: BoundedOrder,
{
    fn max(&self) -> Self::Elem {
        self.diagonal(self.base.max())
    }

    fn min(&self) -> Self::Elem {
        self.diagonal(self.base.min())
    }
}

impl<A> Lattice for VectorAlgebra<A>
where
    A: Lattice,
{
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.base.meet(x, y))
            .collect()
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.len && elem2.len() == self.len);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.base.join(x, y))
            .collect()
    }
}

impl<A> DistributiveLattice for VectorAlgebra<A> where A: DistributiveLattice {}

impl<A> BooleanAlgebra for VectorAlgebra<A>
where
    A: BooleanAlgebra,
{
    fn not(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(elem.len() == self.len);
        elem.iter().map(|x| self.base.not(x)).collect()
    }
}
