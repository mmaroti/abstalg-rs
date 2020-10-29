// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The direct power of the given algebra where the elements are fixed sized
/// vectors.
#[derive(Clone, Debug, Default)]
pub struct VectorAlgebra<A>(pub A, pub usize)
where
    A: Domain;

impl<A> VectorAlgebra<A>
where
    A: Domain,
{
    /// Returns the base algebra from which this vector algebra was created.
    pub fn base(&self) -> &A {
        &self.0
    }

    /// Returns the common length of vectors that are the elements of this
    /// algebra (the exponent of the power algebra).
    pub fn len(&self) -> usize {
        self.1
    }

    /// Returns the constant vector containing the given element.
    pub fn diagonal(&self, elem: A::Elem) -> Vec<A::Elem> {
        vec![elem; self.1]
    }
}

impl<A> Domain for VectorAlgebra<A>
where
    A: Domain,
{
    type Elem = Vec<A::Elem>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        if elem.len() != self.1 {
            false
        } else {
            elem.iter().all(|a| self.0.contains(&a))
        }
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter()
            .zip(elem2.iter())
            .all(|(x, y)| self.0.equals(x, y))
    }
}

impl<A> Semigroup for VectorAlgebra<A>
where
    A: Semigroup,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.0.mul(x, y))
            .collect()
    }

    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter_mut()
            .zip(elem2.iter())
            .for_each(|(x, y)| self.0.mul_assign(x, y));
    }

    fn square(&self, elem: &mut Self::Elem) {
        assert!(elem.len() == self.1);
        elem.iter_mut().for_each(|x| self.0.square(x));
    }
}

impl<A> Monoid for VectorAlgebra<A>
where
    A: Monoid,
{
    fn one(&self) -> Self::Elem {
        self.diagonal(self.0.one())
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        assert!(elem.len() == self.1);
        elem.iter().all(|x| self.0.is_one(x))
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        assert!(elem.len() == self.1);
        let mut v = Vec::with_capacity(self.1);
        for x in elem.iter() {
            if let Some(y) = self.0.try_inv(x) {
                v.push(y)
            } else {
                return None;
            }
        }
        Some(v)
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        assert!(elem.len() == self.1);
        elem.iter().all(|x| self.0.invertible(x))
    }
}

impl<A> Group for VectorAlgebra<A>
where
    A: Group,
{
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(elem.len() == self.1);
        elem.iter().map(|x| self.0.inv(x)).collect()
    }
}

impl<A> AbelianGroup for VectorAlgebra<A>
where
    A: AbelianGroup,
{
    fn zero(&self) -> Self::Elem {
        self.diagonal(self.0.zero())
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        assert!(elem.len() == self.1);
        elem.iter().all(|x| self.0.is_zero(x))
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(elem.len() == self.1);
        elem.iter().map(|x| self.0.neg(x)).collect()
    }

    fn neg_assign(&self, elem: &mut Self::Elem) {
        assert!(elem.len() == self.1);
        elem.iter_mut().for_each(|x| self.0.neg_assign(x))
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.0.add(x, y))
            .collect()
    }

    fn add_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter_mut()
            .zip(elem2.iter())
            .for_each(|(x, y)| self.0.add_assign(x, y));
    }

    fn double(&self, elem: &mut Self::Elem) {
        assert!(elem.len() == self.1);
        elem.iter_mut().for_each(|x| self.0.double(x))
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.0.sub(x, y))
            .collect()
    }

    fn sub_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter_mut()
            .zip(elem2.iter())
            .for_each(|(x, y)| self.0.sub_assign(x, y));
    }
}

impl<A> UnitaryRing for VectorAlgebra<A>
where
    A: UnitaryRing,
{
    fn integer(&self, elem: isize) -> Self::Elem {
        self.diagonal(self.0.integer(elem))
    }
}

impl<A> PartialOrder for VectorAlgebra<A>
where
    A: PartialOrder,
{
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter()
            .zip(elem2.iter())
            .all(|(x, y)| self.0.leq(x, y))
    }
}

impl<A> Lattice for VectorAlgebra<A>
where
    A: Lattice,
{
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.0.meet(x, y))
            .collect()
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(elem1.len() == self.1 && elem2.len() == self.1);
        elem1
            .iter()
            .zip(elem2.iter())
            .map(|(x, y)| self.0.join(x, y))
            .collect()
    }
}

impl<A> BoundedOrder for VectorAlgebra<A>
where
    A: BoundedOrder,
{
    fn max(&self) -> Self::Elem {
        self.diagonal(self.0.max())
    }

    fn min(&self) -> Self::Elem {
        self.diagonal(self.0.min())
    }
}

impl<A> DistributiveLattice for VectorAlgebra<A> where A: DistributiveLattice {}
