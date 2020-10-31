// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The multiplicative group of a unitary ring or field, or more generally the group of invertible
/// elements of any monoid.
#[derive(Clone, Debug)]
pub struct MultiplicativeGroup<A>
where
    A: Monoid,
{
    base: A,
}

impl<A> MultiplicativeGroup<A>
where
    A: Monoid,
{
    /// Creates a new multiplicative group from the given base.
    pub fn new(base: A) -> Self {
        Self { base }
    }

    /// Returns the base monoid from which this group was created.
    pub fn base(&self) -> &A {
        &self.base
    }
}

impl<A> Domain for MultiplicativeGroup<A>
where
    A: Monoid,
{
    type Elem = A::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.invertible(elem)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1, elem2)
    }
}

impl<A> Semigroup for MultiplicativeGroup<A>
where
    A: Monoid,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.mul(elem1, elem2)
    }

    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        self.base.mul_assign(elem1, elem2)
    }

    fn square(&self, elem: &mut Self::Elem) {
        self.base.square(elem)
    }
}

impl<A> Monoid for MultiplicativeGroup<A>
where
    A: Monoid,
{
    fn one(&self) -> Self::Elem {
        self.base.one()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.base.is_one(elem)
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        self.base.try_inv(elem)
    }

    fn invertible(&self, _elem: &Self::Elem) -> bool {
        true
    }
}

impl<A> Group for MultiplicativeGroup<A>
where
    A: Monoid,
{
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        self.base.try_inv(elem).unwrap()
    }
}
