// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The multiplicative group of a unitary ring or field, or more generally the group of invertible
/// elements of any monoid.
#[derive(Clone, Debug)]
pub struct MultiplicativeGroup<A>(pub A)
where
    A: Monoid;

impl<A> MultiplicativeGroup<A>
where
    A: Monoid,
{
    /// Returns the base monoid from which this group was created.
    pub fn base(&self) -> &A {
        &self.0
    }
}

impl<A> Domain for MultiplicativeGroup<A>
where
    A: Monoid,
{
    type Elem = A::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.0.invertible(elem)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.0.equals(elem1, elem2)
    }
}

impl<A> Semigroup for MultiplicativeGroup<A>
where
    A: Monoid,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.0.mul(elem1, elem2)
    }

    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        self.0.mul_assign(elem1, elem2)
    }

    fn square(&self, elem: &mut Self::Elem) {
        self.0.square(elem)
    }
}

impl<A> Monoid for MultiplicativeGroup<A>
where
    A: Monoid,
{
    fn one(&self) -> Self::Elem {
        self.0.one()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.0.is_one(elem)
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        self.0.try_inv(elem)
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
        self.0.try_inv(elem).unwrap()
    }
}
