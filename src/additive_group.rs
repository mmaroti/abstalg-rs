// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The additive group reduct of rings and vector spaces.
#[derive(Clone, Debug)]
pub struct AdditiveGroup<A>(pub A)
where
    A: AbelianGroup;

impl<A> AdditiveGroup<A>
where
    A: AbelianGroup,
{
    /// Returns the base abelian group from which this group was created.
    pub fn base(&self) -> &A {
        &self.0
    }
}

impl<A> Domain for AdditiveGroup<A>
where
    A: AbelianGroup,
{
    type Elem = A::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.0.contains(elem)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.0.equals(elem1, elem2)
    }
}

impl<A> Semigroup for AdditiveGroup<A>
where
    A: AbelianGroup,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.0.add(elem1, elem2)
    }

    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        self.0.add_assign(elem1, elem2)
    }

    fn square(&self, elem: &mut Self::Elem) {
        self.0.double(elem)
    }
}

impl<A> Monoid for AdditiveGroup<A>
where
    A: AbelianGroup,
{
    fn one(&self) -> Self::Elem {
        self.0.zero()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.0.is_zero(elem)
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        Some(self.0.neg(elem))
    }

    fn invertible(&self, _elem: &Self::Elem) -> bool {
        true
    }
}

impl<A> Group for AdditiveGroup<A>
where
    A: AbelianGroup,
{
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        self.0.neg(elem)
    }
}
