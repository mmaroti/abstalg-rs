// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The additive group reduct of rings and vector spaces.
#[derive(Clone, Debug)]
pub struct AdditiveGroup<A>
where
    A: AbelianGroup,
{
    base: A,
}

impl<A> AdditiveGroup<A>
where
    A: AbelianGroup,
{
    /// Creates a new additive group from the given base.
    pub fn new(base: A) -> Self {
        Self { base }
    }

    /// Returns the base abelian group from which this group was created.
    pub fn base(&self) -> &A {
        &self.base
    }
}

impl<A> Domain for AdditiveGroup<A>
where
    A: AbelianGroup,
{
    type Elem = A::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.contains(elem)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1, elem2)
    }
}

impl<A> Semigroup for AdditiveGroup<A>
where
    A: AbelianGroup,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.add(elem1, elem2)
    }

    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        self.base.add_assign(elem1, elem2)
    }

    fn square(&self, elem: &mut Self::Elem) {
        self.base.double(elem)
    }
}

impl<A> Monoid for AdditiveGroup<A>
where
    A: AbelianGroup,
{
    fn one(&self) -> Self::Elem {
        self.base.zero()
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        self.base.is_zero(elem)
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        Some(self.base.neg(elem))
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
        self.base.neg(elem)
    }
}
