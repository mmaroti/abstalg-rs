// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::{Domain, EuclideanDomain, Field, UnitaryRing};
use num::{Float, One, Zero};
use std::fmt::Debug;
use std::marker::PhantomData;

/// The field of real numbers approximated by a primitive floating
/// point. NaN and infinity values are not considered as members,
/// so all operations resulting one of these will panic.
#[derive(Default)]
pub struct ApproxFloats<E> {
    phantom: PhantomData<E>,
}

impl<E> Domain for ApproxFloats<E>
where
    E: Float + Debug + Zero + One,
{
    type Elem = E;

    fn contains(&self, elem: &Self::Elem) -> bool {
        elem.is_finite()
    }
}

impl<E> UnitaryRing for ApproxFloats<E>
where
    E: Float + Debug + Zero + One,
{
    fn zero(&self) -> Self::Elem {
        Zero::zero()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        let r = -*elem;
        assert!(r.is_finite());
        r
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = *elem1 + *elem2;
        assert!(r.is_finite());
        r
    }

    fn one(&self) -> Self::Elem {
        One::one()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = *elem1 * *elem2;
        assert!(r.is_finite());
        r
    }
}

impl<E> EuclideanDomain for ApproxFloats<E>
where
    E: Float + Debug + Zero + One,
{
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        if self.is_zero(elem2) {
            (self.zero(), elem1.clone())
        } else {
            (self.div(elem1, elem2), self.zero())
        }
    }
}

impl<E> Field for ApproxFloats<E>
where
    E: Float + Debug + Zero + One,
{
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        self.div(&self.one(), elem)
    }

    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let r = *elem1 / *elem2;
        assert!(r.is_finite());
        r
    }
}
