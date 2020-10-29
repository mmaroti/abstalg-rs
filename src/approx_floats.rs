// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use num::{Float, One, Zero};
use std::fmt::Debug;
use std::marker::PhantomData;

/// The field of reals approximated by machine `f32` values.
pub const F32: ApproxFloats<f32> = ApproxFloats {
    phantom: PhantomData,
};

/// The field of reals approximated by machine `f64` values.
pub const F64: ApproxFloats<f64> = ApproxFloats {
    phantom: PhantomData,
};

/// The field of real numbers approximated by a primitive floating point
/// number. NaN and infinity values are not considered as members, so all
/// operations resulting one of these will panic. The lattice order is the
/// normal total order, which is not bounded.
#[derive(Clone, Debug)]
pub struct ApproxFloats<E> {
    phantom: PhantomData<E>,
}

impl<E> Domain for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    type Elem = E;

    fn contains(&self, elem: &Self::Elem) -> bool {
        elem.is_finite()
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

impl<E> Semigroup for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = *elem1 * *elem2;
        assert!(elem.is_finite());
        elem
    }
}

impl<E> Monoid for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn one(&self) -> Self::Elem {
        One::one()
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        let elem = self.one() / *elem;
        if elem.is_finite() {
            Some(elem)
        } else {
            None
        }
    }
}

impl<E> AbelianGroup for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn zero(&self) -> Self::Elem {
        Zero::zero()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        elem.is_zero()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        let elem = -*elem;
        assert!(elem.is_finite());
        elem
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = *elem1 + *elem2;
        assert!(elem.is_finite());
        elem
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = *elem1 - *elem2;
        assert!(elem.is_finite());
        elem
    }

    fn times(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let num: Self::Elem = num.into();
        num * *elem
    }
}

impl<E> UnitaryRing for ApproxFloats<E> where E: Float + Debug + Zero + One + From<isize> {}

impl<E> IntegralDomain for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn try_div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Option<Self::Elem> {
        self.auto_try_div(elem1, elem2)
    }

    fn associate_repr(&self, elem: &Self::Elem) -> Self::Elem {
        self.auto_associate_repr(elem)
    }

    fn associate_coef(&self, elem: &Self::Elem) -> Self::Elem {
        self.auto_associate_coef(elem)
    }
}

impl<E> EuclideanDomain for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn quo_rem(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> (Self::Elem, Self::Elem) {
        self.auto_quo_rem(elem1, elem2)
    }
}

impl<E> Field for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        self.div(&self.one(), elem)
    }

    fn div(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        assert!(!self.is_zero(elem2));
        let elem = *elem1 / *elem2;
        assert!(elem.is_finite());
        elem
    }
}

impl<E> PartialOrder for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 <= *elem2
    }
}

impl<E> Lattice for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.min(*elem2)
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.max(*elem2)
    }
}

impl<E> DistributiveLattice for ApproxFloats<E> where E: Float + Debug + Zero + One + From<isize> {}
