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

#[cfg(not(feature = "float_fallback"))]
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

#[cfg(not(feature = "float_fallback"))]
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

#[cfg(not(feature = "float_fallback"))]
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

#[cfg(not(feature = "float_fallback"))]
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

#[cfg(not(feature = "float_fallback"))]
impl<E> UnitaryRing for ApproxFloats<E> where E: Float + Debug + Zero + One + From<isize> {}

#[cfg(not(feature = "float_fallback"))]
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

#[cfg(not(feature = "float_fallback"))]
impl<E> PartialOrder for ApproxFloats<E>
where
    E: Float + Debug + Zero + One + From<isize>,
{
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 <= *elem2
    }
}

#[cfg(not(feature = "float_fallback"))]
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

#[cfg(not(feature = "float_fallback"))]
impl<E> DistributiveLattice for ApproxFloats<E> where E: Float + Debug + Zero + One + From<isize> {}

#[cfg(feature = "float_fallback")]
impl Domain for ApproxFloats<f64> {
    type Elem = f64;

    fn contains(&self, elem: &Self::Elem) -> bool {
        elem.is_finite()
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

#[cfg(feature = "float_fallback")]
impl Semigroup for ApproxFloats<f64> {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = *elem1 * *elem2;
        assert!(elem.is_finite());
        elem
    }
}

#[cfg(feature = "float_fallback")]
impl Monoid for ApproxFloats<f64> {
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

#[cfg(feature = "float_fallback")]
impl AbelianGroup for ApproxFloats<f64> {
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
        let num: Self::Elem = num as f64;
        num * *elem
    }
}

#[cfg(feature = "float_fallback")]
impl UnitaryRing for ApproxFloats<f64> {}

#[cfg(feature = "float_fallback")]
impl Field for ApproxFloats<f64> {
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

#[cfg(feature = "float_fallback")]
impl PartialOrder for ApproxFloats<f64> {
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 <= *elem2
    }
}

#[cfg(feature = "float_fallback")]
impl Lattice for ApproxFloats<f64> {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.min(*elem2)
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.max(*elem2)
    }
}

#[cfg(feature = "float_fallback")]
impl DistributiveLattice for ApproxFloats<f64> {}

#[cfg(feature = "float_fallback")]
impl Domain for ApproxFloats<f32> {
    type Elem = f32;

    fn contains(&self, elem: &Self::Elem) -> bool {
        elem.is_finite()
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

#[cfg(feature = "float_fallback")]
impl Semigroup for ApproxFloats<f32> {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = *elem1 * *elem2;
        assert!(elem.is_finite());
        elem
    }
}

#[cfg(feature = "float_fallback")]
impl Monoid for ApproxFloats<f32> {
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

#[cfg(feature = "float_fallback")]
impl AbelianGroup for ApproxFloats<f32> {
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
        let num: Self::Elem = num as f32;
        num * *elem
    }
}

#[cfg(feature = "float_fallback")]
impl UnitaryRing for ApproxFloats<f32> {}

#[cfg(feature = "float_fallback")]
impl Field for ApproxFloats<f32> {
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

#[cfg(feature = "float_fallback")]
impl PartialOrder for ApproxFloats<f32> {
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 <= *elem2
    }
}

#[cfg(feature = "float_fallback")]
impl Lattice for ApproxFloats<f32> {
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.min(*elem2)
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.max(*elem2)
    }
}

#[cfg(feature = "float_fallback")]
impl DistributiveLattice for ApproxFloats<f32> {}

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(feature = "float_fallback")]
    fn assertions() {
        assert_eq!(0.0, F64.zero());
        assert_eq!(1.0, F64.one());
        assert_eq!(2.0, F64.int(2));
    }
}
