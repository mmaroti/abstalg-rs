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

/// The field of real numbers approximated by primitive floating-point
/// values. NaN and infinite values are excluded from the domain. Checked
/// arithmetic operations panic if their result is not finite. The lattice
/// order is the normal total order, which is not bounded.
#[derive(Clone, Debug)]
pub struct ApproxFloats<E> {
    phantom: PhantomData<E>,
}

impl<E> Domain for ApproxFloats<E>
where
    E: Float + Debug,
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
    E: Float + Debug,
{
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = *elem1 * *elem2;
        assert!(elem.is_finite());
        elem
    }
}

impl<E> Monoid for ApproxFloats<E>
where
    E: Float + Debug,
{
    fn one(&self) -> Self::Elem {
        One::one()
    }
}

impl<E> InvertibleMonoid for ApproxFloats<E>
where
    E: Float + Debug,
{
    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        let elem = self.one() / *elem;
        if elem.is_finite() {
            Some(elem)
        } else {
            None
        }
    }
}

impl<E> CommutativeMonoid for ApproxFloats<E>
where
    E: Float + Debug,
{
    fn zero(&self) -> Self::Elem {
        Zero::zero()
    }

    fn is_zero(&self, elem: &Self::Elem) -> bool {
        elem.is_zero()
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = *elem1 + *elem2;
        assert!(elem.is_finite());
        elem
    }
}

impl<E> AbelianGroup for ApproxFloats<E>
where
    E: Float + Debug,
{
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        let elem = -*elem;
        assert!(elem.is_finite());
        elem
    }

    fn sub(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        let elem = *elem1 - *elem2;
        assert!(elem.is_finite());
        elem
    }

    fn times(&self, num: isize, elem: &Self::Elem) -> Self::Elem {
        let num = num::cast::<isize, E>(num).expect("integer cannot be converted to float");
        self.mul(&num, elem)
    }
}

impl<E> SemiRing for ApproxFloats<E> where E: Float + Debug {}

impl<E> UnitaryRing for ApproxFloats<E> where E: Float + Debug {}

impl<E> Field for ApproxFloats<E>
where
    E: Float + Debug,
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
    E: Float + Debug,
{
    fn leq(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        *elem1 <= *elem2
    }
}

impl<E> Lattice for ApproxFloats<E>
where
    E: Float + Debug,
{
    fn meet(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.min(*elem2)
    }

    fn join(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        elem1.max(*elem2)
    }
}

impl<E> DistributiveLattice for ApproxFloats<E> where E: Float + Debug {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assertions() {
        assert_eq!(F32.zero(), 0.0);
        assert_eq!(F32.one(), 1.0);
        assert_eq!(F32.int(2), 2.0);
        assert_eq!(F32.int(-2), -2.0);
        assert_eq!(F32.add(&1.0, &2.0), 3.0);
        assert_eq!(F32.sub(&1.0, &2.0), -1.0);
        assert_eq!(F32.mul(&2.0, &3.0), 6.0);
        assert_eq!(F32.inv(&2.0), 0.5);
        assert_eq!(F32.div(&3.0, &2.0), 1.5);
        assert_eq!(F32.meet(&1.0, &2.0), 1.0);
        assert_eq!(F32.join(&1.0, &2.0), 2.0);

        assert_eq!(F64.zero(), 0.0);
        assert_eq!(F64.one(), 1.0);
        assert_eq!(F64.int(2), 2.0);
        assert_eq!(F64.int(-2), -2.0);
        assert_eq!(F64.add(&1.0, &2.0), 3.0);
        assert_eq!(F64.sub(&1.0, &2.0), -1.0);
        assert_eq!(F64.mul(&2.0, &3.0), 6.0);
        assert_eq!(F64.inv(&2.0), 0.5);
        assert_eq!(F64.div(&3.0, &2.0), 1.5);
        assert_eq!(F64.meet(&1.0, &2.0), 1.0);
        assert_eq!(F64.join(&1.0, &2.0), 2.0);
    }

    #[test]
    fn scaling() {
        for num in [isize::MIN, -3, -1, 0, 1, 3, isize::MAX] {
            assert_eq!(AbelianGroup::times(&F32, num, &2.0), (num as f32) * 2.0);
            assert_eq!(AbelianGroup::times(&F64, num, &2.0), (num as f64) * 2.0);
        }
        assert_eq!(AbelianGroup::times(&F32, 0, &f32::MAX), 0.0);
        assert_eq!(AbelianGroup::times(&F64, 0, &f64::MAX), 0.0);
    }

    #[test]
    #[should_panic]
    fn scaling_overflow_f32() {
        AbelianGroup::times(&F32, 2, &f32::MAX);
    }

    #[test]
    #[should_panic]
    fn scaling_overflow_f64() {
        AbelianGroup::times(&F64, 2, &f64::MAX);
    }
}
