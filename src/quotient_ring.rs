// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// A quotient ring of an Euclidean domain by a principal ideal.
#[derive(Clone, Debug, Default)]
pub struct QuotientRing<R: EuclideanDomain> {
    base: R,
    modulo: R::Elem,
}

impl<R: EuclideanDomain> QuotientRing<R> {
    /// Creates a new quotient ring from the given Euclidean domain and
    /// one of its element.
    pub fn new(base: R, modulo: R::Elem) -> Self {
        assert!(base.contains(&modulo));
        QuotientRing { base, modulo }
    }

    /// Returns the base ring from which this ring was constructed.
    pub fn base(&self) -> &R {
        &self.base
    }

    /// Returns the modulo element from which this ring was constructed.
    pub fn modulo(&self) -> &R::Elem {
        &self.modulo
    }
}

impl<R: EuclideanDomain> Domain for QuotientRing<R> {
    type Elem = R::Elem;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.is_reduced(elem, &self.modulo)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.base.equals(elem1, elem2)
    }
}

impl<R: EuclideanDomain> AdditiveGroup for QuotientRing<R> {
    fn zero(&self) -> Self::Elem {
        self.base.zero()
    }

    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.neg(elem), &self.modulo)
    }

    fn add(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.add(elem1, elem2), &self.modulo)
    }
}

impl<R: EuclideanDomain> UnitaryRing for QuotientRing<R> {
    fn one(&self) -> Self::Elem {
        self.base.one()
    }

    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.base.rem(&self.base.mul(elem1, elem2), &self.modulo)
    }
}
