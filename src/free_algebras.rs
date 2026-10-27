// Copyright (C) 2026 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The free semigroup on generators indexed by nonnegative values.
/// Elements are right-associated prefix terms: `[n]` is a generator, and
/// `-1` denotes multiplication. The empty vector is not an element.
#[derive(Clone, Debug)]
pub struct FreeSemigroup {
    system: RewriteSystem,
}

impl FreeSemigroup {
    /// Creates a free semigroup using associativity as a rewrite rule.
    pub fn new() -> Self {
        let mut system = RewriteSystem::default();
        system.add_operation("mul", 2);
        system.add_rule(vec![-1, -1, 0, 1, 2], vec![-1, 0, -1, 1, 2]);
        Self { system }
    }

    /// Returns the generator with the given nonnegative index.
    pub fn generator(&self, index: usize) -> Vec<i32> {
        assert!(index <= i32::MAX as usize);
        vec![index as i32]
    }

    /// Returns one more than the largest generator index in the term.
    pub fn num_variables(&self, elem: &[i32]) -> usize {
        self.system.num_variables(elem)
    }

    /// Evaluates an element in another semigroup using the given generator images.
    /// The substitution must contain at least `self.num_variables(elem)` entries.
    pub fn evaluate<A: Semigroup>(
        &self,
        elem: &[i32],
        target: &A,
        substitution: &[A::Elem],
    ) -> A::Elem {
        debug_assert!(self.system.is_valid(elem) && self.system.is_reduced(elem));
        debug_assert!(substitution.iter().all(|elem| target.contains(elem)));
        assert!(substitution.len() >= self.num_variables(elem));
        let mut variables = elem.iter().rev().filter(|&&s| s >= 0);
        let mut result = substitution[*variables.next().unwrap() as usize].clone();
        for &var in variables {
            result = target.mul(&substitution[var as usize], &result);
        }
        result
    }
}

impl Default for FreeSemigroup {
    fn default() -> Self {
        Self::new()
    }
}

impl Domain for FreeSemigroup {
    type Elem = Vec<i32>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.system.contains(elem)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.system.equals(elem1, elem2)
    }
}

impl Semigroup for FreeSemigroup {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.system.evaluate2(0, elem1, elem2)
    }
}

impl UniversalAlgebra for FreeSemigroup {
    fn signature(&self) -> &[(&str, usize)] {
        self.system.signature()
    }

    fn evaluate(&self, oper: usize, elems: &[&Self::Elem]) -> Self::Elem {
        self.system.evaluate(oper, elems)
    }
}

/// The free monoid on generators indexed by nonnegative values.
/// Elements are right-associated prefix terms: `[n]` is a generator,
/// `-1` denotes multiplication, and `[-2]` is the identity.
#[derive(Clone, Debug)]
pub struct FreeMonoid {
    system: RewriteSystem,
}

impl FreeMonoid {
    /// Creates a free monoid using associativity and the identity laws.
    pub fn new() -> Self {
        let mut system = RewriteSystem::default();
        system.add_operation("mul", 2);
        system.add_operation("one", 0);
        system.add_rule(vec![-1, -1, 0, 1, 2], vec![-1, 0, -1, 1, 2]);
        system.add_rule(vec![-1, -2, 0], vec![0]);
        system.add_rule(vec![-1, 0, -2], vec![0]);
        Self { system }
    }

    /// Returns the generator with the given nonnegative index.
    pub fn generator(&self, index: usize) -> Vec<i32> {
        assert!(index <= i32::MAX as usize);
        vec![index as i32]
    }

    /// Returns one more than the largest generator index, or zero for the identity.
    pub fn num_variables(&self, elem: &[i32]) -> usize {
        self.system.num_variables(elem)
    }

    /// Evaluates an element in another monoid using the given generator images.
    /// The substitution must contain at least `self.num_variables(elem)` entries.
    pub fn evaluate<A: Monoid>(
        &self,
        elem: &[i32],
        target: &A,
        substitution: &[A::Elem],
    ) -> A::Elem {
        debug_assert!(self.system.is_valid(elem) && self.system.is_reduced(elem));
        debug_assert!(substitution.iter().all(|elem| target.contains(elem)));
        assert!(substitution.len() >= self.num_variables(elem));
        let mut result = target.one();
        for &var in elem.iter().rev().filter(|&&s| s >= 0) {
            result = target.mul(&substitution[var as usize], &result);
        }
        result
    }
}

impl Default for FreeMonoid {
    fn default() -> Self {
        Self::new()
    }
}

impl Domain for FreeMonoid {
    type Elem = Vec<i32>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.system.contains(elem)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.system.equals(elem1, elem2)
    }
}

impl Semigroup for FreeMonoid {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.system.evaluate2(0, elem1, elem2)
    }
}

impl Monoid for FreeMonoid {
    fn one(&self) -> Self::Elem {
        self.system.evaluate0(1)
    }
}

impl InvertibleMonoid for FreeMonoid {
    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        if self.is_one(elem) {
            Some(self.one())
        } else {
            None
        }
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        self.is_one(elem)
    }
}

impl UniversalAlgebra for FreeMonoid {
    fn signature(&self) -> &[(&str, usize)] {
        self.system.signature()
    }

    fn evaluate(&self, oper: usize, elems: &[&Self::Elem]) -> Self::Elem {
        self.system.evaluate(oper, elems)
    }
}

/// The free group on generators indexed by nonnegative values.
/// Elements are reduced, right-associated prefix terms: `[n]` is a generator,
/// `-1` denotes multiplication, `-2` denotes inversion, and `[-3]` is the identity.
/// Inverses in reduced terms apply only to generators.
#[derive(Clone, Debug)]
pub struct FreeGroup {
    system: RewriteSystem,
}

impl FreeGroup {
    /// Creates a free group using associativity, identity, and inverse laws.
    pub fn new() -> Self {
        let mut system = RewriteSystem::default();
        system.add_operation("mul", 2);
        system.add_operation("inv", 1);
        system.add_operation("one", 0);
        system.add_rule(vec![-1, -1, 0, 1, 2], vec![-1, 0, -1, 1, 2]);
        system.add_rule(vec![-1, -3, 0], vec![0]);
        system.add_rule(vec![-1, 0, -3], vec![0]);
        system.add_rule(vec![-2, -3], vec![-3]);
        system.add_rule(vec![-2, -2, 0], vec![0]);
        system.add_rule(vec![-2, -1, 0, 1], vec![-1, -2, 1, -2, 0]);
        // Cancellation at the head and inside longer right-associated products.
        system.add_rule(vec![-1, -2, 0, 0], vec![-3]);
        system.add_rule(vec![-1, 0, -2, 0], vec![-3]);
        system.add_rule(vec![-1, -2, 0, -1, 0, 1], vec![1]);
        system.add_rule(vec![-1, 0, -1, -2, 0, 1], vec![1]);
        Self { system }
    }

    /// Returns the generator with the given nonnegative index.
    pub fn generator(&self, index: usize) -> Vec<i32> {
        assert!(index <= i32::MAX as usize);
        vec![index as i32]
    }

    /// Returns one more than the largest generator index, or zero for the identity.
    pub fn num_variables(&self, elem: &[i32]) -> usize {
        self.system.num_variables(elem)
    }

    /// Evaluates an element in another group using the given generator images.
    /// The substitution must contain at least `self.num_variables(elem)` entries.
    pub fn evaluate<A: Group>(
        &self,
        elem: &[i32],
        target: &A,
        substitution: &[A::Elem],
    ) -> A::Elem {
        debug_assert!(self.system.is_valid(elem) && self.system.is_reduced(elem));
        debug_assert!(substitution.iter().all(|elem| target.contains(elem)));
        assert!(substitution.len() >= self.num_variables(elem));
        let mut result = target.one();
        for (i, &var) in elem.iter().enumerate().rev() {
            if var >= 0 {
                if i > 0 && elem[i - 1] == -2 {
                    result = target.mul(&target.inv(&substitution[var as usize]), &result);
                } else {
                    result = target.mul(&substitution[var as usize], &result);
                }
            }
        }
        result
    }
}

impl Default for FreeGroup {
    fn default() -> Self {
        Self::new()
    }
}

impl Domain for FreeGroup {
    type Elem = Vec<i32>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.system.contains(elem)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        self.system.equals(elem1, elem2)
    }
}

impl Semigroup for FreeGroup {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        self.system.evaluate2(0, elem1, elem2)
    }
}

impl Monoid for FreeGroup {
    fn one(&self) -> Self::Elem {
        self.system.evaluate0(2)
    }
}

impl InvertibleMonoid for FreeGroup {
    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        Some(self.inv(elem))
    }

    fn invertible(&self, elem: &Self::Elem) -> bool {
        debug_assert!(self.contains(elem));
        true
    }
}

impl Group for FreeGroup {
    fn inv(&self, elem: &Self::Elem) -> Self::Elem {
        self.system.evaluate1(1, elem)
    }
}

impl UniversalAlgebra for FreeGroup {
    fn signature(&self) -> &[(&str, usize)] {
        self.system.signature()
    }

    fn evaluate(&self, oper: usize, elems: &[&Self::Elem]) -> Self::Elem {
        self.system.evaluate(oper, elems)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn free_group() {
        let group = FreeGroup::new();
        let one = group.one();
        let a = group.generator(0);
        let b = group.generator(2);
        let ab = group.mul(&a, &b);
        let inv_ab = group.inv(&ab);
        assert_eq!(group.signature(), &[("mul", 2), ("inv", 1), ("one", 0)]);
        assert_eq!(one, vec![-3]);
        assert_eq!(inv_ab, vec![-1, -2, 2, -2, 0]);
        assert_ne!(ab, group.mul(&b, &a));
        for elem in [&one, &a, &ab, &inv_ab] {
            assert_eq!(group.mul(&one, elem), *elem);
            assert_eq!(group.mul(elem, &one), *elem);
            assert_eq!(group.mul(elem, &group.inv(elem)), one);
            assert_eq!(group.mul(&group.inv(elem), elem), one);
            assert_eq!(group.inv(&group.inv(elem)), *elem);
        }
        assert_eq!(group.mul(&group.inv(&a), &ab), b);
        assert_eq!(group.mul(&a, &group.mul(&group.inv(&a), &b)), b);
        assert_eq!(group.try_inv(&ab), Some(inv_ab.clone()));
        assert!(group.invertible(&ab));
        assert!(group.contains(&inv_ab));
        for elem in [
            vec![],
            vec![-4],
            vec![-2, -2, 0],
            vec![-2, -1, 0, 2],
            vec![-1, 0, -2, 0],
        ] {
            assert!(!group.contains(&elem));
        }
        assert_eq!(group.num_variables(&one), 0);
        assert_eq!(group.num_variables(&inv_ab), 3);
        let target = Permutations::new(3);
        let substitution = vec![vec![1, 2, 0], vec![0, 1, 2], vec![1, 0, 2], vec![2, 0, 1]];
        assert_eq!(group.evaluate(&one, &target, &[]), target.one());
        assert_eq!(
            group.evaluate(&group.inv(&a), &target, &substitution),
            vec![2, 0, 1]
        );
        assert_eq!(group.evaluate(&inv_ab, &target, &substitution), vec![0, 2, 1]);
        assert_eq!(group.system.is_confluent(), None);
    }

    #[test]
    fn free_monoid() {
        let monoid = FreeMonoid::new();
        let one = monoid.one();
        let a = monoid.generator(0);
        let b = monoid.generator(2);
        let ab = monoid.mul(&a, &b);
        assert_eq!(monoid.signature(), &[("mul", 2), ("one", 0)]);
        assert_eq!(one, vec![-2]);
        assert_eq!(ab, vec![-1, 0, 2]);
        assert_eq!(monoid.mul(&ab, &a), monoid.mul(&a, &monoid.mul(&b, &a)));
        for elem in [&one, &a, &ab] {
            assert!(monoid.equals(&monoid.mul(&one, elem), elem));
            assert!(monoid.equals(&monoid.mul(elem, &one), elem));
        }
        assert_eq!(monoid.try_inv(&one), Some(one.clone()));
        assert_eq!(monoid.try_inv(&ab), None);
        assert!(monoid.invertible(&one));
        assert!(!monoid.invertible(&a));
        assert!(monoid.contains(&one));
        for elem in [vec![], vec![-3], vec![-1, -2, 0], vec![-1, 0, -2]] {
            assert!(!monoid.contains(&elem));
        }
        assert_eq!(monoid.num_variables(&one), 0);
        assert_eq!(monoid.num_variables(&ab), 3);
        let target = Permutations::new(3);
        let substitution = vec![vec![1, 0, 2], vec![0, 1, 2], vec![0, 2, 1], vec![2, 1, 0]];
        assert_eq!(monoid.evaluate(&one, &target, &[]), target.one());
        assert_eq!(monoid.evaluate(&ab, &target, &substitution), vec![2, 0, 1]);
        assert_eq!(monoid.system.is_confluent(), None);
    }

    #[test]
    fn evaluate() {
        let semigroup = FreeSemigroup::new();
        let elem = semigroup.mul(&semigroup.generator(2), &semigroup.generator(0));
        let target = Permutations::new(3);
        let substitution = vec![vec![1, 0, 2], vec![0, 1, 2], vec![0, 2, 1], vec![2, 1, 0]];
        assert_eq!(semigroup.num_variables(&elem), 3);
        assert_eq!(semigroup.evaluate(&elem, &target, &substitution), vec![1, 2, 0]);
        assert_eq!(
            semigroup.evaluate(&semigroup.generator(2), &target, &substitution),
            substitution[2]
        );
    }

    #[test]
    fn free_semigroup() {
        let semigroup = FreeSemigroup::new();
        let a = semigroup.generator(0);
        let b = semigroup.generator(1);
        let c = semigroup.generator(2);
        let ab = semigroup.mul(&a, &b);
        assert_eq!(ab, vec![-1, 0, 1]);
        assert!(!semigroup.equals(&ab, &semigroup.mul(&b, &a)));
        let abc = semigroup.mul(&ab, &c);
        assert_eq!(abc, vec![-1, 0, -1, 1, 2]);
        assert!(semigroup.equals(&abc, &semigroup.mul(&a, &semigroup.mul(&b, &c))));
        assert!(semigroup.contains(&abc));
        assert!(semigroup.contains(&semigroup.generator(i32::MAX as usize)));
        for elem in [
            vec![],
            vec![0, 1],
            vec![-2],
            vec![-1, 0],
            vec![-1, -1, 0, 1, 2],
        ] {
            assert!(!semigroup.contains(&elem));
        }
        assert_eq!(semigroup.system.is_confluent(), None);
    }
}
