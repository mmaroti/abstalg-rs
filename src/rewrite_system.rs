// Copyright (C) 2025 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;
use std::cmp::Ordering;
use std::num::NonZeroUsize;

#[derive(Clone, Debug)]
struct Rule {
    left: Vec<i32>,
    right: Vec<i32>,
}

#[derive(Clone, Debug, Default)]
pub struct RewriteSystem {
    signature: Vec<(&'static str, usize)>,
    rules: Vec<Rule>,
}

impl RewriteSystem {
    /// Adds a new operation symbol to this rewrite system.
    pub fn add_operation(&mut self, name: &'static str, arity: usize) {
        assert!(arity <= isize::MAX as usize);
        assert!(self.signature.iter().all(|(n, _)| *n != name));
        self.signature.push((name, arity));
    }

    /// Adds a new rewrite rule to the rewrite system. The left term must be
    /// operation-rooted and ascending, and all variables of the right one must
    /// appear in the left.
    pub fn add_rule(&mut self, left: Vec<i32>, right: Vec<i32>) {
        assert!(self.is_valid(&left) && self.is_valid(&right));
        assert!(left[0] < 0);
        let n = self.is_ascending(&left).unwrap();
        assert!(self.num_variables(&right) <= n);
        self.rules.push(Rule { left, right });
    }

    /// Returns the length of the unique initial subterm fragment of the given
    /// term fragment. If there is no valid initial segment, then None is
    /// returned.
    pub fn get_length(&self, fragment: &[i32]) -> Option<NonZeroUsize> {
        let mut missing = 1usize;
        for (n, &a) in fragment.iter().enumerate() {
            if a < 0 {
                let op = -(a + 1) as usize;
                if op >= self.signature.len() {
                    return None;
                }
                missing = missing.checked_add(self.signature[op].1)?;
            }
            if missing <= 1 {
                return NonZeroUsize::new(n + 1);
            }
            missing -= 1;
        }
        None
    }

    /// Returns true if the given term is a valid (possibly not reduced) term
    /// in the signature of this rewrite system.
    pub fn is_valid(&self, term: &[i32]) -> bool {
        if let Some(n) = self.get_length(term) {
            n.get() == term.len()
        } else {
            false
        }
    }

    /// Returns the number of variables of the given term, which is the least
    /// integer such that all variables of the term are smaller than this
    /// value.
    pub fn num_variables(&self, term: &[i32]) -> usize {
        let mut num = -1isize;
        for &s in term {
            num = std::cmp::max(num, s as isize);
        }
        num.wrapping_add(1) as usize
    }

    /// Returns the number of variables in the term if the variables are first
    /// appearing in ascending order, None otherwise.
    pub fn is_ascending(&self, term: &[i32]) -> Option<usize> {
        let mut num = 0;
        for &s in term {
            if s >= 0 {
                match (s as usize).cmp(&num) {
                    Ordering::Greater => return None,
                    Ordering::Equal => num += 1,
                    Ordering::Less => (),
                }
            }
        }
        Some(num)
    }

    /// Checks if the given term is a variable, and returns its index.
    pub fn is_variable(&self, term: &[i32]) -> Option<usize> {
        debug_assert!(!term.is_empty());
        if term[0] >= 0 {
            debug_assert_eq!(term.len(), 1);
            Some(term[0] as usize)
        } else {
            None
        }
    }

    /// Checks if the given term is the application of an operation to
    /// subterms, and returns the index of the operation and the subterms.
    pub fn is_operation<'a>(&self, term: &'a [i32]) -> Option<(usize, Vec<&'a [i32]>)> {
        debug_assert!(!term.is_empty());
        if term[0] < 0 {
            let op = -(term[0] + 1) as usize;
            let mut subs = Vec::with_capacity(self.signature[op].1);
            let mut pos = 1;
            for _ in 0..self.signature[op].1 {
                let len = self.get_length(&term[pos..]).unwrap().get();
                subs.push(&term[pos..(pos + len)]);
                pos += len;
            }
            debug_assert_eq!(pos, term.len());
            Some((op, subs))
        } else {
            None
        }
    }

    fn match_rule_helper<'a>(
        &self,
        rule_fragment: &[i32],
        term_fragment: &'a [i32],
        subtitution: &mut Vec<Option<&'a [i32]>>,
    ) -> Option<(NonZeroUsize, NonZeroUsize)> {
        debug_assert!(!rule_fragment.is_empty() && !term_fragment.is_empty());
        if rule_fragment[0] >= 0 {
            let var = rule_fragment[0] as usize;
            if subtitution.len() <= var {
                subtitution.resize(var + 1, None);
            }
            if let Some(t) = subtitution[var] {
                if term_fragment.len() >= t.len() && term_fragment[..t.len()] == *t {
                    Some((
                        NonZeroUsize::new(t.len()).unwrap(),
                        NonZeroUsize::new(1).unwrap(),
                    ))
                } else {
                    None
                }
            } else {
                let len = self.get_length(term_fragment).unwrap();
                subtitution[var] = Some(&term_fragment[..len.get()]);
                Some((len, NonZeroUsize::new(1).unwrap()))
            }
        } else if term_fragment[0] != rule_fragment[0] {
            None
        } else {
            let op = -(rule_fragment[0] + 1) as usize;
            let mut pos1 = 1;
            let mut pos2 = 1;
            for _ in 0..self.signature[op].1 {
                if let Some((len1, len2)) = self.match_rule_helper(
                    &rule_fragment[pos2..],
                    &term_fragment[pos1..],
                    subtitution,
                ) {
                    pos1 += len1.get();
                    pos2 += len2.get();
                } else {
                    return None;
                }
            }
            Some((
                NonZeroUsize::new(pos1).unwrap(),
                NonZeroUsize::new(pos2).unwrap(),
            ))
        }
    }

    /// Checks if the given rule matches the term and returns the substitution
    /// of the variables of the rule to subterms that makes them equal.
    pub fn match_rule<'a>(&self, rule: &[i32], term: &'a [i32]) -> Option<Vec<Option<&'a [i32]>>> {
        debug_assert!(!rule.is_empty() && !term.is_empty());
        let mut substitution = vec![];
        if let Some((len1, len2)) = self.match_rule_helper(rule, term, &mut substitution) {
            debug_assert!(len1.get() == term.len() && len2.get() == rule.len());
            Some(substitution)
        } else {
            None
        }
    }

    fn is_reduced_helper<'a>(&self, term: &'a [i32], temp: &mut Vec<Option<&'a [i32]>>) -> bool {
        if let Some((_, subterms)) = self.is_operation(term) {
            for t in subterms {
                if !self.is_reduced_helper(t, temp) {
                    return false;
                }
            }
        }
        for rule in self.rules.iter() {
            let left = &rule.left;
            temp.clear();
            if let Some((len1, len2)) = self.match_rule_helper(left, term, temp) {
                debug_assert!(len1.get() == term.len() && len2.get() == left.len());
                return false;
            }
        }
        true
    }

    /// Returns true if the given valid term is fully reduced.
    pub fn is_reduced(&self, term: &[i32]) -> bool {
        let mut temp = vec![];
        self.is_reduced_helper(term, &mut temp)
    }

    /// Reduces a valid term using the identity substitution for its variables.
    /// The caller must ensure that the rewrite rules terminate.
    pub fn rewrite(&self, term: &[i32]) -> Vec<i32> {
        debug_assert!(self.is_valid(term));
        let mut substitution = vec![None; self.num_variables(term)];
        for (i, &s) in term.iter().enumerate() {
            if s >= 0 {
                substitution[s as usize] = Some(&term[i..i + 1]);
            }
        }
        self.evaluate_helper(term, &substitution)
    }

    /// Replaces the variables in the term with the matching substitution.
    pub fn substitute(&self, term: &[i32], substitution: &[Option<&[i32]>]) -> Vec<i32> {
        let mut result = vec![];
        for &s in term {
            if s < 0 {
                result.push(s)
            } else {
                let s = s as usize;
                assert!(s < substitution.len() && substitution[s].is_some());
                result.extend_from_slice(substitution[s].unwrap());
            }
        }
        result
    }

    /// Evaluates a valid term with fully reduced substitution values.
    fn evaluate_helper(&self, term: &[i32], substitution: &[Option<&[i32]>]) -> Vec<i32> {
        debug_assert!(self.is_valid(term));
        debug_assert!(substitution
            .iter()
            .flatten()
            .all(|t| self.is_valid(t) && self.is_reduced(t)));
        if let Some(var) = self.is_variable(term) {
            substitution[var].unwrap().to_vec()
        } else {
            let (oper, subterms) = self.is_operation(term).unwrap();
            let elems: Vec<_> = subterms
                .iter()
                .map(|t| self.evaluate_helper(t, substitution))
                .collect();
            self.evaluate(oper, &elems.iter().collect::<Vec<_>>())
        }
    }
}

impl Domain for RewriteSystem {
    type Elem = Vec<i32>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.is_valid(elem) && self.is_reduced(elem)
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        debug_assert!(self.contains(elem1) && self.contains(elem2));
        elem1 == elem2
    }
}

impl UniversalAlgebra for RewriteSystem {
    fn signature(&self) -> &[(&'static str, usize)] {
        &self.signature
    }

    /// Applies an operation to fully reduced arguments and returns a normal form.
    /// The caller must ensure that the rewrite rules terminate.
    fn evaluate(&self, oper: usize, elems: &[&Self::Elem]) -> Self::Elem {
        assert!(oper < self.signature.len() && self.signature[oper].1 == elems.len());
        debug_assert!(elems.iter().all(|elem| self.contains(elem)));
        let mut term = vec![-1 - oper as i32];
        for elem in elems {
            term.extend_from_slice(elem);
        }
        for rule in &self.rules {
            if let Some(substitution) = self.match_rule(&rule.left, &term) {
                return self.evaluate_helper(&rule.right, &substitution);
            }
        }
        term
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_validation() {
        let mut system = RewriteSystem::default();
        system.add_operation("mul", 2);
        system.add_operation("one", 0);
        assert_eq!(system.get_length(&[-1, 0, 1, 2]), NonZeroUsize::new(3));
        assert!(system.contains(&vec![-1, 0, 1]));
        assert!(system.contains(&vec![-2]));
        for term in [
            vec![],
            vec![-1],
            vec![-3],
            vec![i32::MIN],
            vec![0, 1],
            vec![-2, 0],
        ] {
            assert!(!system.is_valid(&term));
            assert!(!system.contains(&term));
        }
        assert_eq!(system.num_variables(&[-2]), 0);
        assert_eq!(system.num_variables(&[i32::MAX]), i32::MAX as usize + 1);
        assert_eq!(system.is_ascending(&[-1, 0, 0]), Some(1));
        assert_eq!(system.is_ascending(&[-1, 1, 0]), None);
    }

    #[test]
    fn arity_overflow() {
        let mut system = RewriteSystem::default();
        system.add_operation("huge", isize::MAX as usize);
        system.add_operation("four", 4);
        assert_eq!(system.get_length(&[-1]), None);
        assert!(!system.contains(&vec![-1]));
        // Individually permitted arities overflow when accumulated.
        assert_eq!(system.get_length(&[-1, -1, -2]), None);
        assert!(!system.is_valid(&[-1, -1, -2]));
        assert!(!system.contains(&vec![-1, -1, -2]));
    }

    #[test]
    fn matching_and_substitution() {
        let mut system = RewriteSystem::default();
        system.add_operation("mul", 2);
        let pattern = [-1, 0, 0];
        let term = [-1, -1, 1, 2, -1, 1, 2];
        let substitution = system.match_rule(&pattern, &term).unwrap();
        assert_eq!(substitution, vec![Some(&term[1..4])]);
        assert_eq!(system.substitute(&pattern, &substitution), term);
        assert!(system
            .match_rule(&pattern, &[-1, -1, 1, 2, -1, 2, 1])
            .is_none());
    }

    #[test]
    fn rewrite() {
        let mut system = RewriteSystem::default();
        system.add_operation("mul", 2);
        system.add_operation("one", 0);
        system.add_rule(vec![-1, -1, 0, 1, 2], vec![-1, 0, -1, 1, 2]);
        let term = [-1, -1, -1, 0, 1, 2, -1, -1, 3, 4, 5];
        let result = system.rewrite(&term);
        assert_eq!(result, vec![-1, 0, -1, 1, -1, 2, -1, 3, -1, 4, 5]);
        assert!(system.contains(&result));
        assert_eq!(system.rewrite(&result), result);
        assert_eq!(system.rewrite(&[7]), vec![7]);
        assert_eq!(system.rewrite(&[-2]), vec![-2]);
    }

    #[test]
    fn evaluate() {
        let mut system = RewriteSystem::default();
        system.add_operation("f", 1);
        system.add_operation("g", 1);
        system.add_operation("h", 1);
        system.add_operation("one", 0);
        system.add_operation("alias", 0);
        system.add_rule(vec![-1, 0], vec![-2, -3, 0]);
        system.add_rule(vec![-3, 0], vec![0]);
        system.add_rule(vec![-2, 0], vec![0]);
        system.add_rule(vec![-5], vec![-4]);
        // Both the child and head introduced by f's right side must reduce.
        assert_eq!(system.evaluate1(0, &vec![0]), vec![0]);
        assert_eq!(system.evaluate0(4), vec![-4]);
    }

    #[test]
    fn free_semigroup() {
        let mut system: RewriteSystem = Default::default();
        system.add_operation("mul", 2);
        let left = vec![-1, -1, 0, 1, 2];
        let right = vec![-1, 0, -1, 1, 2];
        system.add_rule(left.clone(), right.clone());
        let term = vec![-1, -1, 3, 4, -1, 5, 6];
        let substitution = system.match_rule(&left, &term).unwrap();
        let result = system.substitute(&right, &substitution);
        assert_eq!(result, vec![-1, 3, -1, 4, -1, 5, 6]);
        assert!(!system.contains(&term));
        assert!(system.contains(&result));
        assert!(!system.contains(&vec![-1, 3, -1, -1, 4, 5, 6]));
        assert_eq!(
            system.evaluate2(0, &vec![-1, 3, -1, 4, 5], &vec![-1, 6, 7]),
            vec![-1, 3, -1, 4, -1, 5, -1, 6, 7]
        );
    }
}
