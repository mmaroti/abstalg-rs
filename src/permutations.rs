// Copyright (C) 2024 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

#[derive(Clone, Debug)]
pub struct Permutations {
    size: u32,
}

/// The group of permutations on a set of fixed size. Each permutation is
/// represented by a vector of u32 values.
impl Permutations {
    pub fn new(size: u32) -> Self {
        Permutations { size }
    }

    pub fn size(&self) -> u32 {
        self.size
    }
}

impl Domain for Permutations {
    type Elem = Vec<u32>;

    fn contains(&self, elem: &Self::Elem) -> bool {
        if elem.len() != self.size as usize {
            false
        } else {
            let mut used = vec![false; self.size as usize];
            for &a in elem.iter() {
                if used[a as usize] {
                    return false;
                }
                used[a as usize] = true;
            }
            true
        }
    }

    fn equals(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> bool {
        elem1 == elem2
    }
}

impl Semigroup for Permutations {
    fn mul(&self, elem1: &Self::Elem, elem2: &Self::Elem) -> Self::Elem {
        debug_assert_eq!(elem1.len(), self.size as usize);
        debug_assert_eq!(elem2.len(), self.size as usize);
        let mut prod = vec![0; self.size as usize];
        for (i, &a) in elem1.iter().enumerate() {
            prod[i] = elem2[a as usize];
        }
        prod
    }

    fn mul_assign(&self, elem1: &mut Self::Elem, elem2: &Self::Elem) {
        debug_assert_eq!(elem1.len(), self.size as usize);
        debug_assert_eq!(elem2.len(), self.size as usize);
        for a in elem1.iter_mut() {
            *a = elem2[*a as usize];
        }
    }
}

impl Monoid for Permutations {
    fn one(&self) -> Self::Elem {
        let mut elem = vec![0; self.size as usize];
        for i in 0..self.size {
            elem[i as usize] = i;
        }
        elem
    }

    fn is_one(&self, elem: &Self::Elem) -> bool {
        debug_assert_eq!(elem.len(), self.size as usize);
        for (i, &a) in elem.iter().enumerate() {
            if i != a as usize {
                return false;
            }
        }
        true
    }

    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        debug_assert_eq!(elem.len(), self.size as usize);
        let mut inv = vec![0; self.size as usize];
        for (i, &a) in elem.iter().enumerate() {
            inv[a as usize] = i as u32;
        }
        Some(inv)
    }

    fn invertible(&self, _elem: &Self::Elem) -> bool {
        true
    }
}

impl Group for Permutations {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn s4() {
        let perm = Permutations::new(4);
        let mut count = 0;

        let mut elem = vec![0; 4];
        for i in 0..256 {
            let mut a = i;
            for b in elem.iter_mut() {
                *b = a % 4;
                a /= 4;
            }
            if perm.contains(&elem) {
                count += 1;
            }
        }
        assert_eq!(count, 24);

        let elem1 = vec![1, 2, 3, 0];
        let elem2 = vec![1, 0, 3, 2];
        let elem3 = vec![0, 3, 2, 1];
        assert_eq!(perm.mul(&elem1, &elem2), elem3);

        let elem4 = vec![3, 0, 1, 2];
        assert_eq!(perm.inv(&elem1), elem4);
    }
}
