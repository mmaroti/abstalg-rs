// Copyright (C) 2024 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// The group of permutations on a set of fixed size. Each permutation is
/// represented by a vector of `u32` values.
#[derive(Clone, Debug)]
pub struct Permutations {
    size: u32,
}

impl Permutations {
    /// Creates a new permutation group on a set of the given size.
    pub fn new(size: u32) -> Self {
        Permutations { size }
    }

    /// Returns the number of elements in the set being permuted.
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
                if a >= self.size || used[a as usize] {
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
}

impl InvertibleMonoid for Permutations {
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
    fn symmetric_groups_exhaustive() {
        // https://oeis.org/A000142 and https://oeis.org/A000085, n = 0..5.
        let factorials = [1, 1, 2, 6, 24, 120];
        let involutions = [1, 1, 2, 4, 10, 26];
        for n in 0..=5u32 {
            let group = Permutations::new(n);
            let identity: Vec<u32> = (0..n).collect();
            assert_eq!(group.one(), identity);
            let mut elems = Vec::new();
            // Also enumerate out-of-range images, independently of contains.
            for mut code in 0..(n + 1).pow(n) {
                let elem: Vec<u32> = (0..n)
                    .map(|_| {
                        let image = code % (n + 1);
                        code /= n + 1;
                        image
                    })
                    .collect();
                let mut sorted = elem.clone();
                sorted.sort();
                let bijective = sorted == identity;
                assert_eq!(group.contains(&elem), bijective);
                if bijective {
                    elems.push(elem);
                }
            }
            assert_eq!(elems.len(), factorials[n as usize]);
            let mut count = 0;
            for a in &elems {
                let inv = group.inv(a);
                assert!(group.contains(&inv));
                assert_eq!(group.mul(a, &inv), identity);
                assert_eq!(group.mul(&inv, a), identity);
                assert_eq!(group.is_one(a), a == &identity);
                for i in 0..n as usize {
                    assert_eq!(inv[a[i] as usize], i as u32);
                }
                let mut squared = a.clone();
                group.square(&mut squared);
                assert_eq!(squared, group.mul(a, a));
                if squared == identity {
                    count += 1;
                }
                // Compute powers independently by following each point's orbit.
                for exponent in -12isize..=12 {
                    let mut expected = Vec::new();
                    for i in 0..n {
                        let mut length = 1;
                        let mut image = a[i as usize];
                        while image != i {
                            length += 1;
                            image = a[image as usize];
                        }
                        let mut image = i;
                        for _ in 0..exponent.rem_euclid(length) {
                            image = a[image as usize];
                        }
                        expected.push(image);
                    }
                    assert_eq!(group.power_signed(exponent, a), expected);
                    if exponent >= 0 {
                        assert_eq!(group.power(exponent as usize, a), expected);
                    }
                }
                let mut malformed = a.clone();
                malformed.push(0);
                assert!(!group.contains(&malformed));
                if n > 0 {
                    malformed = a.clone();
                    malformed.pop();
                    assert!(!group.contains(&malformed));
                    malformed = a.clone();
                    malformed[0] = u32::MAX;
                    assert!(!group.contains(&malformed));
                }
                for b in &elems {
                    let expected: Vec<u32> = a.iter().map(|&i| b[i as usize]).collect();
                    let product = group.mul(a, b);
                    assert_eq!(product, expected);
                    assert!(group.contains(&product));
                    let mut assigned = a.clone();
                    group.mul_assign(&mut assigned, b);
                    assert_eq!(assigned, product);
                    if n <= 4 {
                        for c in &elems {
                            assert_eq!(group.mul(&product, c), group.mul(a, &group.mul(b, c)));
                        }
                    }
                }
            }
            assert_eq!(count, involutions[n as usize]);
        }
    }
}
