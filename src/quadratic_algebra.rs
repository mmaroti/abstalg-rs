// Copyright (C) 2026 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

use crate::*;

/// Supplies a quadratic relation over any commutative coefficient ring.
/// The methods are called only during algebra construction; their results are
/// cached in the algebra. Policies must return valid base-ring elements.
pub trait QuadraticPolicy: Clone {
    /// Linear coefficient in `theta^2 = t*theta + u`.
    fn t<A: CommutativeRing>(&self, base: &A) -> A::Elem;
    /// Constant coefficient in `theta^2 = t*theta + u`.
    fn u<A: CommutativeRing>(&self, base: &A) -> A::Elem;
}

/// The relation `i^2 = -1`, independent of coefficient representation.
#[derive(Clone, Copy, Debug, Default)]
pub struct Imaginary;

impl QuadraticPolicy for Imaginary {
    fn t<A: CommutativeRing>(&self, base: &A) -> A::Elem {
        base.zero()
    }

    fn u<A: CommutativeRing>(&self, base: &A) -> A::Elem {
        base.int(-1)
    }
}

/// The relation `omega^2 = -omega - 1`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Eisenstein;

impl QuadraticPolicy for Eisenstein {
    fn t<A: CommutativeRing>(&self, base: &A) -> A::Elem {
        base.int(-1)
    }

    fn u<A: CommutativeRing>(&self, base: &A) -> A::Elem {
        base.int(-1)
    }
}

/// A quadratic relation whose coefficients are images of ordinary integers.
/// Arbitrary integer parameters need not define an integral domain or field.
#[derive(Clone, Copy, Debug)]
pub struct Generic {
    /// Linear coefficient.
    pub t: isize,
    /// Constant coefficient.
    pub u: isize,
}

impl QuadraticPolicy for Generic {
    fn t<A: CommutativeRing>(&self, base: &A) -> A::Elem {
        base.int(self.t)
    }

    fn u<A: CommutativeRing>(&self, base: &A) -> A::Elem {
        base.int(self.u)
    }
}

/// The commutative algebra `A[theta] / (theta^2 - t*theta - u)`.
/// Elements are pairs `(a, b)` representing `a + b*theta`. The parameters
/// belong to the algebra, not its elements. Reducible polynomials and zero
/// divisors are allowed; this construction does not assume a domain or field.
///
/// ```
/// use abstalg::*;
/// let complex = QuadraticAlgebra::with_policy(QQ, Imaginary);
/// let i = (QQ.zero(), QQ.one());
/// assert_eq!(complex.mul(&i, &i), complex.int(-1));
/// ```
#[derive(Clone, Debug)]
pub struct QuadraticAlgebra<A: CommutativeRing, P: QuadraticPolicy = Generic> {
    policy: P,
    base: A,
    t: A::Elem,
    u: A::Elem,
}

impl<A: CommutativeRing, P: QuadraticPolicy> QuadraticAlgebra<A, P> {
    /// Creates the algebra from a coefficient ring and a relation policy.
    /// The policy computes `t` and `u` once; subsequent operations borrow them.
    pub fn with_policy(base: A, policy: P) -> Self {
        let t = policy.t(&base);
        let u = policy.u(&base);
        assert!(base.contains(&t) && base.contains(&u));
        Self { base, policy, t, u }
    }

    /// Returns the policy used to construct the cached relation.
    pub fn policy(&self) -> &P {
        &self.policy
    }

    /// Returns the coefficient ring.
    pub fn base(&self) -> &A {
        &self.base
    }

    /// Returns the linear coefficient in the defining relation.
    pub fn t(&self) -> &A::Elem {
        &self.t
    }

    /// Returns the constant coefficient in the defining relation.
    pub fn u(&self) -> &A::Elem {
        &self.u
    }

    /// Embeds a coefficient as a constant element.
    pub fn constant(&self, elem: A::Elem) -> (A::Elem, A::Elem) {
        (elem, self.base.zero())
    }

    /// Returns the generator `theta`.
    pub fn generator(&self) -> (A::Elem, A::Elem) {
        (self.base.zero(), self.base.one())
    }

    /// Returns the conjugate, sending `theta` to `t - theta`.
    pub fn conjugate(&self, elem: &(A::Elem, A::Elem)) -> (A::Elem, A::Elem) {
        (
            self.base.add(&elem.0, &self.base.mul(&self.t, &elem.1)),
            self.base.neg(&elem.1),
        )
    }

    /// Returns the trace `2*a + t*b` in the coefficient ring.
    pub fn trace(&self, elem: &(A::Elem, A::Elem)) -> A::Elem {
        self.base.add(
            &self.base.add(&elem.0, &elem.0),
            &self.base.mul(&self.t, &elem.1),
        )
    }

    /// Returns the algebraic norm `a^2 + t*a*b - u*b^2`.
    /// For complex numbers this is the squared magnitude, not the magnitude.
    pub fn norm(&self, elem: &(A::Elem, A::Elem)) -> A::Elem {
        self.base.sub(
            &self.base.add(
                &self.base.mul(&elem.0, &elem.0),
                &self.base.mul(&self.t, &self.base.mul(&elem.0, &elem.1)),
            ),
            &self.base.mul(&self.u, &self.base.mul(&elem.1, &elem.1)),
        )
    }
}

impl<A: CommutativeRing> QuadraticAlgebra<A, Imaginary> {
    /// Creates the imaginary extension with relation `i^2 = -1`.
    pub fn new(base: A) -> Self {
        Self::with_policy(base, Imaginary)
    }
}

impl<A: CommutativeRing> QuadraticAlgebra<A, Eisenstein> {
    /// Creates the Eisenstein extension with relation `omega^2 = -omega - 1`.
    pub fn new(base: A) -> Self {
        Self::with_policy(base, Eisenstein)
    }
}

impl<A: CommutativeRing, P: QuadraticPolicy> Domain for QuadraticAlgebra<A, P> {
    type Elem = (A::Elem, A::Elem);

    fn contains(&self, elem: &Self::Elem) -> bool {
        self.base.contains(&elem.0) && self.base.contains(&elem.1)
    }

    fn equals(&self, a: &Self::Elem, b: &Self::Elem) -> bool {
        self.base.equals(&a.0, &b.0) && self.base.equals(&a.1, &b.1)
    }
}

impl<A: CommutativeRing, P: QuadraticPolicy> Semigroup for QuadraticAlgebra<A, P> {
    fn mul(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem {
        let bd = self.base.mul(&a.1, &b.1);
        (
            self.base
                .add(&self.base.mul(&a.0, &b.0), &self.base.mul(&self.u, &bd)),
            self.base.add(
                &self
                    .base
                    .add(&self.base.mul(&a.0, &b.1), &self.base.mul(&a.1, &b.0)),
                &self.base.mul(&self.t, &bd),
            ),
        )
    }
}

impl<A: CommutativeRing, P: QuadraticPolicy> Monoid for QuadraticAlgebra<A, P> {
    fn one(&self) -> Self::Elem {
        self.constant(self.base.one())
    }
}

impl<A: CommutativeRing + InvertibleMonoid, P: QuadraticPolicy> InvertibleMonoid
    for QuadraticAlgebra<A, P>
{
    fn try_inv(&self, elem: &Self::Elem) -> Option<Self::Elem> {
        let inverse_norm = self.base.try_inv(&self.norm(elem))?;
        let conjugate = self.conjugate(elem);
        Some((
            self.base.mul(&inverse_norm, &conjugate.0),
            self.base.mul(&inverse_norm, &conjugate.1),
        ))
    }
}

impl<A: CommutativeRing, P: QuadraticPolicy> CommutativeMonoid for QuadraticAlgebra<A, P> {
    fn zero(&self) -> Self::Elem {
        self.constant(self.base.zero())
    }

    fn add(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem {
        (self.base.add(&a.0, &b.0), self.base.add(&a.1, &b.1))
    }
}

impl<A: CommutativeRing, P: QuadraticPolicy> AbelianGroup for QuadraticAlgebra<A, P> {
    fn neg(&self, elem: &Self::Elem) -> Self::Elem {
        (self.base.neg(&elem.0), self.base.neg(&elem.1))
    }
}

impl<A: CommutativeRing, P: QuadraticPolicy> SemiRing for QuadraticAlgebra<A, P> {}
impl<A: CommutativeRing, P: QuadraticPolicy> UnitaryRing for QuadraticAlgebra<A, P> {}
impl<A: CommutativeRing, P: QuadraticPolicy> CommutativeRing for QuadraticAlgebra<A, P> {}

/// Numbers `a + b*i` over the chosen coefficient ring, defaulting to `QQ`.
/// Supports conjugation, algebraic norm, and unit inversion through `try_inv`;
/// this alias does not add a `Field` implementation.
///
/// ```
/// use abstalg::*;
/// let exact = ComplexNumbers::new(QQ);
/// let i = exact.generator();
/// assert_eq!(exact.mul(&i, &i), exact.int(-1));
/// assert_eq!(exact.try_inv(&i), Some(exact.neg(&i)));
/// let approximate = ComplexNumbers::new(F64);
/// assert_eq!(approximate.norm(&(3.0, 4.0)), 25.0);
/// ```
pub type ComplexNumbers<A = ReducedFractions<Integers>> = QuadraticAlgebra<A, Imaginary>;

/// Gaussian integers over the chosen integer coefficient representation.
/// Construct with `GaussianIntegers::new(base)`.
pub type GaussianIntegers<A = Integers> = QuadraticAlgebra<A, Imaginary>;

/// Eisenstein integers over the chosen integer coefficient representation.
/// Construct with `EisensteinIntegers::new(base)`.
pub type EisensteinIntegers<A = Integers> = QuadraticAlgebra<A, Eisenstein>;

/// Gaussian integers with arbitrary-precision coefficients, initialized once.
///
/// ```
/// use abstalg::*;
/// let i = ZZI.generator();
/// assert_eq!(ZZI.mul(&i, &i), ZZI.int(-1));
/// let checked = GaussianIntegers::new(I32);
/// assert_eq!(checked.norm(&(3, 2)), 13);
/// ```
pub static ZZI: std::sync::LazyLock<GaussianIntegers> =
    std::sync::LazyLock::new(|| GaussianIntegers::new(ZZ));

/// Eisenstein integers with arbitrary-precision coefficients, initialized once.
///
/// ```
/// use abstalg::*;
/// let omega = ZZW.generator();
/// assert_eq!(ZZW.power(3, &omega), ZZW.one());
/// let checked = EisensteinIntegers::new(I32);
/// assert_eq!(checked.norm(&(1, -1)), 3);
/// ```
pub static ZZW: std::sync::LazyLock<EisensteinIntegers> =
    std::sync::LazyLock::new(|| EisensteinIntegers::new(ZZ));

/// Marks Gaussian or Eisenstein algebras over ordered integer coefficient
/// rings. These algebras support the shared lattice division algorithm and
/// associate normalization. The supported bases are `ZZ` and checked signed
/// integers. Intermediate arithmetic uses the base's overflow behavior.
///
/// Implementors must have relation `(t, u) = (0, -1)` or `(-1, -1)`, and their
/// coefficient ring must have the usual integer order and floor quotient for
/// positive divisors. Other quadratic algebras must not implement this marker.
pub trait QuadraticInteger: Domain {}

impl<A: IntegerDomain> QuadraticInteger for QuadraticAlgebra<A, Imaginary> {}
impl<A: IntegerDomain> QuadraticInteger for QuadraticAlgebra<A, Eisenstein> {}

impl<A, P> QuadraticAlgebra<A, P>
where
    A: IntegerDomain,
    P: QuadraticPolicy,
    Self: QuadraticInteger<Elem = (A::Elem, A::Elem)>,
{
    fn lex_less(&self, a: &(A::Elem, A::Elem), b: &(A::Elem, A::Elem)) -> bool {
        self.base.less_than(&a.0, &b.0)
            || (self.base.equals(&a.0, &b.0) && self.base.less_than(&a.1, &b.1))
    }

    // Both rings' units have coordinates in -1..=1 and norm one. Choose the
    // lexicographically greatest unit multiple as the canonical associate.
    fn integer_associate(
        &self,
        elem: &(A::Elem, A::Elem),
    ) -> ((A::Elem, A::Elem), (A::Elem, A::Elem)) {
        let mut best = elem.clone();
        let mut coefficient = self.one();
        for a in -1..=1 {
            for b in -1..=1 {
                let unit = (self.base.int(a), self.base.int(b));
                if self.base.is_one(&self.norm(&unit)) {
                    let candidate = self.mul(&unit, elem);
                    if self.lex_less(&best, &candidate) {
                        best = candidate;
                        coefficient = unit;
                    }
                }
            }
        }
        (best, coefficient)
    }

    fn integer_quo_rem(
        &self,
        a: &(A::Elem, A::Elem),
        b: &(A::Elem, A::Elem),
    ) -> ((A::Elem, A::Elem), (A::Elem, A::Elem)) {
        let denominator = self.norm(b);
        assert!(!self.base.is_zero(&denominator));
        let numerator = self.mul(a, &self.conjugate(b));
        let x = self.base.quo(&numerator.0, &denominator);
        let y = self.base.quo(&numerator.1, &denominator);
        let mut best = None;
        // At least one corner has remainder norm <= N(b)/2 (Gaussian) or
        // 3*N(b)/4 (Eisenstein). Tie-breaking by greatest remainder makes the
        // choice invariant under translation of a by a multiple of b.
        for dx in 0..=1 {
            for dy in 0..=1 {
                let quotient = (
                    self.base.add(&x, &self.base.int(dx)),
                    self.base.add(&y, &self.base.int(dy)),
                );
                let remainder = self.sub(a, &self.mul(&quotient, b));
                let norm = self.norm(&remainder);
                let replace = best.as_ref().map_or(true, |(_, r, n)| {
                    self.base.less_than(&norm, n)
                        || (self.base.equals(&norm, n) && self.lex_less(r, &remainder))
                });
                if replace {
                    best = Some((quotient, remainder, norm));
                }
            }
        }
        let (quotient, remainder, _) = best.unwrap();
        (quotient, remainder)
    }
}

impl<A, P> IntegralDomain for QuadraticAlgebra<A, P>
where
    A: IntegerDomain,
    P: QuadraticPolicy,
    Self: QuadraticInteger<Elem = (A::Elem, A::Elem)>,
{
    fn try_div(&self, a: &Self::Elem, b: &Self::Elem) -> Option<Self::Elem> {
        let denominator = self.norm(b);
        assert!(!self.base.is_zero(&denominator));
        let numerator = self.mul(a, &self.conjugate(b));
        Some((
            self.base.try_div(&numerator.0, &denominator)?,
            self.base.try_div(&numerator.1, &denominator)?,
        ))
    }

    fn associate_repr(&self, elem: &Self::Elem) -> Self::Elem {
        self.integer_associate(elem).0
    }

    fn associate_coef(&self, elem: &Self::Elem) -> Self::Elem {
        assert!(!self.is_zero(elem));
        self.integer_associate(elem).1
    }
}

impl<A, P> EuclideanDomain for QuadraticAlgebra<A, P>
where
    A: IntegerDomain,
    P: QuadraticPolicy,
    Self: QuadraticInteger<Elem = (A::Elem, A::Elem)>,
{
    fn quo_rem(&self, a: &Self::Elem, b: &Self::Elem) -> (Self::Elem, Self::Elem) {
        self.integer_quo_rem(a, b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::BigInt;
    use std::collections::BTreeSet;

    type Elem = (BigInt, BigInt);

    #[test]
    fn finite_quadratic_algebras_exhaustive() {
        for n in 2..=5i32 {
            let base = QuotientRing::new(I32, n);
            let elems: Vec<_> = (0..n).flat_map(|a| (0..n).map(move |b| (a, b))).collect();
            for t in 0..n {
                for u in 0..n {
                    let ring = QuadraticAlgebra::with_policy(
                        base.clone(),
                        Generic {
                            t: t as isize,
                            u: u as isize,
                        },
                    );
                    assert_eq!(ring.base().modulo(), &n);
                    assert_eq!((*ring.t(), *ring.u()), (t, u));
                    let generator = ring.generator();
                    assert_eq!(ring.mul(&generator, &generator), (u, t));
                    for a in &elems {
                        assert!(ring.contains(a));
                        assert!(!ring.contains(&(a.0 + n, a.1)));
                        assert!(!ring.contains(&(a.0, a.1 + n)));
                        let conjugate = ring.conjugate(a);
                        assert_eq!(ring.conjugate(&conjugate), *a);
                        assert_eq!(ring.add(a, &conjugate), ring.constant(ring.trace(a)));
                        assert_eq!(ring.mul(a, &conjugate), ring.constant(ring.norm(a)));
                        let expected_inverse = elems
                            .iter()
                            .find(|b| {
                                (a.0 * b.0 + u * a.1 * b.1) % n == 1
                                    && (a.0 * b.1 + a.1 * b.0 + t * a.1 * b.1) % n == 0
                            })
                            .copied();
                        assert_eq!(ring.try_inv(a), expected_inverse);
                        assert_eq!(ring.add(a, &ring.neg(a)), ring.zero());
                        for b in &elems {
                            let product = ring.mul(a, b);
                            assert_eq!(
                                product,
                                (
                                    (a.0 * b.0 + u * a.1 * b.1) % n,
                                    (a.0 * b.1 + a.1 * b.0 + t * a.1 * b.1) % n,
                                )
                            );
                            assert_eq!(ring.mul(b, a), product);
                            assert_eq!(ring.norm(&product), (ring.norm(a) * ring.norm(b)) % n);
                            assert_eq!(
                                ring.conjugate(&product),
                                ring.mul(&conjugate, &ring.conjugate(b))
                            );
                            if n <= 3 {
                                for c in &elems {
                                    assert_eq!(ring.mul(&product, c), ring.mul(a, &ring.mul(b, c)));
                                    assert_eq!(
                                        ring.mul(a, &ring.add(b, c)),
                                        ring.add(&product, &ring.mul(a, c))
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn rational_quadratic_inverses() {
        for t in -1..=1 {
            for u in -1..=1 {
                let ring = QuadraticAlgebra::with_policy(QQ, Generic { t, u });
                for a in -3..=3 {
                    for b in -3..=3 {
                        let elem = (QQ.int(a), QQ.int(b));
                        match ring.try_inv(&elem) {
                            Some(inv) => {
                                assert!(!QQ.is_zero(&ring.norm(&elem)));
                                assert_eq!(ring.mul(&elem, &inv), ring.one());
                            }
                            None => assert!(QQ.is_zero(&ring.norm(&elem))),
                        }
                    }
                }
            }
        }
    }

    fn elements(bound: i32) -> Vec<Elem> {
        (-bound..=bound)
            .flat_map(|a| (-bound..=bound).map(move |b| (BigInt::from(a), BigInt::from(b))))
            .collect()
    }

    fn norm(elem: &Elem, t: i32) -> BigInt {
        &elem.0 * &elem.0 + BigInt::from(t) * &elem.0 * &elem.1 + &elem.1 * &elem.1
    }

    fn euclidean_properties<R: EuclideanDomain<Elem = Elem>>(ring: R, t: i32, unit_count: usize) {
        let elems = elements(2);
        let units: Vec<_> = elems
            .iter()
            .filter(|a| norm(a, t) == BigInt::from(1))
            .collect();
        assert_eq!(units.len(), unit_count);
        for a in &elems {
            assert_eq!(ring.try_inv(a).is_some(), norm(a, t) == BigInt::from(1));
            let representative = ring.associate_repr(a);
            assert_eq!(ring.associate_repr(&representative), representative);
            for unit in &units {
                assert_eq!(ring.associate_repr(&ring.mul(a, unit)), representative);
            }
            if !ring.is_zero(a) {
                let coef = ring.associate_coef(a);
                assert!(ring.invertible(&coef));
                assert_eq!(ring.mul(&coef, a), representative);
            }
            for b in &elems {
                if !ring.is_zero(b) {
                    let (q, r) = ring.quo_rem(a, b);
                    assert_eq!(ring.add(&ring.mul(&q, b), &r), *a);
                    assert!(norm(&r, t) < norm(b, t));
                    assert!(ring.reduced(&r, b));
                    assert_eq!(ring.rem(&r, b), r);
                    assert_eq!(
                        ring.try_div(a, b),
                        if ring.is_zero(&r) { Some(q) } else { None }
                    );
                    for k in elements(1) {
                        assert_eq!(ring.rem(&ring.add(a, &ring.mul(&k, b)), b), r);
                    }
                }
                let (g, x, y) = ring.normalized_extended_gcd(a, b);
                assert_eq!(ring.add(&ring.mul(a, &x), &ring.mul(b, &y)), g);
                assert_eq!(ring.associate_repr(&g), g);
                assert!(ring.divisible(a, &g) && ring.divisible(b, &g));
                for c in &elems {
                    if ring.divisible(a, c) && ring.divisible(b, c) {
                        assert!(ring.divisible(&g, c));
                    }
                }
            }
        }

        // A principal quotient has exactly N(modulus) residue classes.
        // The sample contains every class: reduced representatives have norm
        // < N(modulus), and these moduli have coordinates at most one.
        for modulus in elements(1) {
            if ring.is_zero(&modulus) {
                continue;
            }
            let quotient = QuotientRing::new(ring.clone(), modulus.clone());
            let residues: BTreeSet<_> = elements(3).iter().map(|a| ring.rem(a, &modulus)).collect();
            assert_eq!(BigInt::from(residues.len()), norm(&modulus, t));
            for a in &residues {
                assert!(quotient.contains(a));
                let expected = residues
                    .iter()
                    .find(|b| quotient.mul(a, b) == quotient.one());
                assert_eq!(quotient.try_inv(a).as_ref(), expected);
                let solution = ring.solve_congruence(a, &ring.one(), &modulus);
                assert_eq!(solution.is_some(), expected.is_some());
                if let Some((r, period)) = solution {
                    let reduced = ring.rem(&r, &modulus);
                    assert_eq!(quotient.mul(a, &reduced), quotient.one());
                    assert!(ring.associates(&period, &modulus));
                }
            }
        }
    }

    #[test]
    fn gaussian_euclidean_domain_exhaustive() {
        euclidean_properties(ZZI.clone(), 0, 4);
    }

    #[test]
    fn eisenstein_euclidean_domain_exhaustive() {
        euclidean_properties(ZZW.clone(), -1, 6);
    }

    #[test]
    fn unbounded_coefficients() {
        fn check<P: QuadraticPolicy>(algebra: QuadraticAlgebra<Integers, P>)
        where
            QuadraticAlgebra<Integers, P>: QuadraticInteger<Elem = Elem>,
        {
            let scale = BigInt::from(1) << 256;
            for a in elements(1) {
                for b in elements(1) {
                    if algebra.is_zero(&b) {
                        continue;
                    }
                    let large = (&a.0 * &scale, &a.1 * &scale);
                    let product = algebra.mul(&large, &b);
                    assert_eq!(
                        algebra.integer_quo_rem(&product, &b),
                        (large, algebra.zero())
                    );
                }
            }
        }
        check(ZZI.clone());
        check(ZZW.clone());
    }

    fn compare_checked<A, P>(base: A, policy: P)
    where
        A: IntegerDomain,
        P: QuadraticPolicy,
        QuadraticAlgebra<A, P>: QuadraticInteger<Elem = (A::Elem, A::Elem)>,
        QuadraticAlgebra<Integers, P>: QuadraticInteger<Elem = Elem>,
    {
        use num::ToPrimitive;

        let ring = QuadraticAlgebra::with_policy(base, policy.clone());
        let reference = QuadraticAlgebra::with_policy(ZZ, policy);
        let convert = |elem: &Elem| {
            (
                ring.base.int(elem.0.to_isize().unwrap()),
                ring.base.int(elem.1.to_isize().unwrap()),
            )
        };
        // Keep intermediate norms representable even in i8.
        for a in elements(1) {
            let ca = convert(&a);
            assert!(ring.equals(&ring.conjugate(&ca), &convert(&reference.conjugate(&a))));
            assert!(ring.base.equals(
                &ring.norm(&ca),
                &ring.base.int(reference.norm(&a).to_isize().unwrap())
            ));
            assert!(ring.equals(
                &ring.associate_repr(&ca),
                &convert(&reference.associate_repr(&a))
            ));
            for b in elements(1) {
                let cb = convert(&b);
                assert!(ring.equals(&ring.mul(&ca, &cb), &convert(&reference.mul(&a, &b))));
                if !reference.is_zero(&b) {
                    let (q, r) = ring.quo_rem(&ca, &cb);
                    let (rq, rr) = reference.quo_rem(&a, &b);
                    assert!(ring.equals(&q, &convert(&rq)));
                    assert!(ring.equals(&r, &convert(&rr)));
                }
                let (g, x, y) = ring.normalized_extended_gcd(&ca, &cb);
                assert!(ring.equals(&ring.add(&ring.mul(&ca, &x), &ring.mul(&cb, &y)), &g));
                assert!(ring.equals(
                    &g,
                    &convert(&reference.associate_repr(&reference.gcd(&a, &b)))
                ));
            }
        }
    }

    #[test]
    fn checked_integer_specializations() {
        compare_checked(I8, Imaginary);
        compare_checked(I16, Imaginary);
        compare_checked(I32, Imaginary);
        compare_checked(I64, Imaginary);
        compare_checked(I8, Eisenstein);
        compare_checked(I16, Eisenstein);
        compare_checked(I32, Eisenstein);
        compare_checked(I64, Eisenstein);
    }

    #[test]
    fn policy_coefficients_are_cached() {
        use std::cell::Cell;
        use std::rc::Rc;

        #[derive(Clone)]
        struct Counted(Rc<Cell<usize>>);
        impl QuadraticPolicy for Counted {
            fn t<A: CommutativeRing>(&self, base: &A) -> A::Elem {
                self.0.set(self.0.get() + 1);
                base.zero()
            }
            fn u<A: CommutativeRing>(&self, base: &A) -> A::Elem {
                self.0.set(self.0.get() + 1);
                base.int(-1)
            }
        }
        let calls = Rc::new(Cell::new(0));
        let ring = QuadraticAlgebra::with_policy(I32, Counted(calls.clone()));
        for a in -3..=3 {
            for b in -3..=3 {
                let elem = (a, b);
                assert_eq!(
                    ring.mul(&elem, &ring.conjugate(&elem)),
                    ring.constant(ring.norm(&elem))
                );
            }
        }
        assert_eq!(calls.get(), 2);
    }

    #[test]
    fn imaginary_policy_over_different_bases() {
        let rational = ComplexNumbers::new(QQ);
        let approximate = ComplexNumbers::new(F64);
        let polynomial = QuadraticAlgebra::with_policy(PolynomialAlgebra::new(QQ), Imaginary);
        for a in -3..=3 {
            for b in -3..=3 {
                let elem = (QQ.int(a), QQ.int(b));
                let approx = (a as f64, b as f64);
                assert_eq!(rational.norm(&elem), QQ.int(a * a + b * b));
                assert_eq!(approximate.norm(&approx), (a * a + b * b) as f64);
                let polynomials = (vec![QQ.int(a), QQ.one()], vec![QQ.int(b), QQ.one()]);
                assert_eq!(
                    polynomial.mul(&polynomials, &polynomial.conjugate(&polynomials)),
                    polynomial.constant(polynomial.norm(&polynomials))
                );
            }
        }
        // Coefficients must be created using the actual runtime modulus,
        // including the trivial ring where minus one is represented by zero.
        for n in 1..=5 {
            let ring = QuadraticAlgebra::with_policy(QuotientRing::new(I32, n), Imaginary);
            assert_eq!(*ring.u(), (-1i32).rem_euclid(n));
        }
    }
}
