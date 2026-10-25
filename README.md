Abstract Algebra for Rust
=========================
[![Build Status](https://travis-ci.com/mmaroti/abstalg-rs.svg?branch=master)](https://app.travis-ci.com/github/mmaroti/abstalg-rs)
[![Crate](https://img.shields.io/crates/v/abstalg)](https://crates.io/crates/abstalg)
[![Documentation](https://docs.rs/abstalg/badge.svg)](https://docs.rs/abstalg)
[![GitHub](https://img.shields.io/github/license/mmaroti/abstalg-rs)](LICENSE)

This is a crate for doing abstract algebraic calculations in Rust. Unlike other
implementations, the elements do not know which algebraic structure they
belong to, so all operations are performed through algebraic objects.
For example, when calculating within the ring of integers modulo 6, the
elements are still primitive `i32` values, and only the quotient ring stores the
value 6. This allows many such elements to be stored in polynomials or matrices
efficiently, since this common value needs to be stored only once in the algebra.
Another benefit is that matrices are stored as simple vectors, and only the
matrix algebra needs to know the shape of the matrix.

All finite prime fields can be constructed from the ring of integers by
taking the quotient ring by a prime number. The two-element field can also
be used directly on the set of `bool` values. All finite fields can be constructed
by forming the ring of polynomials over their prime field and then taking
the quotient ring by an irreducible polynomial. All finite Boolean algebras
can be constructed as direct powers of the two-element Boolean algebra.
The divisibility order (on the set of associate classes) with distributive
lattice operations can be constructed for Euclidean domains, such as the
ring of integers and the ring of polynomials over a field. The ring of
square matrices can be formed over a field. The general linear group of
invertible matrices and the special linear group of matrices of unit
determinant can be formed over any field.
