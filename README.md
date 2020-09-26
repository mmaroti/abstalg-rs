Abstract Algebra for Rust
=========================
[![Build Status](https://travis-ci.com/mmaroti/abstalg-rs.svg?branch=master)](https://travis-ci.com/mmaroti/abstalg-rs)
[![Crate](https://img.shields.io/crates/v/abstalg)](https://crates.io/crates/abstalg)
[![Documentation](https://docs.rs/abstalg/badge.svg)](https://docs.rs/abstalg)
[![GitHub](https://img.shields.io/github/license/mmaroti/abstalg-rs)](LICENSE)

This is a crate for doing abstract algebraic calculations in Rust. Unlike other
implementations, the elements do not know to which algebraic structure they
belong to, so all operations are performed through the algebra objects. 
For example, calculating within the ring of modular arithmetic modulo 6 the
elements are still primitive i32 values. This allows putting many such 
elements into polynomials or matrices efficiently.
