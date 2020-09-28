// Copyright (C) 2020 Miklos Maroti
// Licensed under the MIT license (see LICENSE)

mod traits;
pub use traits::{Domain, EuclideanDomain, Field, UnitaryRing};

mod integers;
pub use integers::Integers;

mod checked_ints;
pub use checked_ints::CheckedInts;

mod modular_ints;
pub use modular_ints::ModularInts;

mod approx_floats;
pub use approx_floats::ApproxFloats;

mod quotient_ring;
pub use quotient_ring::QuotientRing;

mod quotient_field;
pub use quotient_field::QuotientField;
