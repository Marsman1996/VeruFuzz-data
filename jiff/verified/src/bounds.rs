//! jiff-core bounds.rs -- Verus transcription of the bounded-integer
//! foundation (code/crates/jiff-core/src/bounds.rs, pin 627c7358).
//!
//! Upstream doc (bounds.rs:1-16), module header:
//!   Defines boundary types and their corresponding error values.
//!   The main trait in this module is `Bounds`. It is implemented by each
//!   of several boundary types describing a range of contiguous values
//!   used by Jiff. For example, [`Year`] corresponds to the range of
//!   support calendar year values.
//!   Each range type has concrete methods defined on it that simply
//!   forward to its corresponding method on `Bounds`. For example,
//!   [`Year::check`] forwards to the default implementation of
//!   [`Bounds::check`]. These concrete wrappers exist to make calling the
//!   routines more ergonomic. For example, they don't require that the
//!   `Bounds` trait be in scope. Additionally, a [`Year::checkc`] concrete
//!   method is provide for use in `const` contexts. This is not available
//!   on the `Bounds` trait because generics are not yet supported (as of
//!   2026-02-13) in a `const` context.
//!
//! Materialization ledger (this file):
//! - Result<$ty, BoundsError> faces become Option<$ty>: Option::None is
//!   the upstream error value. Upstream doc (bounds.rs:809-815):
//!     The error type used by the trait implementations of `Bounds` in
//!     this crate.
//!     Callers can think of this as a single unifying error value that
//!     combines all implementations of `Bounds` in this crate.
//!     Internally, it's an enum with each variant corresponding to a
//!     single implementation of `Bounds`. Each variant has a field
//!     containing a zero-sized `RawBoundsError<B>`, where `B` is the type
//!     implementing `Bounds`.
//!   The error value carries only a zero-sized witness, so the bool face
//!   (Option::None) is semantically complete; error message text is not
//!   verified (Display/Debug/defmt are not transcribed).
//! - macro_rules! define_bounds! (bounds.rs:26-137) generates per-type
//!   boilerplate by template; its ~31 instantiations (bounds.rs:139-404)
//!   differ only in the (primitive, min, max) constants. Two
//!   representative instantiations are transcribed verbatim below
//!   (Month: i8, 1..=12; Year: i16, -9999..=9999) against a shared
//!   spec-only Interval model; the rest are the same template with
//!   different constants (spec fn iv_*).
//! - Upstream doc (bounds.rs:547-555), trait header:
//!     An interface for defining boundaries on integer values.
//!     An implementation of this trait defines a single contiguous range
//!     used inside of Jiff. For example, the allowed range of years is
//!     `-9999..=9999`.
//!     Each implementation defines its primitive representation, which is
//!     usally the smallest signed integer type that can hold the minimum
//!     and maximum values. This trait provides `check`, `checked_add` and
//!     `checked_mul` methods that callers likely do not need to
//!     override.
//!   The `Bounds` associated consts (WHAT/MIN/MAX, bounds.rs:642-650)
//!   travel as explicit min/max parameters; `check`/`check_self`
//!   semantics live in the const_check module, and the
//!   `Primitive` cast trait (bounds.rs:406-439) dissolves into direct
//!   casts (widening casts are value-preserving; narrowing casts are
//!   guarded by the interval tests -- the bit-vec BitBlock dissolution
//!   precedent).
//! - const fn (bounds.rs:86-103, 928-970, 981-1027, 1039-1126) has no
//!   verification support in this build and materializes as exec fn;
//!   `impl Into<i64>` parameters materialize as the direct i64 parameter.
//! - The quickcheck-only `arbitrary` helper (bounds.rs:110-118) and the
//!   Display/defmt error-text impls are out of the transcription surface.

use vstd::prelude::*;
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_mod_multiples_basic,
    lemma_mod_multiples_vanish, rust_div, rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_basics, lemma_mul_is_commutative, lemma_mul_is_distributive_add,
    lemma_mul_is_distributive_add_other_way, lemma_mul_unary_negation,
};

verus! {

// ===========================================================================
// spec model: closed bounded interval (spec-only, never constructed in
// exec code; stands for the upstream Bounds MIN/MAX associated consts)
// ===========================================================================

pub struct Interval {
    pub min: int,
    pub max: int,
}

impl Interval {
    /// point membership of the closed interval
    pub open spec fn contains(self, n: int) -> bool {
        self.min <= n <= self.max
    }

    /// number of representable values (upstream: $name::LEN =
    /// MAX as i128 - MIN as i128 + 1, bounds.rs:71)
    pub open spec fn len(self) -> int {
        self.max - self.min + 1
    }
}

/// Month interval (bounds.rs:233-234): 1..=12.
pub open spec fn month_iv() -> Interval {
    Interval { min: 1, max: 12 }
}

/// Year interval (bounds.rs:398-399): -9999..=9999.
pub open spec fn year_iv() -> Interval {
    Interval { min: -9999, max: 9999 }
}

// ===========================================================================
// define_bounds! template instances (bounds.rs:26-137, 139-404).
// Month and Year are the representative transcriptions; every other
// generated type is this same template with different interval constants
// (e.g. Hour 0..=23 at bounds.rs:217, Day 1..=31 at bounds.rs:161,
// UnixEpochSeconds at bounds.rs:379-385).
// ===========================================================================

/// Origin Rust: #[allow(missing_debug_implementations)]
///     #[allow(missing_docs)] #[derive(Eq, PartialEq)] pub struct $name(());
///     (bounds.rs:47-50, instantiated for Month at bounds.rs:234)
/// Upstream doc (bounds.rs:233):
///   The supported range of month values.
/// The unit struct only brands the constants; MIN=1, MAX=12, LEN=12
/// (bounds.rs:69-71) live in month_iv().
pub struct Month {
    _priv: (),
}

impl Month {
    /// Origin Rust: #[inline(always)] pub fn check(n: impl Into<i64>)
    ///     -> Result<$ty, BoundsError> { <$name as Bounds>::check(n) }
    ///     (bounds.rs:80-83, Month instance)
    /// Upstream doc (bounds.rs:671-677), the Bounds::check default it
    /// forwards to:
    ///   Converts the 64-bit integer provided into the primitive
    ///   representation of these bounds.
    ///   # Errors
    ///   This returns an error if the given integer does not fit in the
    ///   bounds prescribed by this trait implementation.
    /// Err materializes as Option::None (witness-only error face).
    pub exec fn check(n: i64) -> (r: Option<i8>)
        ensures
            match r {
                Option::Some(v) => v as int == n as int
                    && month_iv().contains(n as int),
                Option::None => !month_iv().contains(n as int),
            },
    {
        if !(1i64 <= n && n <= 12i64) {
            Option::None
        } else {
            Option::Some(n as i8)
        }
    }

    /// Origin Rust: #[inline(always)] pub const fn checkc(n: i64)
    ///     -> Result<$ty, BoundsError> (bounds.rs:86-93, Month instance;
    ///     const fn materializes as exec fn)
    /// (BoundsErrorKind wrapping drops out of the Option error face.)
    pub exec fn checkc(n: i64) -> (r: Option<i8>)
        ensures
            match r {
                Option::Some(v) => v as int == n as int
                    && month_iv().contains(n as int),
                Option::None => !month_iv().contains(n as int),
            },
    {
        const_check::i8(1, 12, n)
    }

    /// Origin Rust: #[inline(always)] pub const fn checked_add(n1: $ty, n2: $ty)
    ///     -> Result<$ty, BoundsError> (bounds.rs:96-103, Month instance)
    /// Upstream doc (bounds.rs:702-708), the checked-add contract:
    ///   Performs checked addition using this boundary type's primitive
    ///   representation.
    ///   # Errors
    ///   If the result exceeds the boundaries of the primitive type or of
    ///   the declared range for this type, then an error is returned.
    pub exec fn checked_add(n1: i8, n2: i8) -> (r: Option<i8>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) + (n2 as int)
                    && month_iv().contains((n1 as int) + (n2 as int)),
                Option::None => !month_iv().contains(
                    (n1 as int) + (n2 as int),
                ),
            },
    {
        const_checked_add::i8(1, 12, n1, n2)
    }

    /// Origin Rust: #[inline(always)] pub fn checked_mul(n1: $ty, n2: $ty)
    ///     -> Result<$ty, BoundsError> { <$name as Bounds>::checked_mul(n1, n2) }
    ///     (bounds.rs:105-108, Month instance)
    /// Upstream doc (bounds.rs:717-723), the checked-mul contract:
    ///   Performs checked multiplication using this boundary type's
    ///   primitive representation.
    ///   # Errors
    ///   If the result exceeds the boundaries of the primitive type or of
    ///   the declared range for this type, then an error is returned.
    pub exec fn checked_mul(n1: i8, n2: i8) -> (r: Option<i8>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) * (n2 as int)
                    && month_iv().contains((n1 as int) * (n2 as int)),
                Option::None => !month_iv().contains(
                    (n1 as int) * (n2 as int),
                ),
            },
    {
        checked_mul::i8(1, 12, n1, n2)
    }
}

/// Origin Rust: #[allow(missing_debug_implementations)]
///     #[allow(missing_docs)] #[derive(Eq, PartialEq)] pub struct $name(());
///     (bounds.rs:47-50, instantiated for Year at bounds.rs:399)
/// Upstream doc (bounds.rs:398):
///   The range of years supported.
/// MIN=-9999, MAX=9999, LEN=19999 (bounds.rs:69-71) live in year_iv().
pub struct Year {
    _priv: (),
}

impl Year {
    /// Origin Rust: #[inline(always)] pub fn check(n: impl Into<i64>)
    ///     -> Result<$ty, BoundsError> { <$name as Bounds>::check(n) }
    ///     (bounds.rs:80-83, Year instance)
    /// Upstream doc (bounds.rs:671-677), the Bounds::check default it
    /// forwards to:
    ///   Converts the 64-bit integer provided into the primitive
    ///   representation of these bounds.
    ///   # Errors
    ///   This returns an error if the given integer does not fit in the
    ///   bounds prescribed by this trait implementation.
    pub exec fn check(n: i64) -> (r: Option<i16>)
        ensures
            match r {
                Option::Some(v) => v as int == n as int
                    && year_iv().contains(n as int),
                Option::None => !year_iv().contains(n as int),
            },
    {
        if !(-9999i64 <= n && n <= 9999i64) {
            Option::None
        } else {
            Option::Some(n as i16)
        }
    }

    /// Origin Rust: #[inline(always)] pub const fn checkc(n: i64)
    ///     -> Result<$ty, BoundsError> (bounds.rs:86-93, Year instance)
    pub exec fn checkc(n: i64) -> (r: Option<i16>)
        ensures
            match r {
                Option::Some(v) => v as int == n as int
                    && year_iv().contains(n as int),
                Option::None => !year_iv().contains(n as int),
            },
    {
        const_check::i16(-9999, 9999, n)
    }

    /// Origin Rust: #[inline(always)] pub const fn checked_add(n1: $ty, n2: $ty)
    ///     -> Result<$ty, BoundsError> (bounds.rs:96-103, Year instance)
    /// Upstream doc (bounds.rs:702-708), the checked-add contract:
    ///   Performs checked addition using this boundary type's primitive
    ///   representation.
    ///   # Errors
    ///   If the result exceeds the boundaries of the primitive type or of
    ///   the declared range for this type, then an error is returned.
    pub exec fn checked_add(n1: i16, n2: i16) -> (r: Option<i16>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) + (n2 as int)
                    && year_iv().contains((n1 as int) + (n2 as int)),
                Option::None => !year_iv().contains(
                    (n1 as int) + (n2 as int),
                ),
            },
    {
        const_checked_add::i16(-9999, 9999, n1, n2)
    }

    /// Origin Rust: #[inline(always)] pub fn checked_mul(n1: $ty, n2: $ty)
    ///     -> Result<$ty, BoundsError> { <$name as Bounds>::checked_mul(n1, n2) }
    ///     (bounds.rs:105-108, Year instance)
    /// Upstream doc (bounds.rs:717-723), the checked-mul contract:
    ///   Performs checked multiplication using this boundary type's
    ///   primitive representation.
    ///   # Errors
    ///   If the result exceeds the boundaries of the primitive type or of
    ///   the declared range for this type, then an error is returned.
    pub exec fn checked_mul(n1: i16, n2: i16) -> (r: Option<i16>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) * (n2 as int)
                    && year_iv().contains((n1 as int) * (n2 as int)),
                Option::None => !year_iv().contains(
                    (n1 as int) * (n2 as int),
                ),
            },
    {
        checked_mul::i16(-9999, 9999, n1, n2)
    }
}

// ===========================================================================
// const_check (bounds.rs:920-971)
// ===========================================================================

/// Upstream doc (bounds.rs:920-923):
///   Provides routines usable in a `const` context for checking boundary
///   values.
///
///   These routines return a `RawBoundsError` and thus work with any type
///   that implements the `Bounds` trait.
/// Materialization: the upstream generic `B` contributes only MIN/MAX,
/// so they travel as explicit parameters; RawBoundsError folds into
/// Option::None, and const fn materializes as exec fn.
pub mod const_check {
    use super::*;

    /// Origin Rust: #[inline(always)] pub const fn i8<B>(n: i64)
    ///     -> Result<i8, RawBoundsError<B>> where B: Bounds<Primitive = i8>
    ///     (bounds.rs:928-937)
    pub exec fn i8(min: i8, max: i8, n: i64) -> (r: Option<i8>)
        ensures
            match r {
                Option::Some(v) => v as int == n as int
                    && min as int <= n as int
                    && n as int <= max as int,
                Option::None => !(min as int <= n as int && n as int <= max as int),
            },
    {
        if !((min as i64) <= n && n <= (max as i64)) {
            Option::None
        } else {
            Option::Some(n as i8)
        }
    }

    /// Origin Rust: #[inline(always)] pub const fn i16<B>(n: i64)
    ///     -> Result<i16, RawBoundsError<B>> where B: Bounds<Primitive = i16>
    ///     (bounds.rs:939-948)
    pub exec fn i16(min: i16, max: i16, n: i64) -> (r: Option<i16>)
        ensures
            match r {
                Option::Some(v) => v as int == n as int
                    && min as int <= n as int
                    && n as int <= max as int,
                Option::None => !(min as int <= n as int && n as int <= max as int),
            },
    {
        if !((min as i64) <= n && n <= (max as i64)) {
            Option::None
        } else {
            Option::Some(n as i16)
        }
    }

    /// Origin Rust: #[inline(always)] pub const fn i32<B>(n: i64)
    ///     -> Result<i32, RawBoundsError<B>> where B: Bounds<Primitive = i32>
    ///     (bounds.rs:950-959)
    pub exec fn i32(min: i32, max: i32, n: i64) -> (r: Option<i32>)
        ensures
            match r {
                Option::Some(v) => v as int == n as int
                    && min as int <= n as int
                    && n as int <= max as int,
                Option::None => !(min as int <= n as int && n as int <= max as int),
            },
    {
        if !((min as i64) <= n && n <= (max as i64)) {
            Option::None
        } else {
            Option::Some(n as i32)
        }
    }

    /// Origin Rust: #[inline(always)] pub const fn i64<B>(n: i64)
    ///     -> Result<i64, RawBoundsError<B>> where B: Bounds<Primitive = i64>
    ///     (bounds.rs:961-970)
    pub exec fn i64(min: i64, max: i64, n: i64) -> (r: Option<i64>)
        ensures
            match r {
                Option::Some(v) => v as int == n as int
                    && min as int <= n as int
                    && n as int <= max as int,
                Option::None => !(min as int <= n as int && n as int <= max as int),
            },
    {
        if !(min <= n && n <= max) {
            Option::None
        } else {
            Option::Some(n)
        }
    }
}

// ===========================================================================
// Bounds::checked_add / checked_mul trait defaults (bounds.rs:702-730)
// checked_add materializes through the same module as the const path
// (bounds.rs:973-1028) since both upstream bodies have identical
// semantics: machine checked arithmetic, then the bounds test of
// check_self (bounds.rs:695-700).
// ===========================================================================

/// Upstream doc (bounds.rs:973-976):
///   Provides routines usable in a `const` context for checked arithmetic.
///
///   These routines return a `RawBoundsError` and thus work with any type
///   that implements the `Bounds` trait.
pub mod const_checked_add {
    use super::*;

    /// Origin Rust: #[inline(always)] pub const fn i8<B>(n1: i8, n2: i8)
    ///     -> Result<i8, RawBoundsError<B>> where B: Bounds<Primitive = i8>
    ///     (bounds.rs:981-991)
    /// (Bounds::checked_add, bounds.rs:710-715, is the same semantics:
    /// checked machine add, then the bounds test.)
    pub exec fn i8(min: i8, max: i8, n1: i8, n2: i8) -> (r: Option<i8>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) + (n2 as int)
                    && min as int <= (n1 as int) + (n2 as int)
                    && (n1 as int) + (n2 as int) <= max as int,
                Option::None => (n1 as int) + (n2 as int) < min as int
                    || (n1 as int) + (n2 as int) > max as int,
            },
    {
        match n1.checked_add(n2) {
            Option::None => Option::None,
            Option::Some(s) => super::const_check::i8(min, max, s as i64),
        }
    }

    /// Origin Rust: #[inline(always)] pub const fn i16<B>(n1: i16, n2: i16)
    ///     -> Result<i16, RawBoundsError<B>> where B: Bounds<Primitive = i16>
    ///     (bounds.rs:993-1003)
    pub exec fn i16(min: i16, max: i16, n1: i16, n2: i16) -> (r: Option<i16>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) + (n2 as int)
                    && min as int <= (n1 as int) + (n2 as int)
                    && (n1 as int) + (n2 as int) <= max as int,
                Option::None => (n1 as int) + (n2 as int) < min as int
                    || (n1 as int) + (n2 as int) > max as int,
            },
    {
        match n1.checked_add(n2) {
            Option::None => Option::None,
            Option::Some(s) => super::const_check::i16(min, max, s as i64),
        }
    }

    /// Origin Rust: #[inline(always)] pub const fn i32<B>(n1: i32, n2: i32)
    ///     -> Result<i32, RawBoundsError<B>> where B: Bounds<Primitive = i32>
    ///     (bounds.rs:1005-1015)
    pub exec fn i32(min: i32, max: i32, n1: i32, n2: i32) -> (r: Option<i32>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) + (n2 as int)
                    && min as int <= (n1 as int) + (n2 as int)
                    && (n1 as int) + (n2 as int) <= max as int,
                Option::None => (n1 as int) + (n2 as int) < min as int
                    || (n1 as int) + (n2 as int) > max as int,
            },
    {
        match n1.checked_add(n2) {
            Option::None => Option::None,
            Option::Some(s) => super::const_check::i32(min, max, s as i64),
        }
    }

    /// Origin Rust: #[inline(always)] pub const fn i64<B>(n1: i64, n2: i64)
    ///     -> Result<i64, RawBoundsError<B>> where B: Bounds<Primitive = i64>
    ///     (bounds.rs:1017-1027)
    pub exec fn i64(min: i64, max: i64, n1: i64, n2: i64) -> (r: Option<i64>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) + (n2 as int)
                    && min as int <= (n1 as int) + (n2 as int)
                    && (n1 as int) + (n2 as int) <= max as int,
                Option::None => (n1 as int) + (n2 as int) < min as int
                    || (n1 as int) + (n2 as int) > max as int,
            },
    {
        match n1.checked_add(n2) {
            Option::None => Option::None,
            Option::Some(s) => super::const_check::i64(min, max, s),
        }
    }
}

// ===========================================================================
// Bounds::checked_mul (bounds.rs:717-730) materialized per width
// ===========================================================================

/// Upstream doc (bounds.rs:717-723):
///   Performs checked multiplication using this boundary type's
///   primitive representation.
///
///   # Errors
///
///   If the result exceeds the boundaries of the primitive type or of the
///   declared range for this type, then an error is returned.
/// Materialization: the trait default body Self::check_self(
/// n1.checked_mul(n2).ok_or_else(Self::error)?) (bounds.rs:729) becomes
/// the width-indexed free functions with explicit min/max bounds; the
/// check_self test (bounds.rs:695-700) inlines as the domain test.
pub mod checked_mul {
    use super::*;

    /// Origin Rust: #[inline(always)] fn checked_mul(
    ///         n1: Self::Primitive, n2: Self::Primitive)
    ///     -> Result<Self::Primitive, Self::Error> (bounds.rs:725-730),
    ///     i8 width
    pub exec fn i8(min: i8, max: i8, n1: i8, n2: i8) -> (r: Option<i8>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) * (n2 as int)
                    && min as int <= (n1 as int) * (n2 as int)
                    && (n1 as int) * (n2 as int) <= max as int,
                Option::None => (n1 as int) * (n2 as int) < min as int
                    || (n1 as int) * (n2 as int) > max as int,
            },
    {
        match n1.checked_mul(n2) {
            Option::None => Option::None,
            Option::Some(p) => {
                if min <= p && p <= max {
                    Option::Some(p)
                } else {
                    Option::None
                }
            }
        }
    }

    /// (bounds.rs:725-730), i16 width
    pub exec fn i16(min: i16, max: i16, n1: i16, n2: i16) -> (r: Option<i16>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) * (n2 as int)
                    && min as int <= (n1 as int) * (n2 as int)
                    && (n1 as int) * (n2 as int) <= max as int,
                Option::None => (n1 as int) * (n2 as int) < min as int
                    || (n1 as int) * (n2 as int) > max as int,
            },
    {
        match n1.checked_mul(n2) {
            Option::None => Option::None,
            Option::Some(p) => {
                if min <= p && p <= max {
                    Option::Some(p)
                } else {
                    Option::None
                }
            }
        }
    }

    /// (bounds.rs:725-730), i32 width
    pub exec fn i32(min: i32, max: i32, n1: i32, n2: i32) -> (r: Option<i32>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) * (n2 as int)
                    && min as int <= (n1 as int) * (n2 as int)
                    && (n1 as int) * (n2 as int) <= max as int,
                Option::None => (n1 as int) * (n2 as int) < min as int
                    || (n1 as int) * (n2 as int) > max as int,
            },
    {
        match n1.checked_mul(n2) {
            Option::None => Option::None,
            Option::Some(p) => {
                if min <= p && p <= max {
                    Option::Some(p)
                } else {
                    Option::None
                }
            }
        }
    }

    /// (bounds.rs:725-730), i64 width
    pub exec fn i64(min: i64, max: i64, n1: i64, n2: i64) -> (r: Option<i64>)
        ensures
            match r {
                Option::Some(v) => v as int == (n1 as int) * (n2 as int)
                    && min as int <= (n1 as int) * (n2 as int)
                    && (n1 as int) * (n2 as int) <= max as int,
                Option::None => (n1 as int) * (n2 as int) < min as int
                    || (n1 as int) * (n2 as int) > max as int,
            },
    {
        match n1.checked_mul(n2) {
            Option::None => Option::None,
            Option::Some(p) => {
                if min <= p && p <= max {
                    Option::Some(p)
                } else {
                    Option::None
                }
            }
        }
    }
}

// ===========================================================================
// Sign (bounds.rs:1030-1127)
// Neg, the core::ops::Mul family and the From<iX>/From<f64> faces are
// outside this batch's listed surface; from_ordinals is materialized at
// the i64 and i16 widths (the crate's comparison faces; other widths are
// the same template).
// ===========================================================================

/// Origin Rust: pub enum Sign { #[default] Zero = 0, Positive = 1,
///     Negative = -1 } with #[repr(i8)] (bounds.rs:1034-1044)
/// Upstream doc (bounds.rs:1030-1033):
///   A representation of a numeric sign.
///
///   Its `Display` impl emits the ASCII minus sign, `-`, when this is
///   negative. It emits the empty string in all other cases.
/// The i8 discriminants are layout-only upstream; the value embodiment is
/// carried by the as_i8..as_i128 projections transcribed below.
/// Contracts use verus datatype variant tests (`s is Zero`): a derived
/// PartialEq would be an opaque trait impl with no usable spec here.
pub enum Sign {
    Zero,
    Positive,
    Negative,
}

impl Sign {
    /// Origin Rust: #[inline] pub const fn is_zero(self) -> bool
    ///     { matches!(self, Sign::Zero) } (bounds.rs:1049-1051)
    /// Upstream doc (bounds.rs:1047):
    ///   Returns true when the sign is `Sign::Zero`.
    pub exec fn is_zero(s: Sign) -> (r: bool)
        ensures
            r <==> s is Zero,
    {
        match s {
            Sign::Zero => true,
            Sign::Positive => false,
            Sign::Negative => false,
        }
    }

    /// Origin Rust: #[inline] pub const fn is_positive(self) -> bool
    ///     { matches!(self, Sign::Positive) } (bounds.rs:1055-1057)
    /// Upstream doc (bounds.rs:1053):
    ///   Returns true when the sign is `Sign::Positive`.
    pub exec fn is_positive(s: Sign) -> (r: bool)
        ensures
            r <==> s is Positive,
    {
        match s {
            Sign::Zero => false,
            Sign::Positive => true,
            Sign::Negative => false,
        }
    }

    /// Origin Rust: #[inline] pub const fn is_negative(self) -> bool
    ///     { matches!(self, Sign::Negative) } (bounds.rs:1061-1063)
    /// Upstream doc (bounds.rs:1059):
    ///   Returns true when the sign is `Sign::Negative`.
    pub exec fn is_negative(s: Sign) -> (r: bool)
        ensures
            r <==> s is Negative,
    {
        match s {
            Sign::Zero => false,
            Sign::Positive => false,
            Sign::Negative => true,
        }
    }

    /// Origin Rust: #[inline] pub const fn signum(self) -> i8
    ///     { self.as_i8() } (bounds.rs:1069-1071)
    /// Upstream doc (bounds.rs:1065-1068):
    ///   Returns the sign as an `i8`.
    ///
    ///   This is guaranteed to be `-1`, `0` or `1`.
    pub exec fn signum(s: Sign) -> (r: i8)
        ensures
            r == -1 || r == 0 || r == 1,
            s is Zero ==> r == 0,
            s is Positive ==> r == 1,
            s is Negative ==> r == -1,
    {
        Self::as_i8(s)
    }

    /// Origin Rust: #[inline] pub const fn as_i8(self) -> i8
    ///     { self as i8 } (bounds.rs:1077-1079)
    /// Upstream doc (bounds.rs:1073-1076):
    ///   Returns the sign as an `i8`.
    ///
    ///   This is guaranteed to be `-1`, `0` or `1`.
    pub exec fn as_i8(s: Sign) -> (r: i8)
        ensures
            s is Zero ==> r == 0,
            s is Positive ==> r == 1,
            s is Negative ==> r == -1,
    {
        match s {
            Sign::Zero => 0,
            Sign::Positive => 1,
            Sign::Negative => -1,
        }
    }

    /// Origin Rust: #[inline] pub const fn as_i16(self) -> i16
    ///     { self as i16 } (bounds.rs:1085-1087)
    /// Upstream doc (bounds.rs:1081-1084):
    ///   Returns the sign as an `i16`.
    ///
    ///   This is guaranteed to be `-1`, `0` or `1`.
    pub exec fn as_i16(s: Sign) -> (r: i16)
        ensures
            s is Zero ==> r == 0,
            s is Positive ==> r == 1,
            s is Negative ==> r == -1,
    {
        match s {
            Sign::Zero => 0,
            Sign::Positive => 1,
            Sign::Negative => -1,
        }
    }

    /// Origin Rust: #[inline] pub const fn as_i32(self) -> i32
    ///     { self as i32 } (bounds.rs:1093-1095)
    /// Upstream doc (bounds.rs:1089-1092):
    ///   Returns the sign as an `i32`.
    ///
    ///   This is guaranteed to be `-1`, `0` or `1`.
    pub exec fn as_i32(s: Sign) -> (r: i32)
        ensures
            s is Zero ==> r == 0,
            s is Positive ==> r == 1,
            s is Negative ==> r == -1,
    {
        match s {
            Sign::Zero => 0,
            Sign::Positive => 1,
            Sign::Negative => -1,
        }
    }

    /// Origin Rust: #[inline] pub const fn as_i64(self) -> i64
    ///     { self as i64 } (bounds.rs:1101-1103)
    /// Upstream doc (bounds.rs:1097-1100):
    ///   Returns the sign as an `i64`.
    ///
    ///   This is guaranteed to be `-1`, `0` or `1`.
    pub exec fn as_i64(s: Sign) -> (r: i64)
        ensures
            s is Zero ==> r == 0,
            s is Positive ==> r == 1,
            s is Negative ==> r == -1,
    {
        match s {
            Sign::Zero => 0,
            Sign::Positive => 1,
            Sign::Negative => -1,
        }
    }

    /// Origin Rust: #[inline] pub const fn as_i128(self) -> i128
    ///     { self as i128 } (bounds.rs:1109-1111)
    /// Upstream doc (bounds.rs:1105-1108):
    ///   Returns the sign as an `i128`.
    ///
    ///   This is guaranteed to be `-1`, `0` or `1`.
    pub exec fn as_i128(s: Sign) -> (r: i128)
        ensures
            s is Zero ==> r == 0,
            s is Positive ==> r == 1,
            s is Negative ==> r == -1,
    {
        match s {
            Sign::Zero => 0,
            Sign::Positive => 1,
            Sign::Negative => -1,
        }
    }

    /// Origin Rust: #[inline] pub fn from_ordinals<T: Ord>(t1: T, t2: T) -> Sign
    ///     { match t1.cmp(&t2) { Less => Sign::Negative, Equal => Sign::Zero,
    ///     Greater => Sign::Positive } } (bounds.rs:1119-1126)
    /// Upstream doc (bounds.rs:1113-1117):
    ///   Returns a `Sign` as a result of comparing two values.
    ///
    ///   * When `t1 < t2`, returns `Sign::Negative`.
    ///   * When `t1 == t2`, returns `Sign::Zero`.
    ///   * When `t1 > t2`, returns `Sign::Positive`.
    /// Materialization at the i64 width (the crate's main comparison
    /// face); other widths are the same template.
    pub exec fn from_ordinals_i64(t1: i64, t2: i64) -> (r: Sign)
        ensures
            (r is Negative) <==> t1 < t2,
            (r is Zero) <==> t1 == t2,
            (r is Positive) <==> t1 > t2,
    {
        if t1 < t2 {
            Sign::Negative
        } else if t1 == t2 {
            Sign::Zero
        } else {
            Sign::Positive
        }
    }

    /// (bounds.rs:1119-1126), i16 width (the Year compare face)
    pub exec fn from_ordinals_i16(t1: i16, t2: i16) -> (r: Sign)
        ensures
            (r is Negative) <==> t1 < t2,
            (r is Zero) <==> t1 == t2,
            (r is Positive) <==> t1 > t2,
    {
        if t1 < t2 {
            Sign::Negative
        } else if t1 == t2 {
            Sign::Zero
        } else {
            Sign::Positive
        }
    }
}

// ===========================================================================
// next_multiple_of (bounds.rs:1333-1350)
// ===========================================================================

/// Origin Rust: const fn next_multiple_of(lhs: i64, rhs: i64) -> i64 {
///     if rhs == -1 { return lhs; }
///     let r = lhs % rhs;
///     let m = if (r > 0 && rhs < 0) || (r < 0 && rhs > 0) { r + rhs } else { r };
///     if m == 0 { lhs } else { lhs + (rhs - m) } } (bounds.rs:1337-1350)
/// Upstream doc (bounds.rs:1333-1336):
///   Computes the next multiple of `rhs` that is greater than or equal to
///   `lhs`.
///   Taken from:
///   https://github.com/rust-lang/rust/blob/eff958c59e8c07ba0515e164b825c9001b242294/library/core/src/num/int_macros.rs
/// The upstream caller passes rhs = SECS_PER_CIVIL_DAY > 0 and a small
/// positive lhs (the DeltaSeconds MAX derivation, bounds.rs:205-210), so
/// the transcription fixes rhs > 0 and a no-overflow headroom premise;
/// the rhs == -1 early return stays transcribed verbatim (dead under the
/// premise).
pub exec fn next_multiple_of(lhs: i64, rhs: i64) -> (r: i64)
    requires
        rhs > 0,
        lhs <= i64::MAX - rhs,
    ensures
        r as int >= lhs as int,
        (r as int) - (lhs as int) < (rhs as int),
        (r as int) % (rhs as int) == 0,
{
    if rhs == -1 {
        lhs
    } else {
        let r0 = lhs % rhs;
        proof {
            // link the machine remainder to its rust_rem spec face and
            // pin its range under rhs > 0 (proof fn lemma_rust_rem_range)
            assert((r0 as int) == rust_rem(lhs as int, rhs as int));
            assert((r0 as int) > -(rhs as int));
            assert((r0 as int) < (rhs as int));
            lemma_rust_div_rem_decompose(lhs as int, rhs as int);
        }
        let m = if (r0 > 0 && rhs < 0) || (r0 < 0 && rhs > 0) {
            r0 + rhs
        } else {
            r0
        };
        if m == 0 {
            proof {
                // m == 0 forces r0 == 0 (the r0 < 0 arm would give
                // r0 + rhs in (0, rhs)); then lhs is a multiple of rhs
                lemma_rust_div_rem_decompose(lhs as int, rhs as int);
                assert((r0 as int) == 0);
                assert(rust_rem(lhs as int, rhs as int) == 0);
                lemma_rust_rem_multiple_iff(lhs as int, rhs as int);
                assert((lhs as int) % (rhs as int) == 0);
            }
            lhs
        } else {
            let ret = lhs + (rhs - m);
            proof {
                // upper arm: m == r0 > 0, ret == (D+1) * rhs;
                // lower arm: m == r0 + rhs, ret == D * rhs
                let d: int = rust_div(lhs as int, rhs as int);
                if (r0 as int) > 0 {
                    assert((m as int) == (r0 as int));
                    assert((ret as int) == d * (rhs as int) + (rhs as int));
                    lemma_mul_is_commutative(d, rhs as int);
                    lemma_mul_basics(rhs as int);
                    lemma_mul_is_distributive_add(rhs as int, d, 1);
                    lemma_mul_is_commutative(d + 1, rhs as int);
                    assert((d + 1) * (rhs as int) == (rhs as int) * (d + 1));
                    assert((rhs as int) * (d + 1) == (rhs as int) * d + (rhs as int) * 1);
                    assert((rhs as int) * d == d * (rhs as int));
                    assert((rhs as int) * 1 == rhs as int);
                    assert((d + 1) * (rhs as int) == d * (rhs as int) + (rhs as int));
                    assert((ret as int) == (d + 1) * (rhs as int));
                    assert((rhs as int) * (d + 1) + 0 == (ret as int));
                    lemma_mod_multiples_vanish(d + 1, 0, rhs as int);
                    assert(((rhs as int) * (d + 1) + 0) % (rhs as int) == 0int % (rhs as int));
                    assert(0int % (rhs as int) == 0);
                } else {
                    assert((m as int) == (r0 as int) + (rhs as int));
                    assert((ret as int) == d * (rhs as int));
                    lemma_mod_multiples_vanish(d, 0, rhs as int);
                }
                assert((ret as int) % (rhs as int) == 0);
                assert((ret as int) >= (lhs as int));
            }
            ret
        }
    }
}

// ===========================================================================
// proof helpers (next_multiple_of; rust_rem is the remainder this build's
// exec % actually computes, so the closure facts go through trunc-division
// decomposition)
// ===========================================================================

/// Rust trunc-division decomposition for b > 0:
/// a == rust_div(a, b) * b + rust_rem(a, b).
proof fn lemma_rust_div_rem_decompose(a: int, b: int)
    requires
        b > 0,
    ensures
        a == rust_div(a, b) * b + rust_rem(a, b),
{
    if a == 0 {
        assert(rust_div(a, b) == 0);
        assert(rust_rem(a, b) == 0);
    } else if a > 0 {
        lemma_fundamental_div_mod(a, b);
        assert(rust_div(a, b) == a / b);
        assert(rust_rem(a, b) == a % b);
        assert(a == (a / b) * b + (a % b));
    } else {
        let n: int = -a;
        assert(a == 0 - n);
        lemma_fundamental_div_mod(n, b);
        assert(n == b * (n / b) + (n % b));
        let q: int = 0 - (n / b);
        let e: int = 0 - (n % b);
        assert(rust_div(a, b) == q);
        assert(rust_rem(a, b) == e);
        // product chain: q*b == -(b*(n/b)), then a == q*b + e is linear
        lemma_mul_is_commutative(n / b, b);
        lemma_mul_unary_negation(n / b, b);
        assert(q * b == 0 - (b * (n / b)));
        assert(a == q * b + e);
    }
}

/// rust_rem(a, b) == 0 iff b divides a, in Euclid-mod form.
proof fn lemma_rust_rem_multiple_iff(a: int, b: int)
    requires
        b > 0,
    ensures
        rust_rem(a, b) == 0 <==> (a % b) == 0,
{
    if a == 0 {
        assert(rust_rem(a, b) == 0);
        assert(a % b == 0);
    } else if a > 0 {
        assert(rust_rem(a, b) == a % b);
    } else {
        let n: int = -a;
        assert(a == 0 - n);
        let q: int = n / b;
        let e: int = n % b;
        lemma_fundamental_div_mod(n, b);
        assert(n == b * q + e);
        assert(0 <= e < b);
        // same product chain as lemma_rust_div_rem_decompose:
        // a == (-q)*b - e
        lemma_mul_unary_negation(q, b);
        assert(a == (-q) * b + (0 - e));
        if e == 0 {
            assert(a == (-q) * b);
            assert(rust_rem(a, b) == 0);
            lemma_mod_multiples_basic(-q, b);
            assert(((-q) * b) % b == 0);
            assert(a % b == 0);
        } else {
            let w: int = b - e;
            assert(0 < w < b);
            // (q+1)*b == q*b + b, then negate through unary negation
            lemma_mul_is_distributive_add_other_way(b, q, 1);
            lemma_mul_basics(b);
            assert((q + 1) * b == q * b + 1 * b);
            assert(1 * b == b);
            assert((q + 1) * b == q * b + b);
            lemma_mul_unary_negation(q + 1, b);
            assert((-(q + 1)) * b == 0 - ((q + 1) * b));
            assert((-(q + 1)) * b == (0 - q * b) - b);
            // a == (-q)*b - e (chain above); with w = b - e:
            // a == (-q)*b - e == (0 - q*b) - b + (b - e) == (-(q+1))*b + w
            assert(a == (0 - (q + 1)) * b + w);
            lemma_fundamental_div_mod_converse(a, b, 0 - (q + 1), w);
            assert(a % b == w);
            assert(rust_rem(a, b) == 0 - e);
        }
    }
}

} // verus!
