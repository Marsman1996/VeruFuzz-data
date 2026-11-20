//! faest 0.3.0 -- Verus transcription of src/fields/mod.rs, batch FA2.
//!
//! Upstream: fields/mod.rs (170 lines, pin 9ccc68c0) declares the field
//! abstraction traits: Field (:41-74), BaseField (:76-81), Double
//! (:85-93), Square (:95-101) with three blanket implementations over
//! hybrid-array Array (:103-139), and ExtensionField (:141-170). The
//! implementations for the small fields live in small_fields.rs (this
//! directory); the large-field impls are FA3 scope.
//!
//! Upstream doc lines re-erected as obligations or record notes:
//!   - Field (fields/mod.rs:43-44): "The implementation in general does
//!     not require field elements to be inverted. As such, no function to
//!     invert elements is provided." -> record note: no inverse face
//!     exists anywhere downstream of the Field trait in this crate's
//!     transcription scope.
//!   - BaseField (:78-79): "For security, FAEST requires the extension
//!     field to have 3x the length of the base field." -> a const-level
//!     obligation the FA3 extension-field faces will pin (Length ==
//!     Prod<BaseField::Length, U3>).
//!
//! Representation lowerings (trust boundary, per inventory section 4):
//!   - hybrid_array::Array<F, L> and typenum ArraySize/Mul/Prod are the
//!     trusted representation: sizes are tracked as the concrete [u8; N]
//!     of the lowered type (FA1 convention). ArraySize-associated type
//!     algebra does not enter Verus; GF64::Length = U8 is recorded at
//!     the concrete [u8; 8] face gf64_as_bytes.
//!   - std::ops marker bounds (Add/Sub/Neg/Mul/...) on the traits lower
//!     to the named exec faces of small_fields.rs; the trait shape below
//!     records the upstream contract, the exec faces carry the proof.

use vstd::prelude::*;
use vstd::seq::Seq;

// Origin Rust (fields/mod.rs:14-16): pub(crate) mod large_fields;
// pub(crate) mod large_fields_constants; pub(crate) mod small_fields;
// large_fields mounts with FA3 (large_fields_constants' payloads are
// transcribed as const faces inside large_fields.rs); this tree opens
// the module tree pub for the harness #[path] mount (lib.rs
// convention).
pub mod large_fields;
pub mod small_fields;

// Sibling faces this module fronts (representation-lowered impls).
use small_fields::{byte64, gf8_mul_spec, gf64_mul_spec};

verus! {

// ===========================================================================
// Square (upstream fields/mod.rs:95-101).
// Origin Rust:
//     /// Square a field element
//     pub(crate) trait Square {
//         /// Output type
//         type Output;
//         /// Square an element
//         fn square(self) -> Self::Output; }
// ===========================================================================

/// Output-port face of the upstream Square trait: SQUARED produces the
/// element's square in the same field. The two small-field faces are
/// gf8_square / gf64_square (small_fields.rs twin); the generically
/// parameterized Output of upstream (Self::Output) stays concrete here
/// because both small-field instantiations are Self::Output = Self.
pub open spec fn squared64(v: u64) -> u64 {
    gf64_mul_spec(v, v)
}

pub open spec fn squared8(v: u8) -> u8 {
    gf8_mul_spec(v, v)
}

// ===========================================================================
// Field / BaseField / Double / ExtensionField (upstream fields/mod.rs).
// The upstream contracts are recorded as spec faces over the lowered
// machine representation; the trait syntax itself does not survive the
// typenum/ArraySize trust boundary above.
// ===========================================================================

/// Field::ZERO for GF64 (upstream small_fields.rs:287, `const ZERO: Self
/// = Self(0)`), value face over the lowered representation.
pub const FIELD64_ZERO: u64 = 0;
/// Field::ONE for GF64 (upstream small_fields.rs:288, `const ONE: Self
/// = Self(1)`), value face.
pub const FIELD64_ONE: u64 = 1;
/// Field::ZERO for GF8. Upstream defines Field only for GF64 with
/// constants ZERO/ONE derived from the Default/T::ZERO machinery of the
/// trait (`const ZERO: Self = Self(0)`), so the GF8 zero/one faces below
/// are a semantics-preserved projection, not a literal upstream entry
/// (no impl Field for GF8 exists upstream; GF8's ZERO comes from
/// GaloisFieldHelper<u8>::ZERO where it is used).
pub const FIELD8_ZERO: u8 = 0;
pub const FIELD8_ONE: u8 = 1;

/// Field::as_bytes spec face for GF64 (upstream small_fields.rs:292):
/// the 8-byte little-endian representation (Seq view over the lowered
/// fixed array; gf64_as_bytes is the exec twin).
pub open spec fn field64_as_bytes_spec(v: u64) -> Seq<u8>
    recommends
        true,
{
    Seq::new(
        8,
        |j: int| (byte64(v, j) as u8) as u8,
    )
}

/// ExtensionField length relation, record face (upstream BaseField doc,
/// fields/mod.rs:78-79): "For security, FAEST requires the extension
/// field to have 3x the length of the base field." FA3 pins this at the
/// concrete byte lengths of the GF(2^128/192/256) extension faces.
pub const EXTENSION_LENGTH_FACTOR: usize = 3;

// Double (upstream fields/mod.rs:83-93): the doc distinguishes doubling
// from self-addition ("This operation is not equivalent to `self +
// self` but corresponds to a the multiplication with the element
// representing `2`"). No small-field impl upstream (large_fields
// provide it); GF(2^k) doubling lowers to the field multiply by the
// orbit element x (gf*_xtime of Field::ONE) -- recorded for FA3.

} // verus!
