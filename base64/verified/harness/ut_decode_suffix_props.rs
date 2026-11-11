//! harness: the case-table lemmas of decode_suffix
//!   (mirroring the malleability / padding-mode cases of src/engine/tests.rs:1088-1230
//!    + the value domain of src/decode.rs:325 invalid_last_symbol_debug)
//!
//! Table pinning: decode_table is any table satisfying ValidDecodeTable; each case pins,
//! in requires, only the byte look-ups it touches (the whole table = a partial
//! difference set of STANDARD); the agreement with the real STANDARD table is witnessed
//! in full at runtime (out/verus-bugfinder/std_upstream_driver/, see bug-finder-summary).
//!
//! Run: verus database/base64/verified/harness/ut_decode_suffix_props.rs

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod b64;

use b64::decode::{DecodeError, DecodeSliceError};
use b64::engine::DecodePaddingMode;
use b64::engine::general_purpose::decode::{ValidDecodeTable, INVALID_VALUE};
use b64::engine::general_purpose::decode_suffix::decode_suffix;

verus! {

/// Helper: the "every referenced byte is legal (!= INVALID)" table description
pub open spec fn valid_morsels(t: Seq<u8>, bs: Seq<u8>) -> bool {
    forall|j: int| 0 <= j < bs.len() ==> t[(bs[j]) as int] < 64
}

/// UT decode_malleability_test_case_2_byte_suffix_valid_two_padding_symbols
/// (same shape as engine/tests.rs:1128): "AQ==" -> Ok, one output byte [0x01]
/// (pins = the real STANDARD look-ups: 'A'->0, 'Q'->16)
pub exec fn case_two_symbols_valid(
    s: &[u8],
    t: &[u8],
    out: &mut [u8],
) -> (b: bool)
    requires
        s@.len() == 4,
        s@[0] == 65, /* 'A' */
        s@[1] == 81, /* 'Q' */
        s@[2] == 61, /* '=' */
        s@[3] == 61,
        t@.len() == 256,
        ValidDecodeTable(t@),
        t@[65 as int] == 0, /* morsel('A') == 0 */
        t@[81 as int] == 16, /* morsel('Q') == 16 (canonical, low 4 bits zero) */
        out@.len() >= 1,
        out@.len() <= usize::MAX - 4,
{
    let r = decode_suffix(s, 0, out, 0, t, false, 61, DecodePaddingMode::RequireCanonical, Ghost(false));
    match r {
        Result::Ok(md) => (md.decoded_len == 1) && (out[0] == (0 * 4 + 16 / 16) as u8),
        Result::Err(_) => false,
    }
}

/// malleability 2-byte suffix short padding (engine/tests.rs:1139): "AB=D" ->
/// InvalidByte(first_pad=2)
pub exec fn case_two_symbols_short_pad(
    s: &[u8],
    t: &[u8],
    out: &mut [u8],
) -> (b: bool)
    requires
        s@.len() == 4,
        s@[0] == 65,
        s@[1] == 66,
        s@[2] == 61,
        s@[3] == 68, /* 'D' */
        t@.len() == 256,
        ValidDecodeTable(t@),
        t@[65 as int] == 0,
        t@[66 as int] == 1,
        out@.len() >= 1,
        out@.len() <= usize::MAX - 4,
{
    let r = decode_suffix(s, 0, out, 0, t, false, 61, DecodePaddingMode::RequireCanonical, Ghost(false));
    r == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(2, 61)))
}

/// malleability quad early padding (the engine/tests.rs:1088 area): "A===" ->
/// InvalidByte(1, '=') (positions 0/1 inside a quad admit no padding)
pub exec fn case_pad_too_early(
    s: &[u8],
    t: &[u8],
    out: &mut [u8],
) -> (b: bool)
    requires
        s@.len() == 4,
        s@[0] == 65,
        s@[1] == 61,
        s@[2] == 61,
        s@[3] == 61,
        t@.len() == 256,
        ValidDecodeTable(t@),
        t@[65 as int] == 0,
        out@.len() >= 1,
        out@.len() <= usize::MAX - 4,
{
    let r = decode_suffix(s, 0, out, 0, t, false, 61, DecodePaddingMode::RequireCanonical, Ghost(false));
    r == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidByte(1, 61)))
}

/// trailing-bits reachability (the engine/tests.rs:576 family + the allow config):
/// the low 4 bits of B=1 in "AB==" are nonzero => InvalidLastSymbol{offset:1,'B',1}
pub exec fn case_invalid_last_symbol(
    s: &[u8],
    t: &[u8],
    out: &mut [u8],
) -> (b: bool)
    requires
        s@.len() == 4,
        s@[0] == 65,
        s@[1] == 66,
        s@[2] == 61,
        s@[3] == 61,
        t@.len() == 256,
        ValidDecodeTable(t@),
        t@[65 as int] == 0,
        t@[66 as int] == 1,
        out@.len() >= 1,
        out@.len() <= usize::MAX - 4,
{
    let r = decode_suffix(s, 0, out, 0, t, false, 61, DecodePaddingMode::RequireCanonical, Ghost(false));
    r == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidLastSymbol {
        offset: 1,
        symbol: 66,
        symbol_value: 1,
    }))
}

/// decode_invalid_trailing_bits_ignored_when_configured (engine/tests.rs:803):
/// with allow=true the same input is Ok under both padding modes (the low 4 bits of B are ignored)
pub exec fn case_trailing_bits_allowed(
    s: &[u8],
    t: &[u8],
    out: &mut [u8],
) -> (b: bool)
    requires
        s@.len() == 4,
        s@[0] == 65,
        s@[1] == 66,
        s@[2] == 61,
        s@[3] == 61,
        t@.len() == 256,
        ValidDecodeTable(t@),
        t@[65 as int] == 0,
        t@[66 as int] == 1,
        out@.len() >= 1,
        out@.len() <= usize::MAX - 4,
{
    let r = decode_suffix(s, 0, out, 0, t, true, 61, DecodePaddingMode::RequireCanonical, Ghost(false));
    match r {
        Result::Ok(md) => (md.decoded_len == 1) && (out[0] == (0 * 4 + 1 / 16) as u8),
        Result::Err(_) => false,
    }
}

/// decode_pad_mode_requires_no_padding_rejects_any_padding
/// (engine/tests.rs:1205): "AB==" with RequireNone -> InvalidPadding
pub exec fn case_require_none_rejects(
    s: &[u8],
    t: &[u8],
    out: &mut [u8],
) -> (b: bool)
    requires
        s@.len() == 4,
        s@[0] == 65,
        s@[1] == 66,
        s@[2] == 61,
        s@[3] == 61,
        t@.len() == 256,
        ValidDecodeTable(t@),
        t@[65 as int] == 0,
        t@[66 as int] == 5, /* low 4 bits are 1: a path irrelevant to IgnoreLastSymbol */
        out@.len() >= 1,
        out@.len() <= usize::MAX - 4,
{
    let r = decode_suffix(s, 0, out, 0, t, false, 61, DecodePaddingMode::RequireNone, Ghost(false));
    r == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidPadding))
}

/// lone-symbol InvalidLength (the 1-symbol convenience domain after complete_quads_len):
/// a single trailing legal morsel (no padding) -> InvalidLength(1)
pub exec fn case_lone_symbol_invalid_length(
    s: &[u8],
    t: &[u8],
    out: &mut [u8],
) -> (b: bool)
    requires
        s@.len() == 1,
        s@[0] == 65,
        t@.len() == 256,
        ValidDecodeTable(t@),
        t@[65 as int] == 0,
        out@.len() >= 1,
        out@.len() <= usize::MAX - 4,
{
    let r = decode_suffix(s, 0, out, 0, t, false, 61, DecodePaddingMode::RequireCanonical, Ghost(false));
    r == Result::Err(DecodeSliceError::DecodeError(DecodeError::InvalidLength(1)))
}

/// output too small (the OutputSliceTooSmall exit retrieved via decode_slice in engine/tests.rs):
/// "AB==" without allow, Indifferent, empty out -> OutputSliceTooSmall
pub exec fn case_output_too_small(
    s: &[u8],
    t: &[u8],
    out: &mut [u8],
) -> (b: bool)
    requires
        s@.len() == 4,
        s@[0] == 65,
        s@[1] == 66,
        s@[2] == 61,
        s@[3] == 61,
        t@.len() == 256,
        ValidDecodeTable(t@),
        t@[65 as int] == 0,
        t@[66 as int] == 16, /* the spec value of 'Q': canonical, value 16 (low 4 bits of <<4 zero) */
        out@.len() == 0,
{
    let r = decode_suffix(s, 0, out, 0, t, false, 61, DecodePaddingMode::Indifferent, Ghost(false));
    r == Result::Err(DecodeSliceError::OutputSliceTooSmall)
}

} // verus!

fn main() {}
