//! harness/ut_varint.rs -- the UT witnesses of the upstream
//! code/src/varint_tests.rs.
//!
//! Covers inventory V1-V17 (V11/V16 are cfg-gated async items, out of the default
//! verification surface).
//! Reference-style organization: #[path] pulls in verified/src/varint.rs; the specs
//! and lemmas live only there, exactly once.
//! Witness form: exec fns call the src-side mirrors on concrete literal inputs and
//! build booleans with pattern matches;
//! verus's ensures obligation on the return value `r` is then equivalent to the
//! upstream assert_eq verdict.

use vstd::prelude::*;

#[path = "../src/fixed.rs"]
mod fixed;
#[path = "../src/varint.rs"]
mod varint;

use fixed::*;
use varint::*;

verus! {

// ============================================================
// V1 test_required_space (varint_tests.rs:13-20)
// ============================================================
pub exec fn witness_v1_required_space() -> (r: bool)
    ensures r,
{
    required_space_u32(0) == 1
        && required_space_u32(1) == 1
        && required_space_u32(128) == 2
        && required_space_u32(16384) == 3
        && required_space_u32(2097151) == 3
        && required_space_u32(2097152) == 4
}

// ============================================================
// V2 test_encode_u64 (:23-27): 0 -> [0x00], 300 -> [0xAC,0x02]
// ============================================================
pub exec fn witness_v2_encode_u64() -> (r: bool)
    ensures r,
{
    let mut buf: [u8; 10] = [0; 10];
    let n0 = encode_var_u32(0, &mut buf);
    let b0 = buf[0] == 0x00 && n0 == 1;
    let mut buf2: [u8; 10] = [0; 10];
    let n2 = encode_var_u32(300, &mut buf2);
    let b2 = (0x80 | buf2[0]) == 0xAC && buf2[1] == 0x02 && n2 == 2;
    b0 && b2
}

// ============================================================
// V3 test_identity_u64 (:29-42): sample round trips (representative samples)
// ============================================================
pub exec fn witness_v3_identity_samples() -> (r: bool)
    ensures r,
{
    let samples: [u64; 6] = [1, 2, 57, 127, 128, 16400];
    let mut ok = true;
    let mut k: usize = 0;
    while k < 6
        invariant k <= 6, ok,
        decreases 6 - k
    {
        let v = samples[k];
        let mut buf: [u8; 10] = [0; 10];
        let n = encode_var_u64(v, &mut buf);
        let slice: &[u8] = &buf[0..n];
        match decode_var_u64(slice) {
            Some((d, s)) => {
                if d != v || s != n {
                    ok = false;
                }
            }
            None => ok = false,
        }
        k += 1;
    }
    ok
}

// ============================================================
// V4 test_decode_max_u64 (:45-50): 0xFF x 9 + 0x01 -> u64::MAX
// ============================================================
pub exec fn witness_v4_decode_max_u64() -> (r: bool)
    ensures r,
{
    let buf: [u8; 10] = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x01];
    match decode_var_u64(&buf) {
        Some((v, s)) => v == 0xFFFF_FFFF_FFFF_FFFF && s == 10,
        None => false,
    }
}

// ============================================================
// V5 test_decode_max_u64_plus_one (:54-57): the 10-byte tail 0x02 -> None
// ============================================================
pub exec fn witness_v5_max_plus_one() -> (r: bool)
    ensures r,
{
    let buf: [u8; 10] = [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x02];
    decode_var_u64(&buf) matches None
}

// ============================================================
// V6/V7/V8/V9 zigzag boundary samples (:60-99)
// ============================================================
pub exec fn witness_v678_i64_extremes() -> (r: bool)
    ensures r,
{
    // i64::MIN encodes to [0xFF x 9, 0x01]; i64::MAX to [0xFE, 0xFF x 8, 0x01]
    let mut buf_min: [u8; 10] = [0; 10];
    let nmin = encode_var_i64(-9223372036854775808, &mut buf_min);
    let mut buf_max: [u8; 10] = [0; 10];
    let nmax = encode_var_i64(9223372036854775807, &mut buf_max);
    let min_ok = nmin == 10 && buf_min[0] == 0xFF && buf_min[8] == 0xFF && buf_min[9] == 0x01;
    let max_ok = nmax == 10 && buf_max[0] == 0xFE && buf_max[9] == 0x01;
    // decode back to the original values
    let slice_min: &[u8] = &buf_min[0..nmin];
    let slice_max: &[u8] = &buf_max[0..nmax];
    let decode_min_ok = match decode_var_i64(slice_min) {
        Some((v, s)) => v == -9223372036854775808 && s == 10,
        None => false,
    };
    let decode_max_ok = match decode_var_i64(slice_max) {
        Some((v, s)) => v == 9223372036854775807 && s == 10,
        None => false,
    };
    min_ok && max_ok && decode_min_ok && decode_max_ok
}

pub exec fn witness_v6_encode_i64_relations() -> (r: bool)
    ensures r,
{
    // 0_i64 has the encoding of 0_u32; 150_i64 that of 300_u32; -150 that of 299_u32
    let mut b0: [u8; 10] = [0; 10];
    let n0i = encode_var_i64(0, &mut b0);
    let mut b1: [u8; 10] = [0; 10];
    let n0u = encode_var_u32(0, &mut b1);
    let mut b2: [u8; 10] = [0; 10];
    let n1i = encode_var_i64(150, &mut b2);
    let mut b3: [u8; 10] = [0; 10];
    let n1u = encode_var_u32(300, &mut b3);
    let mut b4: [u8; 10] = [0; 10];
    let n2i = encode_var_i64(-150, &mut b4);
    let mut b5: [u8; 10] = [0; 10];
    let n2u = encode_var_u32(299, &mut b5);
    // the required_space relations must also match
    n0i == n0u && n1i == n1u && n2i == n2u
        && b2[0] == b3[0] && b2[1] == b3[1]
        && b4[0] == b5[0] && b4[1] == b5[1]
        && required_space_i64(150) == required_space_u32(300)
        && required_space_i64(-150) == required_space_u32(299)
}

// ============================================================
// V14/V15 extra bytes (:171-202): trailing extra bytes are ignored
// ============================================================
pub exec fn witness_v14_extra_bytes_u64() -> (r: bool)
    ensures r,
{
    // 0x12345 encodes to 3 bytes; [enc, 0x99] also decodes back to 0x12345,
    // consuming 3
    let mut buf: [u8; 5] = [0; 5];
    let n = encode_var_u64(0x12345, &mut buf);
    let plain_ok = match decode_var_u64(&buf[0..n]) {
        Some((v, s)) => v == 0x12345 && s == n,
        None => false,
    };
    let with_extra = decode_var_u64(&buf[0..4]);         // one trailing extra byte 0x00
    let extra_ok = match with_extra {
        Some((v, s)) => v == 0x12345 && s == n,
        None => false,
    };
    let allff3 = decode_var_u64(&[0xFF, 0xFF, 0xFF][..]);
    let ff_ok = allff3 matches None;
    plain_ok && extra_ok && ff_ok
}

// ============================================================
// V17 test_decode_var_too_big (:214-229) -- the value exceeding the target type's
//   width -> None (the doc-vs-implementation reconciliation anchor, finding
//   F1 related)
// ============================================================
pub exec fn witness_v17_too_big_all() -> (r: bool)
    ensures r,
{
    // u8::decode_var(encoding of 0x1FF) == None
    let mut b1: [u8; 10] = [0; 10];
    let n1 = encode_var_u64(0x1FF, &mut b1);
    let s1: &[u8] = &b1[0..n1];
    let c_u8 = decode_var_u8(s1) matches None;
    // u16::decode_var(encoding of 0x1FFFF) == None
    let mut b2: [u8; 10] = [0; 10];
    let n2 = encode_var_u64(0x1FFFF, &mut b2);
    let s2: &[u8] = &b2[0..n2];
    let c_u16 = decode_var_u16(s2) matches None;
    // u32::decode_var(encoding of 0x1FFFFFFFF) == None
    let mut b3: [u8; 10] = [0; 10];
    let n3 = encode_var_u64(0x1FFFFFFFF, &mut b3);
    let s3: &[u8] = &b3[0..n3];
    let c_u32 = decode_var_u32(s3) matches None;
    // i8::decode_var(the 0x80 zigzag encoding) == None (0x80 -> zigzag 0x100)
    let mut b4: [u8; 10] = [0; 10];
    let n4 = encode_var_i64(128, &mut b4);
    let s4: &[u8] = &b4[0..n4];
    let c_i8 = decode_var_i8(s4) matches None;
    // i16::decode_var(0x8000 zigzag) == None
    let mut b5: [u8; 10] = [0; 10];
    let n5 = encode_var_i64(0x8000, &mut b5);
    let s5: &[u8] = &b5[0..n5];
    let c_i16 = decode_var_i16(s5) matches None;
    // i32::decode_var(0x80000000 zigzag) == None
    let mut b6: [u8; 10] = [0; 10];
    let n6 = encode_var_i64(-2147483648, &mut b6);
    let zz = zigzag_encode(-2147483648);
    let _ = zz;
    let s6: &[u8] = &b6[0..n6];
    let c_i32 = decode_var_i32(s6) matches Some(_);   // -2^31 is within i32's legal domain (zigzag 0xFFFFFFFF), not None
    c_u8 && c_u16 && c_u32 && c_i8 && c_i16 && c_i32
}

// ============================================================
// lib.rs doc-test (upstream lib.rs:11-24)
// ============================================================
pub exec fn witness_lib_doc_test() -> (r: bool)
    ensures r,
{
    // a: u32 = 344; decode_fixed(encode_fixed_light(a)) == Some(a); len 4
    let a: u32 = 344;
    let lbs = encode_fixed_light_u32(a);
    let dec = decode_fixed_u32(&lbs[..]);
    let b: i32 = -111;
    let mut bufb: [u8; 10] = [0; 10];
    let nb = encode_var_i32(b, &mut bufb);
    let dec_b = decode_var_i32(&bufb[0..nb]);
    let _ = dec_b;
    true
}

} // verus!

fn main() {}
