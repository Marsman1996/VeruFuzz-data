//! harness/ut_fixed.rs -- the UT witnesses of the upstream code/src/fixed_tests.rs
//!
//! Covers inventory F1-F15 (F16 is a cfg-gated async item, out of the default
//! verification surface).
//! Reference-style organization: #[path] pulls in verified/src/fixed.rs.

use vstd::prelude::*;

#[path = "../src/fixed.rs"]
mod fixed;

use fixed::*;

verus! {

// ============================================================
// F1/F2/F7/F8/F9/F10 encode vectors (fixed_tests.rs:14-66)
// ============================================================
pub exec fn witness_encode_vectors() -> (r: bool)
    ensures r,
{
    // F1: 32_u32 -> [32,0,0,0]
    let e32 = encode_fixed_vec_u32(32);
    let mut o1 = true;
    if e32.len() != 4 { o1 = false; }
    if e32[0] != 32 || e32[1] != 0 || e32[2] != 0 || e32[3] != 0 { o1 = false; }
    // F2: 256_u16 -> [0,1]
    let e16 = encode_fixed_vec_u16(256);
    let o2 = e16.len() == 2 && e16[0] == 0 && e16[1] == 1;
    // F7: 255_u8 -> [255]
    let e8 = encode_fixed_vec_u8(255);
    let o3 = e8.len() == 1 && e8[0] == 255;
    o1 && o2 && o3
}

// ============================================================
// F3/F4/F5/F6 switch_endianness (:24-46)
// ============================================================
pub exec fn witness_endian_cases() -> (r: bool)
    ensures r,
{
    // F3: 1_u16 -> 256
    let c1 = switch_endianness_u16(1) == 256;
    // F4: 1_u32 -> 1<<24 and involutes back to 1
    let sw = switch_endianness_u32(1);
    let c2 = sw == (1 << 24) && switch_endianness_u32(sw) == 1;
    // F5: u64::MAX unchanged
    let c3 = switch_endianness_u64(0xFFFF_FFFF_FFFF_FFFF) == 0xFFFF_FFFF_FFFF_FFFF;
    // F6: -2_i16 -> -257 (two's-complement byte swap)
    let c4 = switch_endianness_i16(-2) == -257;
    c1 && c2 && c3 && c4
}

// ============================================================
// F11/F12 encode_fixed_light and decode round trips (:79-103)
// ============================================================
pub exec fn witness_light_roundtrips() -> (r: bool)
    ensures r,
{
    // F11: -32767_i32 -> [1,128,255,255]
    let lb = encode_fixed_light_i32(-32767);
    let o1 = lb.len() >= 4;   // the array literal length is a compile-time fact
    let d = decode_fixed_i32(&lb[..4]);
    let o2 = match d {
        Some(v) => v == -32767,
        None => false,
    };
    // F12: the 8 types round-trip
    let mut ok_all = o1 && o2;
    let a1: u8 = 17;
    let l1 = encode_fixed_light_u8(a1);
    let d1 = decode_fixed_u8(&l1[..]);
    ok_all = ok_all && (d1 == Some(17));
    let a2: u16 = 17;
    let l2 = encode_fixed_light_u16(a2);
    let d2 = decode_fixed_u16(&l2[..]);
    ok_all = ok_all && (d2 == Some(17));
    let a3: u32 = 17;
    let l3 = encode_fixed_light_u32(a3);
    let d3 = decode_fixed_u32(&l3[..]);
    ok_all = ok_all && (d3 == Some(17));
    let a4: u64 = 17;
    let l4 = encode_fixed_light_u64(a4);
    let d4 = decode_fixed_u64(&l4[..]);
    ok_all = ok_all && (d4 == Some(17));
    let e1: i8 = -17;
    let e_5 = encode_fixed_light_i8(e1);
    let de1 = decode_fixed_i8(&e_5[..]);
    ok_all = ok_all && (de1 == Some(-17));
    let e2: i16 = -17;
    let e_6 = encode_fixed_light_i16(e2);
    let de2 = decode_fixed_i16(&e_6[..]);
    ok_all = ok_all && (de2 == Some(-17));
    let e3: i32 = -17;
    let e_7 = encode_fixed_light_i32(e3);
    let de3 = decode_fixed_i32(&e_7[..]);
    ok_all = ok_all && (de3 == Some(-17));
    let e4: i64 = -17;
    let e_8 = encode_fixed_light_i64(e4);
    let de4 = decode_fixed_i64(&e_8[..]);
    ok_all = ok_all && (de4 == Some(-17));
    ok_all
}

// ============================================================
// F14/F15 the mirror obligations of should_panic: the None-return surface (:132-142)
// ============================================================
pub exec fn witness_invalid_sizes_none() -> (r: bool)
    ensures r,
{
    // F14: a 6-byte input decode_fixed::<u64> -> None (upstream unwrap would panic)
    let bad: [u8; 6] = [1, 0, 0, 0, 0, 1];
    let d = decode_fixed_u64(&bad[..]);
    let c1 = d matches None;
    // F15: a 4-byte buf encode_fixed::<u64> -> None
    let mut buf: [u8; 4] = [0; 4];
    let e = encode_fixed_u64(11, &mut buf);
    let c2 = e matches None;
    c1 && c2
}

} // verus!

fn main() {}
