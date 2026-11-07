//! verified/harness/api_hash128.rs -- Hash128 conversions and equality
//! (the pub interface coverage diff-set)
//! (reference organization: #[path] pulls in the verified/src modules,
//! the spec-side facts are not copied)
//!
//! [Origin Rust: sip128.rs Hash128 / From / as_* / eq (pin 2fcf2a7, code/src/tests.rs)]
//! Proof shape: staged bv sealing (one bv step per spec-chain link,
//! literal state tuples,
//! single-level application) + function congruence propagation along the
//! exec ensures chain + an equality closing step;
//! the literals are re-computed by an isomorphic Python model and
//! machine-checked by Z3 (the official vectors are the final expected
//! values, not the Python model's).

#[path = "../src/common.rs"]
mod common;
#[path = "../src/sip.rs"]
mod sip;
#[path = "../src/sip128.rs"]
mod sip128;

use vstd::prelude::*;

verus! {
use crate::sip::*;
use crate::sip128::*;
use crate::common::compress_spec;


/* ============================================================
 * Hash128 conversions (as_bytes
 * per-position / From / eq / roundtrip)
 * ============================================================ */

/// byte(0) == (h1 >> 0) & 0xff
pub exec fn th_byte_0() -> (r: u8)
    ensures r == (((0xd00d0badfacefeedu64 >> (8 * 0u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(0)
}

/// byte(1) == (h1 >> 8) & 0xff
pub exec fn th_byte_1() -> (r: u8)
    ensures r == (((0xd00d0badfacefeedu64 >> (8 * 1u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(1)
}

/// byte(2) == (h1 >> 16) & 0xff
pub exec fn th_byte_2() -> (r: u8)
    ensures r == (((0xd00d0badfacefeedu64 >> (8 * 2u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(2)
}

/// byte(3) == (h1 >> 24) & 0xff
pub exec fn th_byte_3() -> (r: u8)
    ensures r == (((0xd00d0badfacefeedu64 >> (8 * 3u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(3)
}

/// byte(4) == (h1 >> 32) & 0xff
pub exec fn th_byte_4() -> (r: u8)
    ensures r == (((0xd00d0badfacefeedu64 >> (8 * 4u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(4)
}

/// byte(5) == (h1 >> 40) & 0xff
pub exec fn th_byte_5() -> (r: u8)
    ensures r == (((0xd00d0badfacefeedu64 >> (8 * 5u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(5)
}

/// byte(6) == (h1 >> 48) & 0xff
pub exec fn th_byte_6() -> (r: u8)
    ensures r == (((0xd00d0badfacefeedu64 >> (8 * 6u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(6)
}

/// byte(7) == (h1 >> 56) & 0xff
pub exec fn th_byte_7() -> (r: u8)
    ensures r == (((0xd00d0badfacefeedu64 >> (8 * 7u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(7)
}

/// byte(8) == (h2 >> 0) & 0xff
pub exec fn th_byte_8() -> (r: u8)
    ensures r == (((0x1badcafe0c0ffee0u64 >> (8 * 0u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(8)
}

/// byte(9) == (h2 >> 8) & 0xff
pub exec fn th_byte_9() -> (r: u8)
    ensures r == (((0x1badcafe0c0ffee0u64 >> (8 * 1u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(9)
}

/// byte(10) == (h2 >> 16) & 0xff
pub exec fn th_byte_10() -> (r: u8)
    ensures r == (((0x1badcafe0c0ffee0u64 >> (8 * 2u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(10)
}

/// byte(11) == (h2 >> 24) & 0xff
pub exec fn th_byte_11() -> (r: u8)
    ensures r == (((0x1badcafe0c0ffee0u64 >> (8 * 3u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(11)
}

/// byte(12) == (h2 >> 32) & 0xff
pub exec fn th_byte_12() -> (r: u8)
    ensures r == (((0x1badcafe0c0ffee0u64 >> (8 * 4u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(12)
}

/// byte(13) == (h2 >> 40) & 0xff
pub exec fn th_byte_13() -> (r: u8)
    ensures r == (((0x1badcafe0c0ffee0u64 >> (8 * 5u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(13)
}

/// byte(14) == (h2 >> 48) & 0xff
pub exec fn th_byte_14() -> (r: u8)
    ensures r == (((0x1badcafe0c0ffee0u64 >> (8 * 6u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(14)
}

/// byte(15) == (h2 >> 56) & 0xff
pub exec fn th_byte_15() -> (r: u8)
    ensures r == (((0x1badcafe0c0ffee0u64 >> (8 * 7u64)) & 0xffu64) as u8)
{
    let h = Hash128 { h1: 0xd00d0badfacefeedu64, h2: 0x1badcafe0c0ffee0u64 };
    h.byte(15)
}

/// From<u128> <-> as_u128 roundtrip (universal, LE assumption ledger)
pub exec fn th_hash128_roundtrip(v: u128) -> (r: u128)
    ensures r == v
{
    let h = hash128_from_u128(v);
    let w = h.as_u128();
    proof {
        assert(w == u128_from_pair(h.h1, h.h2));
        assert(u128_from_pair(h.h1, h.h2)
            == u128_from_pair(v as u64, (v >> 64) as u64));
        assert(u128_from_pair(v as u64, (v >> 64) as u64) == v) by(bit_vector);
    }
    w
}

/// Hash128 <-> u128 duality (h1/h2 -> u128 -> h1/h2)
pub exec fn th_hash128_pair_roundtrip(h1: u64, h2: u64) -> (r: (u64, u64))
    ensures r == (h1, h2)
{
    let h = Hash128 { h1, h2 };
    let w = h.as_u128();
    let back = hash128_from_u128(w);
    proof {
        assert(u128_from_pair(h1, h2) == w);
        assert(((((h1 as u128) | ((h2 as u128) << 64)) >> 64) as u64) == h2) by(bit_vector);
        assert(((((h1 as u128) | ((h2 as u128) << 64))) as u64) == h1) by(bit_vector);
    }
    (back.h1, back.h2)
}

/// eq semantics (agrees with field equality)
pub exec fn th_hash128_eq_spec(a: Hash128, b: Hash128) -> (r: bool)
    ensures r == (a.h1 == b.h1 && a.h2 == b.h2)
{
    hash128_eq(a, b)
}

/// Direct semantics of as_u64
pub exec fn th_hash128_as_u64(h1: u64, h2: u64) -> (r: (u64, u64))
    ensures r == (h1, h2)
{
    let h = Hash128 { h1, h2 };
    h.as_u64()
}


} // verus!

fn main() {}
