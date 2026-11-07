//! verified/harness/ut_vectors.rs -- the UT reference-vector theorems
//! (tests.rs / tests128.rs)
//! (reference organization: #[path] pulls in the verified/src modules,
//! the spec-side facts are not copied)
//!
//! [Origin Rust: tests.rs test_siphash_1_3 / test_siphash_2_4 + tests128.rs namesakes (pin 2fcf2a7, code/src/tests.rs)]
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
 * tests.rs test_siphash_1_3 (line 59): the official reference vectors
 * t=0 / t=8
 * ============================================================ */

/// tests.rs vec13[0] (line 61): (dc,c4,0f,05,58,01,ac,ab) LE = 0xabac0158050fc4dc
pub exec fn th_vec13_t0() -> (r: u64)
    ensures r == 0xabac0158050fc4dcu64  // official vector
{
    let mut h = Hasher13::new_with_keys(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64);
    let r0 = h.finish();
    proof {
    assert(spec_new_13(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_finish_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) == 0xabac0158050fc4dcu64) by(bit_vector); // finish whole chain
    assert(r0 == 0xabac0158050fc4dcu64); // closing step
    }
    r0
}


/// tests.rs vec13[8] (line 69): (8e,9a,29,8d,11,95,90,36) LE = 0x369095118d299a8e
pub exec fn th_vec13_t8() -> (r: u64)
    ensures r == 0x369095118d299a8eu64  // official vector
{
    let mut h = Hasher13::new_with_keys(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64);
    h.write_u8(0u8);
    h.write_u8(1u8);
    h.write_u8(2u8);
    h.write_u8(3u8);
    h.write_u8(4u8);
    h.write_u8(5u8);
    h.write_u8(6u8);
    h.write_u8(7u8);
    let r0 = h.finish();
    proof {
    assert(spec_new_13(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u8_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64), 0u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 1u64, 0u64, 1u64)) by(bit_vector); // u8 0u8
    assert(spec_write_u8_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 1u64, 0u64, 1u64), 1u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 2u64, 0x0000000000000100u64, 2u64)) by(bit_vector); // u8 1u8
    assert(spec_write_u8_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 2u64, 0x0000000000000100u64, 2u64), 2u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 3u64, 0x0000000000020100u64, 3u64)) by(bit_vector); // u8 2u8
    assert(spec_write_u8_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 3u64, 0x0000000000020100u64, 3u64), 3u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 4u64, 0x0000000003020100u64, 4u64)) by(bit_vector); // u8 3u8
    assert(spec_write_u8_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 4u64, 0x0000000003020100u64, 4u64), 4u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 5u64, 0x0000000403020100u64, 5u64)) by(bit_vector); // u8 4u8
    assert(spec_write_u8_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 5u64, 0x0000000403020100u64, 5u64), 5u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 6u64, 0x0000050403020100u64, 6u64)) by(bit_vector); // u8 5u8
    assert(spec_write_u8_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 6u64, 0x0000050403020100u64, 6u64), 6u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 7u64, 0x0006050403020100u64, 7u64)) by(bit_vector); // u8 6u8
    assert(spec_write_u8_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 7u64, 0x0006050403020100u64, 7u64), 7u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x63608f969061857fu64, 0x4ed232083d9aa8dcu64, 0xf2f74892d8141a2eu64, 0x9290f9810552f4a8u64, 8u64, 0u64, 0u64)) by(bit_vector); // u8 7u8
    assert(spec_finish_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x63608f969061857fu64, 0x4ed232083d9aa8dcu64, 0xf2f74892d8141a2eu64, 0x9290f9810552f4a8u64, 8u64, 0u64, 0u64)) == 0x369095118d299a8eu64) by(bit_vector); // finish whole chain
    assert(r0 == 0x369095118d299a8eu64); // closing step
    }
    r0
}


/* ============================================================
 * tests.rs test_siphash_2_4 (line 153): the official reference vectors
 * t=0 / t=8
 * ============================================================ */

/// tests.rs vec24[0] (line 155): (31,0e,0e,dd,47,db,6f,72) LE = 0x726fdb47dd0e0e31
pub exec fn th_vec24_t0() -> (r: u64)
    ensures r == 0x726fdb47dd0e0e31u64  // official vector
{
    let mut h = Hasher24::new_with_keys(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_finish_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) == 0x726fdb47dd0e0e31u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x726fdb47dd0e0e31u64); // closing step
    }
    r0
}


/// tests.rs vec24[8] (line 163): (62,24,93,9a,79,f5,f5,93) LE = 0x93f5f5799a932462
pub exec fn th_vec24_t8() -> (r: u64)
    ensures r == 0x93f5f5799a932462u64  // official vector
{
    let mut h = Hasher24::new_with_keys(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64);
    h.write_u8(0u8);
    h.write_u8(1u8);
    h.write_u8(2u8);
    h.write_u8(3u8);
    h.write_u8(4u8);
    h.write_u8(5u8);
    h.write_u8(6u8);
    h.write_u8(7u8);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u8_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64), 0u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 1u64, 0u64, 1u64)) by(bit_vector); // u8 0u8
    assert(spec_write_u8_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 1u64, 0u64, 1u64), 1u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 2u64, 0x0000000000000100u64, 2u64)) by(bit_vector); // u8 1u8
    assert(spec_write_u8_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 2u64, 0x0000000000000100u64, 2u64), 2u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 3u64, 0x0000000000020100u64, 3u64)) by(bit_vector); // u8 2u8
    assert(spec_write_u8_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 3u64, 0x0000000000020100u64, 3u64), 3u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 4u64, 0x0000000003020100u64, 4u64)) by(bit_vector); // u8 3u8
    assert(spec_write_u8_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 4u64, 0x0000000003020100u64, 4u64), 4u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 5u64, 0x0000000403020100u64, 5u64)) by(bit_vector); // u8 4u8
    assert(spec_write_u8_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 5u64, 0x0000000403020100u64, 5u64), 5u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 6u64, 0x0000050403020100u64, 6u64)) by(bit_vector); // u8 5u8
    assert(spec_write_u8_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 6u64, 0x0000050403020100u64, 6u64), 6u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 7u64, 0x0006050403020100u64, 7u64)) by(bit_vector); // u8 6u8
    assert(spec_write_u8_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e6665u64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 7u64, 0x0006050403020100u64, 7u64), 7u8) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x4a017198de0a59e0u64, 0x0d52f6f62a4f59a4u64, 0x634cb3577b01fd3du64, 0xa5224d6f55c7d9c8u64, 8u64, 0u64, 0u64)) by(bit_vector); // u8 7u8
    assert(spec_finish_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x4a017198de0a59e0u64, 0x0d52f6f62a4f59a4u64, 0x634cb3577b01fd3du64, 0xa5224d6f55c7d9c8u64, 8u64, 0u64, 0u64)) == 0x93f5f5799a932462u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x93f5f5799a932462u64); // closing step
    }
    r0
}


/* ============================================================
 * tests128.rs test_siphash128_1_3 (line 45) / _2_4 (line 76): the t=0
 * vectors
 * ============================================================ */

/// tests128 1-3 vec[0]: h1 = LE(231,126,188,178,39,136,165,190), h2 =
/// LE(253,98,219,106,221,48,48,1)
pub exec fn th_vec128_13_t0() -> (r: Hash128)
    ensures
        r.h1 == 0xbea58827b2bc7ee7u64,
        r.h2 == 0x013030dd6adb62fdu64,
{
    let mut h = Hasher128_13::new_with_keys(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64);
    let r0 = h.finish128();
    proof {
    assert(spec_new_128_13(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e668bu64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_finish128_13((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e668bu64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) == (0xbea58827b2bc7ee7u64, 0x013030dd6adb62fdu64)) by(bit_vector); // finish128 whole chain
    assert(r0.h1 == 0xbea58827b2bc7ee7u64); // closing step
    assert(r0.h2 == 0x013030dd6adb62fdu64); // closing step
    }
    r0
}


/// tests128 2-4 vec[0]: h1 = LE(163,129,127,4,186,37,168,230), h2 =
/// LE(109,246,114,20,199,85,2,147)
pub exec fn th_vec128_24_t0() -> (r: Hash128)
    ensures
        r.h1 == 0xe6a825ba047f81a3u64,
        r.h2 == 0x930255c71472f66du64,
{
    let mut h = Hasher128_24::new_with_keys(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64);
    let r0 = h.finish128();
    proof {
    assert(spec_new_128_24(0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64) == (0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e668bu64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_finish128_24((0x0706050403020100u64, 0x0f0e0d0c0b0a0908u64, 0x7469686173716475u64, 0x6b617f6d656e668bu64, 0x6b7f62616d677361u64, 0x7b6b696e727e6c7bu64, 0u64, 0u64, 0u64)) == (0xe6a825ba047f81a3u64, 0x930255c71472f66du64)) by(bit_vector); // finish128 whole chain
    assert(r0.h1 == 0xe6a825ba047f81a3u64); // closing step
    assert(r0.h2 == 0x930255c71472f66du64); // closing step
    }
    r0
}


} // verus!

fn main() {}
