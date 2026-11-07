//! verified/harness/ut_props.rs -- the UT property theorems
//! (no-bytes-dropped / no-concat-alias / idempotent)
//! (reference organization: #[path] pulls in the verified/src modules,
//! the spec-side facts are not copied)
//!
//! [Origin Rust: tests.rs test_hash_no_bytes_dropped_* / test_hash_no_concat_alias / test_hash_idempotent (pin 2fcf2a7, code/src/tests.rs)]
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
 * tests.rs test_hash_no_bytes_dropped_64 (line 253): the write_u64 path,
 * SipHasher::new => keys (0,0) (std Hash for u64 -> write_u64, ledger)
 * ============================================================ */

/// Baseline: hash64(0xdead_beef_dead_beef)
pub exec fn th_nbd64_base() -> (r: u64)
    ensures r == 0x470db687ff3fbad0u64  // official vector
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0xdeadbeefdeadbeefu64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdeadbeefdeadbeefu64) == (0u64, 0u64, 0xc59cadc4922c957eu64, 0xe017aa87c82b5a50u64, 0x5d93fde027503981u64, 0xc7ec71d013daab43u64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0xdeadbeefdeadbeefu64
    assert(spec_finish_24((0u64, 0u64, 0xc59cadc4922c957eu64, 0xe017aa87c82b5a50u64, 0x5d93fde027503981u64, 0xc7ec71d013daab43u64, 8u64, 0u64, 0u64)) == 0x470db687ff3fbad0u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x470db687ff3fbad0u64); // closing step
    }
    r0
}


/// mask byte 0: 0xdead_beef_dead_beef & !(0xff << 0)
pub exec fn th_nbd64_0() -> (r: u64)
    ensures r != 0x470db687ff3fbad0u64  // != the baseline hash (zeroing any single byte must change the hash)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0xdeadbeefdeadbe00u64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdeadbeefdeadbe00u64) == (0u64, 0u64, 0xde17a44094ae957cu64, 0xe017ac8735a7fa5bu64, 0x60075deb27503c78u64, 0xcc67099416bb17afu64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0xdeadbeefdeadbe00u64
    assert(spec_finish_24((0u64, 0u64, 0xde17a44094ae957cu64, 0xe017ac8735a7fa5bu64, 0x60075deb27503c78u64, 0xcc67099416bb17afu64, 8u64, 0u64, 0u64)) == 0x6af53df4142235dbu64) by(bit_vector); // finish whole chain
    assert(r0 == 0x6af53df4142235dbu64); // closing step
    }
    r0
}


/// mask byte 1: 0xdead_beef_dead_beef & !(0xff << 8)
pub exec fn th_nbd64_1() -> (r: u64)
    ensures r != 0x470db687ff3fbad0u64  // != the baseline hash (zeroing any single byte must change the hash)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0xdeadbeefdead00efu64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdeadbeefdead00efu64) == (0u64, 0u64, 0xdfe7cc33e2dfc16cu64, 0xe07f81d252f76850u64, 0x3f4fcfe0273b8351u64, 0x53b113f221d145bdu64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0xdeadbeefdead00efu64
    assert(spec_finish_24((0u64, 0u64, 0xdfe7cc33e2dfc16cu64, 0xe07f81d252f76850u64, 0x3f4fcfe0273b8351u64, 0x53b113f221d145bdu64, 8u64, 0u64, 0u64)) == 0x715453c8f2e0e61cu64) by(bit_vector); // finish whole chain
    assert(r0 == 0x715453c8f2e0e61cu64); // closing step
    }
    r0
}


/// mask byte 2: 0xdead_beef_dead_beef & !(0xff << 16)
pub exec fn th_nbd64_2() -> (r: u64)
    ensures r != 0x470db687ff3fbad0u64  // != the baseline hash (zeroing any single byte must change the hash)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0xdeadbeefde00beefu64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdeadbeefde00beefu64) == (0u64, 0u64, 0x081849ec91e09ea1u64, 0xfed14f5d6f725a50u64, 0xfacafde0394b9defu64, 0x816839daa4b2f8e1u64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0xdeadbeefde00beefu64
    assert(spec_finish_24((0u64, 0u64, 0x081849ec91e09ea1u64, 0xfed14f5d6f725a50u64, 0xfacafde0394b9defu64, 0x816839daa4b2f8e1u64, 8u64, 0u64, 0u64)) == 0xd3b1b9d11dae8aa6u64) by(bit_vector); // finish whole chain
    assert(r0 == 0xd3b1b9d11dae8aa6u64); // closing step
    }
    r0
}


/// mask byte 3: 0xdead_beef_dead_beef & !(0xff << 24)
pub exec fn th_nbd64_3() -> (r: u64)
    ensures r != 0x470db687ff3fbad0u64  // != the baseline hash (zeroing any single byte must change the hash)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0xdeadbeef00adbeefu64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdeadbeef00adbeefu64) == (0u64, 0u64, 0xadd9f1c7a2d90380u64, 0x0ed298c4ca2b5a46u64, 0x5f93fdf53914dbc2u64, 0x2ffc6eabf9673455u64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0xdeadbeef00adbeefu64
    assert(spec_finish_24((0u64, 0u64, 0xadd9f1c7a2d90380u64, 0x0ed298c4ca2b5a46u64, 0x5f93fdf53914dbc2u64, 0x2ffc6eabf9673455u64, 8u64, 0u64, 0u64)) == 0x276b602a455487f8u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x276b602a455487f8u64); // closing step
    }
    r0
}


/// mask byte 4: 0xdead_beef_dead_beef & !(0xff << 32)
pub exec fn th_nbd64_4() -> (r: u64)
    ensures r != 0x470db687ff3fbad0u64  // != the baseline hash (zeroing any single byte must change the hash)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0xdeadbe00deadbeefu64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdeadbe00deadbeefu64) == (0u64, 0u64, 0xc270aa14891feefcu64, 0x2216cba2c82b4588u64, 0x5d93e195254958a4u64, 0xe523caebb8a9e641u64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0xdeadbe00deadbeefu64
    assert(spec_finish_24((0u64, 0u64, 0xc270aa14891feefcu64, 0x2216cba2c82b4588u64, 0x5d93e195254958a4u64, 0xe523caebb8a9e641u64, 8u64, 0u64, 0u64)) == 0x8ced13ec78a86c68u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x8ced13ec78a86c68u64); // closing step
    }
    r0
}


/// mask byte 5: 0xdead_beef_dead_beef & !(0xff << 40)
pub exec fn th_nbd64_5() -> (r: u64)
    ensures r != 0x470db687ff3fbad0u64  // != the baseline hash (zeroing any single byte must change the hash)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0xdead00efdeadbeefu64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdead00efdeadbeefu64) == (0u64, 0u64, 0x2d9c75daec71b9cau64, 0x9acab887c83cc065u64, 0x5d84c84f458d2b81u64, 0xed141bc0630a87fau64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0xdead00efdeadbeefu64
    assert(spec_finish_24((0u64, 0u64, 0x2d9c75daec71b9cau64, 0x9acab887c83cc065u64, 0x5d84c84f458d2b81u64, 0xed141bc0630a87fau64, 8u64, 0u64, 0u64)) == 0xf7077c91aaf93b1bu64) by(bit_vector); // finish whole chain
    assert(r0 == 0xf7077c91aaf93b1bu64); // closing step
    }
    r0
}


/// mask byte 6: 0xdead_beef_dead_beef & !(0xff << 48)
pub exec fn th_nbd64_6() -> (r: u64)
    ensures r != 0x470db687ff3fbad0u64  // != the baseline hash (zeroing any single byte must change the hash)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0xde00beefdeadbeefu64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xde00beefdeadbeefu64) == (0u64, 0u64, 0xc9c74101970c81ccu64, 0xa24aaa87e4c7d16au64, 0x7090cb2a650d3981u64, 0x7f1abe13983a2c93u64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0xde00beefdeadbeefu64
    assert(spec_finish_24((0u64, 0u64, 0xc9c74101970c81ccu64, 0xa24aaa87e4c7d16au64, 0x7090cb2a650d3981u64, 0x7f1abe13983a2c93u64, 8u64, 0u64, 0u64)) == 0x6fe8bfdb0926e265u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x6fe8bfdb0926e265u64); // closing step
    }
    r0
}


/// mask byte 7: 0xdead_beef_dead_beef & !(0xff << 56)
pub exec fn th_nbd64_7() -> (r: u64)
    ensures r != 0x470db687ff3fbad0u64  // != the baseline hash (zeroing any single byte must change the hash)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(0x00adbeefdeadbeefu64);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u64_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0x00adbeefdeadbeefu64) == (0u64, 0u64, 0x85ea9bd7c8cb257eu64, 0xb217aa7b8443d110u64, 0x677b86a07550397au64, 0x5b38ba91492e583bu64, 8u64, 0u64, 0u64)) by(bit_vector); // u64 0x00adbeefdeadbeefu64
    assert(spec_finish_24((0u64, 0u64, 0x85ea9bd7c8cb257eu64, 0xb217aa7b8443d110u64, 0x677b86a07550397au64, 0x5b38ba91492e583bu64, 8u64, 0u64, 0u64)) == 0xc4d9610eac1e62dau64) by(bit_vector); // finish whole chain
    assert(r0 == 0xc4d9610eac1e62dau64); // closing step
    }
    r0
}


/* ============================================================
 * tests.rs test_hash_no_bytes_dropped_32 (line 272): the write_u32 path
 * (std Hash for u32 -> write_u32, ledger)
 * ============================================================ */

/// Baseline: hash64(0xdeadbeef) (the write_u32 path)
pub exec fn th_nbd32_base() -> (r: u64)
    ensures r == 0xed719c0679fc8805u64  // official vector
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u32(0xdeadbeefu32);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u32_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdeadbeefu32) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x00000000deadbeefu64, 4u64)) by(bit_vector); // u32 0xdeadbeefu32
    assert(spec_finish_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x00000000deadbeefu64, 4u64)) == 0xed719c0679fc8805u64) by(bit_vector); // finish whole chain
    assert(r0 == 0xed719c0679fc8805u64); // closing step
    }
    r0
}


/// mask byte 0
pub exec fn th_nbd32_0() -> (r: u64)
    ensures r != 0xed719c0679fc8805u64  // != the baseline
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u32(0xdeadbe00u32);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u32_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdeadbe00u32) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x00000000deadbe00u64, 4u64)) by(bit_vector); // u32 0xdeadbe00u32
    assert(spec_finish_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x00000000deadbe00u64, 4u64)) == 0xd7f1bcb883dd459eu64) by(bit_vector); // finish whole chain
    assert(r0 == 0xd7f1bcb883dd459eu64); // closing step
    }
    r0
}


/// mask byte 1
pub exec fn th_nbd32_1() -> (r: u64)
    ensures r != 0xed719c0679fc8805u64  // != the baseline
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u32(0xdead00efu32);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u32_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xdead00efu32) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x00000000dead00efu64, 4u64)) by(bit_vector); // u32 0xdead00efu32
    assert(spec_finish_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x00000000dead00efu64, 4u64)) == 0x6a744e9929448625u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x6a744e9929448625u64); // closing step
    }
    r0
}


/// mask byte 2
pub exec fn th_nbd32_2() -> (r: u64)
    ensures r != 0xed719c0679fc8805u64  // != the baseline
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u32(0xde00beefu32);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u32_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0xde00beefu32) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x00000000de00beefu64, 4u64)) by(bit_vector); // u32 0xde00beefu32
    assert(spec_finish_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x00000000de00beefu64, 4u64)) == 0x4723f92260611b61u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x4723f92260611b61u64); // closing step
    }
    r0
}


/// mask byte 3
pub exec fn th_nbd32_3() -> (r: u64)
    ensures r != 0xed719c0679fc8805u64  // != the baseline
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u32(0x00adbeefu32);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u32_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 0x00adbeefu32) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x0000000000adbeefu64, 4u64)) by(bit_vector); // u32 0x00adbeefu32
    assert(spec_finish_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x0000000000adbeefu64, 4u64)) == 0x4e65d6c8013ff519u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x4e65d6c8013ff519u64); // closing step
    }
    r0
}


/* ============================================================
 * tests.rs test_hash_no_concat_alias (line 287) -- the modeled form
 * (assumption ledger: std Hash for &str = write(bytes);
 * write_u8(0xff) is the terminator; tuples are concatenated in element
 * order. The usize/slice prefix domain
 * depends on the std Hash encoding semantics; blocked scope)
 * ============================================================ */

/// Stream s = [97, 97, 255, 98, 98, 255] (Hash byte-stream model)
pub exec fn th_concat_s() -> (r: u64)
    ensures r == 0xe464e0f0abe0b497u64  // official vector
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u8(97u8);
    h.write_u8(97u8);
    h.write_u8(255u8);
    h.write_u8(98u8);
    h.write_u8(98u8);
    h.write_u8(255u8);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 97u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 1u64, 97u64, 1u64)) by(bit_vector); // u8 97u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 1u64, 97u64, 1u64), 97u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 2u64, 0x0000000000006161u64, 2u64)) by(bit_vector); // u8 97u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 2u64, 0x0000000000006161u64, 2u64), 255u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 3u64, 0x0000000000ff6161u64, 3u64)) by(bit_vector); // u8 255u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 3u64, 0x0000000000ff6161u64, 3u64), 98u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x0000000062ff6161u64, 4u64)) by(bit_vector); // u8 98u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x0000000062ff6161u64, 4u64), 98u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 5u64, 0x0000006262ff6161u64, 5u64)) by(bit_vector); // u8 98u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 5u64, 0x0000006262ff6161u64, 5u64), 255u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 6u64, 0x0000ff6262ff6161u64, 6u64)) by(bit_vector); // u8 255u8
    assert(spec_finish_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 6u64, 0x0000ff6262ff6161u64, 6u64)) == 0xe464e0f0abe0b497u64) by(bit_vector); // finish whole chain
    assert(r0 == 0xe464e0f0abe0b497u64); // closing step
    }
    r0
}


/// Stream t = [97, 97, 98, 98, 255, 255] (Hash byte-stream model)
pub exec fn th_concat_t() -> (r: u64)
    ensures r == 0x21b89a8efca360d7u64  // official vector
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u8(97u8);
    h.write_u8(97u8);
    h.write_u8(98u8);
    h.write_u8(98u8);
    h.write_u8(255u8);
    h.write_u8(255u8);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 97u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 1u64, 97u64, 1u64)) by(bit_vector); // u8 97u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 1u64, 97u64, 1u64), 97u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 2u64, 0x0000000000006161u64, 2u64)) by(bit_vector); // u8 97u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 2u64, 0x0000000000006161u64, 2u64), 98u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 3u64, 0x0000000000626161u64, 3u64)) by(bit_vector); // u8 98u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 3u64, 0x0000000000626161u64, 3u64), 98u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x0000000062626161u64, 4u64)) by(bit_vector); // u8 98u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x0000000062626161u64, 4u64), 255u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 5u64, 0x000000ff62626161u64, 5u64)) by(bit_vector); // u8 255u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 5u64, 0x000000ff62626161u64, 5u64), 255u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 6u64, 0x0000ffff62626161u64, 6u64)) by(bit_vector); // u8 255u8
    assert(spec_finish_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 6u64, 0x0000ffff62626161u64, 6u64)) == 0x21b89a8efca360d7u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x21b89a8efca360d7u64); // closing step
    }
    r0
}


/// Stream u = [97, 255, 97, 98, 98, 255] (Hash byte-stream model)
pub exec fn th_concat_u() -> (r: u64)
    ensures r == 0x70270988c7866111u64  // official vector
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u8(97u8);
    h.write_u8(255u8);
    h.write_u8(97u8);
    h.write_u8(98u8);
    h.write_u8(98u8);
    h.write_u8(255u8);
    let r0 = h.finish();
    proof {
    assert(spec_new_24(0u64, 0u64) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64)) by(bit_vector); // reset
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 0u64, 0u64, 0u64), 97u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 1u64, 97u64, 1u64)) by(bit_vector); // u8 97u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 1u64, 97u64, 1u64), 255u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 2u64, 0x000000000000ff61u64, 2u64)) by(bit_vector); // u8 255u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 2u64, 0x000000000000ff61u64, 2u64), 97u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 3u64, 0x000000000061ff61u64, 3u64)) by(bit_vector); // u8 97u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 3u64, 0x000000000061ff61u64, 3u64), 98u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x000000006261ff61u64, 4u64)) by(bit_vector); // u8 98u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 4u64, 0x000000006261ff61u64, 4u64), 98u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 5u64, 0x000000626261ff61u64, 5u64)) by(bit_vector); // u8 98u8
    assert(spec_write_u8_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 5u64, 0x000000626261ff61u64, 5u64), 255u8) == (0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 6u64, 0x0000ff626261ff61u64, 6u64)) by(bit_vector); // u8 255u8
    assert(spec_finish_24((0u64, 0u64, 0x736f6d6570736575u64, 0x646f72616e646f6du64, 0x6c7967656e657261u64, 0x7465646279746573u64, 6u64, 0x0000ff626261ff61u64, 6u64)) == 0x70270988c7866111u64) by(bit_vector); // finish whole chain
    assert(r0 == 0x70270988c7866111u64); // closing step
    }
    r0
}


/* ============================================================
 * tests.rs test_hash_idempotent (line 245) / tests128.rs (line 36):
 * idempotence -- the hash chain stays the same for the same input
 * (the write_u64 / write_u32 universal paths)
 * ============================================================ */

/// write_u64 path (SipHasher::new => keys (0,0); the tests.rs val64 branch)
pub exec fn th_idempotent_u64(v: u64) -> (r: u64)
    ensures r == hash_u64_24(0u64, 0u64, v)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u64(v);
    let r0 = h.finish();
    proof { assert(r0 == hash_u64_24(0u64, 0u64, v)); }
    r0
}

/// write_u32 path (the tests.rs val32 branch)
pub exec fn th_idempotent_u32(v: u32) -> (r: u64)
    ensures r == hash_u32_24(0u64, 0u64, v)
{
    let mut h = Hasher24::new_with_keys(0u64, 0u64);
    h.write_u32(v);
    let r0 = h.finish();
    proof { assert(r0 == hash_u32_24(0u64, 0u64, v)); }
    r0
}

/// 128-bit output idempotence (the finish128 paths of the tests128
/// val64/val32 branches)
pub exec fn th_idempotent128_u64(v: u64) -> (r: (u64, u64))
    ensures
        r.0 == spec_finish128_24(spec_write_u64_128_24(spec_new_128_24(0u64, 0u64), v)).0,
        r.1 == spec_finish128_24(spec_write_u64_128_24(spec_new_128_24(0u64, 0u64), v)).1,
{
    let mut h = Hasher128_24::new_with_keys(0u64, 0u64);
    h.write_u64(v);
    let r0 = h.finish128();
    (r0.h1, r0.h2)
}


// ===========================================================================
// Proof lemma -- the pairwise non-aliasing witness of the three modeled
// Hash byte streams, at the end of the file (an order-only relocation,
// measured panel-neutral: ut_props 152v/0e)
/// The three streams are pairwise non-aliasing (the modeled form of the
/// tests.rs assertion)
pub proof fn th_no_concat_alias_core()
    ensures
        0xe464e0f0abe0b497u64 != 0x21b89a8efca360d7u64,
        0xe464e0f0abe0b497u64 != 0x70270988c7866111u64,
        0x21b89a8efca360d7u64 != 0x70270988c7866111u64,
{
    assert(0xe464e0f0abe0b497u64 != 0x21b89a8efca360d7u64) by(bit_vector);
    assert(0xe464e0f0abe0b497u64 != 0x70270988c7866111u64) by(bit_vector);
    assert(0x21b89a8efca360d7u64 != 0x70270988c7866111u64) by(bit_vector);
}


} // verus!

fn main() {}
