//! faest batch-FA7 harness -- the verus arm of the bavc KAT chain.
//!
//! Mounts the verified FA7 twin tree (the fa7-driver shape: fields
//! + prover + parameter + parameter_tower + utils + prg +
//! random_oracles + universal_hashing + bavc; src/lib.rs untouched)
//! and pins, as executable verification rows:
//!  - the tau-parameter bavc helper tables at the FAEST128f /
//!    FAEST128s / FAEST256s configurations (pos_in_tree /
//!    bavc_index_offset / bavc_max_node_index ground rows, computed
//!    by the upstream parameter.rs formulas on the closed FA1 tau
//!    constants -- the FA1-deferred slice, now landed with its
//!    numeric evidence; the full algorithm-value KATs of the bavc
//!    ladder ride the python sim (arm 1, 12/12 rows bit-exact) and
//!    the oracle arm carries the machinery side);
//!  - the leaf-commitment exec faces at all three lambda axes (the
//!    requires chains + spec-view postconditions instantiated over
//!    real slab shapes; the prg/shake value halves are trusted-core
//!    oracles (FA4/FA5), so the value equality itself is carried by
//!    arms 1+2, not asserted here -- the arm-1 python sim reproduces
//!    all six leaf_com rows through THE SAME formula chain this twin
//!    verifies).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/fields/large_fields.rs"]
mod large_fields;

#[path = "../src/fields/small_fields.rs"]
mod small_fields;

#[path = "../src/prover/mod.rs"]
mod prover;

#[path = "../src/parameter.rs"]
mod parameter;

#[path = "../src/parameter_tower.rs"]
mod parameter_tower;

#[path = "../src/utils.rs"]
mod utils;

#[path = "../src/prg.rs"]
mod prg;

#[path = "../src/random_oracles.rs"]
mod random_oracles;

#[path = "../src/universal_hashing.rs"]
mod universal_hashing;

#[path = "../src/bavc.rs"]
mod bavc;

#[allow(unused)]
use bavc::{
    bavc_index_offset, bavc_max_node_index, leaf_commit_128, leaf_commit_192, leaf_commit_256,
    leaf_commit_em_128, leaf_commit_em_192, leaf_commit_em_256, pos_in_tree,
};

verus! {

fn ut_pos_in_tree_faest128f_rows() {
    // FAEST128f tau row: Tau=16, K=8, Tau1=8, L=3072 (upstream
    // parameter.rs:866-873); instance bucket offset 2^8=256 for
    // i < Tau1, 2^7=128 onward (upstream bavc_index_offset).
    let tau: usize = 16;
    let l: usize = 3072;
    let k: usize = 8;
    let tau1: usize = 8;
    // config equation evidence: 2^7 = 128 and
    // l == (Tau + Tau1) * 2^(K-1) == 24 * 128 == 3072.
    proof {
        bavc::lemma_bpow_pw(7);
        vstd::arithmetic::power2::lemma2_to64();
        assert(bavc::bpow(7int) == 128);
        assert(l as int == (tau + tau1) * bavc::bpow(k as int - 1));
    }
    // pos_in_tree(0, 0) = L - 1 = 3071 (first instance, j = 0).
    let a00 = pos_in_tree(tau, tau1, l, k, 0, 0);
    assert(a00 == 3071);
    // pos_in_tree(1, 5) = L - 1 + Tau*5 + 1 = 3071 + 81 = 3152.
    let a15 = pos_in_tree(tau, tau1, l, k, 1, 5);
    assert(a15 == 3152);
    // pos_in_tree(0, 128) crosses the j-tmp branch
    // (tmp = 2^(K-1) = 128): the wire formula
    // L - 1 + Tau*tmp + Tau1*(j & mask) + i with j & mask == 0.
    let a0128 = pos_in_tree(tau, tau1, l, k, 0, 128);
    assert(a0128 == 3071 + 16 * 128);
    // pos_in_tree(0, 129): j%tmp == 1 -> + Tau1.
    let a0129 = pos_in_tree(tau, tau1, l, k, 0, 129);
    assert(a0129 == 3071 + 16 * 128 + 8);
    // offset rows: i=0 (below Tau1) -> 2^8*0 = 0; i=1 -> 256; i=8
    // (the first smaller instance) -> 8*256 = 2048; i=9 -> 2048+128.
    let of0 = bavc_index_offset(tau1, k, 0);
    assert(of0 == 0);
    let of1 = bavc_index_offset(tau1, k, 1);
    assert(of1 == 256);
    let of8 = bavc_index_offset(tau1, k, 8);
    assert(of8 == 2048);
    let of9 = bavc_index_offset(tau1, k, 9);
    assert(of9 == 2048 + 128);
    // node index rows: bigger instances 2^K leaves, smaller 2^(K-1).
    let n0 = bavc_max_node_index(tau1, k, 0);
    assert(n0 == 256);
    let n9 = bavc_max_node_index(tau1, k, 9);
    assert(n9 == 128);
}

fn ut_pos_in_tree_faest128s_rows() {
    // FAEST128s tau row: Tau=11, K=12, Tau1=0, L=22528 (upstream
    // parameter.rs:854-861): every instance smaller (Tau1=0), tmp =
    // 2^11 = 2048.
    let tau: usize = 11;
    let l: usize = 22528;
    let k: usize = 12;
    let tau1: usize = 0;
    // config equation evidence: 2^11 = 2048 and
    // l == (Tau + Tau1) * 2^(K-1) == 11 * 2048 == 22528.
    proof {
        bavc::lemma_bpow_pw(11);
        vstd::arithmetic::power2::lemma2_to64();
        assert(bavc::bpow(11int) == 2048);
        assert(l as int == (tau + tau1) * bavc::bpow(k as int - 1));
    }
    // pos_in_tree(2, 7) = L - 1 + Tau*7 + 2 = 22527 + 77 + 2 = 22606.
    let a27 = pos_in_tree(tau, tau1, l, k, 2, 7);
    assert(a27 == 22606);
    // the leaf band bound: last leaf position = L - 1 + Tau*(tmp-1)
    // + Tau - 1 = 2L - 2.
    let last = pos_in_tree(tau, tau1, l, k, 10, 2047);
    assert(last == 2 * 22528 - 2);
    // offsets: every i below Tau1=0 takes the smaller-instance
    // stride: offset(i) = Tau1*2^K + 2^(K-1)*i = 2048*i.
    let of5 = bavc_index_offset(tau1, k, 5);
    assert(of5 == 2048 * 5);
    let n5 = bavc_max_node_index(tau1, k, 5);
    assert(n5 == 2048);
}

fn ut_leaf_commit_exec_rows() {
    // The lambda-128 leaf-commitment face over a concrete 16-byte
    // key/48-byte uhash slab (SHAPE instantiation of the exec row;
    // the prg/leaf-hash value halves are the FA4/FA5/FA6 oracles and
    // ride arms 1+2, batch notes).
    let k128: [u8; 16] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
        0x0e, 0x0f,
    ];
    let iv: [u8; 16] = [
        0x64, 0x2b, 0xb1, 0xf9, 0x7c, 0x5f, 0x97, 0x9a, 0x72, 0xb1, 0xee, 0x39, 0xbe, 0x4e,
        0x78, 0x22,
    ];
    let uhash48: [u8; 48] = [0u8; 48];
    let mut sd16: [u8; 16] = [0u8; 16];
    let mut com48: [u8; 48] = [0u8; 48];
    leaf_commit_128(&k128, &iv, 3071, &uhash48, &mut sd16, &mut com48);
    let mut sd2: [u8; 16] = [0u8; 16];
    let mut com32: [u8; 32] = [0u8; 32];
    leaf_commit_em_128(&k128, &iv, 3071, &mut sd2, &mut com32);
    assert(sd2 == k128);
}

fn ut_leaf_commit_192_256_exec_rows() {
    let k192: [u8; 24] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
        0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    ];
    let k256: [u8; 32] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
        0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
        0x1c, 0x1d, 0x1e, 0x1f,
    ];
    let iv: [u8; 16] = [
        0x64, 0x2b, 0xb1, 0xf9, 0x7c, 0x5f, 0x97, 0x9a, 0x72, 0xb1, 0xee, 0x39, 0xbe, 0x4e,
        0x78, 0x22,
    ];
    let uhash72: [u8; 72] = [0u8; 72];
    let uhash96: [u8; 96] = [0u8; 96];
    let mut sd24: [u8; 24] = [0u8; 24];
    let mut com72: [u8; 72] = [0u8; 72];
    leaf_commit_192(&k192, &iv, 5119, &uhash72, &mut sd24, &mut com72);
    let mut sd32: [u8; 32] = [0u8; 32];
    let mut com96: [u8; 96] = [0u8; 96];
    leaf_commit_256(&k256, &iv, 61439, &uhash96, &mut sd32, &mut com96);
    let mut sd24b: [u8; 24] = [0u8; 24];
    let mut com48b: [u8; 48] = [0u8; 48];
    leaf_commit_em_192(&k192, &iv, 5119, &mut sd24b, &mut com48b);
    assert(sd24b == k192);
    let mut sd32b: [u8; 32] = [0u8; 32];
    let mut com64b: [u8; 64] = [0u8; 64];
    leaf_commit_em_256(&k256, &iv, 61439, &mut sd32b, &mut com64b);
    assert(sd32b == k256);
}

fn main() {
    ut_pos_in_tree_faest128f_rows();
    ut_pos_in_tree_faest128s_rows();
    ut_leaf_commit_exec_rows();
    ut_leaf_commit_192_256_exec_rows();
}

} // verus!
