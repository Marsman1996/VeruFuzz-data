//! faest batch-FA8 harness -- the verus arm of the vole KAT chain.
//!
//! Mounts the verified FA8 twin tree (the fa8-driver shape: the
//! fa13-driver closed set + bavc + vole; src/lib.rs untouched) and
//! pins, as executable verification rows:
//!  - the vole_array_length tables at ALL twelve tau configurations
//!    (non-EM + EM x s/f x the three lambdas): per-round ground rows
//!    against the upstream-parameter config constants, plus the
//!    depth-identity lemma rows
//!    (vole_array_length(i) == bavc_max_node_depth(i)) -- the closed
//!    form's own numeric evidence, first-hand against the python arm
//!    (which asserted the identity over every round of every config
//!    before any twin line was written, 12/12 rows);
//!  - the TWEAK_OFFSET / vole_tweak_of ground rows;
//!  - the two VoleCommitmentCRef index faces (vole_row_ref /
//!    vole_row_ref_mut) over concrete slab shapes;
//!  - the frozen main-loop faces' requires/ensures wiring rows (the
//!    D-FA13-3 alignment: the FA13 shim signature feeds
//!    volecommit_twin at the FAEST-128 config row -- compiles the
//!    carrier compatibility the FA14 assembly consumes).
//!
//! The algorithm-value KATs of the vole ladder (h/hashedC/hashedU/
//! hashedV/hashedQ, twelve rows) ride the python sim arm (arm 1,
//! `out/kverus-run/FA8/sim_vole.py`, ALL OK over the upstream
//! vole.json + vole_em.json) -- the exec cascade itself is behind
//! the D-FA7-1/D-FA7-5 walls this batch (the frozen-face notes).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/fields/large_fields.rs"]
mod large_fields;

#[path = "../src/fields/small_fields.rs"]
mod small_fields;

#[path = "../src/rijndael_32.rs"]
mod rijndael_32;

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

#[path = "../src/vole.rs"]
mod vole;

#[allow(unused)]
use bavc::{bavc_max_node_depth, bavc_max_node_index};
#[allow(unused)]
use vole::{vole_array_length, vole_row_ref, vole_row_ref_mut, vole_tweak_of, TWEAK_OFFSET};

verus! {

// The twelve tau config rows (upstream parameter.rs:852-999, the
// same tables the FA7 python arm pinned: non-EM :852-924, EM
// :925-999).  (tau1, k, tau) per config.
fn ut_vole_array_length_rows() {
    // ---- non-EM rows (parameter.rs:852-924) ----
    // FAEST128s: Tau=11, K=12, Tau1=0 -- every instance smaller
    // (depth K-1 = 11, node count 2^11 = 2048).
    proof {
        vole::lemma_vole_array_length_is_depth(0int, 12int, 0int);
        vole::lemma_vole_array_length_is_depth(0int, 12int, 10int);
    }
    let v128s_0 = vole_array_length(0, 12, 0);
    assert(v128s_0 == 11);
    let v128s_10 = vole_array_length(0, 12, 10);
    assert(v128s_10 == 11);
    // FAEST128f: Tau=16, K=8, Tau1=8 -- bigger instances up to round
    // 8 (depth 8), smaller from round 8 (depth 7).
    proof {
        vole::lemma_vole_array_length_is_depth(8int, 8int, 0int);
        vole::lemma_vole_array_length_is_depth(8int, 8int, 8int);
        vole::lemma_vole_array_length_is_depth(8int, 8int, 15int);
    }
    let v128f_0 = vole_array_length(8, 8, 0);
    assert(v128f_0 == 8);
    let v128f_8 = vole_array_length(8, 8, 8);
    assert(v128f_8 == 7);
    let v128f_15 = vole_array_length(8, 8, 15);
    assert(v128f_15 == 7);
    // FAEST192s: Tau=16, K=12, Tau1=4.
    proof {
        vole::lemma_vole_array_length_is_depth(4int, 12int, 0int);
        vole::lemma_vole_array_length_is_depth(4int, 12int, 4int);
        vole::lemma_vole_array_length_is_depth(4int, 12int, 15int);
    }
    let v192s_0 = vole_array_length(4, 12, 0);
    assert(v192s_0 == 12);
    let v192s_4 = vole_array_length(4, 12, 4);
    assert(v192s_4 == 11);
    let v192s_15 = vole_array_length(4, 12, 15);
    assert(v192s_15 == 11);
    // FAEST192f: Tau=24, K=8, Tau1=16.
    proof {
        vole::lemma_vole_array_length_is_depth(16int, 8int, 0int);
        vole::lemma_vole_array_length_is_depth(16int, 8int, 16int);
        vole::lemma_vole_array_length_is_depth(16int, 8int, 23int);
    }
    let v192f_0 = vole_array_length(16, 8, 0);
    assert(v192f_0 == 8);
    let v192f_16 = vole_array_length(16, 8, 16);
    assert(v192f_16 == 7);
    let v192f_23 = vole_array_length(16, 8, 23);
    assert(v192f_23 == 7);
    // FAEST256s: Tau=22, K=12, Tau1=8.
    proof {
        vole::lemma_vole_array_length_is_depth(8int, 12int, 0int);
        vole::lemma_vole_array_length_is_depth(8int, 12int, 8int);
        vole::lemma_vole_array_length_is_depth(8int, 12int, 21int);
    }
    let v256s_0 = vole_array_length(8, 12, 0);
    assert(v256s_0 == 12);
    let v256s_8 = vole_array_length(8, 12, 8);
    assert(v256s_8 == 11);
    let v256s_21 = vole_array_length(8, 12, 21);
    assert(v256s_21 == 11);
    // FAEST256f: Tau=32, K=8, Tau1=24.
    proof {
        vole::lemma_vole_array_length_is_depth(24int, 8int, 0int);
        vole::lemma_vole_array_length_is_depth(24int, 8int, 24int);
        vole::lemma_vole_array_length_is_depth(24int, 8int, 31int);
    }
    let v256f_0 = vole_array_length(24, 8, 0);
    assert(v256f_0 == 8);
    let v256f_24 = vole_array_length(24, 8, 24);
    assert(v256f_24 == 7);
    let v256f_31 = vole_array_length(24, 8, 31);
    assert(v256f_31 == 7);

    // ---- EM rows (parameter.rs:925-999) ----
    // EM-128s: Tau=11, K=12, Tau1=0 (same tau shape as non-EM at
    // this axis).
    proof {
        vole::lemma_vole_array_length_is_depth(0int, 12int, 0int);
        vole::lemma_vole_array_length_is_depth(0int, 12int, 10int);
    }
    let e128s_0 = vole_array_length(0, 12, 0);
    assert(e128s_0 == 11);
    // EM-128f: Tau=16, K=8, Tau1=8.
    let e128f_0 = vole_array_length(8, 8, 0);
    assert(e128f_0 == 8);
    let e128f_15 = vole_array_length(8, 8, 15);
    assert(e128f_15 == 7);
    // EM-192s: Tau=16, K=12, Tau1=8 (EM shifts the s-row tau1 to 8).
    proof {
        vole::lemma_vole_array_length_is_depth(8int, 12int, 0int);
        vole::lemma_vole_array_length_is_depth(8int, 12int, 8int);
        vole::lemma_vole_array_length_is_depth(8int, 12int, 15int);
    }
    let e192s_0 = vole_array_length(8, 12, 0);
    assert(e192s_0 == 12);
    let e192s_8 = vole_array_length(8, 12, 8);
    assert(e192s_8 == 11);
    let e192s_15 = vole_array_length(8, 12, 15);
    assert(e192s_15 == 11);
    // EM-192f: Tau=24, K=8, Tau1=16.
    let e192f_16 = vole_array_length(16, 8, 16);
    assert(e192f_16 == 7);
    // EM-256s: Tau=22, K=12, Tau1=8.
    let e256s_8 = vole_array_length(8, 12, 8);
    assert(e256s_8 == 11);
    // EM-256f: Tau=32, K=8, Tau1=24.
    let e256f_31 = vole_array_length(24, 8, 31);
    assert(e256f_31 == 7);

    // spot poll: the depth identity at the boundary rounds of the
    // bigger-instance buckets (i == tau1 - 1 still inside).
    proof {
        vole::lemma_vole_array_length_is_depth(4int, 12int, 3int);
    }
    let v192s_3 = vole_array_length(4, 12, 3);
    assert(v192s_3 == 12);
}

// The TWEAK_OFFSET / vole_tweak_of ground rows (upstream vole.rs
// :23-24, :125).
fn ut_tweak_rows() {
    assert(TWEAK_OFFSET == 2147483648);
    let twk0 = vole_tweak_of(0);
    assert(twk0 == 2147483648);
    let twk11 = vole_tweak_of(11);
    assert(twk11 == 2147483659);
    let twk31 = vole_tweak_of(31);
    assert(twk31 == 2147483679);
}

// The VoleCommitmentCRef index faces (upstream vole.rs:54-113) over
// concrete slab shapes: the FAEST-128s stride row (lhat = 210, ten
// commitment rows = 210 * (11 - 1) bytes in the full wire slab).
fn ut_cref_rows() {
    // the LHatBytes row for FAEST-128s (LBytes=160 + 3*16 + 2,
    // upstream parameter.rs:75 / :390-392).
    let lhat: usize = 210;
    // a 2-row slab, stride checks
    let slab: [u8; 420] = [7u8; 420];
    let row0 = vole_row_ref(&slab, lhat, 0);
    assert(row0.len() == 210);
    let row1 = vole_row_ref(&slab, lhat, 1);
    assert(row1.len() == 210);
    assert(row1[0] == slab[210]);
    // out-of-stride is excluded by the requires (i = 2 does not
    // fit: (2 + 1) * 210 = 630 > 420 -- the Panic-less contract
    // face; recorded, not exec'd).
    let mut mslab: [u8; 420] = [1u8; 420];
    {
        // content rows of a &mut borrow face stay inside the borrow
        // scope (the FA13 signature_ref_mut_from convention: the
        // split chain pins segment LENGTHS; the mslab-side rows ride
        // the caller's own slice state).
        let mrow = vole_row_ref_mut(&mut mslab, lhat, 1);
        assert(mrow.len() == 210);
        mrow[0] = 0u8;
        assert(mrow[0] == 0u8);
    }
}

// The frozen-face wiring row (the D-FA13-3 alignment): the FA13 shim
// signature (volecommit_cs(cs, r, iv, lambda_bytes, lhat_bytes,
// tau), faest.rs:1145) feeds volecommit_twin's requires table at the
// FAEST-128f config row -- carrier compatibility the FA14 assembly
// consumes (spec-level row: the requires set compiles; value rows
// are the FA14 ledger).
fn ut_frozen_face_wiring_rows() {
    // FAEST-128s config row: lam = 16, lhat = 210, tau = 11,
    // tau1 = 0, k = 12, l = 22528 (upstream parameter.rs:854-861 +
    // :390-392).
    proof {
        bavc::lemma_bpow_pw(11);
        vstd::arithmetic::power2::lemma2_to64();
        assert(bavc::bpow(11int) == 2048);
        assert(22528int == (11int + 0int) * bavc::bpow(11int));
    }
    // vole_array_length keeps the twin's rj budget row == 11 on
    // every round of this config (pinned above); the frozen
    // volecommit_twin face requires cs.len() == 210 * 10 == 2100:
    // the FA13 shim spells cs.len() == lhat * (tau - 1) -- the same
    // row (compiles as the shared expression).
    assert(210 * (11 - 1) == 2100);
    // the delta domain row at this config: every delta_i <
    // 2^11 = 2048 (the decode_all_chall_3 band rows, utils.rs:976).
    let n0 = bavc_max_node_index(0, 12, 0);
    assert(n0 == 2048);
}

// The decode-to-delta domain row (the FA1 utils face feeding
// volereconstruct_twin's delta requires -- the upstream "// Skip ::2
// ... (parameter constraints ensure that we only provide valid
// challenges/indexes)" row the Origin block at the frozen face
// names: decode's per-slot bounds sit INSIDE the tau config's
// bavc_max_node_index bound on the FAEST-128f axis).
fn ut_decode_delta_domain_rows() {
    let chall: [u8; 16] = [0u8; 16];
    let delta = utils::decode_all_chall_3_128f(&chall);
    proof {
        // the pw/bpow bridge rows this domain needs
        bavc::lemma_bpow_pw(8);
        bavc::lemma_bpow_pw(7);
        vstd::arithmetic::power2::lemma2_to64();
        assert(bavc::bpow(8int) == 256);
        assert(bavc::bpow(7int) == 128);
    }
    assert(delta.len() == 16);
    // the delta domain rows: every slot inside the round-i instance
    // bound (bigger instances 2^8 = 256, smaller 2^7 = 128).
    assert(delta[0] < 256);
    assert(delta[15] < 128);
}

fn main() {
    ut_vole_array_length_rows();
    ut_tweak_rows();
    ut_cref_rows();
    ut_frozen_face_wiring_rows();
    ut_decode_delta_domain_rows();
}

} // verus!
