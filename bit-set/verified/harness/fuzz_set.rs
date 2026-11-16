//! bit-set 0.11.1 x Verus -- fuzz harness, batch H3 (fuzz_set).
//!
//! Transcription of upstream code/fuzz/src/main.rs `do_test_set`
//! (lines 230-305): the AFL/honggfuzz byte-stream interpreter over
//! `BitSet`. The harness concretizes the input: ops decode from an
//! explicit `&[u8]` read one byte at a time, with the upstream
//! `unwrap_or(0)` padding spelled as the end-of-data default.
//!
//! The obligations carried at every op site (the interpreter's
//! member-pair semantics):
//!   - insert(p) then contains(p) -- the insert/contains pair,
//!     including the double-insert idempotence (the second insert
//!     reports false);
//!   - remove(p) then !contains(p);
//!   - a loop-carried tracked member survives the member-preserving
//!     ops (shrink_to_fit / reserve_len / reserve_len_exact), is
//!     dropped by truncate past its position, and is reset by every
//!     fresh-set op;
//!   - the universe bound stays loop-invariant, so every op's
//!     overflow-facing requires (insert value, shrink length bound,
//!     from_bytes length bound) closes at each call site.
//!
//! Concretization notes (recorded in the batch notes):
//!   - ops 2/11 (the get_ref().to_bytes() round-trip) closed in batch
//!     H4 on the bit-vec byte<->word bridge lemma
//!     (lemma_bytes_roundtrip_member): the rebuilt set keeps every
//!     member below the old universe, the universe is the
//!     byte-aligned width, and the pad region reads false;
//!   - op 7 (black_box display) is the string-format layer;
//!   - op codes >= 16 (the upstream saturating_sub(16) fold-back) are
//!     skipped: the harness drives the bounded code alphabet 0..=15.
//!
//! Reference-style organization: `#[path]` mounts `verified/src/lib.rs`
//! (the established source of verified facts); src-side specs/lemmas
//! are never duplicated here.

#![feature(allocator_api)] // needed by the referenced src assume_specification signature
#![verifier::timeout(240)] // the crate-root timeout face (moved from src/lib.rs)

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod bitset_lib;

verus! {

use bitset_lib::set::{BitSet, bs_at, bs_inv};
#[allow(unused_imports)]
use bitset_lib::bitvec_lib::{bit_at, bytes_for_bits, from_bytes_bit,
    lemma_bytes_roundtrip_member};

/// one decoded argument byte: the upstream `unwrap_or(0)` padding of a
/// byte iterator, materialized as a value/next-index pair.
pub exec fn take_arg(data: &[u8], idx: usize) -> (r: (u8, usize))
    requires
        idx <= data.len(),
    ensures
        (idx as int) < (data.len() as int)
            ==> r.1 == idx + 1 && r.0 == data@[idx as int],
        !((idx as int) < (data.len() as int))
            ==> r.1 == idx && r.0 == 0u8,
    // (the two-way contract of the decode step; the caller guards)
{
    if idx < data.len() {
        (data[idx], idx + 1)
    } else {
        (0u8, idx)
    }
}

/// the decoded argument value: upstream `next_usize!` is a single byte
/// widened to usize (values 0..=255).
pub exec fn arg_value(b: u8) -> (r: usize)
    ensures
        r <= 255,
{
    b as usize
}

/// the concretized do_test_set interpreter: drives the op sequence
/// decoded from `data`, asserting the member-pair obligations at each
/// op site and carrying the tracked-member invariant around the loop.
/// (Loop bodies here see facts only through the invariant list -- the
/// length bounds and anchors live as invariant clauses, not as
/// surrounding linear facts.)
pub exec fn fuzz_set_run(data: &[u8])
    requires
        (data.len() as int) <= 100000, // the concretized input bound
{
    let nl = data.len();
    let mut v = BitSet::new_general();
    let ghost mut t: usize = 0;
    let ghost mut ti: bool = false;
    let mut idx: usize = 0;
    while idx < nl
        invariant
            idx <= nl,
            nl == data.len(),
            bs_inv(&v),
            // the tracked member face: still inserted, still contained
            ti ==> bs_at(&v, t),
            // the carried input facts: the concretized bound and the
            // from_bytes length precondition
            (nl as int) <= 100000,
            (nl as int) <= ((usize::MAX as int) / 8),
            // the universe bound: every op either resets the universe
            // below a byte-decoded argument or grows it by at most 32
            // bits per consumed code byte
            (v.bit_vec.nbits as int)
                <= 8 * (nl as int) + 32 * (idx as int) + 2040,
        decreases
            nl - idx,
    {
        let op = data[idx];
        idx = idx + 1;
        if op == 0u8 {
            // upstream op 0: a fresh empty set
            v = BitSet::new_general();
            proof { ti = false; }
        } else if op == 1u8 {
            // upstream op 1: with_capacity_general(next_usize)
            let (b, i2) = take_arg(data, idx);
            idx = i2;
            let ncap = arg_value(b);
            proof { assert(ncap as int <= 255); }
            v = BitSet::with_capacity_general(ncap);
            proof { ti = false; }
        } else if op == 3u8 || op == 13u8 {
            // upstream ops 3/13: reserve_len, guarded by the
            // CAP_GROWTH face (the argument byte stays unconsumed when
            // the guard declines, matching upstream)
            if v.bit_vec.nbits < 256 {
                let (b, i2) = take_arg(data, idx);
                idx = i2;
                let nlen = arg_value(b);
                proof { assert((nlen as int) < ((usize::MAX as int) / 32)); }
                v.reserve_len(nlen);
                proof {
                    // members survive the reserve: the row keeps both
                    // the storage sequence and the universe
                    if ti {
                        assert(bs_at(&v, t));
                    }
                }
            }
        } else if op == 4u8 || op == 14u8 {
            // upstream ops 4/14: reserve_len_exact, same guard
            if v.bit_vec.nbits < 256 {
                let (b, i2) = take_arg(data, idx);
                idx = i2;
                let nlen = arg_value(b);
                proof { assert((nlen as int) < ((usize::MAX as int) / 32)); }
                v.reserve_len_exact(nlen);
                proof {
                    if ti {
                        assert(bs_at(&v, t));
                    }
                }
            }
        } else if op == 5u8 {
            // upstream op 5: shrink_to_fit. The strengthened contract
            // pins the kept length (universe <= old + 32) and the
            // full-range member preservation (the tracked member
            // survives below the old universe)
            let ghost pre_len = v.bit_vec.storage@.len();
            let ghost pre_nb = v.bit_vec.nbits;
            proof {
                assert((v.bit_vec.nbits as int)
                    < ((usize::MAX as int) / 32));
            }
            v.shrink_to_fit();
            proof {
                assert((v.bit_vec.nbits as int) <= 32 * (pre_len as int));
                assert((pre_len as int) <= (pre_nb as int) / 32 + 1);
                if ti {
                    assert(bs_at(&v, t));
                }
            }
        } else if op == 6u8 {
            // upstream op 6: truncate(next_usize)
            let ghost pre_nb6 = v.bit_vec.nbits;
            let (b, i2) = take_arg(data, idx);
            idx = i2;
            let len = arg_value(b);
            let ghost new_nb = if (len as int) < (pre_nb6 as int) {
                len
            } else {
                pre_nb6
            };
            v.truncate(len);
            // the tracked member survives only below the new universe
            proof {
                ti = ti && ((t as int) < (new_nb as int));
                if ti {
                    assert(bs_at(&v, t));
                }
            }
        } else if op == 8u8 {
            // upstream op 8: remove(next_usize % len), only when
            // nonempty
            let nonempty = v.is_empty();
            if !nonempty {
                let (b, i2) = take_arg(data, idx);
                idx = i2;
                let arg = arg_value(b);
                let len = v.bit_vec.nbits;
                let p = arg % len;
                v.remove(p);
                proof {
                    // the member pair: the removed position is clear;
                    // the tracked face keeps every other member
                    assert(!bs_at(&v, p));
                    ti = ti && (t != p);
                    if ti {
                        assert(bs_at(&v, t));
                    }
                }
            }
        } else if op == 9u8 {
            // upstream op 9: reset -- the empty state, tracked member
            // cleared
            v.reset();
            let ie = v.is_empty();
            proof {
                assert(ie == true);
                ti = false;
            }
        } else if op == 10u8 {
            // upstream op 10: insert(next_usize % (len + 1)) -- the
            // interpreter's member-pair core: inserted is contained,
            // the second insert reports the hit
            let nb = v.bit_vec.nbits;
            proof { assert((nb as int) < (usize::MAX as int)); }
            let (b, i2) = take_arg(data, idx);
            idx = i2;
            let arg = arg_value(b);
            let p = arg % (nb + 1);
            let _r1 = v.insert(p);
            let r2 = v.insert(p);
            proof {
                assert(r2 == false);
                assert(bs_at(&v, p));
                t = p;
                ti = true;
            }
        } else if op == 12u8 {
            // upstream op 12: rebuild from the whole input
            v = BitSet::from_bytes_general(data);
            proof { ti = false; }
        } else if op == 15u8 {
            // upstream op 15: rebuild from a decoded slice
            // (next_u8 length, then that many padded bytes)
            let (b, i2) = take_arg(data, idx);
            idx = i2;
            let count = arg_value(b);
            let mut slice: Vec<u8> = Vec::new();
            let mut k: usize = 0;
            // the decode loop never rewinds idx: the outer decreases
            // face rides this bound through the nested loop
            let ghost pre_idx = idx;
            while k < count
                invariant
                    k <= count,
                    slice@.len() == k,
                    idx <= nl,
                    nl == data.len(),
                    (idx as int) >= (pre_idx as int),
                    bs_inv(&v),
                    ti ==> bs_at(&v, t),
                    (v.bit_vec.nbits as int)
                        <= 8 * (nl as int) + 32 * (idx as int) + 2040,
                decreases
                    count - k,
            {
                let (b2, i3) = take_arg(data, idx);
                idx = i3;
                slice.push(b2);
                k += 1;
            }
            proof {
                assert(slice@.len() <= 255);
                assert(slice@.len() <= ((usize::MAX as int) / 8));
            }
            v = BitSet::from_bytes_general(&slice[..]);
            proof { ti = false; }
        } else if op == 2u8 || op == 11u8 {
            // upstream ops 2/11: rebuild from the serialized image of
            // the current set (the get_ref().to_bytes() round trip).
            // The batch-H4 bit-vec bridge lemma carries the faces: the
            // universe becomes the byte-aligned width
            // (8 * bytes_for_bits), every member below the old
            // universe survives, and the pad region reads false (the
            // upstream to_bytes trailing-fill-with-false doc face).
            let ghost pre_v = v;
            let bytes = v.get_ref().to_bytes();
            let img: &[u8] = &bytes;
            proof {
                // the from_bytes length precondition: the image is the
                // byte ceiling of the (bounded) old universe
                assert((pre_v.bit_vec.nbits as int)
                    <= 8 * (nl as int) + 32 * (idx as int) + 2040);
                assert((bytes.len() as int)
                    == (bytes_for_bits(pre_v.bit_vec.nbits) as int));
                assert((img@.len() as int) <= ((pre_v.bit_vec.nbits as int) / 8) + 1int);
                assert((img@.len() as int) <= ((usize::MAX as int) / 8));
            }
            v = BitSet::from_bytes_general(img);
            proof {
                let ghost pre_nb = pre_v.bit_vec.nbits;
                let ghost new_nb = v.bit_vec.nbits;
                // serial faces: the to_bytes length row (receiver bound
                // through get_ref) and the decode row (the bs_at view of
                // from_bytes_general unfolded to the bit_at model)
                assert((bytes.len() as int) == (bytes_for_bits(pre_nb) as int));
                assert((new_nb as int) == 8 * (img@.len() as int));
                assert forall|i: usize| (i as int) < (new_nb as int) implies
                    (#[trigger] bit_at(v.bit_vec.storage@, new_nb, i)
                        == from_bytes_bit(img@, i)) by {
                    assert(bs_at(&v, i) == (i < new_nb
                        && bit_at(v.bit_vec.storage@, new_nb, i)));
                    assert(bs_at(&v, i) == from_bytes_bit(img@, i));
                }
                // the bridge call: hypotheses are the two postcondition
                // faces above; conclusions carry member preservation
                // and the zero-filled pad
                lemma_bytes_roundtrip_member(
                    pre_v.bit_vec.storage@, pre_nb,
                    v.bit_vec.storage@, new_nb, img@);
                // the byte-alignment pad fits the per-op 32-bit growth
                // budget of the universe bound (no code byte consumed)
                assert((new_nb as int) <= (pre_nb as int) + 7int);
                // the tracked member survives the round trip
                if ti {
                    assert(bs_at(&pre_v, t) == (t < pre_nb
                        && bit_at(pre_v.bit_vec.storage@, pre_nb, t)));
                    assert(bit_at(v.bit_vec.storage@, new_nb, t)
                        == bit_at(pre_v.bit_vec.storage@, pre_nb, t));
                    assert(bs_at(&v, t));
                }
                // the pad region (old universe up to the new one) is
                // memberless
                assert forall|j: usize|
                    (pre_nb as int) <= (j as int) && (j as int) < (new_nb as int) implies
                    !bs_at(&v, j) by {
                    assert(bit_at(v.bit_vec.storage@, new_nb, j) == false);
                }
            }
        } else {
            // op code 7 and every code >= 16: skipped (see the
            // module-level notes)
        }
    }
}

/// a concrete drive of the interpreter: a fixed seed exercising every
/// implemented op arm (the concretized counterpart of the upstream
/// duplicate_crash seed test -- a fixed byte list, decoded by the
/// same semantics, obligations closed op by op).
pub exec fn fuzz_set_seed() -> (r: bool)
    ensures
        r == true,
{
    // ops: 0 fresh | 10 opens the insert arm three times (3, then a
    // larger unaligned position, then a no-op repeat), 6 truncates,
    // 8 removes, 9 resets, 5 shrinks, 1 reserves capacity, 3/4/13/14
    // run both reserve arms, 12 rebuilds from data, 15 rebuilds from
    // a decoded slice, 200 (>= 16) exercises the skip arm, and the
    // 6-then-2-then-11 tail drives both round-trip arms: the first on
    // an unaligned universe (10 bits -> 16, live pad face, tracked
    // member 9 carried through), the second on the aligned one.
    let seed: &[u8] = &[
        0u8,
        10u8, 3u8,
        10u8, 17u8,
        10u8, 3u8,
        6u8, 8u8,
        8u8, 1u8,
        9u8,
        10u8, 2u8,
        5u8,
        1u8, 32u8,
        3u8, 9u8,
        4u8, 200u8,
        13u8, 250u8,
        14u8, 0u8,
        12u8,
        15u8, 2u8, 255u8, 255u8,
        5u8,
        10u8, 9u8,
        6u8, 10u8,
        2u8,
        11u8,
        8u8, 7u8,
        200u8, 99u8,
        6u8, 0u8,
        0u8,
    ];
    fuzz_set_run(seed);
    true
}

} // verus!

fn main() {}
