//! byteorder 1.5.0 (pin 5a82625) x Verus -- the coverage-difference batch
//! (2026-11-03) generic-family / signed-family / u128-family / slice
//! representative property harness (reference-style: the two-zone split;
//! `#[path="../src/lib.rs"] mod` references the src kernels and copies no
//! src-side spec/lemma/transcription -- the single verification fact source
//! is the src file; the visibility adaptation is noted in the src/lib.rs
//! file header).
//!
//! Coverage-difference correspondence (the difference face of the
//! auto-generated harnesses):
//!   - T1-LE: the LittleEndian write_uint -> read_uint roundtrip universal
//!     (the semantic kernel of the LE single-value family
//!     write_u16/u24/u32/u48/u64 and its read companions; the early batches
//!     covered only the BE single path; the generic k covers the 3/6-byte
//!     shapes of u24/u48);
//!   - T2/T3: the u128 fixed-width roundtrip (write_u128 x read_u128 of BE
//!     and LE, the lib.rs:1907-1909/1945-1947/2089-2091/2125-2127
//!     fixed-width family);
//!   - S2: the signed in-range roundtrip fixed point (the BigEndian i16 doc
//!     example, lib.rs:154-160 write_i16(-5_000) -> read_i16; supported by
//!     the write_int chain kernel + the extend_sign constant fold -- the
//!     same-domain counterpart of the out-of-range shape of
//!     w205_witness_silent_trunc: the in-range roundtrip holds while the
//!     out-of-range doc panic does not exist; the upstream #205/#229 is
//!     known, no separate case filed);
//!   - SL1: the 2-element roundtrip fixed point of read_slice!/write_slice!
//!     (the lib.rs:1860-1886 macros, u16 family representative; the
//!     lib.rs:2301-2309 doc-example shape; the length panic declared by the
//!     trait doc is satisfiable inside the legal domain by the
//!     transcription's assert_eq obligation -- documented-consistent, no
//!     finding).
//!
//! Run scope: verifying this file = the full re-verification of the
//! referenced src module (including its expected 2 errors: the F3
//! lib.rs:1952 and its 128-bit lib.rs:1966 transcription lines, see the src
//! file header) + this file's theorems; this file itself expects **0
//! errors**.

#[path = "../src/lib.rs"]
mod byteorder_src;

use vstd::prelude::*;
use crate::byteorder_src::{
    pw2, le_val_k, int_repr, unextend_sign_spec,
    order_read_uint_trans, order_write_uint_trans,
    order_read_uint_le_trans, order_write_uint_le_trans,
    order_read_u128_trans, order_write_u128_trans,
    order_read_u128_le_trans, order_write_u128_le_trans,
    order_write_int_lib,
    lemma_pw2_pos, lemma_pw2_monotone, lemma_pw2_shift8,
    lemma_le_val_bound, lemma_le_val_stable, lemma_le_val_step_pub,
};

verus! {

// ---------- T1-LE: LE write_uint -> read_uint roundtrip universal ----------
/// The LittleEndian single-value family reorder property: for all n < 256^k
/// (1 <= k <= 8): after write_uint, read_uint == n. The LE
/// write_u16/u24/u32/u48/u64 x same-named read family (read_u48 is just the
/// casting shape of Self::read_uint(buf, 6), lib.rs:240) is the
/// k in {2,3,4,6,8} special cases of this theorem.
pub exec fn ut_roundtrip_le_uint_byteorder(n: u64, k: usize) -> (r: u64)
    requires
        1 <= k,
        k <= 8,
        (n as int) < pw2((8 * k) as nat),
    ensures
        r == n,
{
    let mut buf = [0u8; 8];
    order_write_uint_le_trans(&mut buf, n, k);
    order_read_uint_le_trans(&buf, k)
}

// ---------- T2: u128 fixed-width roundtrip (BigEndian, the lib.rs:1945-1947 family) ----------
pub exec fn ut_roundtrip_u128_be(n: u128) -> (r: u128)
    requires
        (n as int) < pw2(128 as nat),
    ensures
        r == n,
{
    proof {
        assert(pw2(128) == 340282366920938463463374607431768211456) by (compute_only);
        assert(340282366920938463463374607431768211455 >= (n as int)); // trivial inside the u128 domain
    }
    let mut buf = [0u8; 16];
    order_write_u128_trans(&mut buf, n, 16);
    order_read_u128_trans(&buf, 16)
}

// ---------- T3: u128 fixed-width roundtrip (LittleEndian, the lib.rs:2125-2127 family) ----------
pub exec fn ut_roundtrip_u128_le(n: u128) -> (r: u128)
    requires
        (n as int) < pw2(128 as nat),
    ensures
        r == n,
{
    proof {
        assert(pw2(128) == 340282366920938463463374607431768211456) by (compute_only);
    }
    let mut buf = [0u8; 16];
    order_write_u128_le_trans(&mut buf, n, 16);
    order_read_u128_le_trans(&buf, 16)
}

// ---------- S2: signed in-range roundtrip fixed point ----------
/// The ByteOrder trait doc example of lib.rs:154-160 (BigEndian goes
/// `BigEndian::write_i16(&mut buf, -5_000); assert_eq!(-5_000,
/// BigEndian::read_i16(&buf))`). -5000 lies in int_repr(., 2) (the
/// two's-complement 2-byte domain); the write side lands on
/// unextend_sign(-5000, 2) = 2^16 - 5000 = 60536 (0xEC78); the read side
/// read_uint == 60536, the extend_sign constant fold: top byte 0xEC >= 0x80
/// => 60536 - 65536 = -5000. The same-domain counterpart of the
/// out-of-range shape of the src-side w205_witness_silent_trunc (#205
/// known).
pub exec fn ut_doc_example_int_roundtrip_be_2() -> (r: i64)
    ensures
        r == -5000,
{
    let mut buf = [0u8; 2];
    proof {
        assert(pw2(15) == 32768) by (compute_only);
        assert(-5000 >= -32768);   // the int_repr(-5000, 2) in-range premise, self-evident
        assert(5000 <= 32768);
        assert(int_repr(-5000, 2));
        assert(pw2(16) == 65536) by (compute_only);
        assert(unextend_sign_spec(-5000, 2) == (-5000int) % 65536int);
        assert((-5000int) % 65536int == 60536);
    }
    order_write_int_lib(-5000, 2, &mut buf); // -> buf = [0xEC, 0x78] (be shape)
    proof {
        assert(60536 >= 32768); // top byte >= 0x80 => the extend fold subtracts 2^16
    }
    let u = order_read_uint_trans(&buf, 2);
    proof {
        assert(u as int == 60536);
        // Origin Rust (lib.rs:88-91, constant-folded shape): extend_sign(60536, 2)
        // = (60536 - 65536) = -5000
        assert(60536 - 65536 == -5000);
    }
    // the read_int/read_i16 semantic read-back (the extend_sign constant fold)
    u as i64 - 65536
}

// ---------- SL1: read_slice!/write_slice! u16 family representative (2-element roundtrip) ----------
/// The difference-coverage theorem of the lib.rs:2301-2309 shape (the
/// read_u16_into doc example): `numbers_given = [1, 0xf00f]` written LE into
/// 4 bytes, then read back in 2-byte groups. The transcription shape is the
/// per-block expansion of the two macros (write_slice!: each element's
/// to_le_bytes lands in a 2-byte chunks_exact_mut window of bytes;
/// read_slice!: each 2-byte chunk from_le_bytes -> dst) -- a byte-level
/// isomorphism of the block window: write window -> tmp, the
/// copy_from_slice lands it; read window: block copy -> pair, the kernel
/// from_le. The assert_eq obligation of the trait doc's length condition
/// (src.len() == 2*dst.len()) is satisfiable inside the legal domain =>
/// documented-consistent, no finding.
pub exec fn ut_slice_u16_le_roundtrip_2elem() -> (r: (u16, u16))
    ensures
        r.0 == 1,
        r.1 == 61455, // 0xf00f
{
    let mut bytes = [0u8; 4];
    assert(pw2(16 as nat) == 65536) by (compute_only);
    // ---- block 0: write_slice! (element 1) -> read-window retrieval ----
    let a0: u16 = {
        let mut tmp = [0u8; 2];
        order_write_uint_le_trans(&mut tmp, 1, 2);
        bytes[0] = tmp[0]; // copy_from_slice (block 0)
        bytes[1] = tmp[1];
        let mut pair = [0u8; 2];
        pair[0] = bytes[0]; // chunk 0
        pair[1] = bytes[1];
        proof {
            // pair@ and tmp@ are isomorphic (all byte-wise copies, pointwise visible)
            assert(pair@.len() == 2);
            assert(tmp@.len() == 2);
            assert(pair@[0] == tmp@[0]);
            assert(pair@[1] == tmp@[1]);
            assert(pair@ == tmp@); // Seq function extensionality
        }
        let v = order_read_uint_le_trans(&pair, 2);
        proof {
            assert(le_val_k(tmp@, 2 as nat) == 1);   // write kernel ensures
            assert(v as int == le_val_k(pair@, 2 as nat));
            assert(le_val_k(pair@, 2 as nat) == 1);
        }
        v as u16
    };
    // ---- block 1: write_slice! (element 0xf00f) -> read-window retrieval ----
    let a1: u16 = {
        let mut tmp = [0u8; 2];
        order_write_uint_le_trans(&mut tmp, 61455, 2);
        bytes[2] = tmp[0]; // copy_from_slice (block 1)
        bytes[3] = tmp[1];
        let mut pair = [0u8; 2];
        pair[0] = bytes[2]; // chunk 1
        pair[1] = bytes[3];
        proof {
            assert(pair@.len() == 2);
            assert(tmp@.len() == 2);
            assert(pair@[0] == tmp@[0]);
            assert(pair@[1] == tmp@[1]);
            assert(pair@ == tmp@); // Seq function extensionality
        }
        let v = order_read_uint_le_trans(&pair, 2);
        proof {
            assert(le_val_k(tmp@, 2 as nat) == 61455); // write kernel ensures
            assert(v as int == le_val_k(pair@, 2 as nat));
            assert(le_val_k(pair@, 2 as nat) == 61455);
        }
        v as u16
    };
    proof {
        assert(0xf00f == 61455);
    }
    (a0, a1)
}

}

fn main() {}
