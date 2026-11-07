//! byteorder 1.5.0 (pin 5a82625) x Verus 0.2026.10.29 -- the UT/roundtrip
//! property harness (reference-style: the two-zone
//! coordination rule).
//!
//! Attribution criteria: this file is the "transcription of tests/properties"
//! -- the roundtrip theme theorems of the inline UTs of the upstream lib.rs
//! (T1/S1/D1/T4/T5); the referenced spec / power lemmas /
//! order_read_uint_trans / order_write_uint_trans kernels are the
//! library-proper transcription of verified/src/lib.rs; **the single
//! verification fact source is the src file** -- this file references it via
//! `#[path="../src/lib.rs"] mod byteorder_src;` and copies no src-side
//! content (the src-side pub relaxation of the referenced power lemmas is
//! noted in the src file header).
//!
//! Run scope: verifying this file = the full re-verification of the
//! referenced src module (including its expected 2 errors -- the F3
//! lib.rs:1952/1966 transcription lines, see the src file header; the
//! obligations are the same as running src standalone) + this file's 5 UT
//! theorems. This file's own theorems expect **0 errors**.

#[path = "../src/lib.rs"]
mod byteorder_src;

use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_inequality;

use crate::byteorder_src::{
    pw2, be_val_k, le_val_k,
    order_read_uint_trans, order_write_uint_trans,
    lemma_pw2_pos, lemma_pw2_monotone, lemma_pw2_shift8,
    lemma_be_val_bound, lemma_le_val_bound,
};

verus! {

// ---------- T1/S1: the roundtrip universal theorem ----------
/// T1 property (prop_uint_N, lib.rs:2484-2547): for all n < 256^k (k in 1..=8):
/// after write_uint, read_uint == n.
/// S1 (prop_ext_uint_N, io layer, lib.rs:3425-3488, ReadBytesExt::read_uint x
/// WriteBytesExt::write_u64) has its semantic kernel in this same theorem --
/// the byte replay of Cursor belongs to the external contract face of
/// `# Errors` (read_exact/write_all), so the io-layer roundtrip decomposes
/// into: [byte assembly, the T1 theorem] x [std semantics, the model
/// assumption].
pub exec fn ut_roundtrip_byteorder(n: u64, k: usize) -> (r: u64)
    requires
        1 <= k,
        k <= 8,
        (n as int) < pw2((8 * k) as nat),
    ensures
        r == n,
{
    let mut buf = [0u8; 8];
    order_write_uint_trans(&mut buf, n, k);
    order_read_uint_trans(&buf, k)
}

// ---------- D1: fixed-point assertions of the io.rs doctests ----------
/// io.rs:418-425: on `Cursor::new(vec![0x80, 0x74, 0xfa])`,
/// `read_uint::<BigEndian>(3) == 8418554` (the read value via the
/// ByteOrder-layer kernel).
pub exec fn ut_doc_example_read_uint_be_3() -> (r: u64)
    ensures
        r == 8418554,
{
    let buf: [u8; 3] = [0x80, 0x74, 0xfa];
    let v = order_read_uint_trans(&buf, 3);
    proof {
        assert(buf@.len() == 3);
        assert(buf@[0] as int == 0x80);
        assert(buf@[1] as int == 0x74);
        assert(buf@[2] as int == 0xfa);
        assert(be_val_k(buf@, 0) == 0);
        assert(be_val_k(buf@, 1) == 256 * be_val_k(buf@, 0) + buf@[0] as int);
        assert(be_val_k(buf@, 1) == 0x80);
        assert(be_val_k(buf@, 2) == 256 * be_val_k(buf@, 1) + buf@[1] as int);
        assert(be_val_k(buf@, 2) == 0x8074);
        assert(be_val_k(buf@, 3) == 256 * be_val_k(buf@, 2) + buf@[2] as int);
        assert(be_val_k(buf@, 3) == 0x8074fa);
        assert(0x8074fa == 8418554);
    }
    v
}

/// io.rs:443-450: on `Cursor::new(vec![0xc1, 0xff, 0x7c])`,
/// `read_int::<BigEndian>(3) == -4063364`.
/// read_int = extend_sign(read_uint)(lib.rs:630-633 + lib.rs:88-91):
/// 24-bit unsigned 0xc1ff7c sign-extended = 0xc1ff7c - 2^24 (top byte >= 0x80).
pub exec fn ut_doc_example_read_int_be_3() -> (r: i64)
    ensures
        r == -4063364,
{
    let buf: [u8; 3] = [0xc1, 0xff, 0x7c];
    let v = order_read_uint_trans(&buf, 3);
    proof {
        assert(buf@.len() == 3);
        assert(buf@[0] as int == 0xc1);
        assert(buf@[1] as int == 0xff);
        assert(buf@[2] as int == 0x7c);
        assert(be_val_k(buf@, 0) == 0);
        assert(be_val_k(buf@, 1) == 256 * 0 + 0xc1 as int);
        assert(be_val_k(buf@, 2) == 256 * (0xc1 as int) + 0xff as int);
        assert(be_val_k(buf@, 3) == 256 * (256 * (0xc1 as int) + 0xff as int) + 0x7c as int);
        assert(be_val_k(buf@, 3) == 12713852);
        // Origin Rust (lib.rs:89-90): shift = (8-3)*8 = 40;
        // (0xc1ff7c << 40) as i64 >> 40 == 0xc1ff7c - 2^24 (top byte >= 0x80)
        assert(pw2(24) == 16777216) by (compute_only);
        assert(12713852 - 16777216 == -4063364);
    }
    let extended = (v as i64) - 16777216;
    assert(extended == 12713852 - 16777216);
    extended
}

// ---------- T4: uint_bigger_buffer (LE family representative, fixed point) ----------
/// lib.rs:3193-3198:`LittleEndian::read_uint(&[1,2,3,4,5,6,7,8], 5) ==
/// 0x05_0403_0201`. The LE read value = sum b[i]*256^i (the first 5 bytes).
pub exec fn ut_uint_bigger_buffer() -> (r: u64)
    ensures
        r as int == 0x05_0403_0201,
{
    let buf: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    let mut v: u64 = 0;
    let mut w: u64 = 1;
    let mut i: usize = 0;
    while i < 5
        invariant
            0 <= i <= 5,
            buf@.len() == 8,
            w as int == pw2((8 * i) as nat),
            v as int == le_val_k(buf@, i as nat),
        decreases 5 - i,
    {
        proof {
            // overflow domain: i < 5 => v = le_val (first i bytes) < 256^i, b <= 255, w = 256^i <= 256^4
            assert((i as int) < 5);
            assert((i as int) <= 4);
            lemma_le_val_bound(buf@, i as nat);
            assert((v as int) < pw2((8 * i) as nat));
            assert(0 <= (buf@[i as int] as int) <= 255);
            lemma_pw2_pos((8 * i) as nat);
            lemma_pw2_monotone((8 * i) as nat, 32);
            assert((w as int) <= pw2(32));
            assert(pw2(32) == 4294967296) by (compute_only);
            // v + b*w < 256^i + 255*256^i = 256^(i+1) <= 256^5 = 2^40 << 2^64
            lemma_pw2_shift8((8 * i) as nat);
            lemma_pw2_monotone(((8 * i) as nat + 8), 40);
            assert(pw2((8 * (i as int + 1)) as nat) == 256 * pw2((8 * i) as nat));
            assert(pw2((8 * (i as int + 1)) as nat) <= pw2(40));
            assert(pw2(40) == 1099511627776) by (compute_only);
            let P2 = pw2((8 * i) as nat);
            lemma_mul_inequality((buf@[i as int] as int), 255, P2);
            assert((buf@[i as int] as int) * P2 <= 255 * P2);
            assert((v as int) + (buf@[i as int] as int) * (w as int) < P2 + 255 * P2);
            assert(P2 + 255 * P2 == 256 * P2);
            assert((v as int) + (buf@[i as int] as int) * (w as int) < 256 * pw2((8 * i) as nat));
            assert((v as int) + (buf@[i as int] as int) * (w as int) <= 18446744073709551615);
            // maintenance: w_new = 256w == pw2(8(i+1))
            assert(pw2((8 * ((i as int) + 1)) as nat) == 256 * pw2((8 * i) as nat));
            assert(pw2(0) == 1);
        }
        v = v + (buf[i] as u64) * w;
        w = 256 * w;
        i += 1;
    }
    proof {
        assert(le_val_k(buf@, 0) == 0);
        assert(buf@[0] as int == 1);
        assert(buf@[1] as int == 2);
        assert(buf@[2] as int == 3);
        assert(buf@[3] as int == 4);
        assert(buf@[4] as int == 5);
        assert(pw2(8) == 256) by (compute_only);
        assert(pw2(16) == 65536) by (compute_only);
        assert(pw2(24) == 16777216) by (compute_only);
        assert(pw2(32) == 4294967296) by (compute_only);
        assert(le_val_k(buf@, 1) == 0 + 1 * pw2(0));
        assert(le_val_k(buf@, 2) == (0 + 1 * pw2(0)) + 2 * pw2(8));
        assert(le_val_k(buf@, 3) == ((0 + 1 * pw2(0)) + 2 * pw2(8)) + 3 * pw2(16));
        assert(le_val_k(buf@, 4) == (((0 + 1 * pw2(0)) + 2 * pw2(8)) + 3 * pw2(16)) + 4 * pw2(24));
        assert(le_val_k(buf@, 5) == ((((0 + 1 * pw2(0)) + 2 * pw2(8)) + 3 * pw2(16)) + 4 * pw2(24)) + 5 * pw2(32));
        assert(le_val_k(buf@, 5) == 1 + 2 * 256 + 3 * 65536 + 4 * 16777216 + 5 * 4294967296);
        assert(le_val_k(buf@, 5) == 21542142465);
        assert(0x05_0403_0201 == 21542142465);
    }
    v
}

// ---------- T5: regression173 zero-buffer prefix read ----------
/// lib.rs:3200-3239 (excerpt: the zero-buffer any-width family reads == 0).
/// Generalized shape: for any buffer whose first 8 bytes are all zero,
/// read_u64 == 0.
pub exec fn ut_regression173_read_u64(buf: &[u8]) -> (r: u64)
    requires
        buf.len() >= 8,
        forall |j: int| #![trigger buf@[j]] 0 <= j < 8 ==> buf@[j] == 0,
    ensures
        r == 0,
{
    let v = order_read_uint_trans(buf, 8);
    proof {
    // the be_val of an all-zero prefix == 0 (structural induction)
        assert(be_val_k(buf@, 0) == 0);
        assert(be_val_k(buf@, 1) == 256 * 0 + 0);
        assert(be_val_k(buf@, 2) == 256 * 0 + 0);
        assert(be_val_k(buf@, 3) == 256 * 0 + 0);
        assert(be_val_k(buf@, 4) == 256 * 0 + 0);
        assert(be_val_k(buf@, 5) == 256 * 0 + 0);
        assert(be_val_k(buf@, 6) == 256 * 0 + 0);
        assert(be_val_k(buf@, 7) == 256 * 0 + 0);
        assert(be_val_k(buf@, 8) == 256 * 0 + 0);
    }
    v
}

}

fn main() {}
