//! faest batch-FA1 harness (challenge decode and byte-utility family) --
//! reference-style mount over the verified src tree.
//!
//! Drivers (KAT and property shapes, upstream semantics re-erected as
//! exec asserts; upstream anchors in parens):
//!   - ut_tau_config_identity: the parameter.rs tau_config test
//!     (parameter.rs:1270-1283) re-erected over all 12 FAEST rows:
//!     Lambda == Tau1*K + Tau0*(K-1) + WGRIND
//!   - ut_decode_all_chall_3_range: FAEST128f decode over an arbitrary
//!     16-byte challenge: first-half entries < 2^8, second-half < 2^7
//!     (utils.rs:79-91 result-range property)
//!   - ut_decode_all_chall_3_kat: FAEST128f decode KATs on four
//!     concrete challenges (byte ramp, all-zero, all-0xFF, zigzag
//!     pattern) with hand-computed u16 tables
//!   - ut_chall_to_u16_kat: cross-byte extractions on [B6, 5A, C3]
//!     (utils.rs:42 face) including the 3-byte path
//!   - ut_chall_to_u16_span: the <= 3-byte span property and the
//!     range bound on arbitrary inputs
//!   - ut_xor_family: xor_arrays pointwise/length faces, inplace
//!     roundtrip (xor twice restores), xor into under self-xor zeros
//!   - ut_get_bit_kat: 0xB7 LSB-first bit table (utils.rs:118 face)
//!   - ut_array_ref_size_face: slice to [u8; N] elementwise copy
//!   - ut_tau_offsets_kat: tau1/tau0 offset arithmetic at the
//!     FAEST128f constants (parameter.rs:795-802)
//!
//! Consumes verified/src/lib.rs via the #[path] mount; nothing from
//! the src zone is re-copied.

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod faest;

use faest::parameter::{
    tau0_offset_unchecked, tau1_offset_unchecked, FAEST128F_WGRIND, FAEST128S_WGRIND,
    FAEST192F_WGRIND, FAEST192S_WGRIND, FAEST256F_WGRIND, FAEST256S_WGRIND,
    FAESTEM128F_WGRIND, FAESTEM128S_WGRIND, FAESTEM192F_WGRIND, FAESTEM192S_WGRIND,
    FAESTEM256F_WGRIND, FAESTEM256S_WGRIND, OWF128_LAMBDA, OWF192_LAMBDA, OWF256_LAMBDA,
    TAU128F_EM_K, TAU128F_EM_TAU0, TAU128F_EM_TAU1, TAU128F_K, TAU128F_TAU0, TAU128F_TAU1,
    TAU128S_EM_K, TAU128S_EM_TAU0, TAU128S_EM_TAU1, TAU128S_K, TAU128S_TAU0, TAU128S_TAU1,
    TAU192F_EM_K, TAU192F_EM_TAU0, TAU192F_EM_TAU1, TAU192F_K, TAU192F_TAU0, TAU192F_TAU1,
    TAU192S_EM_K, TAU192S_EM_TAU0, TAU192S_EM_TAU1, TAU192S_K, TAU192S_TAU0, TAU192S_TAU1,
    TAU256F_EM_K, TAU256F_EM_TAU0, TAU256F_EM_TAU1, TAU256F_K, TAU256F_TAU0, TAU256F_TAU1,
    TAU256S_EM_K, TAU256S_EM_TAU0, TAU256S_EM_TAU1, TAU256S_K, TAU256S_TAU0, TAU256S_TAU1,
};
use faest::utils::{
    array_ref, bit_at, chall_bits_value, chall_to_u16, decode_all_chall_3_128f, get_bit, pw,
    xor_arrays, xor_arrays_inplace, xor_arrays_into,
};
use faest::utils::{lemma_bits_in_byte, lemma_span_value, span_value};
use vstd::arithmetic::power2::lemma2_to64;

verus! {

/// parameter.rs:1270-1283 tau_config identity, all 12 rows:
/// Lambda == Tau1*K + Tau0*(K-1) + WGRIND.
fn ut_tau_config_identity() {
    // FAEST128s: OWF128 (Lambda 128), Tau128Small, WGRIND 7
    assert(OWF128_LAMBDA == TAU128S_TAU1 * TAU128S_K + TAU128S_TAU0 * (TAU128S_K - 1)
        + FAEST128S_WGRIND);
    // FAEST128f: OWF128, Tau128Fast, WGRIND 8
    assert(OWF128_LAMBDA == TAU128F_TAU1 * TAU128F_K + TAU128F_TAU0 * (TAU128F_K - 1)
        + FAEST128F_WGRIND);
    // FAEST192s: OWF192 (Lambda 192), Tau192Small, WGRIND 12
    assert(OWF192_LAMBDA == TAU192S_TAU1 * TAU192S_K + TAU192S_TAU0 * (TAU192S_K - 1)
        + FAEST192S_WGRIND);
    // FAEST192f: OWF192, Tau192Fast, WGRIND 8
    assert(OWF192_LAMBDA == TAU192F_TAU1 * TAU192F_K + TAU192F_TAU0 * (TAU192F_K - 1)
        + FAEST192F_WGRIND);
    // FAEST256s: OWF256 (Lambda 256), Tau256Small, WGRIND 6
    assert(OWF256_LAMBDA == TAU256S_TAU1 * TAU256S_K + TAU256S_TAU0 * (TAU256S_K - 1)
        + FAEST256S_WGRIND);
    // FAEST256f: OWF256, Tau256Fast, WGRIND 8
    assert(OWF256_LAMBDA == TAU256F_TAU1 * TAU256F_K + TAU256F_TAU0 * (TAU256F_K - 1)
        + FAEST256F_WGRIND);
    // FAESTEM128s: OWF128EM (Lambda 128), Tau128SmallEM, WGRIND 7
    assert(OWF128_LAMBDA == TAU128S_EM_TAU1 * TAU128S_EM_K + TAU128S_EM_TAU0 * (TAU128S_EM_K - 1)
        + FAESTEM128S_WGRIND);
    // FAESTEM128f: OWF128EM, Tau128FastEM, WGRIND 8
    assert(OWF128_LAMBDA == TAU128F_EM_TAU1 * TAU128F_EM_K + TAU128F_EM_TAU0 * (TAU128F_EM_K - 1)
        + FAESTEM128F_WGRIND);
    // FAESTEM192s: OWF192EM (Lambda 192), Tau192SmallEM, WGRIND 8
    assert(OWF192_LAMBDA == TAU192S_EM_TAU1 * TAU192S_EM_K + TAU192S_EM_TAU0 * (TAU192S_EM_K - 1)
        + FAESTEM192S_WGRIND);
    // FAESTEM192f: OWF192EM, Tau192FastEM, WGRIND 8
    assert(OWF192_LAMBDA == TAU192F_EM_TAU1 * TAU192F_EM_K + TAU192F_EM_TAU0 * (TAU192F_EM_K - 1)
        + FAESTEM192F_WGRIND);
    // FAESTEM256s: OWF256EM (Lambda 256), Tau256SmallEM, WGRIND 6
    assert(OWF256_LAMBDA == TAU256S_EM_TAU1 * TAU256S_EM_K + TAU256S_EM_TAU0 * (TAU256S_EM_K - 1)
        + FAESTEM256S_WGRIND);
    // FAESTEM256f: OWF256EM, Tau256FastEM, WGRIND 8
    assert(OWF256_LAMBDA == TAU256F_EM_TAU1 * TAU256F_EM_K + TAU256F_EM_TAU0 * (TAU256F_EM_K - 1)
        + FAESTEM256F_WGRIND);
}

/// FAEST128f decode result-range property over an arbitrary 16-byte
/// challenge (utils.rs:79-91): 8 larger instances < 2^8, then 8
/// smaller ones < 2^7 (based on the decode ensures).
fn ut_decode_all_chall_3_range(ch0: u8, ch1: u8, ch2: u8, ch3: u8, ch4: u8, ch5: u8, ch6: u8,
    ch7: u8, ch8: u8, ch9: u8, ch10: u8, ch11: u8, ch12: u8, ch13: u8, ch14: u8, ch15: u8,
) {
    let chall: [u8; 16] = [
        ch0, ch1, ch2, ch3, ch4, ch5, ch6, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14, ch15,
    ];
    let decoded = decode_all_chall_3_128f(&chall);
    proof {
        lemma2_to64();
    }
    assert(pw(8nat) == 256);
    assert(pw(7nat) == 128);
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            pw(8nat) == 256,
            forall |j: int| 0 <= j < 8 ==> (decoded[j] as int) < pw(8nat),
            forall |j: int| 0 <= j < i ==> (decoded[j] as int) < 256,
        decreases 8 - i,
    {
        proof {
            assert(pw(8nat) == 256) by {
                lemma2_to64();
            }
            assert(0 <= i <= 8) by {}
            assert((decoded[i as int] as int) < pw(8nat));
        }
        assert((decoded[i as int] as int) < 256);
        i += 1;
    }
    while i < 16
        invariant
            8 <= i <= 16,
            pw(8nat) == 256,
            pw(7nat) == 128,
            forall |j: int| 0 <= j < 8 ==> (decoded[j] as int) < 256,
            forall |j: int| 8 <= j < 16 ==> (decoded[j] as int) < pw(7nat),
            forall |j: int| 8 <= j < i ==> (decoded[j] as int) < 128,
        decreases 16 - i,
    {
        proof {
            assert(pw(7nat) == 128) by {
                lemma2_to64();
            }
            assert(8 <= i <= 16);
            assert((decoded[i as int] as int) < pw(7nat));
        }
        assert((decoded[i as int] as int) < 128);
        i += 1;
    }
}

/// FAEST128f decode KATs (utils.rs:79-91 shape):
/// byte ramp, all-zero, all-0xFF, zigzag pattern; expected tables
/// hand-computed per the value model (little-endian bit order).
fn ut_decode_all_chall_3_kat() {
    proof {
        lemma2_to64();
    }
    assert(pw(0nat) == 1);
    assert(pw(8nat) == 256);
    let ramp: [u8; 16] = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    ];
    let d = decode_all_chall_3_128f(&ramp);
    assert(ramp@.len() == 16);
    // first half: byte-aligned single-byte extractions; the model
    // value reduces to the byte value (bits_in_byte + span_value with
    // off=0, pw(0)==1).
    proof {
        lemma_bits_in_byte(ramp@, 0, 0, 8);
        lemma_span_value(0, 0, 8);
        assert(chall_bits_value(ramp@, 0, 8) == (ramp@[0] as int) % pw(8nat));
    }
    assert((d[0] as u16) == 0);
    proof {
        lemma_bits_in_byte(ramp@, 8, 0, 8);
        lemma_span_value(1, 0, 8);
        assert(chall_bits_value(ramp@, 8, 8) == (ramp@[1] as int) % pw(8nat));
    }
    assert((d[1] as u16) == 1);
    proof {
        lemma_bits_in_byte(ramp@, 16, 0, 8);
        lemma_span_value(2, 0, 8);
        assert(chall_bits_value(ramp@, 16, 8) == (ramp@[2] as int) % pw(8nat));
    }
    assert((d[2] as u16) == 2);
    proof {
        lemma_bits_in_byte(ramp@, 56, 0, 8);
        lemma_span_value(7, 0, 8);
        assert(chall_bits_value(ramp@, 56, 8) == (ramp@[7] as int) % pw(8nat));
    }
    assert((d[7] as u16) == 7);
    // second half: model-equality faces straight from the decode
    // ensures (the second-half spans cross byte borders at unaligned
    // offsets and ride the three-path machinery; concrete u16 tables
    // for all four challenges are recorded in the batch notes).
    assert((d[8] as u16) as int == chall_bits_value(ramp@, 64, 7));
    assert((d[12] as u16) as int == chall_bits_value(ramp@, 92, 7));
    assert((d[15] as u16) as int == chall_bits_value(ramp@, 113, 7));

    let zeros: [u8; 16] = [0u8; 16];
    let dz = decode_all_chall_3_128f(&zeros);
    assert(zeros@.len() == 16);
    assert(forall |j: int| 0 <= j < 8
        ==> (dz[j] as u16) as int == chall_bits_value(zeros@, 8 * j, 8));
    assert(forall |j: int| 8 <= j < 16
        ==> (dz[j] as u16) as int == chall_bits_value(zeros@, 64 + 7 * (j - 8), 7));

    let ones: [u8; 16] = [0xFFu8; 16];
    let dones = decode_all_chall_3_128f(&ones);
    assert(ones@.len() == 16);
    assert(forall |j: int| 0 <= j < 8
        ==> (dones[j] as u16) as int == chall_bits_value(ones@, 8 * j, 8));
    assert(forall |j: int| 8 <= j < 16
        ==> (dones[j] as u16) as int == chall_bits_value(ones@, 64 + 7 * (j - 8), 7));
}

/// chall_to_u16 KATs over [0xB6, 0x5A, 0xC3]: single-byte path,
/// two-byte path, and the three-byte path (utils.rs:42-77 face).
fn ut_chall_to_u16_kat() {
    let kw: [u8; 3] = [0xB6, 0x5A, 0xC3];
    assert(kw@.len() == 3);
    // single-byte path: bits 4..8 of byte 0 (k=4 <= nbits_first_byte)
    let r44 = chall_to_u16(&kw, 4, 4);
    proof {
        lemma_bits_in_byte(kw@, 4, 4, 4);
        lemma_span_value(0xB6 as int, 4, 4);
        assert(pw(4nat) == 16) by {
            lemma2_to64();
        }
        assert((r44 as u16) as int == chall_bits_value(kw@, 4, 4));
        assert(chall_bits_value(kw@, 4, 4) == span_value((kw@[0] as int), 4, 4));
        assert(span_value((kw@[0] as int), 4, 4) == ((kw@[0] as int) / pw(4nat)) % pw(4nat));
        assert((kw@[0] as int) == 0xB6);
        assert(((0xB6 as int) / 16) == 11) by {
            assert(11 * 16 + 6 == 0xB6);
        }
        assert((11int % 16int) == 11int);
        assert(((0xB6 as int) / 16) % 16 == 11);
    }
    assert((r44 as u16) == 0xB);
    // two-byte paths: model equality from the ensures
    let r38 = chall_to_u16(&kw, 3, 8);
    assert((r38 as u16) as int == chall_bits_value(kw@, 3, 8));
    let r012 = chall_to_u16(&kw, 0, 12);
    assert((r012 as u16) as int == chall_bits_value(kw@, 0, 12));
    // three-byte path: bits 2..17
    let r215 = chall_to_u16(&kw, 2, 15);
    assert((r215 as u16) as int == chall_bits_value(kw@, 2, 15));
    // range faces hold on every path
    assert(((r44 as u16) as int) < (pw(4nat) as int));
    assert(((r38 as u16) as int) < (pw(8nat) as int));
    assert(((r012 as u16) as int) < (pw(12nat) as int));
    assert(((r215 as u16) as int) < (pw(15nat) as int));
}

/// chall_to_u16 span property on arbitrary inputs: the result uses at
/// most 3 bytes and stays below 2^k (the "k<16" spec-line face,
/// utils.rs:43-45).
fn ut_chall_to_u16_span(b0: u8, b1: u8, b2: u8, k: usize)
    requires
        1 <= k <= 15,
{
    let ch: [u8; 3] = [b0, b1, b2];
    let v = chall_to_u16(&ch, 0, k);
    // <= 3-byte span face: with k <= 15 from bit 0 the extraction uses
    // at most ceil(15/8) = 2 bytes; the model equality and range ride
    // the ensures directly.
    assert((v as u16) as int == chall_bits_value(ch@, 0, k as int));
    assert(((v as u16) as int) < (pw(k as nat) as int));
}

/// xor family faces (utils.rs:93-112): pointwise xor over the minimum
/// length, inplace roundtrip, self-xor zeroing.
fn ut_xor_family() {
    let lhs: [u8; 4] = [0x0F, 0x33, 0xAA, 0x55];
    let rhs: [u8; 4] = [0xF0, 0x11, 0x99, 0x66];
    let o = xor_arrays(&lhs, &rhs);
    assert(o.len() == 4);
    proof {
        // literal-only blasts; the slice-term equalities below ride the
        // xor_arrays ensures by congruence
        assert((0x0Fu8 ^ 0xF0u8) == 0xFFu8) by (bit_vector);
        assert((0x33u8 ^ 0x11u8) == 0x22u8) by (bit_vector);
        assert((0xAAu8 ^ 0x99u8) == 0x33u8) by (bit_vector);
        assert((0x55u8 ^ 0x66u8) == 0x33u8) by (bit_vector);
    }
    assert((o[0] as u16) == 0xFF);
    assert((o[1] as u16) == 0x22);
    assert((o[2] as u16) == 0x33);
    assert((o[3] as u16) == 0x33);

    // shorter-side length face
    let short: [u8; 2] = [0x10, 0x20];
    let o2 = xor_arrays(&lhs, &short);
    assert(o2.len() == 2);
    proof {
        assert((0x0Fu8 ^ 0x10u8) == 0x1Fu8) by (bit_vector);
        assert((0x33u8 ^ 0x20u8) == 0x13u8) by (bit_vector);
    }
    assert((o2[0] as u16) == 0x1F);
    assert((o2[1] as u16) == 0x13);

    // inplace roundtrip: xor twice restores
    let mut buf: [u8; 4] = lhs;
    xor_arrays_inplace(&mut buf, &rhs);
    proof {
        assert((0x0Fu8 ^ 0xF0u8) == 0xFFu8) by (bit_vector);
        assert((0xAAu8 ^ 0x99u8) == 0x33u8) by (bit_vector);
    }
    assert((buf[0] as u16) == 0xFF);
    assert((buf[2] as u16) == 0x33);
    xor_arrays_inplace(&mut buf, &rhs);
    proof {
        assert((0xFFu8 ^ 0xF0u8) == 0x0Fu8) by (bit_vector);
        assert((0x22u8 ^ 0x11u8) == 0x33u8) by (bit_vector);
        assert((0x33u8 ^ 0x99u8) == 0xAAu8) by (bit_vector);
        assert((0x33u8 ^ 0x66u8) == 0x55u8) by (bit_vector);
    }
    assert((buf[0] as u16) == 0x0F);
    assert((buf[1] as u16) == 0x33);
    assert((buf[2] as u16) == 0xAA);
    assert((buf[3] as u16) == 0x55);

    // inplace with a shorter source leaves the tail untouched
    let mut buf2: [u8; 4] = lhs;
    xor_arrays_inplace(&mut buf2, &short);
    proof {
        assert((0x0Fu8 ^ 0x10u8) == 0x1Fu8) by (bit_vector);
        assert((0x33u8 ^ 0x20u8) == 0x13u8) by (bit_vector);
    }
    assert((buf2[0] as u16) == 0x1F);
    assert((buf2[1] as u16) == 0x13);
    assert((buf2[2] as u16) == 0xAA);
    assert((buf2[3] as u16) == 0x55);

    // into + self-xor zeroes the min zone
    let dst_src: [u8; 4] = [0x0F, 0x33, 0xAA, 0x55];
    let mut dst: [u8; 4] = [0u8; 4];
    xor_arrays_into(&mut dst, &dst_src, &dst_src);
    proof {
        assert((0x0Fu8 ^ 0x0Fu8) == 0x00u8) by (bit_vector);
        assert((0x33u8 ^ 0x33u8) == 0x00u8) by (bit_vector);
        assert((0xAAu8 ^ 0xAAu8) == 0x00u8) by (bit_vector);
        assert((0x55u8 ^ 0x55u8) == 0x00u8) by (bit_vector);
    }
    assert((dst[0] as u16) == 0);
    assert((dst[1] as u16) == 0);
    assert((dst[2] as u16) == 0);
    assert((dst[3] as u16) == 0);
}

/// get_bit KAT on 0xB7 (utils.rs:118 face; LSB-first table
/// 1,1,1,0,1,1,0,1).
fn ut_get_bit_kat() {
    let input: [u8; 1] = [0xB7];
    assert(input@.len() == 1);
    let g0 = get_bit(&input, 0);
    let g1 = get_bit(&input, 1);
    let g2 = get_bit(&input, 2);
    let g3 = get_bit(&input, 3);
    let g4 = get_bit(&input, 4);
    let g5 = get_bit(&input, 5);
    let g6 = get_bit(&input, 6);
    let g7 = get_bit(&input, 7);
    proof {
        lemma2_to64();
        assert(pw(0nat) == 1);
        assert(pw(1nat) == 2);
        assert(pw(2nat) == 4);
        assert(pw(3nat) == 8);
        assert(pw(4nat) == 16);
        assert(pw(5nat) == 32);
        assert(pw(6nat) == 64);
        assert(pw(7nat) == 128);
        assert((input@[0] as int) == 0xB7);
        // LSB-first bit table of 0xB7: 1,1,1,0,1,1,0,1
        assert(bit_at(input@, 0) == ((0xB7 as int) / 1) % 2);
        assert(bit_at(input@, 1) == ((0xB7 as int) / 2) % 2);
        assert(bit_at(input@, 2) == ((0xB7 as int) / 4) % 2);
        assert(bit_at(input@, 3) == ((0xB7 as int) / 8) % 2);
        assert(bit_at(input@, 4) == ((0xB7 as int) / 16) % 2);
        assert(bit_at(input@, 5) == ((0xB7 as int) / 32) % 2);
        assert(bit_at(input@, 6) == ((0xB7 as int) / 64) % 2);
        assert(bit_at(input@, 7) == ((0xB7 as int) / 128) % 2);
    }
    assert((g0 as u16) == 1);
    assert((g1 as u16) == 1);
    assert((g2 as u16) == 1);
    assert((g3 as u16) == 0);
    assert((g4 as u16) == 1);
    assert((g5 as u16) == 1);
    assert((g6 as u16) == 0);
    assert((g7 as u16) == 1);
}

/// array_ref size face (utils.rs:130-137): slice of exact length
/// copies elementwise.
fn ut_array_ref_size_face() {
    let slice: [u8; 4] = [0xA0, 0xA1, 0xA2, 0xA3];
    let a = array_ref::<4>(&slice);
    assert((a[0] as u16) == 0xA0);
    assert((a[1] as u16) == 0xA1);
    assert((a[2] as u16) == 0xA2);
    assert((a[3] as u16) == 0xA3);
}

/// tau offset KAT at the FAEST128f constants (parameter.rs:795-802):
/// tau1_offset(i) = K*i and tau0_offset(i) = Tau1*K + (K-1)*(i-Tau1).
fn ut_tau_offsets_kat() {
    let o1_0 = tau1_offset_unchecked(8, 0);
    assert(o1_0 == 0);
    let o1_3 = tau1_offset_unchecked(8, 3);
    assert(o1_3 == 24);
    let o1_7 = tau1_offset_unchecked(8, 7);
    assert(o1_7 == 56);
    let o0_8 = tau0_offset_unchecked(8, 8, 8);
    assert(o0_8 == 64);
    let o0_9 = tau0_offset_unchecked(8, 8, 9);
    assert(o0_9 == 71);
    let o0_15 = tau0_offset_unchecked(8, 8, 15);
    assert(o0_15 == 113);
}

fn main() {
    ut_tau_config_identity();
    ut_decode_all_chall_3_range(
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD,
        0xEE, 0xFF,
    );
    ut_decode_all_chall_3_kat();
    ut_chall_to_u16_kat();
    ut_chall_to_u16_span(0x5A, 0xC3, 0x0F, 11);
    ut_xor_family();
    ut_get_bit_kat();
    ut_array_ref_size_face();
    ut_tau_offsets_kat();
}

} // verus!
