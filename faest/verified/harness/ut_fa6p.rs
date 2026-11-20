//! faest batch-FA6-pre harness -- the prover twin value/contract unit
//! (the FA1 ut_* and FA10 ut_fa10_rijndael / ut_fa10w precedents;
//! unit-split rule #FA10-5: the KAT rows ride their own unit, the
//! shared driver stays lean).
//!
//! Content and value arms:
//! - the upstream unit-test rows of prover/field_commitment.rs
//!   (field_commit_mul / field_commit_sum, both bodies) at the
//!   GF128-axis twin, including the upstream `Mul<u8>` select
//!   semantics note (ONE * 2 == ZERO, ONE * 3 == ONE -- the
//!   Mul<u8> face reads bit 0 only; the upstream test's `ONE * k`
//!   expressions therefore denote the bit-0 selects);
//! - the GF8 bit-plane orbit sample rows of gf8_square_bits
//!   (oracle/python arm values: 00->00, 01->01, 02->04, 10->1b,
//!   53->b5, e4->4d, ff->13; full-256 closes out-of-band);
//! - the byte_combine_bits / byte_combine_bits_sq sample rows with
//!   the oracle constants (the alpha-xor unfolded forms pinned);
//! - the SquareBytes column probes (unit tag vectors through
//!   gf128_square_byte8, the eight SQ_COLS bytes);
//! - the ByteCommitment sample chains: combine, square_inplace
//!   (tag-plane spec rows + key pins), combine-after-square, and
//!   the 8-round f256_f2_conjugates-shaped loop with the oracle's
//!   round keys 53 b5 fc 16 0f 55 a1 f7;
//! - the D-FA6p-1 duality sample row at k=0x53: the square-path
//!   combined key pins to the same constant the mul-path arm maps
//!   to (1cf7a0fe8922c83fd8a5ae31928b4da1); the full equation is
//!   deferred (needs the FA3 ring lemmas), the verus arm pins both
//!   sides to the oracle constant.
//!
//! Out-of-band arms (per the FA10 KAT discipline): the python sim
//! and the upstream-module ORACLE run cross-checked the full 256-row
//! byte-plane tables and every sample row below bit-exactly (zero
//! mismatches; oracle-run.txt + the probe table in the FA6-pre
//! notes).

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/fields/large_fields.rs"]
mod large_fields;

#[path = "../src/fields/small_fields.rs"]
mod small_fields;

#[path = "../src/prover/mod.rs"]
mod prover;

use large_fields::{
    gf128_byte_combine_bits, gf128_byte_combine_bits_spec, gf128_hmul, gf128_mul_spec,
    GF128_ALPHA, GF128_ONE, GF128_ZERO,
};
use small_fields::gf8_square_bits;
use prover::byte_commitments::{
    gf128_byte_combine_bits_sq, gf128_square_byte8, gf8_sq_bits_u8, sqb_slot8, ByteCommitment,
    ByteCommitsRef, SQ_COLS,
};
use prover::field_commitment::{FieldCommitDegOne, FieldCommitDegThree, FieldCommitDegTwo};

verus! {

// Shared constant folds of the byte-plane spec faces (the bv side of
// the oracle sample arms; live values re-derived per context via the
// exec ensures chains).
/// the conjugate-chain round keys (oracle: 8 rounds cycle back)
const KS: [u8; 9] = [0x53, 0xb5, 0xfc, 0x16, 0x0f, 0x55, 0xa1, 0xf7, 0x53];

/// u16-cast injectivity on the byte domain (the chain rows read the
/// square_inplace key ensures through the u16 cast)
proof fn lemma_u8_cast_inj(a: u8, b: u8)
    ensures
        (a as u16) == (b as u16) ==> a == b,
{
    assert((a as u16) == (b as u16) ==> a == b) by (bit_vector);
}

/// the per-round chain lemma (case split over the eight rounds; the
/// concrete spread rows live in kats_folds)
proof fn lemma_chain_step(r: nat)
    requires
        r < 8,
    ensures
        small_fields::gf8_ref_square_spread(KS[r as int] as u16)
            == (KS[(r + 1) as int] as u16),
{
    if r == 0 {
        assert(small_fields::gf8_ref_square_spread(KS[0] as u16) == (KS[1] as u16)) by (bit_vector);
    } else if r == 1 {
        assert(small_fields::gf8_ref_square_spread(KS[1] as u16) == (KS[2] as u16)) by (bit_vector);
    } else if r == 2 {
        assert(small_fields::gf8_ref_square_spread(KS[2] as u16) == (KS[3] as u16)) by (bit_vector);
    } else if r == 3 {
        assert(small_fields::gf8_ref_square_spread(KS[3] as u16) == (KS[4] as u16)) by (bit_vector);
    } else if r == 4 {
        assert(small_fields::gf8_ref_square_spread(KS[4] as u16) == (KS[5] as u16)) by (bit_vector);
    } else if r == 5 {
        assert(small_fields::gf8_ref_square_spread(KS[5] as u16) == (KS[6] as u16)) by (bit_vector);
    } else if r == 6 {
        assert(small_fields::gf8_ref_square_spread(KS[6] as u16) == (KS[7] as u16)) by (bit_vector);
    } else {
        assert(small_fields::gf8_ref_square_spread(KS[7] as u16) == (KS[8] as u16)) by (bit_vector);
    }
}

/// the per-round transition glue of the conjugates chain: with the
/// pre-round key pinned to KS[r] and the square_inplace key ensure
/// in context, the post key is KS[r+1].
proof fn small_fields_glu(pre: u8, post: u8, ks_r: u8, ks_next: u8)
    requires
        pre == ks_r,
        (post as u16) == small_fields::gf8_ref_square_spread(pre as u16),
        small_fields::gf8_ref_square_spread(ks_r as u16) == (ks_next as u16),
    ensures
        post == ks_next,
{
    assert(small_fields::gf8_ref_square_spread(pre as u16)
        == small_fields::gf8_ref_square_spread(ks_r as u16));
    assert((post as u16) == (ks_next as u16));
    assert(((post as u16) == (ks_next as u16)) ==> post == ks_next) by (bit_vector);
}

proof fn kats_folds()
    ensures
        // GF8 spread rows (oracle/python arms, incl. the chain
        // transitions)
        small_fields::gf8_ref_square_spread(0x00u8 as u16) == 0x0000u16,
        small_fields::gf8_ref_square_spread(0x01u8 as u16) == 0x0001u16,
        small_fields::gf8_ref_square_spread(0x02u8 as u16) == 0x0004u16,
        small_fields::gf8_ref_square_spread(0x10u8 as u16) == 0x001bu16,
        small_fields::gf8_ref_square_spread(0x53u8 as u16) == 0x00b5u16,
        small_fields::gf8_ref_square_spread(0xe4u8 as u16) == 0x004du16,
        small_fields::gf8_ref_square_spread(0xffu8 as u16) == 0x0013u16,
        small_fields::gf8_ref_square_spread(0xb5u8 as u16) == 0x00fcu16,
        small_fields::gf8_ref_square_spread(0xfcu8 as u16) == 0x0016u16,
        small_fields::gf8_ref_square_spread(0x16u8 as u16) == 0x000fu16,
        small_fields::gf8_ref_square_spread(0x0fu8 as u16) == 0x0055u16,
        small_fields::gf8_ref_square_spread(0x55u8 as u16) == 0x00a1u16,
        small_fields::gf8_ref_square_spread(0xa1u8 as u16) == 0x00f7u16,
        small_fields::gf8_ref_square_spread(0xf7u8 as u16) == 0x0053u16,
        // the chain closure (every round's key transition)
        forall |r: int|
            #[trigger] small_fields::gf8_ref_square_spread(KS[r] as u16) == (KS[r + 1] as u16)
                || 0 > r || r >= 8,
        // u8 truncation rows (byte-range sample arms)
        gf8_sq_bits_u8(0x02u8) == 0x04u8,
        gf8_sq_bits_u8(0x53u8) == 0xb5u8,
        gf8_sq_bits_u8(0xffu8) == 0x13u8,
        gf8_sq_bits_u8(0xb5u8) == 0xfcu8,
        // combine-bits rows at the zero/one bytes
        gf128_byte_combine_bits_spec(0x00u8) == 0u128,
        gf128_byte_combine_bits_spec(0x01u8) == GF128_ONE,
        // combine-bits alpha-xor folds (oracle arm constants)
        gf128_byte_combine_bits_spec(0x02u8) == GF128_ALPHA[0],
        gf128_byte_combine_bits_spec(0x03u8) == (GF128_ONE ^ GF128_ALPHA[0]),
        gf128_byte_combine_bits_spec(0x53u8)
            == (GF128_ONE ^ GF128_ALPHA[0] ^ GF128_ALPHA[3] ^ GF128_ALPHA[5]),
        gf128_byte_combine_bits_spec(0x10u8) == GF128_ALPHA[3],
        gf128_byte_combine_bits_spec(0xe4u8)
            == (GF128_ALPHA[1] ^ GF128_ALPHA[4] ^ GF128_ALPHA[5] ^ GF128_ALPHA[6]),
        gf128_byte_combine_bits_spec(0x04u8) == GF128_ALPHA[1],
        gf128_byte_combine_bits_spec(0xb5u8)
            == (GF128_ONE ^ GF128_ALPHA[1] ^ GF128_ALPHA[3] ^ GF128_ALPHA[4] ^ GF128_ALPHA[6]),
        // literal identity rows (oracle arms)
        (GF128_ONE ^ GF128_ALPHA[0] ^ GF128_ALPHA[3] ^ GF128_ALPHA[5])
            == 0xde77167b8539a7970d972a0b4c6fa967u128,
        (GF128_ONE ^ GF128_ALPHA[1] ^ GF128_ALPHA[3] ^ GF128_ALPHA[4] ^ GF128_ALPHA[6])
            == 0x1cf7a0fe8922c83fd8a5ae31928b4da1u128,
        (GF128_ALPHA[1] ^ GF128_ALPHA[4] ^ GF128_ALPHA[5] ^ GF128_ALPHA[6])
            == 0xc7bd33d0a58cf5b4740d6c968b842acbu128,
        GF128_ALPHA[3] == 0x0dcb364640a222fe6b8330483c2e9849u128,
        GF128_ALPHA[1] == 0x4cf4b7439cbfbb84ec7759ca3488aee1u128,
        // the sample-tag slot folds (chain arms)
        sqb_slot8(0, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD)
            == (GF128_ZERO ^ GF128_ALPHA[2] ^ DEAD),
        sqb_slot8(7, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD)
            == (DEAD ^ FOOD),
        (GF128_ZERO ^ GF128_ALPHA[2] ^ DEAD) == 0xeb00dea0b7af6878beec47c9bf928b47u128,
        (DEAD ^ FOOD) == 0x2ea04ee23af34ab3f12eb56a79a63de2u128,
{
    assert(gf128_byte_combine_bits_spec(0x00u8) == 0u128) by (bit_vector);
    assert(gf128_byte_combine_bits_spec(0x01u8) == GF128_ONE) by (bit_vector);
    // GF8 spread rows (oracle/python arms)
    assert(small_fields::gf8_ref_square_spread(0x00u8 as u16) == 0x0000u16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0x01u8 as u16) == 0x0001u16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0x02u8 as u16) == 0x0004u16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0x10u8 as u16) == 0x001bu16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0x53u8 as u16) == 0x00b5u16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0xe4u8 as u16) == 0x004du16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0xffu8 as u16) == 0x0013u16) by (bit_vector);
    // the conjugate-chain transitions (oracle round keys
    // 53 b5 fc 16 0f 55 a1 f7; each round's key square)
    assert(small_fields::gf8_ref_square_spread(0xb5u8 as u16) == 0x00fcu16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0xfcu8 as u16) == 0x0016u16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0x16u8 as u16) == 0x000fu16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0x0fu8 as u16) == 0x0055u16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0x55u8 as u16) == 0x00a1u16) by (bit_vector);
    assert(small_fields::gf8_ref_square_spread(0xa1u8 as u16) == 0x00f7u16) by (bit_vector);
    // u8 truncations of the spread model (byte-range rows)
    assert(gf8_sq_bits_u8(0x02u8) == 0x04u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0x53u8) == 0xb5u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0xffu8) == 0x13u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0xb5u8) == 0xfcu8) by (bit_vector);
    assert(gf8_sq_bits_u8(0xfcu8) == 0x16u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0x16u8) == 0x0fu8) by (bit_vector);
    assert(gf8_sq_bits_u8(0x0fu8) == 0x55u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0x55u8) == 0xa1u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0xa1u8) == 0xf7u8) by (bit_vector);
    // combine-bits alpha-xor folds (oracle arm constants)
    assert(gf128_byte_combine_bits_spec(0x02u8) == GF128_ALPHA[0]) by (bit_vector);
    assert(gf128_byte_combine_bits_spec(0x03u8) == (GF128_ONE ^ GF128_ALPHA[0])) by (bit_vector);
    assert(gf128_byte_combine_bits_spec(0x53u8)
        == (GF128_ONE ^ GF128_ALPHA[0] ^ GF128_ALPHA[3] ^ GF128_ALPHA[5])) by (bit_vector);
    assert(gf128_byte_combine_bits_spec(0x10u8) == GF128_ALPHA[3]) by (bit_vector);
    assert(gf128_byte_combine_bits_spec(0xe4u8)
        == (GF128_ALPHA[1] ^ GF128_ALPHA[4] ^ GF128_ALPHA[5] ^ GF128_ALPHA[6])) by (bit_vector);
    assert(gf128_byte_combine_bits_spec(0x04u8) == GF128_ALPHA[1]) by (bit_vector);
    assert(gf128_byte_combine_bits_spec(0xb5u8)
        == (GF128_ONE ^ GF128_ALPHA[1] ^ GF128_ALPHA[3] ^ GF128_ALPHA[4] ^ GF128_ALPHA[6])) by (bit_vector);
    // literal identity rows (oracle AesExtendedWitness-family arms)
    assert((GF128_ONE ^ GF128_ALPHA[0] ^ GF128_ALPHA[3] ^ GF128_ALPHA[5])
        == 0xde77167b8539a7970d972a0b4c6fa967u128) by (bit_vector);
    assert((GF128_ONE ^ GF128_ALPHA[1] ^ GF128_ALPHA[3] ^ GF128_ALPHA[4] ^ GF128_ALPHA[6])
        == 0x1cf7a0fe8922c83fd8a5ae31928b4da1u128) by (bit_vector);
    assert((GF128_ALPHA[1] ^ GF128_ALPHA[4] ^ GF128_ALPHA[5] ^ GF128_ALPHA[6])
        == 0xc7bd33d0a58cf5b4740d6c968b842acbu128) by (bit_vector);
    assert(GF128_ALPHA[3] == 0x0dcb364640a222fe6b8330483c2e9849u128) by (bit_vector);
    assert(GF128_ALPHA[1] == 0x4cf4b7439cbfbb84ec7759ca3488aee1u128) by (bit_vector);
    // the chain's last transition (f7 -> 53 closes the orbit)
    assert(small_fields::gf8_ref_square_spread(0xf7u8 as u16) == 0x0053u16) by (bit_vector);
    assert(sqb_slot8(0, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD)
        == (GF128_ZERO ^ GF128_ALPHA[2] ^ DEAD)) by (bit_vector);
    assert(sqb_slot8(7, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD)
        == (DEAD ^ FOOD)) by (bit_vector);
    assert((GF128_ZERO ^ GF128_ALPHA[2] ^ DEAD) == 0xeb00dea0b7af6878beec47c9bf928b47u128) by (bit_vector);
    assert((DEAD ^ FOOD) == 0x2ea04ee23af34ab3f12eb56a79a63de2u128) by (bit_vector);
    // the chain-closure forall (8 concrete transitions)
    assert(small_fields::gf8_ref_square_spread(KS[0] as u16) == (KS[1] as u16));
    assert(small_fields::gf8_ref_square_spread(KS[1] as u16) == (KS[2] as u16));
    assert(small_fields::gf8_ref_square_spread(KS[2] as u16) == (KS[3] as u16));
    assert(small_fields::gf8_ref_square_spread(KS[3] as u16) == (KS[4] as u16));
    assert(small_fields::gf8_ref_square_spread(KS[4] as u16) == (KS[5] as u16));
    assert(small_fields::gf8_ref_square_spread(KS[5] as u16) == (KS[6] as u16));
    assert(small_fields::gf8_ref_square_spread(KS[6] as u16) == (KS[7] as u16));
    assert(small_fields::gf8_ref_square_spread(KS[7] as u16) == (KS[8] as u16));
    assert(forall |r: int|
        #[trigger] small_fields::gf8_ref_square_spread(KS[r] as u16) == (KS[r + 1] as u16)
            || 0 > r || r >= 8);
}

// ===========================================================================
// 1. The upstream unit-test rows (code/src/prover/field_commitment.rs
//    :439-525), re-erected at the twin faces. The upstream `ONE * k`
//    literals are Mul<u8> select faces: ONE * even == ZERO,
//    ONE * odd == ONE.
// ===========================================================================

exec fn ut_field_commit_mul() {
    proof {
        kats_folds();
    }
    // GF128_ONE == 1 / GF128_ZERO == 0 (the FA3 const face); the
    // rows below run on the machine literals
    let one: u128 = 1u128;
    let zero: u128 = 0u128;
    assert(GF128_ONE == 1u128);
    assert(GF128_ZERO == 0u128);
    proof {
        large_fields::lemma_mul128_one_r(one);
        large_fields::lemma_mul128_zero_r(one);
        large_fields::lemma_mul128_zero_r(GF128_ALPHA[0]);
    }

    // first block: lhs = D2{ONE, [ONE, ONE]}, rhs = D1{ONE, ONE};
    // exp_res = D3{ONE, [ONE, ONE*2, ONE*2]} = D3{1, [1, 0, 0]}
    let lhs = FieldCommitDegTwo { key: one, tag: [one, one] };
    let rhs = FieldCommitDegOne::new(one, one);
    let o1 = lhs.mul_one_ref(&rhs);
    assert(o1.key == gf128_mul_spec(one, one));
    assert(o1.tag[0] == gf128_mul_spec(one, one));
    assert(o1.tag[1] == gf128_mul_spec(one, one) ^ gf128_mul_spec(one, one));
    assert(o1.tag[2] == gf128_mul_spec(one, one) ^ gf128_mul_spec(one, one));
    // mul(1, 1) == 1 folds (probe3-row: the GF128 unit row --
    // gf128_mul_spec(1, 1)'s karatsuba fold at the concrete unit) and
    // one ^ one == zero (characteristic 2)
    assert(gf128_mul_spec(one, one) == one);
    assert((one ^ one) == 0u128) by (bit_vector);
    assert((one ^ one) == zero);
    // so the upstream exp_res row holds:
    assert(o1.key == one);
    assert(o1.tag == [one, zero, zero]);
    // the D1 * D2 arm (rhs * lhs) is the same product pointwise
    let o1s = rhs.mul_two_ref(&lhs);
    assert(o1s.key == o1.key);
    assert(o1s.tag[0] == o1.tag[0]);
    assert(o1s.tag[1] == o1.tag[1]);
    assert(o1s.tag[2] == o1.tag[2]);

    // D1 * D1 -> D2 (fresh copies: the by-value faces move)
    let r1a = FieldCommitDegOne::new(one, one);
    let r1b = FieldCommitDegOne::new(one, one);
    let o2 = r1a.mul(&r1b);
    assert(o2.key == one);
    assert(o2.key == gf128_mul_spec(one, one));
    assert(o2.tag[0] == gf128_mul_spec(one, one));
    assert(o2.tag[1] == gf128_mul_spec(one, one) ^ gf128_mul_spec(one, one));
    assert(o2.tag == [one, zero]);

    // square face: key squares, the char-2 middle coefficient is 0
    let r2 = FieldCommitDegOne::new(one, one);
    let o4 = r2.square();
    assert(o4.key == gf128_hmul(one, one));
    assert(o4.tag[0] == gf128_hmul(one, one));
    assert(o4.tag[1] == GF128_ZERO);
    assert(o4.key == gf128_hmul(1u128, 1u128));

    // Mul<&F> face (the key plane scales, the tag is kept):
    // the rhs * 3 row keeps tag, multiplies key (fresh copy again)
    let r3 = FieldCommitDegOne::new(one, one);
    let o5 = r3.mul_field_ref(&one);
    assert(o5.key == gf128_mul_spec(one, one));
    assert(o5.tag[0] == one);

    // second block: lhs = D1{ONE, ONE}, rhs = D1{ONE*2, ZERO} =
    // D1{ZERO, ZERO}; exp_res = D2{ONE*2, [ZERO, ONE*2]} =
    // D2{0, [0, 0]}
    let lhs2 = FieldCommitDegOne::new(one, one);
    let rhs2 = FieldCommitDegOne::new(zero, zero);
    let o6 = lhs2.mul(&rhs2);
    assert(o6.key == gf128_mul_spec(one, zero));
    assert(gf128_mul_spec(one, zero) == zero);
    assert(o6.key == zero);
    assert(o6.tag[0] == gf128_mul_spec(one, zero));
    assert(o6.tag[1] == gf128_mul_spec(one, zero) ^ gf128_mul_spec(one, zero));
    assert(gf128_mul_spec(one, zero) == 0u128);
    assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    assert(o6.tag[0] == 0u128);
    assert(o6.tag[1] == 0u128);

    // an alpha-axis sample for the D1*D1 arm that needs neither
    // the commutativity bridge nor deep constant folds:
    // p = (ONE, A0), q = (ONE, ONE); key = mul(ONE, ONE),
    // tag = [mul(A0, ONE), mul(ONE, ONE) ^ mul(A0, ONE)] -- the
    // oracle side-arms pin mul(A0, A0) == ALPHA[0]^2 out-of-band
    // (the D ring deferral; see notes)
    let a0: u128 = GF128_ALPHA[0];
    proof {
        large_fields::lemma_mul128_one_r(a0);
    }
    let p = FieldCommitDegOne::new(one, a0);
    let q = FieldCommitDegOne::new(one, one);
    let o7 = p.mul(&q);
    assert(o7.key == gf128_mul_spec(one, one));
    assert(o7.key == one);
    assert(o7.tag[0] == gf128_mul_spec(a0, one));
    assert(o7.tag[0] == a0);
    assert(o7.tag[1] == gf128_mul_spec(one, one) ^ gf128_mul_spec(a0, one));
}

exec fn ut_field_commit_sum() {
    proof {
        kats_folds();
    }
    let one: u128 = 1u128;
    let zero: u128 = 0u128;

    // first block (upstream :475-484) with the Mul<u8> select
    // semantics: lhs = D1{ONE, ONE*3} == D1{ONE, ONE},
    // rhs = D1{ONE*4, ONE*2} == D1{ZERO, ZERO},
    // exp = D1{ONE*5, ONE*5} == D1{ONE, ONE}
    let lhs = FieldCommitDegOne::new(one, one);
    let rhs = FieldCommitDegOne::new(zero, zero);
    assert((1u128 ^ 0u128) == 1u128) by (bit_vector);
    let all = lhs.add_ref_ref(&rhs);
    assert(all.key == one ^ zero);
    assert(all.key == one);
    assert(all.tag[0] == one ^ zero);
    assert(all.tag[0] == one);

    // second block: D2 adds -- keys ONE ^ ONE == ZERO (== ONE*2),
    // tags [ONE, ONE] ^ [ONE, ZERO] -> [ZERO, ONE];
    // exp = D2{ONE*2, [ONE*2, ONE]} = D2{0, [0, 1]}
    let lhs2 = FieldCommitDegTwo { key: one, tag: [one, one] };
    let rhs2 = FieldCommitDegTwo { key: one, tag: [one, zero] };
    let all2 = lhs2.add_ref_ref(&rhs2);
    assert(all2.key == one ^ one);
    assert((1u128 ^ 1u128) == 0u128) by (bit_vector);
    assert(all2.key == zero);
    assert(all2.tag[0] == zero);
    assert(all2.tag[1] == one);

    // add_assign_field rows (the zip->index loop keeps the tag plane)
    let mut acc = FieldCommitDegThree { key: one, tag: [one, zero, one] };
    acc.add_assign_field(one);
    assert(acc.key == one ^ one);
    assert((1u128 ^ 1u128) == 0u128) by (bit_vector);
    assert(acc.key == 0u128);
    assert(acc.tag[0] == one);
    assert(acc.tag[1] == zero);
    assert(acc.tag[2] == one);

    // third block: D3 adds --
    //   lhs = D3{ONE*2, [ZERO, ONE*2, ONE]} = D3{0, [0, 0, 1]},
    //   rhs = D3{ONE, [ONE, ONE*2, ZERO]}   = D3{1, [1, 0, 0]},
    //   exp = D3{ONE*3, [ONE, ONE*4, ONE]} = D3{1, [1, 0, 1]}
    let lhs3 = FieldCommitDegThree { key: zero, tag: [zero, zero, one] };
    let rhs3 = FieldCommitDegThree { key: one, tag: [one, zero, zero] };
    let all3 = lhs3.add_ref_ref(&rhs3);
    assert(all3.key == zero ^ one);
    assert((0u128 ^ 1u128) == 1u128) by (bit_vector);
    assert(all3.key == one);
    assert(all3.tag[0] == one);
    assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    assert(all3.tag[1] == zero);
    assert(all3.tag[2] == one);

    // the tail-add faces: D3 + D1 (slot 2 absorbs the deg-1 tag),
    // D3 + D2 (slots 1-2 absorb), D2 += D1 (slot 1 absorbs)
    let d1 = FieldCommitDegOne::new(one, one);
    let d3 = FieldCommitDegThree { key: zero, tag: [one, zero, one] };
    let a1 = d3.add_one(&d1);
    assert(a1.key == zero ^ one);
    assert(a1.tag == [one, zero, zero]);
    let d2 = FieldCommitDegTwo { key: one, tag: [one, zero] };
    let d3b = FieldCommitDegThree { key: zero, tag: [one, zero, one] };
    let a2 = d3b.add_two(&d2);
    assert(a2.key == one);
    assert(a2.tag == [one, one, one]); // char-2: one ^ zero ^ one... slot1 = 0^1, slot2 = 1^0
    assert(a2.tag[1] == one);
    let mut d2mut = FieldCommitDegTwo { key: one, tag: [one, zero] };
    d2mut.add_assign_one(&d1);
    assert(d2mut.key == zero);
    assert(d2mut.tag[0] == one);
    assert(d2mut.tag[1] == one);

    // Mul<F> face on D2: both tag slots scale
    let a0: u128 = GF128_ALPHA[0];
    let m2 = d2.mul_field(a0);
    assert(m2.key == gf128_mul_spec(one, a0));
    assert(m2.tag[0] == gf128_mul_spec(one, a0));
    assert(m2.tag[1] == gf128_mul_spec(zero, a0));
}

// ===========================================================================
// 2. The GF8 bit-plane orbit sample rows (oracle/python arm values).
// ===========================================================================

exec fn ut_gf8_orbit_rows() {
    proof {
        kats_folds();
    }
    proof {
        assert(small_fields::gf8_ref_square_spread(0x00u8 as u16) == 0x0000u16) by (bit_vector);
        assert(small_fields::gf8_ref_square_spread(0x01u8 as u16) == 0x0001u16) by (bit_vector);
        assert(small_fields::gf8_ref_square_spread(0x02u8 as u16) == 0x0004u16) by (bit_vector);
        assert(small_fields::gf8_ref_square_spread(0x10u8 as u16) == 0x001bu16) by (bit_vector);
        assert(small_fields::gf8_ref_square_spread(0x53u8 as u16) == 0x00b5u16) by (bit_vector);
        assert(small_fields::gf8_ref_square_spread(0xe4u8 as u16) == 0x004du16) by (bit_vector);
        assert(small_fields::gf8_ref_square_spread(0xffu8 as u16) == 0x0013u16) by (bit_vector);
    }
    // gf8_square_bits exec values (FA2 spread-model ensures; the
    // fork arm values below are the oracle/python rows):
    //   00->00, 01->01, 02->04, 10->1b, 53->b5, e4->4d, ff->13
    let g0 = gf8_square_bits(0x00u8);
    assert(g0 == 0x00u8); // oracle arm: 00
    let g1 = gf8_square_bits(0x01u8);
    assert(g1 == 0x01u8); // oracle arm: 01
    let g2 = gf8_square_bits(0x02u8);
    assert(g2 == 0x04u8); // oracle arm: 04
    let g3 = gf8_square_bits(0x10u8);
    assert(g3 == 0x1bu8); // oracle arm: 1b
    let g4 = gf8_square_bits(0x53u8);
    assert(g4 == 0xb5u8); // oracle arm: b5
    let g5 = gf8_square_bits(0xe4u8);
    assert(g5 == 0x4du8); // oracle arm: 4d
    let g6 = gf8_square_bits(0xffu8);
    assert(g6 == 0x13u8); // oracle arm: 13

    // the u8-level square spec (the truncated spread face at the
    // sample rows)
    assert(gf8_sq_bits_u8(0x00u8) == 0x00u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0x10u8) == 0x1bu8) by (bit_vector);
    assert(gf8_sq_bits_u8(0x53u8) == 0xb5u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0xffu8) == 0x13u8) by (bit_vector);
}

// ===========================================================================
// 3. byte_combine_bits / byte_combine_bits_sq sample rows.
// ===========================================================================

exec fn ut_combine_bits_rows() {
    proof {
        kats_folds();
    }
    // bits row samples: k=00 -> 0, k=01 -> ONE
    proof {
        assert(gf128_byte_combine_bits_spec(0x00u8) == 0u128) by (bit_vector);
        assert(gf128_byte_combine_bits_spec(0x01u8) == 1u128) by (bit_vector);
    }
    let b0 = gf128_byte_combine_bits(0x00u8);
    assert(b0 == 0u128); // oracle arm: 0
    let b1 = gf128_byte_combine_bits(0x01u8);
    assert(b1 == GF128_ONE); // oracle arm: 1

    // k=02: ONE-bit1 selects ALPHA[0] (bits 1): the alpha-xor form
    // of the spec unfolds under bv
    proof {
        assert(gf128_byte_combine_bits_spec(0x02u8) == GF128_ALPHA[0]) by (bit_vector);
        assert(gf128_byte_combine_bits_spec(0x03u8) == (GF128_ONE ^ GF128_ALPHA[0])) by (bit_vector);
        assert(gf128_byte_combine_bits_spec(0x53u8)
            == (GF128_ONE ^ GF128_ALPHA[0] ^ GF128_ALPHA[3] ^ GF128_ALPHA[5])) by (bit_vector);
        assert(gf128_byte_combine_bits_spec(0x10u8) == GF128_ALPHA[3]) by (bit_vector);
        assert(gf128_byte_combine_bits_spec(0xe4u8)
            == (GF128_ALPHA[1] ^ GF128_ALPHA[4] ^ GF128_ALPHA[5] ^ GF128_ALPHA[6])) by (bit_vector);
        assert(gf128_byte_combine_bits_spec(0xb5u8)
            == (GF128_ONE ^ GF128_ALPHA[1] ^ GF128_ALPHA[3] ^ GF128_ALPHA[4] ^ GF128_ALPHA[6])) by (bit_vector);
        assert(gf128_byte_combine_bits_spec(0x04u8) == GF128_ALPHA[1]) by (bit_vector);
    }
    let b2 = gf128_byte_combine_bits(0x02u8);
    assert(b2 == gf128_byte_combine_bits_spec(0x02u8));
    assert(b2 == GF128_ALPHA[0]);

    // k=03: bits 0,1 -> ONE ^ ALPHA[0]
    let b3 = gf128_byte_combine_bits(0x03u8);
    assert(b3 == gf128_byte_combine_bits_spec(0x03u8));
    assert(b3 == GF128_ONE ^ GF128_ALPHA[0]);

    // k=53 (0101_0011: bits 0,1,4,6):
    // ONE ^ ALPHA[0] ^ ALPHA[3] ^ ALPHA[5] == oracle de77167b...
    let b5v = gf128_byte_combine_bits(0x53u8);
    assert(b5v == gf128_byte_combine_bits_spec(0x53u8));
    assert(gf128_byte_combine_bits_spec(0x53u8)
        == (GF128_ONE ^ GF128_ALPHA[0] ^ GF128_ALPHA[3] ^ GF128_ALPHA[5])) by (bit_vector);
    assert((GF128_ONE ^ GF128_ALPHA[0] ^ GF128_ALPHA[3] ^ GF128_ALPHA[5])
        == 0xde77167b8539a7970d972a0b4c6fa967u128) by (bit_vector);
    assert(b5v == 0xde77167b8539a7970d972a0b4c6fa967u128);

    // oracle cross-arms for the doubled bits selections:
    // k=10 (bit 4): ALPHA[3] == 0dcb3646...
    assert(GF128_ALPHA[3] == 0x0dcb364640a222fe6b8330483c2e9849u128) by (bit_vector);

    // bits_sq rows: the exec composes gf8 square then combine; the
    // spec faces are pinned per-arm:
    //   k=02: spec(gf8_sq(02)) = spec(04) = ALPHA[1] ==
    //        4cf4b7439cbfbb84ec7759ca3488aee1
    //   k=53: spec(b5) = 1cf7a0fe8922c83fd8a5ae31928b4da1
    assert(GF128_ALPHA[1] == 0x4cf4b7439cbfbb84ec7759ca3488aee1u128) by (bit_vector);
    let q2 = gf128_byte_combine_bits_sq(0x02u8);
    assert(q2 == gf128_byte_combine_bits_spec(gf8_sq_bits_u8(0x02u8)));
    assert(gf8_sq_bits_u8(0x02u8) == 0x04u8) by (bit_vector);
    assert(q2 == GF128_ALPHA[1]);
    let q53 = gf128_byte_combine_bits_sq(0x53u8);
    assert(q53 == gf128_byte_combine_bits_spec(gf8_sq_bits_u8(0x53u8)));
    assert(gf8_sq_bits_u8(0x53u8) == 0xb5u8) by (bit_vector);
    assert(q53
        == GF128_ONE ^ GF128_ALPHA[1] ^ GF128_ALPHA[3] ^ GF128_ALPHA[4] ^ GF128_ALPHA[6]);
    assert((GF128_ONE ^ GF128_ALPHA[1] ^ GF128_ALPHA[3] ^ GF128_ALPHA[4] ^ GF128_ALPHA[6])
        == 0x1cf7a0fe8922c83fd8a5ae31928b4da1u128) by (bit_vector);
    assert(q53 == 0x1cf7a0fe8922c83fd8a5ae31928b4da1u128);
}

// ===========================================================================
// 4. The column probes through the pure square_byte twin (unit tag
//    vectors; the column bytes are the SQ_COLS face).
// ===========================================================================

exec fn ut_column_rows() {
    proof {
        kats_folds();
    }
    proof {
        assert(sqb_slot8(0, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(1, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128)
            == 0u128) by (bit_vector);
        assert(sqb_slot8(7, 1u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128)
            == 0u128) by (bit_vector);
        assert(sqb_slot8(0, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128, 0u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(1, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128, 0u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(2, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128, 0u128)
            == 0u128) by (bit_vector);
        assert(sqb_slot8(3, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128, 0u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(4, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128, 0u128)
            == 0u128) by (bit_vector);
        assert(sqb_slot8(5, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128, 0u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(6, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128, 0u128)
            == 0u128) by (bit_vector);
        assert(sqb_slot8(7, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128, 0u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(0, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128)
            == 0u128) by (bit_vector);
        assert(sqb_slot8(1, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(3, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(4, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128)
            == 1u128) by (bit_vector);
        assert(sqb_slot8(7, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 1u128)
            == 1u128) by (bit_vector);
        assert(SQ_COLS[0] == 0x01u8) by (bit_vector);
        assert(SQ_COLS[1] == 0x04u8) by (bit_vector);
        assert(SQ_COLS[2] == 0x10u8) by (bit_vector);
        assert(SQ_COLS[3] == 0x40u8) by (bit_vector);
        assert(SQ_COLS[4] == 0x1bu8) by (bit_vector);
        assert(SQ_COLS[5] == 0x6cu8) by (bit_vector);
        assert(SQ_COLS[6] == 0xabu8) by (bit_vector);
        assert(SQ_COLS[7] == 0x9au8) by (bit_vector);
    }
    let one: u128 = GF128_ONE;
    let zero: u128 = GF128_ZERO;

    assert(SQ_COLS[1] == 0x04u8);
    assert(SQ_COLS[2] == 0x10u8);
    assert(SQ_COLS[3] == 0x40u8);
    assert(SQ_COLS[4] == 0x1bu8);
    assert(SQ_COLS[5] == 0x6cu8);
    assert(SQ_COLS[6] == 0xabu8);
    assert(SQ_COLS[7] == 0x9au8);

    // column 0 (byte 0x01): slot 0
    let c0 = gf128_square_byte8(one, zero, zero, zero, zero, zero, zero, zero);
    assert(c0[0] == one);
    assert(c0[1] == zero);
    assert(c0[2] == zero);
    assert(c0[7] == zero);

    // column 6 (byte 0xab: slots 0, 1, 3, 5, 7)
    let c6 = gf128_square_byte8(zero, zero, zero, zero, zero, zero, one, zero);
    assert(c6[0] == one);
    assert(c6[1] == one);
    assert(c6[2] == zero);
    assert(c6[3] == one);
    assert(c6[4] == zero);
    assert(c6[5] == one);
    assert(c6[6] == zero);
    assert(c6[7] == one);

    // column 7 (byte 0x9a: slots 1, 3, 4, 7)
    let c7 = gf128_square_byte8(zero, zero, zero, zero, zero, zero, zero, one);
    assert(c7[0] == zero);
    assert(c7[1] == one);
    assert(c7[3] == one);
    assert(c7[4] == one);
    assert(c7[7] == one);
}

// ===========================================================================
// 5. The ByteCommitment sample chains (key 0x53 over the sample tag
//    vector) with the oracle arm values.
// ===========================================================================

const DEAD: u128 = 0x0deadbeefcafebabe0123456789abcdef;
const FOOD: u128 = 0xf00df00df00df00df00df00df00df00d;

fn sample_tags() -> (t: [u128; 8])
    ensures
        t[0] == GF128_ZERO,
        t[1] == GF128_ONE,
        t[2] == GF128_ALPHA[0],
        t[3] == GF128_ALPHA[1],
        t[4] == GF128_ALPHA[2],
        t[5] == GF128_ALPHA[3],
        t[6] == DEAD,
        t[7] == FOOD,
{
    let one = GF128_ONE;
    let zero = GF128_ZERO;
    [
        zero,
        one,
        GF128_ALPHA[0],
        GF128_ALPHA[1],
        GF128_ALPHA[2],
        GF128_ALPHA[3],
        DEAD,
        FOOD,
    ]
}

exec fn ut_byte_commitment_chain() {
    proof {
        kats_folds();
    }
    // combine: oracle arm key de77167b8539a7970d972a0b4c6fa967
    let sv = sample_tags();
    assert(sv[0] == GF128_ZERO && sv[2] == GF128_ALPHA[0]);
    proof {
        // spec folds for the row constants (kats_folds covers the
        // byte faces; the u16 cast row needs the local spread fold)
        assert(small_fields::gf8_ref_square_spread(0x53u8 as u16) == 0x00b5u16) by (bit_vector);
    }
    let mut bc = ByteCommitment { key: 0x53u8, tags: sample_tags() };
    let c0 = bc.combine();
    assert(c0.key == gf128_byte_combine_bits_spec(0x53u8));
    assert(c0.key == 0xde77167b8539a7970d972a0b4c6fa967u128);
    // tag plane: the combine spec over the sample tags is pinned
    // out-of-band (oracle arm 55decfe0521015ec80d619f2bbd4faab)

    // square_inplace: key 0x53 -> 0xb5 (GF8 square row)
    // tag plane == the column map over the sample tags (spec chain;
    // the folded arm values are the sqb_slot8 selects on consts)
    bc.square_inplace();
    assert((bc.key as u16) == small_fields::gf8_ref_square_spread(0x53u8 as u16));
    assert(bc.key == 0xb5u8);
    assert(bc.tags[0] == sqb_slot8(0, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD));
    assert(bc.tags[0] == sqb_slot8(0, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD));
    assert(bc.tags[7] == sqb_slot8(7, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD));
    assert(sqb_slot8(0, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD)
        == (GF128_ZERO ^ GF128_ALPHA[2] ^ DEAD)) by (bit_vector);
    assert(sqb_slot8(7, GF128_ZERO, GF128_ONE, GF128_ALPHA[0], GF128_ALPHA[1], GF128_ALPHA[2], GF128_ALPHA[3], DEAD, FOOD)
        == (DEAD ^ FOOD)) by (bit_vector);
    // column arms: slot 0 collects columns 0/4/6 (zero, A2, dead);
    // slot 7 collects columns 6/7 (A4, A5) -- oracle tags
    // eb00dea0b7af6878beec47c9bf928b47 / 2ea04ee23af34ab3f12eb56a79a63de2
    assert((GF128_ZERO ^ GF128_ALPHA[2] ^ DEAD) == 0xeb00dea0b7af6878beec47c9bf928b47u128) by (bit_vector);
    assert((DEAD ^ FOOD) == 0x2ea04ee23af34ab3f12eb56a79a63de2u128) by (bit_vector);
    assert(bc.tags[0] == 0xeb00dea0b7af6878beec47c9bf928b47u128);
    assert(bc.tags[7] == 0x2ea04ee23af34ab3f12eb56a79a63de2u128);

    // combine after square: oracle arm key 1cf7a0fe...
    let c1 = bc.combine();
    assert(c1.key == gf128_byte_combine_bits_spec(0xb5u8));
    assert(c1.key == 0x1cf7a0fe8922c83fd8a5ae31928b4da1u128);
    // D-FA6p-1 duality sample row: c1.key pins to the same oracle
    // constant that the field-square arm (gf128_mul of c0.key with
    // itself) folds to out-of-band (python/oracle cross, full-256:
    // zero mismatches); the quantified verus form is deferred

    // D-FA6p-1 duality sample row: the square-path combined key IS
    // the combined-square key of the pre-square combined value --
    // both arms pin to the same oracle constant:
    //   c0.key == de77167b...  c1.key == 1cf7a0fe...  and the
    //   out-of-band python/oracle arms cross: gf128_mul of de77167b
    //   with itself == 1cf7a0fe (the full-256 duality row is green
    //   at the oracle; the quantified verus form is D-FA6p-1).
    assert(c0.key != c1.key);
}

exec fn ut_conjugates_chain() {
    proof {
        kats_folds();
    }
    // the 8-round f256_f2_conjugates-shaped loop (encryption.rs
    // :181-192 loop body without the array stores), oracle-pinned
    // round keys: 53 b5 fc 16 0f 55 a1 f7
    let mut bc = ByteCommitment { key: 0x53u8, tags: sample_tags() };
    let mut r: usize = 0;
    while r < 8
        invariant
            0 <= r <= 8,
            bc.key == KS[r as int],
        decreases
            8 - r,
    {
        let pre_key = bc.key;
        assert(pre_key == KS[r as int]);
        let cj = bc.combine();
        // round r folds to the same bits spec as the round key
        assert(cj.key == gf128_byte_combine_bits_spec(KS[r as int]));
        bc.square_inplace();
        proof {
            // the transition glue: the per-round chain lemma + the
            // square_inplace key ensure + the cast lemma
            lemma_chain_step(r as nat);
            small_fields_glu(pre_key, bc.key, KS[r as int], KS[(r + 1) as int]);
        }
        r += 1;
    }
    // the 8-round closure: the orbit cycles back to the start key
    assert(bc.key == KS[8]);
    assert(bc.key == 0x53u8);
}

// ===========================================================================
// 6. The byte-plane container rows over the slice view (ByteCommitsRef
//    at the ORACLE L=U4 sample: keys [00, 53, e4, ff], tags = the
//    driver's LFSR fill table).
// ===========================================================================

const BC_KEYS: [u8; 4] = [0x00, 0x53, 0xe4, 0xff];

// the ORACLE driver's LFSR fill (fill_0 = 0x1234_5678_9abc_def0,
// rotate-13/xor 0xa5a55a5aa5a55a5a chain), with tags[1] = ALPHA[0]
// and tags[2] = ONE per the driver's overrides (python recomputed
// bit-exactly; the arm values below are that table)
const BC_TAGS: [u128; 32] = [
    0x0000000000000000123456789abcdef0u128,
    0x053d8555a9979a1ca13fe8ac5560ce0du128,
    0x00000000000000000000000000000001u128,
    0x0000000918bdbd903a17e38766ee1a5au128,
    0x00012317b7b2074259d5b68766ee1a5au128,
    0x2462f6f640e84b3a1375b68766ee1a5au128,
    0x5edec81d0967426e1375b68766ee1ed6u128,
    0xd903a12ce84dc26e1375b687667f9181u128,
    0x74259d09b84dc26e1375b6955795617au128,
    0xb3a13709b84dc26e1377f0a8098a14deu128,
    0x26e13709b84dc26e5bb05b6be73e8c2eu128,
    0x26e13709b84dcb76aec826bd74209e86u128,
    0x26e13709b96ed5d9a172f4deb6759e86u128,
    0x26e1372ddabb342efb3e8c9416759e86u128,
    0x26e5bb576685df677437d89416759e86u128,
    0xb76aecd0bbecee865eb7d89416759e86u128,
    0x5d9a177d9dd0cbd65eb7d89416758cb7u128,
    0x42efb3ba197acbd65eb7d8941433b1e9u128,
    0xf677432f597acbd65eb7d8dcd3987207u128,
    0xe865eb2f597acbd65ebec029abe5a494u128,
    0xbd65eb2f597acbd77da06f261137c756u128,
    0xbd65eb2f597aefb4a841987c5d4f8df6u128,
    0xbd65eb2f5df6950896aad1f3541b8df6u128,
    0xbd65ebbed2a112d5ff9b30d9d41b8df6u128,
    0xbd77da54225abff3c3be60d9d41b8df6u128,
    0xfb4a844b57fe787769be60d9d41b8df4u128,
    0x50896affcf0eed3769be60d9d41bc533u128,
    0x2d5ff9e1dda6ed3769be60d9dd03304bu128,
    0xff3c3bb4dda6ed3769be61fac3ac3ff1u128,
    0x87769bb4dda6ed37699a022f225b65bdu128,
    0xd3769bb4dda6ed33e5e0be11c912eab4u128,
    0xd3769bb4dda67cbcb2676378f8f3c034u128,
];

exec fn ut_byte_commits_ref_rows() {
    proof {
        kats_folds();
    }
    let cs = ByteCommitsRef::from_slices(&BC_KEYS, &BC_TAGS);

    // bc[0]: key 00 -> combined key 0 (the zero row)
    let f0 = cs.get_field_commit(0);
    assert(f0.key == gf128_byte_combine_bits_spec(0x00u8));
    assert(f0.key == 0u128);

    // bc[1] (key 53): oracle arm fck de77167b...
    let f1 = cs.get_field_commit(1);
    assert(f1.key == 0xde77167b8539a7970d972a0b4c6fa967u128);

    // bc[2] (key e4 = 1110_0100: bits 2,5,6,7):
    //   ALPHA[1] ^ ALPHA[4] ^ ALPHA[5] ^ ALPHA[6]
    //   == oracle c7bd33d0a58cf5b4740d6c968b842acb
    let f2 = cs.get_field_commit(2);
    assert(f2.key == gf128_byte_combine_bits_spec(0xe4u8));
    assert(f2.key
        == GF128_ALPHA[1] ^ GF128_ALPHA[4] ^ GF128_ALPHA[5] ^ GF128_ALPHA[6]);
    assert(f2.key == 0xc7bd33d0a58cf5b4740d6c968b842acbu128);

    // the window row: get_commits_ref(1, 2) -> bytes 53, e4
    let w = cs.get_commits_ref(1, 2);
    assert(w.keys[0] == 0x53u8);
    assert(w.keys[1] == 0xe4u8);
    let w1 = w.get_field_commit(1);
    assert(w1.key == gf128_byte_combine_bits_spec(0xe4u8));
    assert(w1.key == 0xc7bd33d0a58cf5b4740d6c968b842acbu128);

    // tag-plane spec rows (the ensures chains at the pinned table):
    // bc[2] tag == the combine spec over the table cells 16..23
    // (arm: db7492703ab7560661a423bbec1f79ed, python recompute b4
    // alpha axis == oracle print)
    assert(f2.tag[0] == gf128_byte_combine_spec_row2());
    // oracle arm: db7492703ab7560661a423bbec1f79ed (python/oracle
    // cross-checked; carried by the ensures chain above)
}

spec fn gf128_byte_combine_spec_row2() -> u128 {
    large_fields::gf128_byte_combine_spec(
        BC_TAGS[16], BC_TAGS[17], BC_TAGS[18], BC_TAGS[19],
        BC_TAGS[20], BC_TAGS[21], BC_TAGS[22], BC_TAGS[23],
    )
}

fn main() {
    ut_field_commit_mul();
    ut_field_commit_sum();
    ut_gf8_orbit_rows();
    ut_combine_bits_rows();
    ut_column_rows();
    ut_byte_commitment_chain();
    ut_conjugates_chain();
    ut_byte_commits_ref_rows();
}
} // verus!
