//! faest batch-FA11-beta harness (the six-item fields supplement) --
//! reference-style mount over the verified src tree (the ut_fa3
//! shape; consumes verified/src/lib.rs via #[path], nothing
//! re-copied).
//!
//! Three pin groups over the ORACLE constants
//! (out/kverus-run/FA11-beta/oracle-run.txt, the upstream-copy run):
//!   - the freshly landed const faces: per-axis sample rows (limb
//!     pins by bv), the ONE-at-index-5 SIGMA rows, the BETA wrap-
//!     around value rows, and the SQ_2/SQ_3 rows incl. the
//!     SQ_2 == ALPHA[1] derivational pins;
//!   - the pair-axis spec folds at sample bytes (the shallow arm of
//!     the 256-row oracle CSV tables: single-bit bytes and 0x53, the
//!     same key byte the FA6-pre chain used) with the
//!     BYTE_COMBINE_SQ_2 == byte_combine_bits(0x04) constants tie;
//!   - exec chains at the sample bytes: byte_combine_bits /
//!     byte_combine_bits_sq rows collapsing to the const folds,
//!     from_bit rows, square_byte slot rows at const-tag vectors,
//!     and the slot-map structural rows (the sqb_slot_pair
//!     componentwise decomposition).
//!
//! The full-256 value evidence and every literal of the const tables
//! ride the python two-tree diff (sim.py) against the oracle CSV --
//! the harness pins the mechanically provable rows, the ut_fa3
//! precedent for the deep mul chains.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod faest;

use faest::fields::large_fields::{
    gf192_byte_combine_bits, gf192_byte_combine_bits_spec, gf192_byte_combine_bits_sq,
    gf192_from_bit, gf256_byte_combine_bits, gf256_byte_combine_bits_spec,
    gf256_byte_combine_bits_sq, gf256_from_bit, gf256_square_byte8, gf192_square_byte8,
    gf8_sq_bits_u8, sqb_slot8, sqb_slot_pair, GF128_ALPHA, GF128_BETA_CUBES,
    GF128_BETA_SQUARES, GF128_BYTE_COMBINE_SQ_2, GF128_BYTE_COMBINE_SQ_3, GF128_ONE,
    GF128_SIGMA, GF128_SIGMA_SQUARES, GF192_ALPHA, GF192_BETA_CUBES, GF192_BETA_SQUARES,
    GF192_BYTE_COMBINE_SQ_2, GF192_BYTE_COMBINE_SQ_3, GF192_ONE, GF192_SIGMA, GF192_SIGMA_SQUARES,
    GF192_ZERO, GF256_ALPHA, GF256_BETA_CUBES, GF256_BETA_SQUARES, GF256_BYTE_COMBINE_SQ_2,
    GF256_BYTE_COMBINE_SQ_3, GF256_ONE, GF256_SIGMA, GF256_SIGMA_SQUARES, GF256_ZERO,
};

verus! {

/// Shared constant-fold row bank (the FA6-pre kats_folds shape): the
/// shallow spec folds + the const-limb pins, exported to the exec
/// row drivers through the ensures list.
proof fn kats_folds_fa11b()
    ensures
        // ---- GF128: SIGMA[5] = ONE + BETA wraparound + SQ rows ----
        GF128_SIGMA[5] == GF128_ONE,
        GF128_SIGMA_SQUARES[5] == GF128_ONE,
        GF128_BETA_SQUARES[4] == GF128_BETA_SQUARES[0],
        GF128_BETA_CUBES[0] == GF128_BETA_SQUARES[3],
        GF128_BYTE_COMBINE_SQ_2 == GF128_ALPHA[1],
        GF128_BYTE_COMBINE_SQ_3 == (GF128_ALPHA[1] ^ GF128_ONE),
        GF128_BYTE_COMBINE_SQ_2 == 0x4cf4b7439cbfbb84ec7759ca3488aee1,
        GF128_BYTE_COMBINE_SQ_3 == 0x4cf4b7439cbfbb84ec7759ca3488aee0,
        GF128_SIGMA[0] == 0x4cf4b7439cbfbb84ec7759ca3488aee0,
        GF128_BETA_SQUARES[0] == 0xdb4a932e2cae3d8baca8c2a7190f676b,
        GF128_BETA_CUBES[2] == 0x500317bd159d73bb34d2f7fba603e341,
        // ---- GF192: the ONE-at-5 rows + wrapped BETA + SQ rows ---
        GF192_SIGMA[5] == GF192_ONE,
        GF192_SIGMA_SQUARES[5] == GF192_ONE,
        GF192_BETA_SQUARES[4] == GF192_BETA_SQUARES[0],
        GF192_BETA_CUBES[0] == GF192_BETA_SQUARES[3],
        GF192_BETA_CUBES[2] == GF192_BETA_SQUARES[1],
        GF192_BYTE_COMBINE_SQ_2 == GF192_ALPHA[1],
        GF192_BYTE_COMBINE_SQ_3
            == (GF192_BYTE_COMBINE_SQ_2.0 ^ 1, GF192_BYTE_COMBINE_SQ_2.1),
        GF192_BYTE_COMBINE_SQ_2
            == (0x7bf61f19d5633f26b233619e7cf450bb, 0x0000000000000000da933726d491db34),
        GF192_BYTE_COMBINE_SQ_3
            == (0x7bf61f19d5633f26b233619e7cf450ba, 0x0000000000000000da933726d491db34),
        GF192_SIGMA[0].0 == 0x7bf61f19d5633f26b233619e7cf450ba,
        GF192_SIGMA[0].1 == 0x0000000000000000da933726d491db34,
        GF192_BETA_SQUARES[0].0 == 0x89bfb5055f8ff2664a2fe80a53fe16e7,
        GF192_BETA_CUBES[3].1 == 0x0000000000000000ee0fc537c5a9cb74,
        // ---- GF256 mirror rows ----
        GF256_SIGMA[5] == GF256_ONE,
        GF256_SIGMA_SQUARES[5] == GF256_ONE,
        GF256_BETA_SQUARES[4] == GF256_BETA_SQUARES[0],
        GF256_BETA_CUBES[0] == GF256_BETA_SQUARES[3],
        GF256_BETA_CUBES[3] == GF256_BETA_SQUARES[2],
        GF256_BYTE_COMBINE_SQ_2 == GF256_ALPHA[1],
        GF256_BYTE_COMBINE_SQ_3
            == (GF256_BYTE_COMBINE_SQ_2.0 ^ 1, GF256_BYTE_COMBINE_SQ_2.1),
        GF256_BYTE_COMBINE_SQ_2
            == (0x2ba5c48d2c42072fa95af52ad52289c1, 0x064e4d699c5b4af1d14a0d376c00b0ea),
        GF256_BYTE_COMBINE_SQ_3
            == (0x2ba5c48d2c42072fa95af52ad52289c0, 0x064e4d699c5b4af1d14a0d376c00b0ea),
        GF256_SIGMA[0].0 == 0x2ba5c48d2c42072fa95af52ad52289c0,
        GF256_BETA_SQUARES[0].0 == 0xd9ca3e577cc14c4a4074aaa06e5faade,
        GF256_BETA_CUBES[2].1 == 0x67dbaeb2ec4abc7c2adc5a08c13f1cfb,
        // ---- pair-axis spec folds at the sample bytes ----
        gf192_byte_combine_bits_spec(0x00u8) == GF192_ZERO,
        gf192_byte_combine_bits_spec(0x01u8) == GF192_ONE,
        gf192_byte_combine_bits_spec(0x02u8) == GF192_ALPHA[0],
        gf192_byte_combine_bits_spec(0x03u8)
            == (GF192_ONE.0 ^ GF192_ALPHA[0].0, GF192_ONE.1 ^ GF192_ALPHA[0].1),
        gf192_byte_combine_bits_spec(0x04u8) == GF192_ALPHA[1],
        gf192_byte_combine_bits_spec(0x04u8) == GF192_BYTE_COMBINE_SQ_2,
        gf192_byte_combine_bits_spec(0x53u8)
            == (GF192_ONE.0 ^ GF192_ALPHA[0].0 ^ GF192_ALPHA[3].0 ^ GF192_ALPHA[5].0,
                GF192_ONE.1 ^ GF192_ALPHA[0].1 ^ GF192_ALPHA[3].1 ^ GF192_ALPHA[5].1),
        gf256_byte_combine_bits_spec(0x00u8) == GF256_ZERO,
        gf256_byte_combine_bits_spec(0x01u8) == GF256_ONE,
        gf256_byte_combine_bits_spec(0x02u8) == GF256_ALPHA[0],
        gf256_byte_combine_bits_spec(0x04u8) == GF256_ALPHA[1],
        gf256_byte_combine_bits_spec(0x04u8) == GF256_BYTE_COMBINE_SQ_2,
        gf256_byte_combine_bits_spec(0x53u8)
            == (GF256_ONE.0 ^ GF256_ALPHA[0].0 ^ GF256_ALPHA[3].0 ^ GF256_ALPHA[5].0,
                GF256_ONE.1 ^ GF256_ALPHA[0].1 ^ GF256_ALPHA[3].1 ^ GF256_ALPHA[5].1),
        // ---- the GF8 square-bit fold rows of the sample chain ----
        gf8_sq_bits_u8(0x02u8) == 0x04u8,
        gf8_sq_bits_u8(0x53u8) == 0xb5u8,
        // ---- slot-map rows: sqb_slot8 handled at FA6-pre; the pair
        // face is the componentwise decomposition probe ----
        sqb_slot_pair(
            0,
            GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
            GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
        ) == (GF192_ZERO.0 ^ GF192_ALPHA[2].0 ^ GF192_ALPHA[4].0,
              GF192_ZERO.1 ^ GF192_ALPHA[2].1 ^ GF192_ALPHA[4].1),
        sqb_slot_pair(
            1,
            GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
            GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
        ) == (GF192_ALPHA[2].0 ^ GF192_ALPHA[4].0 ^ GF192_ALPHA[5].0,
              GF192_ALPHA[2].1 ^ GF192_ALPHA[4].1 ^ GF192_ALPHA[5].1),
        sqb_slot_pair(
            7,
            GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
            GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
        )
            == (GF192_ALPHA[4].0 ^ GF192_ALPHA[5].0,
                GF192_ALPHA[4].1 ^ GF192_ALPHA[5].1),
{
    // ---- the const-limb pins: direct bv (the probe-1 (c) form; the
    // const must live inside the blast -- no let-locals) ----
    assert(GF128_BYTE_COMBINE_SQ_2 == 0x4cf4b7439cbfbb84ec7759ca3488aee1) by (bit_vector);
    assert(GF128_BYTE_COMBINE_SQ_3 == 0x4cf4b7439cbfbb84ec7759ca3488aee0) by (bit_vector);
    assert(GF128_SIGMA[0] == 0x4cf4b7439cbfbb84ec7759ca3488aee0) by (bit_vector);
    assert(GF128_BETA_SQUARES[0] == 0xdb4a932e2cae3d8baca8c2a7190f676b) by (bit_vector);
    assert(GF128_BETA_CUBES[2] == 0x500317bd159d73bb34d2f7fba603e341) by (bit_vector);
    assert(GF128_BETA_CUBES[0] == GF128_BETA_SQUARES[3]) by (bit_vector);
    assert(GF128_SIGMA[5] == GF128_ONE) by (bit_vector);
    assert(GF128_SIGMA_SQUARES[5] == GF128_ONE) by (bit_vector);
    assert(GF128_BETA_SQUARES[4] == GF128_BETA_SQUARES[0]) by (bit_vector);
    assert(GF128_BYTE_COMBINE_SQ_2 == GF128_ALPHA[1]) by (bit_vector);
    assert(GF128_BYTE_COMBINE_SQ_3 == (GF128_ALPHA[1] ^ GF128_ONE)) by (bit_vector);

    assert(GF192_BYTE_COMBINE_SQ_2.0 == 0x7bf61f19d5633f26b233619e7cf450bb) by (bit_vector);
    assert(GF192_BYTE_COMBINE_SQ_2.1 == 0x0000000000000000da933726d491db34) by (bit_vector);
    assert(GF192_BYTE_COMBINE_SQ_3.0 == 0x7bf61f19d5633f26b233619e7cf450ba) by (bit_vector);
    assert(GF192_BYTE_COMBINE_SQ_3.1 == 0x0000000000000000da933726d491db34) by (bit_vector);
    assert(GF192_SIGMA[5] == GF192_ONE) by (bit_vector);
    assert(GF192_SIGMA_SQUARES[5] == GF192_ONE) by (bit_vector);
    assert(GF192_BETA_SQUARES[4].0 == GF192_BETA_SQUARES[0].0) by (bit_vector);
    assert(GF192_BETA_SQUARES[4].1 == GF192_BETA_SQUARES[0].1) by (bit_vector);
    assert(GF192_BETA_CUBES[0].0 == GF192_BETA_SQUARES[3].0) by (bit_vector);
    assert(GF192_BETA_CUBES[0].1 == GF192_BETA_SQUARES[3].1) by (bit_vector);
    assert(GF192_BETA_CUBES[2].0 == GF192_BETA_SQUARES[1].0) by (bit_vector);
    assert(GF192_BETA_CUBES[2].1 == GF192_BETA_SQUARES[1].1) by (bit_vector);
    assert(GF192_SIGMA[0].0 == 0x7bf61f19d5633f26b233619e7cf450ba) by (bit_vector);
    assert(GF192_SIGMA[0].1 == 0x0000000000000000da933726d491db34) by (bit_vector);
    assert(GF192_BETA_SQUARES[0].0 == 0x89bfb5055f8ff2664a2fe80a53fe16e7) by (bit_vector);
    assert(GF192_BETA_CUBES[3].1 == 0x0000000000000000ee0fc537c5a9cb74) by (bit_vector);
    assert(GF192_BYTE_COMBINE_SQ_2 == GF192_ALPHA[1]) by (bit_vector);
    // the SQ_3/SQ_2 ONE-carry: plain limb equalities (tuple
    // projections out of the blast)
    assert(GF192_BYTE_COMBINE_SQ_3.0 == (GF192_BYTE_COMBINE_SQ_2.0 ^ 1)) by (bit_vector);
    assert(GF192_BYTE_COMBINE_SQ_3.1 == GF192_BYTE_COMBINE_SQ_2.1) by (bit_vector);

    assert(GF256_BYTE_COMBINE_SQ_2.0 == 0x2ba5c48d2c42072fa95af52ad52289c1) by (bit_vector);
    assert(GF256_BYTE_COMBINE_SQ_2.1 == 0x064e4d699c5b4af1d14a0d376c00b0ea) by (bit_vector);
    assert(GF256_BYTE_COMBINE_SQ_3.0 == 0x2ba5c48d2c42072fa95af52ad52289c0) by (bit_vector);
    assert(GF256_BYTE_COMBINE_SQ_3.1 == 0x064e4d699c5b4af1d14a0d376c00b0ea) by (bit_vector);
    assert(GF256_SIGMA[5] == GF256_ONE) by (bit_vector);
    assert(GF256_SIGMA_SQUARES[5] == GF256_ONE) by (bit_vector);
    assert(GF256_BETA_SQUARES[4].0 == GF256_BETA_SQUARES[0].0) by (bit_vector);
    assert(GF256_BETA_SQUARES[4].1 == GF256_BETA_SQUARES[0].1) by (bit_vector);
    assert(GF256_BETA_CUBES[0].0 == GF256_BETA_SQUARES[3].0) by (bit_vector);
    assert(GF256_BETA_CUBES[0].1 == GF256_BETA_SQUARES[3].1) by (bit_vector);
    assert(GF256_BETA_CUBES[3].0 == GF256_BETA_SQUARES[2].0) by (bit_vector);
    assert(GF256_BETA_CUBES[3].1 == GF256_BETA_SQUARES[2].1) by (bit_vector);
    assert(GF256_SIGMA[0].0 == 0x2ba5c48d2c42072fa95af52ad52289c0) by (bit_vector);
    assert(GF256_BETA_SQUARES[0].0 == 0xd9ca3e577cc14c4a4074aaa06e5faade) by (bit_vector);
    assert(GF256_BETA_CUBES[2].1 == 0x67dbaeb2ec4abc7c2adc5a08c13f1cfb) by (bit_vector);
    assert(GF256_BYTE_COMBINE_SQ_2 == GF256_ALPHA[1]) by (bit_vector);
    assert(GF256_BYTE_COMBINE_SQ_3.0 == (GF256_BYTE_COMBINE_SQ_2.0 ^ 1)) by (bit_vector);
    assert(GF256_BYTE_COMBINE_SQ_3.1 == GF256_BYTE_COMBINE_SQ_2.1) by (bit_vector);

    // ---- pair-axis spec folds at the sample bytes (the shallow CSV
    // rows; plain encoding does not fold the const-select chains,
    // so each fold closes limb-wise by bv, tuple row by injectivity)
    // ----
    assert(gf192_byte_combine_bits_spec(0x02u8).0 == GF192_ALPHA[0].0) by (bit_vector);
    assert(gf192_byte_combine_bits_spec(0x02u8).1 == GF192_ALPHA[0].1) by (bit_vector);
    assert(gf192_byte_combine_bits_spec(0x04u8).0 == GF192_ALPHA[1].0) by (bit_vector);
    assert(gf192_byte_combine_bits_spec(0x04u8).1 == GF192_ALPHA[1].1) by (bit_vector);
    assert(gf192_byte_combine_bits_spec(0x00u8).0 == 0u128) by (bit_vector);
    assert(gf192_byte_combine_bits_spec(0x00u8).1 == 0u128) by (bit_vector);
    assert(gf192_byte_combine_bits_spec(0x01u8).0 == 1u128) by (bit_vector);
    assert(gf192_byte_combine_bits_spec(0x01u8).1 == 0u128) by (bit_vector);
    // the 0x53 fold: four selected terms per limb (bits 0/1/4/6)
    assert((GF192_ONE.0 ^ GF192_ALPHA[0].0 ^ GF192_ALPHA[3].0 ^ GF192_ALPHA[5].0)
        == gf192_byte_combine_bits_spec(0x53u8).0) by (bit_vector);
    assert((GF192_ONE.1 ^ GF192_ALPHA[0].1 ^ GF192_ALPHA[3].1 ^ GF192_ALPHA[5].1)
        == gf192_byte_combine_bits_spec(0x53u8).1) by (bit_vector);
    assert(gf256_byte_combine_bits_spec(0x02u8).0 == GF256_ALPHA[0].0) by (bit_vector);
    assert(gf256_byte_combine_bits_spec(0x02u8).1 == GF256_ALPHA[0].1) by (bit_vector);
    assert(gf256_byte_combine_bits_spec(0x04u8).0 == GF256_ALPHA[1].0) by (bit_vector);
    assert(gf256_byte_combine_bits_spec(0x04u8).1 == GF256_ALPHA[1].1) by (bit_vector);
    assert(gf256_byte_combine_bits_spec(0x00u8).0 == 0u128) by (bit_vector);
    assert(gf256_byte_combine_bits_spec(0x00u8).1 == 0u128) by (bit_vector);
    assert(gf256_byte_combine_bits_spec(0x01u8).0 == 1u128) by (bit_vector);
    assert(gf256_byte_combine_bits_spec(0x01u8).1 == 0u128) by (bit_vector);
    assert((GF256_ONE.0 ^ GF256_ALPHA[0].0 ^ GF256_ALPHA[3].0 ^ GF256_ALPHA[5].0)
        == gf256_byte_combine_bits_spec(0x53u8).0) by (bit_vector);
    assert((GF256_ONE.1 ^ GF256_ALPHA[0].1 ^ GF256_ALPHA[3].1 ^ GF256_ALPHA[5].1)
        == gf256_byte_combine_bits_spec(0x53u8).1) by (bit_vector);
    // the 0x03 fold (ONE ^ ALPHA[0]) limb-wise then tuple
    assert((GF192_ONE.0 ^ GF192_ALPHA[0].0) == gf192_byte_combine_bits_spec(0x03u8).0) by (bit_vector);
    assert((GF192_ONE.1 ^ GF192_ALPHA[0].1) == gf192_byte_combine_bits_spec(0x03u8).1) by (bit_vector);

    // ---- the sqb_slot_pair slot folds at the const-tag vector
    // (slot 0 = x0^x4^x6, slot 1 = x4^x6^x7, slot 7 = x6^x7; the
    // pair face unfolds to the componentwise sqb_slot8 columns) ----
    assert(sqb_slot_pair(
        0,
        GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
        GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
    ).0 == (GF192_ZERO.0 ^ GF192_ALPHA[2].0 ^ GF192_ALPHA[4].0)) by (bit_vector);
    assert(sqb_slot_pair(
        0,
        GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
        GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
    ).1 == (GF192_ZERO.1 ^ GF192_ALPHA[2].1 ^ GF192_ALPHA[4].1)) by (bit_vector);
    assert(sqb_slot_pair(
        1,
        GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
        GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
    ).0 == (GF192_ALPHA[2].0 ^ GF192_ALPHA[4].0 ^ GF192_ALPHA[5].0)) by (bit_vector);
    assert(sqb_slot_pair(
        1,
        GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
        GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
    ).1 == (GF192_ALPHA[2].1 ^ GF192_ALPHA[4].1 ^ GF192_ALPHA[5].1)) by (bit_vector);
    assert(sqb_slot_pair(
        7,
        GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
        GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
    ).0 == (GF192_ALPHA[4].0 ^ GF192_ALPHA[5].0)) by (bit_vector);
    assert(sqb_slot_pair(
        7,
        GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
        GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
    ).1 == (GF192_ALPHA[4].1 ^ GF192_ALPHA[5].1)) by (bit_vector);

    // ---- GF8 bit-spread rows ----
    assert(gf8_sq_bits_u8(0x02u8) == 0x04u8) by (bit_vector);
    assert(gf8_sq_bits_u8(0x53u8) == 0xb5u8) by (bit_vector);
}

/// Exec row group 1: byte_combine_bits / byte_combine_bits_sq at
/// the GF192 axis collapse to the const folds (the exec==spec rows
/// are proven in the src twin; the folds here pin the VALUES to
/// the oracle constants).
exec fn fa11b_exec_bits_gf192()
    requires
        true,
{
    proof {
        kats_folds_fa11b();
    }
    // single-bit bytes: ALPHA selections; 0x04 also closes the
    // SQ_2 const derivation end to end
    let b2 = gf192_byte_combine_bits(0x02u8);
    assert(b2 == GF192_ALPHA[0]);
    let b4sq = gf192_byte_combine_bits_sq(0x02u8);
    assert(b4sq == gf192_byte_combine_bits_spec(0x04u8));
    assert(b4sq == GF192_BYTE_COMBINE_SQ_2);
    // 0x53: the four-selection fold (ONE ^ ALPHA[0,3,5])
    let b53 = gf192_byte_combine_bits(0x53u8);
    assert(b53
        == (GF192_ONE.0 ^ GF192_ALPHA[0].0 ^ GF192_ALPHA[3].0 ^ GF192_ALPHA[5].0,
            GF192_ONE.1 ^ GF192_ALPHA[0].1 ^ GF192_ALPHA[3].1 ^ GF192_ALPHA[5].1));
    let _ = b2;
    let _ = b53;
    let _ = b4sq;
}

/// Exec row group 2: the same rows at the GF256 axis.
exec fn fa11b_exec_bits_gf256()
{
    proof {
        kats_folds_fa11b();
    }
    let b2 = gf256_byte_combine_bits(0x02u8);
    assert(b2 == GF256_ALPHA[0]);
    let b4sq = gf256_byte_combine_bits_sq(0x02u8);
    assert(b4sq == gf256_byte_combine_bits_spec(0x04u8));
    assert(b4sq == GF256_BYTE_COMBINE_SQ_2);
    let b53 = gf256_byte_combine_bits(0x53u8);
    assert(b53
        == (GF256_ONE.0 ^ GF256_ALPHA[0].0 ^ GF256_ALPHA[3].0 ^ GF256_ALPHA[5].0,
            GF256_ONE.1 ^ GF256_ALPHA[0].1 ^ GF256_ALPHA[3].1 ^ GF256_ALPHA[5].1));
    let _ = b2;
    let _ = b53;
    let _ = b4sq;
}

/// Exec row group 3: from_bit rows (both pair axes) + the square
/// map slots at the const-tag vector (basis projection of the
/// sample).
exec fn fa11b_exec_frombit_square()
{
    proof {
        kats_folds_fa11b();
    }
    let o192 = gf192_from_bit(1u8);
    proof {
        assert((1u8 & 1) == 1) by (bit_vector);
    }
    assert(o192 == GF192_ONE);
    let z192 = gf192_from_bit(2u8);
    proof {
        assert((2u8 & 1) == 0) by (bit_vector);
    }
    assert(z192 == GF192_ZERO);
    let o256 = gf256_from_bit(1u8);
    proof {
        assert((1u8 & 1) == 1) by (bit_vector);
    }
    assert(o256 == GF256_ONE);
    let z256 = gf256_from_bit(2u8);
    proof {
        assert((2u8 & 1) == 0) by (bit_vector);
    }
    assert(z256 == GF256_ZERO);

    // the const-tag vector: slot checks at slots 0/1/7 (column
    // formulas x0^x4^x6 / x4^x7 columns / x6^x7 limbs)
    let tag = [
        GF192_ZERO, GF192_ONE, GF192_ALPHA[0], GF192_ALPHA[1],
        GF192_ALPHA[2], GF192_ALPHA[3], GF192_ALPHA[4], GF192_ALPHA[5],
    ];
    let s = gf192_square_byte8(
        tag[0], tag[1], tag[2], tag[3], tag[4], tag[5], tag[6], tag[7],
    );
    assert(s[0] == (GF192_ZERO.0 ^ GF192_ALPHA[2].0 ^ GF192_ALPHA[4].0,
                    GF192_ZERO.1 ^ GF192_ALPHA[2].1 ^ GF192_ALPHA[4].1));
    assert(s[1] == (GF192_ALPHA[2].0 ^ GF192_ALPHA[4].0 ^ GF192_ALPHA[5].0,
                    GF192_ALPHA[2].1 ^ GF192_ALPHA[4].1 ^ GF192_ALPHA[5].1));
    let _ = o192;
    let _ = z192;
    let _ = o256;
    let _ = z256;
    let _ = s;
}

} // verus!

fn main() {}
