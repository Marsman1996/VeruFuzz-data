//! harness: the roundtrip synthesis -- decode(encode(x)) == x, the property the
//! upstream fuzz roundtrip.rs driver states (fuzz/fuzzers/roundtrip.rs:
//! "encode then decode is the identity"), now as a single verified composition:
//!
//!   roundtrip_naive_canonical  <- the universal domain through the naive-oracle
//!                                 engine (naive_internal_encode + add_padding,
//!                                 then complete_quads_len + decode_complete_quads
//!                                 + decode_suffix with the sufficient-Ok suffix
//!                                 forms gated on)
//!
//! All decode-side faces come from the src tree contracts (the region model of
//! decode_complete_quads, the sufficient-Ok suffix forms of decode_suffix, the
//! S*-shape value clauses); the encode side from naive_internal_encode's
//! per-byte model. The value bridges are the 6-bit-index inverse lemmas at the
//! file's top; the arithmetic and model joins are stated as standalone lemmas
//! right above the theorem so each verification query stays small.
//!
//! Run: ./third_party/verus-docker.sh verus database/base64/verified/harness/ut_roundtrip.rs

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod b64;

use b64::encode::{add_padding, pad_bytes_model};
use b64::engine::DecodePaddingMode;
use b64::engine::general_purpose::decode::{
    complete_quads_len, decode_complete_quads, dec_quad_byte, morsel_pair_hi, morsel_pair_lo,
    morsel_pair_mid, nonterminal_quads_len_model, ValidDecodeTable,
};
use b64::engine::general_purpose::decode_suffix::{
    decode_suffix, suff_form_2sym_pad2, suff_form_3sym_pad1, suff_form_4sym,
};
use b64::engine::general_purpose::encode::{
    enc_idx0, enc_idx1, enc_idx2, enc_idx3, enc_tail_byte, encode_helper, tail_unpadded_len,
};
use b64::engine::general_purpose::ValidAlphabetSymbols;
use b64::engine::naive::{
    naive_enc_idx0, naive_enc_idx1, naive_enc_idx2, naive_enc_idx3, naive_encoded_byte,
    naive_first_invalid, naive_internal_encode, naive_unpadded_enc_len, nfi_skip,
};

verus! {

/* ============================================================
 * The 6-bit-index inverse bridges: the decode morsel-pair models consume the
 * table values; the encode models produce the same values as the 6-bit
 * indices; these lemmas close the roundtrip value identity per group.
 * ============================================================ */

/// lo(idx0(b0), idx1(b0,b1)) == b0 over the naive (division-form) indices
pub proof fn nai_lo(b0: u8, b1: u8)
    ensures
        morsel_pair_lo(naive_enc_idx0(b0) as u8, naive_enc_idx1(b0, b1) as u8) == b0,
{
    let m0 = naive_enc_idx0(b0) as u8;
    let m1 = naive_enc_idx1(b0, b1) as u8;
    assert(naive_enc_idx0(b0) == (b0 as u32) / 4);
    assert(naive_enc_idx1(b0, b1) == (b0 as u32) % 4 * 16 + (b1 as u32) / 16);
    assert(m0 == b0 / 4);
    assert(m1 == b0 % 4 * 16 + b1 / 16);
    assert((b1 as u32) / 16 < 16);
    assert((m1 as u32) == (b0 as u32) % 4 * 16 + (b1 as u32) / 16);
    assert((m1 as u32) / 16 == (b0 as u32) % 4);
    assert((m0 as u32) * 4 + (m1 as u32) / 16 == b0 as u32);
    assert(morsel_pair_lo(m0, m1) == ((m0 as u32) * 4 + (m1 as u32) / 16) as u8);
    assert(morsel_pair_lo(m0, m1) == b0);
}

/// mid(idx1(b0,b1), idx2(b1,b2)) == b1 over the naive indices
pub proof fn nai_mid(b0: u8, b1: u8, b2: u8)
    ensures
        morsel_pair_mid(naive_enc_idx1(b0, b1) as u8, naive_enc_idx2(b1, b2) as u8) == b1,
{
    let m1 = naive_enc_idx1(b0, b1) as u8;
    let m2 = naive_enc_idx2(b1, b2) as u8;
    assert(naive_enc_idx1(b0, b1) == (b0 as u32) % 4 * 16 + (b1 as u32) / 16);
    assert(naive_enc_idx2(b1, b2) == (b1 as u32) % 16 * 4 + (b2 as u32) / 64);
    assert(m1 == b0 % 4 * 16 + b1 / 16);
    assert(m2 == b1 % 16 * 4 + b2 / 64);
    assert((m1 as u32) % 16 == (b1 as u32) / 16);
    assert((m2 as u32) / 4 == (b1 as u32) % 16);
    assert((m1 as u32) % 16 * 16 + (m2 as u32) / 4 == b1 as u32);
    assert(morsel_pair_mid(m1, m2) == ((m1 as u32) % 16 * 16 + (m2 as u32) / 4) as u8);
    assert(morsel_pair_mid(m1, m2) == b1);
}

/// hi(idx2(b1,b2), idx3(b2)) == b2 over the naive indices
pub proof fn nai_hi(b1: u8, b2: u8)
    ensures
        morsel_pair_hi(naive_enc_idx2(b1, b2) as u8, naive_enc_idx3(b2) as u8) == b2,
{
    let m2 = naive_enc_idx2(b1, b2) as u8;
    let m3 = naive_enc_idx3(b2) as u8;
    assert(naive_enc_idx2(b1, b2) == (b1 as u32) % 16 * 4 + (b2 as u32) / 64);
    assert(naive_enc_idx3(b2) == (b2 as u32) % 64);
    assert(m2 == b1 % 16 * 4 + b2 / 64);
    assert(m3 == b2 % 64);
    assert((m2 as u32) % 4 == (b2 as u32) / 64);
    assert((m2 as u32) % 4 * 64 + (m3 as u32) == b2 as u32);
    assert(morsel_pair_hi(m2, m3) == ((m2 as u32) % 4 * 64 + (m3 as u32)) as u8);
    assert(morsel_pair_hi(m2, m3) == b2);
}

/// the 3-symbol unpadded tail's second byte: mid(idx1(b0,b1), idx2(b1,0)) == b1
pub proof fn nai_tail_mid(b0: u8, b1: u8)
    ensures
        morsel_pair_mid(naive_enc_idx1(b0, b1) as u8, naive_enc_idx2(b1, 0) as u8) == b1,
{
    nai_mid(b0, b1, 0);
}

/// the 2-symbol tail's low-bits pin: idx1(b0, 0) has its low 4 bits zero
pub proof fn nai_lowbits_4(b0: u8)
    ensures
        (naive_enc_idx1(b0, 0) as u8) & 15 == 0,
{
    let v = naive_enc_idx1(b0, 0) as u8;
    assert(naive_enc_idx1(b0, 0) == (b0 as u32) % 4 * 16);
    assert(v == b0 % 4 * 16);
    assert((v & 15) == 0) by (bit_vector)
        requires
            v == ((b0 % 4) * 16);
}

/// the 3-symbol tail's low-bits pin: idx2(b1, 0) has its low 2 bits zero
pub proof fn nai_lowbits_2(b1: u8)
    ensures
        (naive_enc_idx2(b1, 0) as u8) & 3 == 0,
{
    let v = naive_enc_idx2(b1, 0) as u8;
    assert(naive_enc_idx2(b1, 0) == (b1 as u32) % 16 * 4);
    assert(v == b1 % 16 * 4);
    assert((v & 3) == 0) by (bit_vector)
        requires
            v == ((b1 % 16) * 4);
}

/// the len <= 26 tail's unpadded lengths per input class (the chain_len_lemma
/// shape restated for this harness) and the padding join
pub proof fn rt_len_classes(n: int)
    requires
        0 <= n,
    ensures
        naive_unpadded_enc_len(n) >= 0,
        n % 3 == 0 ==> naive_unpadded_enc_len(n) % 4 == 0,
        n % 3 == 1 ==> naive_unpadded_enc_len(n) % 4 == 2,
        n % 3 == 2 ==> naive_unpadded_enc_len(n) % 4 == 3,
{
}

/// the padding join: (m + pad_bytes_model(m)) % 4 == 0
pub proof fn rt_pad_arith(m: int)
    requires
        0 <= m,
        m % 4 == 0 || m % 4 == 2 || m % 4 == 3,
    ensures
        (m + pad_bytes_model(m)) % 4 == 0,
{
    let pm = m % 4;
    assert(pad_bytes_model(m) == (4 - pm) % 4);
}

/// the front-check arithmetic per input class: the nonterminal length and the
/// region bounds (x is nonempty iff the padded total reaches a full quad)
pub proof fn rt_front_arith(xlen: int, total: int, nt: int)
    requires
        0 <= xlen,
        total == naive_unpadded_enc_len(xlen) + pad_bytes_model(naive_unpadded_enc_len(xlen)),
        (naive_unpadded_enc_len(xlen) + pad_bytes_model(naive_unpadded_enc_len(xlen))) % 4 == 0,
        nt == nonterminal_quads_len_model(total, 0),
    ensures
        (xlen == 0 <==> total == 0),
        (xlen == 0 ==> nt == 0),
        (xlen > 0 ==> nt == total - 4),
        nt % 4 == 0,
        nt >= 0,
        nt / 4 * 3 <= xlen,
        nt <= 4 * (xlen / 3),
        (xlen % 3 == 1 ==> nt + 2 == naive_unpadded_enc_len(xlen)),
        (xlen % 3 == 2 ==> nt + 3 == naive_unpadded_enc_len(xlen)),
        (xlen % 3 == 0 && xlen > 0 ==> nt + 4 == naive_unpadded_enc_len(xlen)),
{
    if xlen == 0 {
        assert(naive_unpadded_enc_len(0) == 0);
        assert(pad_bytes_model(0) == 0);
        assert(nonterminal_quads_len_model(0, 0) == 0);
    } else {
        let q = xlen / 3;
        let r = xlen % 3;
        assert(total >= 4);
        let base = total - 4;
        assert(nonterminal_quads_len_model(total, 0) == base);
        assert(nt == base);
        if r == 1 {
            assert(naive_unpadded_enc_len(xlen) == 4 * q + 2);
            assert((4 * q + 2) % 4 == 2);
            assert(pad_bytes_model(4 * q + 2) == 2);
            assert(total == 4 * q + 4);
            assert(nt == 4 * q);
            assert(nt / 4 * 3 == 3 * q);
            assert(xlen == 3 * q + 1);
            assert(naive_unpadded_enc_len(xlen) == nt + 2);
        } else if r == 2 {
            assert(naive_unpadded_enc_len(xlen) == 4 * q + 3);
            assert((4 * q + 3) % 4 == 3);
            assert(pad_bytes_model(4 * q + 3) == 1);
            assert(total == 4 * q + 4);
            assert(nt == 4 * q);
            assert(nt / 4 * 3 == 3 * q);
            assert(xlen == 3 * q + 2);
            assert(naive_unpadded_enc_len(xlen) == nt + 3);
        } else {
            assert(naive_unpadded_enc_len(xlen) == 4 * q);
            assert(q >= 1);
            assert(pad_bytes_model(4 * q) == 0);
            assert(total == 4 * q);
            assert(nt == 4 * q - 4);
            assert(nt / 4 * 3 == 3 * q - 3);
            assert(xlen == 3 * q);
            assert(naive_unpadded_enc_len(xlen) == nt + 4);
        }
    }
}

/// the region model facts: every complete-quads byte is a legal symbol whose
/// table value is the naive 6-bit index of its quad position
pub proof fn naive_region_facts(
    gs: Seq<u8>,
    gt: Seq<u8>,
    gy: Seq<u8>,
    gx: Seq<u8>,
    nt: int,
)
    requires
        gs.len() == 64,
        (forall|v: int| 0 <= v < 64 ==> gt[gs[v] as int] == v as u8),
        0 <= nt <= 4 * (gx.len() / 3),
        forall|k: int|
            #![trigger gy[k]] 0 <= k < nt ==> gy[k] == naive_encoded_byte(gs, gx, k),
    ensures
        forall|k: int|
            #![trigger gt[gy[k] as int]] 0 <= k < nt ==> ((gt[gy[k] as int] < 64)
                && (k % 4 == 0 ==> gt[gy[k] as int]
                    == naive_enc_idx0(gx[k / 4 * 3]) as u8)
                && (k % 4 == 1 ==> gt[gy[k] as int]
                    == naive_enc_idx1(gx[k / 4 * 3], gx[k / 4 * 3 + 1]) as u8)
                && (k % 4 == 2 ==> gt[gy[k] as int]
                    == naive_enc_idx2(gx[k / 4 * 3 + 1], gx[k / 4 * 3 + 2]) as u8)
                && (k % 4 == 3 ==> gt[gy[k] as int]
                    == naive_enc_idx3(gx[k / 4 * 3 + 2]) as u8)),
{
    assert forall|k: int|
        #![trigger gt[gy[k] as int]] 0 <= k < nt ==> ((gt[gy[k] as int] < 64)
            && (k % 4 == 0 ==> gt[gy[k] as int] == naive_enc_idx0(gx[k / 4 * 3]) as u8)
            && (k % 4 == 1 ==> gt[gy[k] as int]
                == naive_enc_idx1(gx[k / 4 * 3], gx[k / 4 * 3 + 1]) as u8)
            && (k % 4 == 2 ==> gt[gy[k] as int]
                == naive_enc_idx2(gx[k / 4 * 3 + 1], gx[k / 4 * 3 + 2]) as u8)
            && (k % 4 == 3 ==> gt[gy[k] as int]
                == naive_enc_idx3(gx[k / 4 * 3 + 2]) as u8)) by {
        if 0 <= k < nt {
            assert(k < 4 * (gx.len() / 3));
            assert(gy[k] == naive_encoded_byte(gs, gx, k));
            let c = k / 4;
            let pv = k % 4;
            let b0 = gx[c * 3];
            let b1 = gx[c * 3 + 1];
            let b2 = gx[c * 3 + 2];
            if pv == 0 {
                assert(gy[k] == gs[naive_enc_idx0(b0) as int]);
                assert(0 <= naive_enc_idx0(b0) < 64);
                assert(gt[gs[naive_enc_idx0(b0) as int] as int] == naive_enc_idx0(b0) as u8);
            } else if pv == 1 {
                assert(gy[k] == gs[naive_enc_idx1(b0, b1) as int]);
                assert(0 <= naive_enc_idx1(b0, b1) < 64);
                assert(gt[gs[naive_enc_idx1(b0, b1) as int] as int]
                    == naive_enc_idx1(b0, b1) as u8);
            } else if pv == 2 {
                assert(gy[k] == gs[naive_enc_idx2(b1, b2) as int]);
                assert(0 <= naive_enc_idx2(b1, b2) < 64);
                assert(gt[gs[naive_enc_idx2(b1, b2) as int] as int]
                    == naive_enc_idx2(b1, b2) as u8);
            } else {
                assert(gy[k] == gs[naive_enc_idx3(b2) as int]);
                assert(0 <= naive_enc_idx3(b2) < 64);
                assert(gt[gs[naive_enc_idx3(b2) as int] as int]
                    == naive_enc_idx3(b2) as u8);
            }
        }
    }
}

/// the region value join, residue 0: the lo-paired region bytes equal the
/// originals (the morsel-pair inverse bridge)
pub proof fn naive_region_lo(gt: Seq<u8>, gy: Seq<u8>, gx: Seq<u8>, ocql: int)
    requires
        gt.len() == 256,
        0 <= ocql,
        ocql == ocql / 3 * 3,
        gx.len() >= ocql,
        forall|k: int|
            #![trigger gt[gy[k] as int]] 0 <= k < ocql / 3 * 4 ==> ((gt[gy[k] as int]
                < 64)
                && (k % 4 == 0 ==> gt[gy[k] as int]
                    == naive_enc_idx0(gx[k / 4 * 3]) as u8)
                && (k % 4 == 1 ==> gt[gy[k] as int]
                    == naive_enc_idx1(gx[k / 4 * 3], gx[k / 4 * 3 + 1]) as u8)),
    ensures
        forall|j: int|
            #![trigger dec_quad_byte(gt, gy, 0, j)] (0 <= j < ocql && j % 3 == 0)
                ==> dec_quad_byte(gt, gy, 0, j) == gx[j],
{
    assert forall|j: int|
        #![trigger dec_quad_byte(gt, gy, 0, j)] (0 <= j < ocql && j % 3 == 0)
            ==> dec_quad_byte(gt, gy, 0, j) == gx[j] by {
        if 0 <= j < ocql && j % 3 == 0 {
            let c = j / 3;
            let b0 = gx[c * 3];
            let b1 = gx[c * 3 + 1];
            let k0 = 4 * c;
            assert(gt[gy[k0] as int] == naive_enc_idx0(b0) as u8);
            assert(gt[gy[k0 + 1] as int] == naive_enc_idx1(b0, b1) as u8);
            nai_lo(b0, b1);
            assert(dec_quad_byte(gt, gy, 0, j) == morsel_pair_lo(
                gt[gy[k0] as int],
                gt[gy[k0 + 1] as int],
            ));
            assert(morsel_pair_lo(gt[gy[k0] as int], gt[gy[k0 + 1] as int]) == b0);
            assert(gx[j] == b0);
        }
    }
}

/// the region value join, residue 1: the mid-paired region bytes
pub proof fn naive_region_mid(gt: Seq<u8>, gy: Seq<u8>, gx: Seq<u8>, ocql: int)
    requires
        gt.len() == 256,
        0 <= ocql,
        ocql == ocql / 3 * 3,
        gx.len() >= ocql,
        forall|k: int|
            #![trigger gt[gy[k] as int]] 0 <= k < ocql / 3 * 4 ==> ((gt[gy[k] as int]
                < 64)
                && (k % 4 == 1 ==> gt[gy[k] as int]
                    == naive_enc_idx1(gx[k / 4 * 3], gx[k / 4 * 3 + 1]) as u8)
                && (k % 4 == 2 ==> gt[gy[k] as int]
                    == naive_enc_idx2(gx[k / 4 * 3 + 1], gx[k / 4 * 3 + 2]) as u8)),
    ensures
        forall|j: int|
            #![trigger dec_quad_byte(gt, gy, 0, j)] (0 <= j < ocql && j % 3 == 1)
                ==> dec_quad_byte(gt, gy, 0, j) == gx[j],
{
    assert forall|j: int|
        #![trigger dec_quad_byte(gt, gy, 0, j)] (0 <= j < ocql && j % 3 == 1)
            ==> dec_quad_byte(gt, gy, 0, j) == gx[j] by {
        if 0 <= j < ocql && j % 3 == 1 {
            let c = j / 3;
            let b0 = gx[c * 3];
            let b1 = gx[c * 3 + 1];
            let b2 = gx[c * 3 + 2];
            let k0 = 4 * c;
            assert(gt[gy[k0 + 1] as int] == naive_enc_idx1(b0, b1) as u8);
            assert(gt[gy[k0 + 2] as int] == naive_enc_idx2(b1, b2) as u8);
            nai_mid(b0, b1, b2);
            assert(dec_quad_byte(gt, gy, 0, j) == morsel_pair_mid(
                gt[gy[k0 + 1] as int],
                gt[gy[k0 + 2] as int],
            ));
            assert(morsel_pair_mid(
                gt[gy[k0 + 1] as int],
                gt[gy[k0 + 2] as int],
            ) == b1);
            assert(gx[j] == b1);
        }
    }
}

/// the region value join, residue 2: the hi-paired region bytes
pub proof fn naive_region_hi(gt: Seq<u8>, gy: Seq<u8>, gx: Seq<u8>, ocql: int)
    requires
        gt.len() == 256,
        0 <= ocql,
        ocql == ocql / 3 * 3,
        gx.len() >= ocql,
        forall|k: int|
            #![trigger gt[gy[k] as int]] 0 <= k < ocql / 3 * 4 ==> ((gt[gy[k] as int]
                < 64)
                && (k % 4 == 2 ==> gt[gy[k] as int]
                    == naive_enc_idx2(gx[k / 4 * 3 + 1], gx[k / 4 * 3 + 2]) as u8)
                && (k % 4 == 3 ==> gt[gy[k] as int]
                    == naive_enc_idx3(gx[k / 4 * 3 + 2]) as u8)),
    ensures
        forall|j: int|
            #![trigger dec_quad_byte(gt, gy, 0, j)] (0 <= j < ocql && j % 3 == 2)
                ==> dec_quad_byte(gt, gy, 0, j) == gx[j],
{
    assert forall|j: int|
        #![trigger dec_quad_byte(gt, gy, 0, j)] (0 <= j < ocql && j % 3 == 2)
            ==> dec_quad_byte(gt, gy, 0, j) == gx[j] by {
        if 0 <= j < ocql && j % 3 == 2 {
            let c = j / 3;
            let b1 = gx[c * 3 + 1];
            let b2 = gx[c * 3 + 2];
            let k0 = 4 * c;
            assert(gt[gy[k0 + 2] as int] == naive_enc_idx2(b1, b2) as u8);
            assert(gt[gy[k0 + 3] as int] == naive_enc_idx3(b2) as u8);
            nai_hi(b1, b2);
            assert(dec_quad_byte(gt, gy, 0, j) == morsel_pair_hi(
                gt[gy[k0 + 2] as int],
                gt[gy[k0 + 3] as int],
            ));
            assert(morsel_pair_hi(
                gt[gy[k0 + 2] as int],
                gt[gy[k0 + 3] as int],
            ) == b2);
            assert(gx[j] == b2);
        }
    }
}

/* ============================================================
 * The suffix form pins, one lemma per input class. Each lemma takes the
 * y-model facts (region + padding phase) and the class arithmetic, and
 * returns the sufficient-Ok form decode_suffix's ghost hypothesis needs.
 * ============================================================ */

/// the %3==1 suffix pin: the tail quad is "AA==" (the 2sym+2pad form)
pub proof fn naive_suffix_pin_r1(
    gs: Seq<u8>,
    gt: Seq<u8>,
    gy: Seq<u8>,
    gx: Seq<u8>,
    nt: int,
    gm: int,
    padding: u8,
    zlen: int,
    ocql: int,
    m: DecodePaddingMode,
)
    requires
        gs.len() == 64,
        (forall|v: int| 0 <= v < 64 ==> gt[gs[v] as int] == v as u8),
        (forall|v: int| 0 <= v < 64 ==> gs[v] != padding),
        gx.len() as int == 3 * (gx.len() as int / 3) + 1,
        gx.len() >= 1,
        nt == 4 * (gx.len() as int / 3),
        gm == naive_unpadded_enc_len(gx.len() as int),
        nt + 2 == gm,
        gy.len() == gm + pad_bytes_model(gm),
        zlen == gx.len() as int,
        ocql == nt / 4 * 3,
        forall|k: int|
            #![trigger gy[k]] 0 <= k < gm ==> gy[k] == naive_encoded_byte(gs, gx, k),
        forall|k: int|
            #![trigger gy[k]] gm <= k < gy.len() ==> gy[k] == padding,
        m == DecodePaddingMode::RequireCanonical || m == DecodePaddingMode::Indifferent,
    ensures
        suff_form_2sym_pad2(gy, nt, gt, padding, m, zlen, ocql),
{
    let q = gx.len() as int / 3;
    let b0 = gx[q * 3];
    rt_len_classes(gx.len() as int);
    assert(gm % 4 == 2);
    assert(pad_bytes_model(gm) == 2);
    assert(gy.len() == gm + 2);
    assert(gy.len() == nt + 4);
    assert(gy[nt] == naive_encoded_byte(gs, gx, nt));
    assert(gy[nt + 1] == naive_encoded_byte(gs, gx, nt + 1));
    assert(gy[nt + 2] == padding);
    assert(gy[nt + 3] == padding);
    assert(naive_encoded_byte(gs, gx, nt) == gs[naive_enc_idx0(b0) as int]);
    assert(naive_encoded_byte(gs, gx, nt + 1) == gs[naive_enc_idx1(b0, 0) as int]);
    nai_lowbits_4(b0);
    assert(gt[gy[nt + 1] as int] == naive_enc_idx1(b0, 0) as u8);
    assert((gt[gy[nt + 1] as int]) & 15 == 0);
    assert(gt[gy[nt] as int] < 64);
    assert(gt[gy[nt + 1] as int] < 64);
    assert(ocql == 3 * q);
    assert(zlen == 3 * q + 1);
    assert(zlen >= ocql + 1);
}

/// the %3==2 suffix pin: the tail quad is "AAA=" (the 3sym+1pad form)
pub proof fn naive_suffix_pin_r2(
    gs: Seq<u8>,
    gt: Seq<u8>,
    gy: Seq<u8>,
    gx: Seq<u8>,
    nt: int,
    gm: int,
    padding: u8,
    zlen: int,
    ocql: int,
    m: DecodePaddingMode,
)
    requires
        gs.len() == 64,
        (forall|v: int| 0 <= v < 64 ==> gt[gs[v] as int] == v as u8),
        (forall|v: int| 0 <= v < 64 ==> gs[v] != padding),
        gx.len() as int == 3 * (gx.len() as int / 3) + 2,
        gx.len() >= 2,
        nt == 4 * (gx.len() as int / 3),
        gm == naive_unpadded_enc_len(gx.len() as int),
        nt + 3 == gm,
        gy.len() == gm + pad_bytes_model(gm),
        zlen == gx.len() as int,
        ocql == nt / 4 * 3,
        forall|k: int|
            #![trigger gy[k]] 0 <= k < gm ==> gy[k] == naive_encoded_byte(gs, gx, k),
        forall|k: int|
            #![trigger gy[k]] gm <= k < gy.len() ==> gy[k] == padding,
        m == DecodePaddingMode::RequireCanonical || m == DecodePaddingMode::Indifferent,
    ensures
        suff_form_3sym_pad1(gy, nt, gt, padding, m, zlen, ocql),
{
    let q = gx.len() as int / 3;
    let b0 = gx[q * 3];
    let b1 = gx[q * 3 + 1];
    rt_len_classes(gx.len() as int);
    assert(gm % 4 == 3);
    assert(pad_bytes_model(gm) == 1);
    assert(gy.len() == gm + 1);
    assert(gy.len() == nt + 4);
    assert(gy[nt] == naive_encoded_byte(gs, gx, nt));
    assert(gy[nt + 1] == naive_encoded_byte(gs, gx, nt + 1));
    assert(gy[nt + 2] == naive_encoded_byte(gs, gx, nt + 2));
    assert(gy[nt + 3] == padding);
    assert(naive_encoded_byte(gs, gx, nt) == gs[naive_enc_idx0(b0) as int]);
    assert(naive_encoded_byte(gs, gx, nt + 1) == gs[naive_enc_idx1(b0, b1) as int]);
    assert(naive_encoded_byte(gs, gx, nt + 2) == gs[naive_enc_idx2(b1, 0) as int]);
    nai_lowbits_2(b1);
    assert(gt[gy[nt + 2] as int] == naive_enc_idx2(b1, 0) as u8);
    assert((gt[gy[nt + 2] as int]) & 3 == 0);
    assert(gt[gy[nt] as int] < 64);
    assert(gt[gy[nt + 1] as int] < 64);
    assert(gt[gy[nt + 2] as int] < 64);
    assert(ocql == 3 * q);
    assert(zlen == 3 * q + 2);
    assert(zlen >= ocql + 2);
}

/// the %3==0 suffix pin: the tail quad is a complete symbol quad (the 4sym
/// form; no low-bits condition is needed)
pub proof fn naive_suffix_pin_r0(
    gs: Seq<u8>,
    gt: Seq<u8>,
    gy: Seq<u8>,
    gx: Seq<u8>,
    nt: int,
    gm: int,
    padding: u8,
    zlen: int,
    ocql: int,
)
    requires
        gs.len() == 64,
        (forall|v: int| 0 <= v < 64 ==> gt[gs[v] as int] == v as u8),
        (forall|v: int| 0 <= v < 64 ==> gs[v] != padding),
        gx.len() as int == 3 * (gx.len() as int / 3),
        gx.len() >= 3,
        nt == 4 * (gx.len() as int / 3) - 4,
        gm == naive_unpadded_enc_len(gx.len() as int),
        nt + 4 == gm,
        gy.len() == gm + pad_bytes_model(gm),
        zlen == gx.len() as int,
        ocql == nt / 4 * 3,
        forall|k: int|
            #![trigger gy[k]] 0 <= k < gm ==> gy[k] == naive_encoded_byte(gs, gx, k),
        forall|k: int|
            #![trigger gy[k]] gm <= k < gy.len() ==> gy[k] == padding,
    ensures
        suff_form_4sym(gy, nt, gt, padding, zlen, ocql),
{
    let q = gx.len() as int / 3;
    let b0 = gx[q * 3 - 3];
    let b1 = gx[q * 3 - 2];
    let b2 = gx[q * 3 - 1];
    rt_len_classes(gx.len() as int);
    assert(gm % 4 == 0);
    assert(pad_bytes_model(gm) == 0);
    assert(gy.len() == gm);
    assert(gy.len() == nt + 4);
    assert(gy[nt] == naive_encoded_byte(gs, gx, nt));
    assert(gy[nt + 1] == naive_encoded_byte(gs, gx, nt + 1));
    assert(gy[nt + 2] == naive_encoded_byte(gs, gx, nt + 2));
    assert(gy[nt + 3] == naive_encoded_byte(gs, gx, nt + 3));
    assert(naive_encoded_byte(gs, gx, nt) == gs[naive_enc_idx0(b0) as int]);
    assert(naive_encoded_byte(gs, gx, nt + 1) == gs[naive_enc_idx1(b0, b1) as int]);
    assert(naive_encoded_byte(gs, gx, nt + 2) == gs[naive_enc_idx2(b1, b2) as int]);
    assert(naive_encoded_byte(gs, gx, nt + 3) == gs[naive_enc_idx3(b2) as int]);
    assert(gt[gy[nt] as int] < 64);
    assert(gt[gy[nt + 1] as int] < 64);
    assert(gt[gy[nt + 2] as int] < 64);
    assert(gt[gy[nt + 3] as int] < 64);
    assert(ocql == 3 * q - 3);
    assert(zlen == 3 * q);
    assert(zlen >= ocql + 3);
}

/* ============================================================
 * Theorem 1: the universal-domain roundtrip through the naive oracle
 * ============================================================ */

/// For ANY input bytes x (up to the usize working slack), any 64-symbol
/// alphabet, any padding byte outside the alphabet and any decode table
/// paired with the alphabet: encode x canonically (the unpadded content plus
/// padding to the next quad boundary), then decode -- the result is Ok at
/// exactly x.len() and every decoded byte equals the original.
/* rlimit note (ledgered raise, this fn only): the whole-chain composition body
   check is over the default budget. It stayed unclosable at default across
   three restructure rounds (pin-lemma extraction, residue-split region joins,
   component-form table requires); with the front-check arithmetic hoisted
   ahead of the result match the query turns sound and the ladder is default
   fail, 100 fail, 200 fail, 300 green on this harness panel (the default-fail
   is re-measured at each round; the raise is this fn only). */
#[verifier::rlimit(300)]
pub exec fn roundtrip_naive_canonical(
    symbols: &[u8],
    x: &[u8],
    ebuf: &mut [u8],
    z: &mut [u8],
    decode_table: &[u8],
    padding: u8,
) -> (b: bool)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        32 <= padding as int <= 126,
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        /* the encode/decode pairing as its two components this composition
           consumes (the table maps each symbol to its index; the pad byte is
           no symbol of the alphabet) */
        forall|v: int| 0 <= v < 64 ==> decode_table@[(symbols[v]) as int] == v as u8,
        forall|v: int| 0 <= v < 64 ==> symbols[v] != padding,
        (x@.len() as int) <= usize::MAX as int / 16,
        (ebuf@.len() as int) == naive_unpadded_enc_len((x@.len() as int))
            + pad_bytes_model(naive_unpadded_enc_len((x@.len() as int))),
        (z@.len() as int) == (x@.len() as int),
    ensures
        b,
        final(z)@.len() == old(z)@.len(),
        forall|j: int|
            #![trigger final(z)@ [j]]
            0 <= j < (x@.len() as int) ==> final(z)@ [j] == x@ [j],
{
    let ghost gx = x@;
    let ghost gs = symbols@;
    let ghost gt = decode_table@;
    /* ---------- the encode half ---------- */
    let m = naive_internal_encode(symbols, x, ebuf);
    let ghost gy_enc = ebuf@;
    let ghost gm: int = m as int;
    proof {
        assert(m@ == naive_unpadded_enc_len(gx.len() as int));
        rt_len_classes(gx.len() as int);
        assert(gm == naive_unpadded_enc_len(gx.len() as int));
        rt_pad_arith(gm);
        assert(pad_bytes_model(gm) <= ebuf@.len() as int - gm);
    }
    let tail = &mut ebuf[m..];
    assert(tail@ == gy_enc.subrange(gm, gy_enc.len() as int));
    let p = add_padding(m, padding, tail);
    let total = m + p;
    let ghost gy = ebuf@;
    proof {
        assert(p@ == pad_bytes_model(gm));
        assert((total as int) == gm + pad_bytes_model(gm));
        rt_pad_arith(gm);
        assert((total as int) % 4 == 0);
        /* the padding phase: the padded positions per the tail slice map, the
           parent prefix untouched by the borrow */
        assert(p@ <= tail@.len());
        assert(forall|j: int| 0 <= j < p@ ==> tail@ [j] == padding);
        assert(forall|j: int|
            p@ <= j < tail@.len() ==> tail@ [j] == gy_enc[gm + j]);
        assert(forall|k: int| 0 <= k < gm ==> gy[k] == gy_enc[k]);
        assert(forall|k: int|
            #![trigger gy[k]] gm <= k < (total as int) ==> gy[k] == padding);
        assert(forall|k: int|
            #![trigger gy[k]] (total as int) <= k < gy.len() ==> gy[k] == gy_enc[k]);
        assert(forall|k: int|
            #![trigger gy[k]] 0 <= k < gm ==> gy[k] == naive_encoded_byte(gs, gx, k));
        assert(gy.len() == gy_enc.len());
    }
    /* ---------- the front check ---------- */
    /* the class arithmetic is established BEFORE the result match so the
       front-check's Ok-establishment clause (its named exclusions plus the
       output room) discharges the Err arm outright */
    let ghost gnt_model: int = nonterminal_quads_len_model((total as int), 0);
    proof {
        rt_front_arith(gx.len() as int, (total as int), gnt_model);
        assert((z@.len() as int) >= gnt_model / 4 * 3);
        assert(gnt_model % 4 == 0 && gnt_model >= 0);
    }
    let front = complete_quads_len(ebuf, 0, z.len(), decode_table, padding);
    let nt = match front {
        Result::Err(_) => return false,
        Result::Ok(v) => v,
    };
    proof {
        assert(nt@ == gnt_model);
    }
    let ocql = nt / 4 * 3;
    assert((ocql as int) == (nt as int) / 4 * 3);
    if x.len() == 0 {
        proof {
            assert((nt as int) == 0);
            assert((ocql as int) == 0);
            assert(gy.len() == 0);
        }
        let cq = decode_complete_quads(ebuf, 0, nt, decode_table, z, 0);
        match cq {
            Result::Err(_) => return false,
            Result::Ok(()) => (),
        }
        let suf = decode_suffix(
            ebuf,
            nt,
            z,
            ocql,
            decode_table,
            false,
            padding,
            DecodePaddingMode::RequireCanonical,
            Ghost(false),
        );
        match suf {
            Result::Err(_) => return false,
            Result::Ok(md) => {
                proof {
                    assert(ebuf@ == gy);
                    assert(md.decoded_len as int == 0);
                    assert(gx.len() == 0);
                }
                true
            }
        }
    } else {
        proof {
            assert((nt as int) == (total as int) - 4);
            assert((nt as int) % 4 == 0);
            assert(((nt as int) / 4 * 3) <= gx.len() as int);
            assert((nt as int) <= 4 * (gx.len() as int / 3));
        }
        /* the region legality and the per-position table-value facts */
        proof {
            naive_region_facts(gs, gt, gy, gx, (nt as int));
            assert((ocql as int) / 3 * 4 == (nt as int));
            naive_region_lo(gt, gy, gx, (ocql as int));
            naive_region_mid(gt, gy, gx, (ocql as int));
            naive_region_hi(gt, gy, gx, (ocql as int));
            nfi_skip(gy, gt, (nt as int), 0, (nt as int));
            assert(naive_first_invalid(gy, gt, (nt as int), 0) == (nt as int));
        }
        /* the suffix form pins (per input class) */
        proof {
            let r = gx.len() as int % 3;
            if r == 1 {
                naive_suffix_pin_r1(
                    gs,
                    gt,
                    gy,
                    gx,
                    (nt as int),
                    gm,
                    padding,
                    (z@.len() as int),
                    (ocql as int),
                    DecodePaddingMode::RequireCanonical,
                );
            } else if r == 2 {
                naive_suffix_pin_r2(
                    gs,
                    gt,
                    gy,
                    gx,
                    (nt as int),
                    gm,
                    padding,
                    (z@.len() as int),
                    (ocql as int),
                    DecodePaddingMode::RequireCanonical,
                );
            } else {
                naive_suffix_pin_r0(
                    gs,
                    gt,
                    gy,
                    gx,
                    (nt as int),
                    gm,
                    padding,
                    (z@.len() as int),
                    (ocql as int),
                );
            }
        }
        let cq = decode_complete_quads(ebuf, 0, nt, decode_table, z, 0);
        match cq {
            Result::Err(_) => return false,
            Result::Ok(()) => (),
        }
        let suf = decode_suffix(
            ebuf,
            nt,
            z,
            ocql,
            decode_table,
            false,
            padding,
            DecodePaddingMode::RequireCanonical,
            Ghost(true),
        );
        match suf {
            Result::Err(_) => return false,
            Result::Ok(md) => {
                if x.len() % 3 == 1 {
                    proof {
                        let q = gx.len() as int / 3;
                        let b0 = gx[q * 3];
                        assert((ocql as int) == 3 * q);
                        assert(gx.len() as int == 3 * q + 1);
                        assert(md.decoded_len as int == (ocql as int) + 1);
                        assert(md.decoded_len as int == gx.len() as int);
                        nai_lo(b0, 0);
                        assert(final(z)@ [(ocql as int)] == morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ));
                        assert(morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ) == b0);
                        assert(final(z)@ [(ocql as int)] == b0);
                    }
                    true
                } else if x.len() % 3 == 2 {
                    proof {
                        let q = gx.len() as int / 3;
                        let b0 = gx[q * 3];
                        let b1 = gx[q * 3 + 1];
                        assert((ocql as int) == 3 * q);
                        assert(gx.len() as int == 3 * q + 2);
                        assert(md.decoded_len as int == (ocql as int) + 2);
                        assert(md.decoded_len as int == gx.len() as int);
                        nai_lo(b0, b1);
                        nai_tail_mid(b0, b1);
                        assert(final(z)@ [(ocql as int)] == morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ));
                        assert(final(z)@ [(ocql as int) + 1] == morsel_pair_mid(
                            gt[gy[(nt as int) + 1] as int],
                            gt[gy[(nt as int) + 2] as int],
                        ));
                        assert(morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ) == b0);
                        assert(morsel_pair_mid(
                            gt[gy[(nt as int) + 1] as int],
                            gt[gy[(nt as int) + 2] as int],
                        ) == b1);
                        assert(final(z)@ [(ocql as int)] == b0);
                        assert(final(z)@ [(ocql as int) + 1] == b1);
                    }
                    true
                } else {
                    proof {
                        let q = gx.len() as int / 3;
                        let b0 = gx[q * 3 - 3];
                        let b1 = gx[q * 3 - 2];
                        let b2 = gx[q * 3 - 1];
                        assert((ocql as int) == 3 * (q - 1));
                        assert(gx.len() as int == 3 * q);
                        assert(md.decoded_len as int == (ocql as int) + 3);
                        assert(md.decoded_len as int == gx.len() as int);
                        nai_lo(b0, b1);
                        nai_mid(b0, b1, b2);
                        nai_hi(b1, b2);
                        assert(final(z)@ [(ocql as int)] == morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ));
                        assert(final(z)@ [(ocql as int) + 1] == morsel_pair_mid(
                            gt[gy[(nt as int) + 1] as int],
                            gt[gy[(nt as int) + 2] as int],
                        ));
                        assert(final(z)@ [(ocql as int) + 2] == morsel_pair_hi(
                            gt[gy[(nt as int) + 2] as int],
                            gt[gy[(nt as int) + 3] as int],
                        ));
                        assert(morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ) == b0);
                        assert(morsel_pair_mid(
                            gt[gy[(nt as int) + 1] as int],
                            gt[gy[(nt as int) + 2] as int],
                        ) == b1);
                        assert(morsel_pair_hi(
                            gt[gy[(nt as int) + 2] as int],
                            gt[gy[(nt as int) + 3] as int],
                        ) == b2);
                        assert(final(z)@ [(ocql as int)] == b0);
                        assert(final(z)@ [(ocql as int) + 1] == b1);
                        assert(final(z)@ [(ocql as int) + 2] == b2);
                    }
                    true
                }
            }
        }
    }
}

/* ============================================================
 * The gp-chain links: the scalar engine encodes through the shift-form
 * index models (enc_idx*) on the input domain len <= 26. The links below
 * equate them with the naive oracle's division-form models, so the scalar
 * chain rides the same decode composition as the naive theorem.
 * ============================================================ */

/// idx-link 0: b0 >> 2 == b0 / 4
pub proof fn gp_link_0(b0: u8)
    ensures
        naive_enc_idx0(b0) as u8 == enc_idx0(b0),
{
    let a = naive_enc_idx0(b0) as u8;
    assert(naive_enc_idx0(b0) == (b0 as u32) / 4);
    assert(a == b0 / 4);
    assert(a == enc_idx0(b0)) by (bit_vector)
        requires
            a == ((b0 / 4)),
}

/// idx-link 1: (b0<<4 | b1>>4) & 0x3F == b0%4*16 + b1/16
pub proof fn gp_link_1(b0: u8, b1: u8)
    ensures
        naive_enc_idx1(b0, b1) as u8 == enc_idx1(b0, b1),
{
    let a = naive_enc_idx1(b0, b1) as u8;
    assert(naive_enc_idx1(b0, b1) == (b0 as u32) % 4 * 16 + (b1 as u32) / 16);
    assert(a == b0 % 4 * 16 + b1 / 16);
    assert(a == enc_idx1(b0, b1)) by (bit_vector)
        requires
            a == ((b0 % 4) * 16 + (b1 / 16));
}

/// idx-link 2: (b1<<2 | b2>>6) & 0x3F == b1%16*4 + b2/64
pub proof fn gp_link_2(b1: u8, b2: u8)
    ensures
        naive_enc_idx2(b1, b2) as u8 == enc_idx2(b1, b2),
{
    let a = naive_enc_idx2(b1, b2) as u8;
    assert(naive_enc_idx2(b1, b2) == (b1 as u32) % 16 * 4 + (b2 as u32) / 64);
    assert(a == b1 % 16 * 4 + b2 / 64);
    assert(a == enc_idx2(b1, b2)) by (bit_vector)
        requires
            a == ((b1 % 16) * 4 + (b2 / 64));
}

/// idx-link 3: b2 & 0x3F == b2 % 64
pub proof fn gp_link_3(b2: u8)
    ensures
        naive_enc_idx3(b2) as u8 == enc_idx3(b2),
{
    let a = naive_enc_idx3(b2) as u8;
    assert(naive_enc_idx3(b2) == (b2 as u32) % 64);
    assert(a == b2 % 64);
    assert(a == enc_idx3(b2)) by (bit_vector)
        requires
            a == ((b2 % 64));
}

/// the chain's length model equals the naive length model on the harness domain
pub proof fn gp_len_eq_naive(n: int)
    requires
        0 <= n,
    ensures
        tail_unpadded_len(n) == naive_unpadded_enc_len(n),
{
}

/// per-position model agreement: the gp chain's byte at k (input_index 0) is the
/// naive oracle's byte at k (region positions and both tail classes)
pub proof fn gp_tail_eq_naive(gs: Seq<u8>, gx: Seq<u8>, k: int)
    requires
        gs.len() == 64,
        0 <= k < naive_unpadded_enc_len(gx.len() as int),
    ensures
        naive_encoded_byte(gs, gx, k) == enc_tail_byte(gs, gx, 0, k),
{
    let n = gx.len() as int;
    let q = n / 3;
    let r = n % 3;
    let comp = n - r;
    if k < comp / 3 * 4 {
        let c = k / 4;
        let pv = k % 4;
        let b0 = gx[c * 3];
        let b1 = gx[c * 3 + 1];
        let b2 = gx[c * 3 + 2];
        let base = 3 * c;
        assert(base + 2 < n);
        /* the chain's model at (input_index 0, k) resolves to this group */
        assert(enc_tail_byte(gs, gx, 0, k) == (if pv == 0 {
            gs[enc_idx0(gx[base]) as int]
        } else if pv == 1 {
            gs[enc_idx1(gx[base], gx[base + 1]) as int]
        } else if pv == 2 {
            gs[enc_idx2(gx[base + 1], gx[base + 2]) as int]
        } else {
            gs[enc_idx3(gx[base + 2]) as int]
        }));
        if pv == 0 {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx0(b0) as int]);
            gp_link_0(b0);
            assert(naive_enc_idx0(b0) as u8 == enc_idx0(gx[base]));
            assert(naive_encoded_byte(gs, gx, k) == enc_tail_byte(gs, gx, 0, k));
        } else if pv == 1 {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx1(b0, b1) as int]);
            gp_link_1(b0, b1);
            assert(naive_enc_idx1(b0, b1) as u8 == enc_idx1(gx[base], gx[base + 1]));
            assert(naive_encoded_byte(gs, gx, k) == enc_tail_byte(gs, gx, 0, k));
        } else if pv == 2 {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx2(b1, b2) as int]);
            gp_link_2(b1, b2);
            assert(naive_enc_idx2(b1, b2) as u8 == enc_idx2(gx[base + 1], gx[base + 2]));
            assert(naive_encoded_byte(gs, gx, k) == enc_tail_byte(gs, gx, 0, k));
        } else {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx3(b2) as int]);
            gp_link_3(b2);
            assert(naive_enc_idx3(b2) as u8 == enc_idx3(gx[base + 2]));
            assert(naive_encoded_byte(gs, gx, k) == enc_tail_byte(gs, gx, 0, k));
        }
    } else if r == 2 {
        let b0 = gx[comp];
        let b1 = gx[comp + 1];
        let pv = k - comp / 3 * 4;
        assert(pv == 0 || pv == 1 || pv == 2);
        assert(comp + 1 < n);
        assert(enc_tail_byte(gs, gx, 0, k) == (if pv == 0 {
            gs[enc_idx0(b0) as int]
        } else if pv == 1 {
            gs[enc_idx1(b0, b1) as int]
        } else {
            gs[enc_idx2(b1, 0) as int]
        }));
        if pv == 0 {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx0(b0) as int]);
            gp_link_0(b0);
        } else if pv == 1 {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx1(b0, b1) as int]);
            gp_link_1(b0, b1);
        } else {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx2(b1, 0) as int]);
            gp_link_2(b1, 0);
        }
        assert(naive_encoded_byte(gs, gx, k) == enc_tail_byte(gs, gx, 0, k));
    } else {
        /* r == 1 (r == 0 never indexes the tail region) */
        let b0 = gx[comp];
        let pv = k - comp / 3 * 4;
        assert(pv == 0 || pv == 1);
        assert(enc_tail_byte(gs, gx, 0, k) == (if pv == 0 {
            gs[enc_idx0(b0) as int]
        } else {
            gs[enc_idx1(b0, 0) as int]
        }));
        if pv == 0 {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx0(b0) as int]);
            gp_link_0(b0);
        } else {
            assert(naive_encoded_byte(gs, gx, k) == gs[naive_enc_idx1(b0, 0) as int]);
            gp_link_1(b0, 0);
        }
        assert(naive_encoded_byte(gs, gx, k) == enc_tail_byte(gs, gx, 0, k));
    }
}

/* ============================================================
 * Theorem 2: the scalar-chain subdomain roundtrip (input len <= 26)
 * ============================================================ */

/// The SAME roundtrip property over the scalar GeneralPurpose chain's verified
/// domain (encode_helper input len <= 26): encode via the u64 fast-path chain
/// plus add_padding, decode via the same verified composition. The chain's
/// shift-form index models are linked to the naive models, so both engines
/// ride the identical decode-side proof.
/* rlimit note (ledgered raise, this fn only): the body check fails at the
   default budget (re-measured after the gp-link restructure round; identical
   mass to the naive-theorem fn whose ladder is default/100/200 fail, 300
   green) -- 300 green on this harness panel. */
#[verifier::rlimit(300)]
pub exec fn roundtrip_scalar_26(
    symbols: &[u8],
    x: &[u8],
    ebuf: &mut [u8],
    z: &mut [u8],
    decode_table: &[u8],
    padding: u8,
) -> (b: bool)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
        32 <= padding as int <= 126,
        decode_table@.len() == 256,
        ValidDecodeTable(decode_table@),
        forall|v: int| 0 <= v < 64 ==> decode_table@[(symbols[v]) as int] == v as u8,
        forall|v: int| 0 <= v < 64 ==> symbols[v] != padding,
        (x@.len() as int) <= 26,
        (ebuf@.len() as int) == tail_unpadded_len((x@.len() as int))
            + pad_bytes_model(tail_unpadded_len((x@.len() as int))),
        (z@.len() as int) == (x@.len() as int),
    ensures
        b,
        final(z)@.len() == old(z)@.len(),
        forall|j: int|
            #![trigger final(z)@ [j]]
            0 <= j < (x@.len() as int) ==> final(z)@ [j] == x@ [j],
{
    let ghost gx = x@;
    let ghost gs = symbols@;
    let ghost gt = decode_table@;
    /* ---------- the encode half (the scalar chain) ---------- */
    let u = encode_helper(symbols, x, ebuf);
    let ghost gy_enc = ebuf@;
    let ghost gm: int = u as int;
    proof {
        assert(u@ == tail_unpadded_len(gx.len() as int));
        gp_len_eq_naive(gx.len() as int);
        rt_len_classes(gx.len() as int);
        assert(gm == naive_unpadded_enc_len(gx.len() as int));
        /* the chain's model bytes linked to the naive model bytes */
        assert(forall|k: int|
            #![trigger gy_enc[k]] 0 <= k < gm ==> gy_enc[k] == enc_tail_byte(
                gs,
                gx,
                0,
                k,
            ));
        rt_pad_arith(gm);
        assert(pad_bytes_model(gm) <= ebuf@.len() as int - gm);
    }
    let tail = &mut ebuf[u..];
    assert(tail@ == gy_enc.subrange(gm, gy_enc.len() as int));
    let p = add_padding(u, padding, tail);
    let total = u + p;
    let ghost gy = ebuf@;
    proof {
        assert(p@ == pad_bytes_model(gm));
        assert((total as int) == gm + pad_bytes_model(gm));
        rt_pad_arith(gm);
        assert((total as int) % 4 == 0);
        assert(p@ <= tail@.len());
        assert(forall|j: int| 0 <= j < p@ ==> tail@ [j] == padding);
        assert(forall|j: int|
            p@ <= j < tail@.len() ==> tail@ [j] == gy_enc[gm + j]);
        assert(forall|k: int| 0 <= k < gm ==> gy[k] == gy_enc[k]);
        assert(forall|k: int|
            #![trigger gy[k]] gm <= k < (total as int) ==> gy[k] == padding);
        assert(forall|k: int|
            #![trigger gy[k]] (total as int) <= k < gy.len() ==> gy[k] == gy_enc[k]);
        /* the joined byte model: chain bytes == naive model bytes per position
           (the gp links close the model agreement at each written position) */
        assert forall|k: int|
            #![trigger gy[k]] 0 <= k < gm ==> gy[k] == naive_encoded_byte(gs, gx, k) by {
            if 0 <= k < gm {
                assert(gy[k] == gy_enc[k]);
                assert(gy_enc[k] == enc_tail_byte(gs, gx, 0, k));
                gp_tail_eq_naive(gs, gx, k);
            }
        }
        assert(gy.len() == gy_enc.len());
    }
    /* ---------- the decode half (the same verified composition) ---------- */
    let ghost gnt_model: int = nonterminal_quads_len_model((total as int), 0);
    proof {
        rt_front_arith(gx.len() as int, (total as int), gnt_model);
        assert((z@.len() as int) >= gnt_model / 4 * 3);
        assert(gnt_model % 4 == 0 && gnt_model >= 0);
    }
    let front = complete_quads_len(ebuf, 0, z.len(), decode_table, padding);
    let nt = match front {
        Result::Err(_) => return false,
        Result::Ok(v) => v,
    };
    proof {
        assert(nt@ == gnt_model);
    }
    let ocql = nt / 4 * 3;
    assert((ocql as int) == (nt as int) / 4 * 3);
    if x.len() == 0 {
        proof {
            assert((nt as int) == 0);
            assert((ocql as int) == 0);
            assert(gy.len() == 0);
        }
        let cq = decode_complete_quads(ebuf, 0, nt, decode_table, z, 0);
        match cq {
            Result::Err(_) => return false,
            Result::Ok(()) => (),
        }
        let suf = decode_suffix(
            ebuf,
            nt,
            z,
            ocql,
            decode_table,
            false,
            padding,
            DecodePaddingMode::RequireCanonical,
            Ghost(false),
        );
        match suf {
            Result::Err(_) => return false,
            Result::Ok(md) => {
                proof {
                    assert(ebuf@ == gy);
                    assert(md.decoded_len as int == 0);
                    assert(gx.len() == 0);
                }
                true
            }
        }
    } else {
        proof {
            assert((nt as int) == (total as int) - 4);
            assert((nt as int) % 4 == 0);
            assert(((nt as int) / 4 * 3) <= gx.len() as int);
            assert((nt as int) <= 4 * (gx.len() as int / 3));
        }
        proof {
            naive_region_facts(gs, gt, gy, gx, (nt as int));
            assert((ocql as int) / 3 * 4 == (nt as int));
            naive_region_lo(gt, gy, gx, (ocql as int));
            naive_region_mid(gt, gy, gx, (ocql as int));
            naive_region_hi(gt, gy, gx, (ocql as int));
            nfi_skip(gy, gt, (nt as int), 0, (nt as int));
            assert(naive_first_invalid(gy, gt, (nt as int), 0) == (nt as int));
        }
        proof {
            let r = gx.len() as int % 3;
            if r == 1 {
                naive_suffix_pin_r1(
                    gs,
                    gt,
                    gy,
                    gx,
                    (nt as int),
                    gm,
                    padding,
                    (z@.len() as int),
                    (ocql as int),
                    DecodePaddingMode::RequireCanonical,
                );
            } else if r == 2 {
                naive_suffix_pin_r2(
                    gs,
                    gt,
                    gy,
                    gx,
                    (nt as int),
                    gm,
                    padding,
                    (z@.len() as int),
                    (ocql as int),
                    DecodePaddingMode::RequireCanonical,
                );
            } else {
                naive_suffix_pin_r0(
                    gs,
                    gt,
                    gy,
                    gx,
                    (nt as int),
                    gm,
                    padding,
                    (z@.len() as int),
                    (ocql as int),
                );
            }
        }
        let cq = decode_complete_quads(ebuf, 0, nt, decode_table, z, 0);
        match cq {
            Result::Err(_) => return false,
            Result::Ok(()) => (),
        }
        let suf = decode_suffix(
            ebuf,
            nt,
            z,
            ocql,
            decode_table,
            false,
            padding,
            DecodePaddingMode::RequireCanonical,
            Ghost(true),
        );
        match suf {
            Result::Err(_) => return false,
            Result::Ok(md) => {
                if x.len() % 3 == 1 {
                    proof {
                        let q = gx.len() as int / 3;
                        let b0 = gx[q * 3];
                        assert((ocql as int) == 3 * q);
                        assert(gx.len() as int == 3 * q + 1);
                        assert(md.decoded_len as int == (ocql as int) + 1);
                        assert(md.decoded_len as int == gx.len() as int);
                        nai_lo(b0, 0);
                        assert(final(z)@ [(ocql as int)] == morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ));
                        assert(morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ) == b0);
                        assert(final(z)@ [(ocql as int)] == b0);
                    }
                    true
                } else if x.len() % 3 == 2 {
                    proof {
                        let q = gx.len() as int / 3;
                        let b0 = gx[q * 3];
                        let b1 = gx[q * 3 + 1];
                        assert((ocql as int) == 3 * q);
                        assert(gx.len() as int == 3 * q + 2);
                        assert(md.decoded_len as int == (ocql as int) + 2);
                        assert(md.decoded_len as int == gx.len() as int);
                        nai_lo(b0, b1);
                        nai_tail_mid(b0, b1);
                        assert(final(z)@ [(ocql as int)] == morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ));
                        assert(final(z)@ [(ocql as int) + 1] == morsel_pair_mid(
                            gt[gy[(nt as int) + 1] as int],
                            gt[gy[(nt as int) + 2] as int],
                        ));
                        assert(morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ) == b0);
                        assert(morsel_pair_mid(
                            gt[gy[(nt as int) + 1] as int],
                            gt[gy[(nt as int) + 2] as int],
                        ) == b1);
                        assert(final(z)@ [(ocql as int)] == b0);
                        assert(final(z)@ [(ocql as int) + 1] == b1);
                    }
                    true
                } else {
                    proof {
                        let q = gx.len() as int / 3;
                        let b0 = gx[q * 3 - 3];
                        let b1 = gx[q * 3 - 2];
                        let b2 = gx[q * 3 - 1];
                        assert((ocql as int) == 3 * (q - 1));
                        assert(gx.len() as int == 3 * q);
                        assert(md.decoded_len as int == (ocql as int) + 3);
                        assert(md.decoded_len as int == gx.len() as int);
                        nai_lo(b0, b1);
                        nai_mid(b0, b1, b2);
                        nai_hi(b1, b2);
                        assert(final(z)@ [(ocql as int)] == morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ));
                        assert(final(z)@ [(ocql as int) + 1] == morsel_pair_mid(
                            gt[gy[(nt as int) + 1] as int],
                            gt[gy[(nt as int) + 2] as int],
                        ));
                        assert(final(z)@ [(ocql as int) + 2] == morsel_pair_hi(
                            gt[gy[(nt as int) + 2] as int],
                            gt[gy[(nt as int) + 3] as int],
                        ));
                        assert(morsel_pair_lo(
                            gt[gy[(nt as int)] as int],
                            gt[gy[(nt as int) + 1] as int],
                        ) == b0);
                        assert(morsel_pair_mid(
                            gt[gy[(nt as int) + 1] as int],
                            gt[gy[(nt as int) + 2] as int],
                        ) == b1);
                        assert(morsel_pair_hi(
                            gt[gy[(nt as int) + 2] as int],
                            gt[gy[(nt as int) + 3] as int],
                        ) == b2);
                        assert(final(z)@ [(ocql as int)] == b0);
                        assert(final(z)@ [(ocql as int) + 1] == b1);
                        assert(final(z)@ [(ocql as int) + 2] == b2);
                    }
                    true
                }
            }
        }
    }
}

} // verus!

fn main() {}
