//! faest 0.3.0 -- Verus transcription of src/fields/large_fields.rs,
//! batch FA3 (first wave: the GF(2^128) axis + the shared carry-less
//! multiply core).
//!
//! Upstream: fields/large_fields.rs (1826 lines, pin 9ccc68c0). This
//! twin covers, per the batch scope:
//!   - the shared carry-less multiply machinery: u128_clmul_64 (the
//!     64-rung mask loop, :91-99) with u128_clmul_ll/lh/hh (:61-88),
//!     karatsuba_mul_128 / karatsuba_mul_128_uncombined (:101-146),
//!     allignr_8bytes (:30-36) and the GF192/GF256 combiners' spec
//!     faces (:38-55, value-level, consumed at the [u128; 2] limbs);
//!   - the GF128 multiplication core gf128_mul (:858-886, karatsuba +
//!     Intel-paper reduction for x^128 + x^7 + x^2 + x + 1) with its
//!     Mul/MulAssign faces (:888-916);
//!   - the generic BigGF orbit machinery specialized at GF128:
//!     Modulus (:847-849), the ToMask/ApplyMask/ShiftLeft1 inlined
//!     single-limb selects (:582-627), Double (:746-762), Square
//!     (:766-791), Mul<GF64> (:680-705), the generic mul loop (:518-542,
//!     consumed at the extension fields), Mul<u8> (:668-678);
//!   - FromBit (:316-319, body :361-371), ByteCompose faces for BigGF
//!     (:375-402) with the GF128 constants of
//!     large_fields_constants.rs (:11-21) and ByteCombineConstants
//!     (:929-932);
//!   - the GF128 Field face: ZERO/ONE (:918-920), Length = U16 (:921),
//!     as_bytes (:923-926), From<&[u8]> (:934-941).
//!
//! Representation lowering (trust boundary, FA2 convention):
//!   - BigGF<u128, 1, 128> (GF128) lowers to a plain u128 (the
//!     single-limb array is documented at each face); the hybrid-array
//!     typenum Length spec lowers to byte counts (U16 -> 16).
//!   - The mask idiom `lhs & (-Wrapping(rhs & 1)).0` lowers to the
//!     select face `if rhs & 1 == 1 { lhs } else { 0 }` (the FA2
//!     cmov->select convention; upstream's constant-time shape -- no
//!     data-dependent branch, no early return -- is preserved in the
//!     twin, which is select-only and full-domain).
//!   - Alphas/Betas/Sigmas/ByteCombineSquared/SquareBytes/SumPoly
//!     trait towers: the declaration syntax drops at the trait
//!     boundary; the constant payloads that carry semantics are
//!     transcribed as const faces (first wave: the GF128 ALPHA
//!     payload; the rest are second-wave records).
//!
//! Model architecture (probe-decided, out/kverus-run/FA3/probe1/2):
//!   - clmul64_bits: the plain low-bit-Horner carry-less multiply over
//!     64-bit halves with a plain-shift orbit (matches the exec lhs
//!     register exactly; no reduction). THE exec obligation of the
//!     shared core is the 64-rung loop == this model, proven
//!     every-input (probe1).
//!   - gf128_mul_spec: the upstream algorithm's own composition
//!     (karatsuba over three clmul64_bits applications + the Intel
//!     reduction), as a pure spec fn; the exec twin gf128_mul equals
//!     it for every input by plain congruence (probe2) -- the only
//!     exec residue is the clmul loop, which is fully proven.
//!   - gf128_mul_bits / gf128_xtime: the independent textbook
//!     low-bit-Horner model ("hmul") over the full 128-bit domain
//!     with the xtime-orbit reduction -- the model the generic orbit
//!     loops (Double/Square/Mul<GF64>) are proven against. The
//!     full-quantifier bridge mul_spec == hmul is DEFERRED: closing it
//!     needs mod-f linearity (reduce commutes with the linear sum),
//!     which is outside this batch's blast budgets; the harness closes
//!     it at the sample level with dual chains over the upstream
//!     LargeFieldMul.json lambda==128 tuples (both models chain
//!     independently to the KAT constants).

use vstd::prelude::*;
// FA11-beta: upstream large_fields.rs :25 imports GF8 from the
// parent fields mod (`use super::{Double, ExtensionField, Field,
// GF8, GF64, Square};`); the twin re-spells the GF8 entry to the
// sibling module (every mount of this file pairs it with
// small_fields.rs -- the lib.rs fields tree, the ut_fa3
// harness mount, and every #[path] driver).
use super::small_fields::{gf8_ref_square_spread, gf8_square_bits};

verus! {

// ===========================================================================
// Constants (upstream large_fields.rs :27-28, :847-849, :918-922).
// Origin Rust:
//     const U128_LOWER_MASK: u128 = u64::MAX as u128;
//     impl Modulus<u128> for BigGF<u128, 1, 128> {
//         const MODULUS: u128 = 0b10000111u128; }
//     impl Field for BigGF<u128, 1, 128> {
//         const ZERO: Self = Self([0]);
//         const ONE: Self = Self([1]);
//         type Length = U16; }
// The modulus 0x87 is the low half of x^128 + x^7 + x^2 + x + 1.
// ===========================================================================

/// Upstream U128_LOWER_MASK (:28): the low-64 selection mask.
pub const U128_LOWER_MASK: u128 = 0xFFFF_FFFF_FFFF_FFFF;

/// Reduction-polynomial low half for GF(2^128) (upstream `MODULUS`,
/// large_fields.rs :848).
pub const GF128_MODULUS: u128 = 0x87;

/// Field::Length of GF128 (upstream `type Length = U16`) at the
/// byte-count lowering (16 bytes == 128 bits).
pub const GF128_LENGTH_BYTES: usize = 16;

/// Field::ZERO for GF128 (:919), value face over the lowered u128.
pub const GF128_ZERO: u128 = 0;

/// Field::ONE for GF128 (:920), value face.
pub const GF128_ONE: u128 = 1;

// ===========================================================================
// Spec models.
// ===========================================================================

/// Carry-less multiplication of two 64-bit polynomials over GF(2)
/// (model of upstream u128_clmul_64, :91-99): low-bit Horner over the
/// multiplier with a plain-shift orbit, no reduction; high bits wrap
/// off exactly like the exec register. Fuel `w`; `w == 64` covers the
/// full u64 operand domain.
pub open spec fn clmul64_bits(orbit: u128, r_tail: u128, w: nat) -> u128
    decreases w,
{
    if w == 0 {
        0u128
    } else {
        (if r_tail & 1 == 1 { orbit } else { 0u128 })
            ^ clmul64_bits(orbit << 1, r_tail >> 1, (w - 1) as nat)
    }
}

/// The GF(2^128) orbit step: v * x in the field (shift up, then
/// conditionally reduce by the low half of x^128 + x^7 + x^2 + x + 1).
pub open spec fn gf128_xtime(v: u128) -> u128 {
    (v << 1) ^ (if (v >> 127) & 1 == 1 { GF128_MODULUS } else { 0u128 })
}

/// The textbook GF(2^128) multiplication ("hmul"): low-bit Horner
/// over the multiplier with the xtime orbit; fuel `w`.
pub open spec fn gf128_mul_bits(orbit: u128, r_tail: u128, w: nat) -> u128
    decreases w,
{
    if w == 0 {
        0u128
    } else {
        (if r_tail & 1 == 1 { orbit } else { 0u128 })
            ^ gf128_mul_bits(gf128_xtime(orbit), r_tail >> 1, (w - 1) as nat)
    }
}

/// The full 128-bit-domain hmul face -- the model of the generic
/// orbit-loop faces below (Double/Square/Mul<GF64> at fuel 64).
pub open spec fn gf128_hmul(l: u128, r: u128) -> u128 {
    gf128_mul_bits(l, r, 128nat)
}

/// Origin Rust (large_fields.rs :30-36):
///     /// Takes two 128-bit integers `x = x_l + 2^64 * x_h` and
///     /// `y = y_l + 2^64 y_h`.
///     /// Returns `y_h + 2^64 x_l`.
///     const fn allignr_8bytes(x: u128, y: u128) -> u128 {
///         x << 64 ^ y >> 64 }
/// Value face (the GF192/GF256 combiners consume it; upstream
/// doc-comment slip noted: the returned value is x_l in the low half
/// and y_h in the high half, the doc's value order transcribed
/// verbatim above).
pub open spec fn allignr_8bytes(x: u128, y: u128) -> u128 {
    (x << 64) ^ (y >> 64)
}

/// The Intel-paper reduction of a 256-bit carry-less product (lo
/// bottom limb, hi top limb) to GF(2^128) (upstream gf128_mul steps
/// 1-4, :866-885, expression-preserving lowering of the spec).
pub open spec fn gf128_reduce(lo: u128, hi: u128) -> u128 {
    // Step 1
    let x2 = hi & U128_LOWER_MASK;
    let x3 = hi >> 64;
    let a = x3 >> 63;
    let b = x3 >> 62;
    let c = x3 >> 57;
    // Step 2
    let x3_d = (x3 << 64) ^ x2 ^ a ^ b ^ c;
    // Step 3
    let e1_e0 = x3_d << 1;
    let f1_f0 = x3_d << 2;
    let g1_g0 = x3_d << 7;
    // Step 4
    let h1_h0 = x3_d ^ e1_e0 ^ f1_f0 ^ g1_g0;
    lo ^ h1_h0
}

/// Karatsuba recombination, spec faces (upstream karatsuba_mul_128
/// :119-129 resp. karatsuba_mul_128_uncombined :105-114).
pub open spec fn gf128_karatsuba_mid(x: u128, y: u128) -> u128 {
    let lo = clmul64_bits(x & U128_LOWER_MASK, y & U128_LOWER_MASK, 64nat);
    let hi = clmul64_bits(x >> 64, y >> 64, 64nat);
    let xs = (x >> 64) ^ (x & U128_LOWER_MASK);
    let ys = (y >> 64) ^ (y & U128_LOWER_MASK);
    clmul64_bits(xs, ys, 64nat) ^ lo ^ hi
}

pub open spec fn gf128_karatsuba_lo(x: u128, y: u128) -> u128 {
    let lo = clmul64_bits(x & U128_LOWER_MASK, y & U128_LOWER_MASK, 64nat);
    lo ^ (gf128_karatsuba_mid(x, y) << 64)
}

pub open spec fn gf128_karatsuba_hi(x: u128, y: u128) -> u128 {
    let hi = clmul64_bits(x >> 64, y >> 64, 64nat);
    hi ^ (gf128_karatsuba_mid(x, y) >> 64)
}

/// The GF(2^128) multiplication spec face (upstream karatsuba_mul_128
/// + the Intel reduction; the docstring chain :858-886).
pub open spec fn gf128_mul_spec(x: u128, y: u128) -> u128 {
    gf128_reduce(gf128_karatsuba_lo(x, y), gf128_karatsuba_hi(x, y))
}

// ===========================================================================
// Machine-level xor lemma bank (bit_vector-verified at u128 width);
// every loop-invariant regroup routes through these (the plain
// encoding does not fold xor commutativity by itself: probe1).
// ===========================================================================

proof fn bv_xor_comm128(a: u128, b: u128)
    ensures
        (a ^ b) == (b ^ a),
{
    assert((a ^ b) == (b ^ a)) by (bit_vector);
}

proof fn bv_xor_ac128(a: u128, b: u128, c: u128)
    ensures
        ((a ^ b) ^ c) == (a ^ (b ^ c)),
        ((a ^ b) ^ c) == (b ^ (c ^ a)),
{
    assert((a ^ b) ^ c == a ^ (b ^ c)) by (bit_vector);
    assert((a ^ b) ^ c == b ^ (c ^ a)) by (bit_vector);
}

proof fn bv_xor_zero128(t: u128)
    ensures
        (0u128 ^ t) == t,
{
    assert((0u128 ^ t) == t) by (bit_vector);
}

proof fn bv_xor_zero_l_fold(t: u128)
    ensures
        (t ^ 0u128) == t,
{
    assert((t ^ 0u128) == t) by (bit_vector);
}

proof fn bv_xor_cancel128(a: u128, b: u128)
    ensures
        ((a ^ b) ^ b) == a,
{
    assert(((a ^ b) ^ b) == a) by (bit_vector);
}

proof fn bv_concrete_zero128()
    ensures
        (0u128 & 1) == 0u128,
        !(0u128 & 1 == 1),
{
    assert((0u128 & 1) == 0u128) by (bit_vector);
}

// ===========================================================================
// Model-level lemmas (the FA2 library shape).
// ===========================================================================

/// Definitional one-level unfold of the clmul model at non-zero fuel.
pub proof fn lemma_clmul64_bits_unfold(o: u128, q: u128, w: nat)
    requires
        0 < w,
    ensures
        clmul64_bits(o, q, w)
            == (if q & 1 == 1 { o } else { 0u128 })
                ^ clmul64_bits(o << 1, q >> 1, (w - 1) as nat),
{
}

/// Definitional one-level unfold of the hmul model at non-zero fuel.
pub proof fn lemma_hmul128_bits_unfold(o: u128, q: u128, w: nat)
    requires
        0 < w,
    ensures
        gf128_mul_bits(o, q, w)
            == (if q & 1 == 1 { o } else { 0u128 })
                ^ gf128_mul_bits(gf128_xtime(o), q >> 1, (w - 1) as nat),
{
}

/// Zero-tail collapse for the clmul model (any remaining fuel).
pub proof fn lemma_clmul64_zero_tail(o: u128, w: nat)
    ensures
        clmul64_bits(o, 0u128, w) == 0u128,
    decreases w,
{
    if w == 0 {
    } else {
        bv_concrete_zero128();
        assert((0u128 & 1) == 0u128);
        assert(!(0u128 & 1 == 1));
        assert((0u128 >> 1) == 0u128) by (bit_vector);
        lemma_clmul64_bits_unfold(o, 0u128, w);
        assert((if 0u128 & 1 == 1 { o } else { 0u128 }) == 0u128);
        bv_xor_zero128(clmul64_bits(o << 1, 0u128, (w - 1) as nat));
        lemma_clmul64_zero_tail(o << 1, (w - 1) as nat);
    }
}

/// Zero-tail collapse for the hmul model (any remaining fuel).
pub proof fn lemma_hmul128_zero_tail(o: u128, w: nat)
    ensures
        gf128_mul_bits(o, 0u128, w) == 0u128,
    decreases w,
{
    if w == 0 {
    } else {
        bv_concrete_zero128();
        assert((0u128 & 1) == 0u128);
        assert(!(0u128 & 1 == 1));
        assert((0u128 >> 1) == 0u128) by (bit_vector);
        lemma_hmul128_bits_unfold(o, 0u128, w);
        assert((if 0u128 & 1 == 1 { o } else { 0u128 }) == 0u128);
        bv_xor_zero128(gf128_mul_bits(gf128_xtime(o), 0u128, (w - 1) as nat));
        lemma_hmul128_zero_tail(gf128_xtime(o), (w - 1) as nat);
    }
}

/// One-tail collapse for the hmul model: multiplier == 1 gives the
/// orbit itself, at any non-zero fuel (bit 0 carries the whole
/// contribution).
pub proof fn lemma_hmul128_one_tail(o: u128, w: nat)
    requires
        0 < w,
    ensures
        gf128_mul_bits(o, 1u128, w) == o,
{
    assert((1u128 & 1) == 1u128) by (bit_vector);
    lemma_hmul128_bits_unfold(o, 1u128, w);
    assert((if (1u128 & 1) == 1u128 { o } else { 0u128 }) == o);
    assert(1u128 >> 1 == 0u128) by (bit_vector);
    lemma_hmul128_zero_tail(gf128_xtime(o), (w - 1) as nat);
    assert(gf128_mul_bits(o, 1u128, w)
        == o ^ gf128_mul_bits(gf128_xtime(o), 0u128, (w - 1) as nat));
    bv_xor_zero_l_fold(o);
}

/// Left annihilation for the clmul model: the zero orbit stays zero
/// (the plain-shift orbit is stationary at zero), every input, full
/// domain.
pub proof fn lemma_clmul64_zero_l(r: u128)
    ensures
        clmul64_bits(0u128, r, 64nat) == 0u128,
{
    lemma_clmul64_zero_l_fuel(r, 64nat);
}

proof fn lemma_clmul64_zero_l_fuel(r: u128, w: nat)
    ensures
        clmul64_bits(0u128, r, w) == 0u128,
    decreases w,
{
    if w == 0 {
    } else {
        assert((0u128 << 1) == 0u128) by (bit_vector);
        lemma_clmul64_bits_unfold(0u128, r, w);
        assert((if r & 1 == 1 { 0u128 } else { 0u128 }) == 0u128);
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
        lemma_clmul64_zero_l_fuel(r >> 1, (w - 1) as nat);
    }
}

/// Right multiplicative identity for the clmul model (multiplier 1, bit
/// 0 only).
pub proof fn lemma_clmul64_one_r(l: u128)
    ensures
        clmul64_bits(l, 1u128, 64nat) == l,
{
    assert((1u128 & 1) == 1u128) by (bit_vector);
    lemma_clmul64_bits_unfold(l, 1u128, 64nat);
    assert((if (1u128 & 1) == 1u128 { l } else { 0u128 }) == l);
    assert(1u128 >> 1 == 0u128) by (bit_vector);
    lemma_clmul64_zero_tail(l << 1, 63nat);
    assert(clmul64_bits(l, 1u128, 64nat)
        == l ^ clmul64_bits(l << 1, 0u128, 63nat));
    bv_xor_zero_l_fold(l);
}

/// Left annihilation for the hmul model (xtime keeps zero at zero).
pub proof fn lemma_hmul128_zero_l(r: u128)
    ensures
        gf128_hmul(0u128, r) == 0u128,
{
    lemma_hmul128_zero_l_fuel(r, 128nat);
}

proof fn lemma_hmul128_zero_l_fuel(r: u128, w: nat)
    ensures
        gf128_mul_bits(0u128, r, w) == 0u128,
    decreases w,
{
    if w == 0 {
    } else {
        assert((((0u128 << 1) ^ (if ((0u128 >> 127) & 1) == 1u128 { GF128_MODULUS } else { 0u128 }))) == 0u128) by (bit_vector);
        lemma_hmul128_bits_unfold(0u128, r, w);
        assert((if r & 1 == 1 { 0u128 } else { 0u128 }) == 0u128);
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
        lemma_hmul128_zero_l_fuel(r >> 1, (w - 1) as nat);
    }
}

/// Right annihilation of the field mul: mul_spec(x, 0) == 0 (upstream
/// mul_bit test line `anything * F::ZERO == F::ZERO`,
/// large_fields.rs:1615-1617, proven here at the mul face).
pub proof fn lemma_mul128_zero_r(x: u128)
    ensures
        gf128_mul_spec(x, 0u128) == 0u128,
{
    // the three clmul sites of the karatsuba fold all annihilate
    lemma_clmul64_zero_tail(x & U128_LOWER_MASK, 64nat);
    lemma_clmul64_zero_tail(x >> 64, 64nat);
    lemma_clmul64_zero_tail((x >> 64) ^ (x & U128_LOWER_MASK), 64nat);
    // constant subs of y == 0 in the folded expression planes
    assert(((0u128 & U128_LOWER_MASK) == 0u128)) by (bit_vector);
    assert(((0u128 >> 64) == 0u128)) by (bit_vector);
    assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    assert((0u128 << 64) == 0u128) by (bit_vector);
    assert((0u128 >> 63) == 0u128) by (bit_vector);
    assert((0u128 >> 62) == 0u128) by (bit_vector);
    assert((0u128 >> 57) == 0u128) by (bit_vector);
    assert((0u128 << 1) == 0u128) by (bit_vector);
    assert((0u128 << 2) == 0u128) by (bit_vector);
    assert((0u128 << 7) == 0u128) by (bit_vector);
    // karatsuba mid/lo/hi all zero at y == 0
    assert(gf128_karatsuba_mid(x, 0u128) == 0u128);
    assert(gf128_karatsuba_lo(x, 0u128) == 0u128);
    assert(gf128_karatsuba_hi(x, 0u128) == 0u128);
    assert(gf128_reduce(0u128, 0u128) == 0u128);
}

/// The field multiplicative identity: mul_spec(x, 1) == x -- the
/// upstream mul_bit test `anything * 1u8` closes at its Mul<u8> face
/// and the general model identity here. Route: y == 1 degenerates the
/// karatsuba fold to (lo, hi) == (x, 0) via one_r + xor-cancel, and
/// reduce(x, 0) == x (every hi-side term vanishes as a constant).
pub proof fn lemma_mul128_one_r(x: u128)
    ensures
        gf128_mul_spec(x, 1u128) == x,
{
    // constant halves of y == 1
    assert((1u128 & U128_LOWER_MASK) == 1u128) by (bit_vector);
    assert((1u128 >> 64) == 0u128) by (bit_vector);
    assert(((1u128 >> 64) ^ (1u128 & U128_LOWER_MASK)) == 1u128) by (bit_vector);
    // model degeneracies at y == 1
    lemma_clmul64_one_r(x & U128_LOWER_MASK);
    lemma_clmul64_one_r((x >> 64) ^ (x & U128_LOWER_MASK));
    lemma_clmul64_zero_tail(x >> 64, 64nat);
    // const recombination planes
    assert((0u128 ^ 1u128) == 1u128) by (bit_vector);
    assert((0u128 << 64) == 0u128) by (bit_vector);
    // name the three clmul sites exactly as the mid definition spells
    // them, then bridge through the def lemma
    let loS: u128 = clmul64_bits(x & U128_LOWER_MASK, (1u128 & U128_LOWER_MASK), 64nat);
    let hiS: u128 = clmul64_bits(x >> 64, (1u128 >> 64), 64nat);
    let xsS: u128 = (x >> 64) ^ (x & U128_LOWER_MASK);
    let ysS: u128 = (1u128 >> 64) ^ (1u128 & U128_LOWER_MASK);
    assert(loS == (x & U128_LOWER_MASK));
    assert(hiS == 0u128);
    assert(ysS == 1u128);
    assert(clmul64_bits(xsS, ysS, 64nat) == xsS) by {
        lemma_clmul64_one_r(xsS);
    }
    let mid_v: u128 = xsS ^ loS ^ hiS;
    assert(gf128_karatsuba_mid(x, 1u128) == mid_v) by {
        lemma_karatsuba_mid_def(x, 1u128);
    }
    // xor-cancel: xsS ^ (x & M) == x >> 64
    // explicit regroup: (xsS ^ loS) ^ hiS == xsS ^ (loS ^ hiS)
    bv_xor_ac128(xsS, loS, hiS);
    assert(mid_v == (xsS ^ loS) ^ hiS);
    bv_xor_cancel128((x >> 64), (x & U128_LOWER_MASK));
    assert(xsS == ((x >> 64) ^ (x & U128_LOWER_MASK)));
    assert(loS == (x & U128_LOWER_MASK));
    assert((xsS ^ loS) == (x >> 64));
    assert((loS ^ hiS) == ((x & U128_LOWER_MASK) ^ 0u128));
    bv_xor_zero_l_fold(x & U128_LOWER_MASK);
    assert((loS ^ hiS) == (x & U128_LOWER_MASK));
    assert(mid_v == (x >> 64));
    assert(gf128_karatsuba_mid(x, 1u128) == (x >> 64));
    // recombination over the 2^64 boundary (probe3-verified blasts)
    assert((((x >> 64) << 64) ^ (x & U128_LOWER_MASK)) == x) by (bit_vector);
    assert(gf128_karatsuba_lo(x, 1u128)
        == loS ^ ((gf128_karatsuba_mid(x, 1u128)) << 64)) by {
        lemma_karatsuba_lo_def(x, 1u128);
    }
    assert(loS == (x & U128_LOWER_MASK));
    assert(gf128_karatsuba_lo(x, 1u128)
        == (x & U128_LOWER_MASK) ^ ((x >> 64) << 64));
    bv_xor_comm128(((x >> 64) << 64), (x & U128_LOWER_MASK));
    assert((((x >> 64) << 64) ^ (x & U128_LOWER_MASK)) == ((x & U128_LOWER_MASK) ^ ((x >> 64) << 64)));
    assert((((x >> 64) << 64) ^ (x & U128_LOWER_MASK)) == x);
    assert(gf128_karatsuba_lo(x, 1u128) == x);
    assert(((x >> 64) >> 64) == 0u128) by (bit_vector);
    assert(gf128_karatsuba_hi(x, 1u128)
        == hiS ^ ((gf128_karatsuba_mid(x, 1u128)) >> 64)) by {
        lemma_karatsuba_hi_def(x, 1u128);
    }
    assert(hiS == 0u128);
    assert(((x >> 64) >> 64) == 0u128) by (bit_vector);
    assert(((x >> 64) ^ 0u128) == (x >> 64));
    bv_xor_zero128((x >> 64) >> 64);
    assert(gf128_karatsuba_hi(x, 1u128) == (0u128 ^ 0u128));
    assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    assert(gf128_karatsuba_hi(x, 1u128) == 0u128);
    // reduce(x, 0) == x: all hi-side terms vanish as constants
    assert(((0u128 & U128_LOWER_MASK) == 0u128)) by (bit_vector);
    assert(((0u128 >> 64) == 0u128)) by (bit_vector);
    assert(gf128_reduce(x, 0u128) == x) by {
        assert(((0u128 >> 63) == 0u128)) by (bit_vector);
        assert(((0u128 >> 62) == 0u128)) by (bit_vector);
        assert(((0u128 >> 57) == 0u128)) by (bit_vector);
        assert(((0u128 << 64) == 0u128)) by (bit_vector);
        assert(((0u128 << 1) == 0u128)) by (bit_vector);
        assert(((0u128 << 2) == 0u128)) by (bit_vector);
        assert(((0u128 << 7) == 0u128)) by (bit_vector);
        assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
        bv_xor_zero_l_fold(x);
    }
    assert(gf128_mul_spec(x, 1u128) == x) by {
        lemma_mul128_spec_def(x, 1u128);
    }
}

// ===========================================================================
// Definitional bridge lemmas (helper spec fns are open, but their
// definition axioms need an explicit instantiation point in the
// dependent proofs -- probe3 pattern; each bridge is checkable by
// definitional unfolding alone).
// ===========================================================================

/// Definitional bridge of the karatsuba mid composition.
pub proof fn lemma_karatsuba_mid_def(x: u128, y: u128)
    ensures
        gf128_karatsuba_mid(x, y)
            == clmul64_bits((x >> 64) ^ (x & U128_LOWER_MASK),
                (y >> 64) ^ (y & U128_LOWER_MASK), 64nat) ^ clmul64_bits(
                x & U128_LOWER_MASK, y & U128_LOWER_MASK, 64nat) ^ clmul64_bits(
                x >> 64, y >> 64, 64nat),
{
}

/// Definitional bridge of the karatsuba lo recombination.
pub proof fn lemma_karatsuba_lo_def(x: u128, y: u128)
    ensures
        gf128_karatsuba_lo(x, y)
            == clmul64_bits(x & U128_LOWER_MASK, y & U128_LOWER_MASK, 64nat)
                ^ ((gf128_karatsuba_mid(x, y)) << 64),
{
}

/// Definitional bridge of the karatsuba hi recombination.
pub proof fn lemma_karatsuba_hi_def(x: u128, y: u128)
    ensures
        gf128_karatsuba_hi(x, y)
            == clmul64_bits(x >> 64, y >> 64, 64nat)
                ^ ((gf128_karatsuba_mid(x, y)) >> 64),
{
}

/// Definitional bridge of the mul_spec composition.
pub proof fn lemma_mul128_spec_def(x: u128, y: u128)
    ensures
        gf128_mul_spec(x, y)
            == gf128_reduce(gf128_karatsuba_lo(x, y), gf128_karatsuba_hi(x, y)),
{
}

// ===========================================================================
// u128_clmul_64 (upstream large_fields.rs :91-99) -- the shared
// carry-less multiplication heart of all three large-field cores.
// Origin Rust:
//     #[inline]
//     fn u128_clmul_64(mut lhs: u128, mut rhs: u128) -> u128 {
//         let mut res = lhs & (-Wrapping(rhs & 1)).0;
//         for _ in 1..64 {
//             lhs <<= 1;
//             rhs >>= 1;
//             res ^= lhs & (-Wrapping(rhs & 1)).0;
//         }
//         res }
// Loop shape preserved verbatim apart from the mask idiom lowering
// (head note); no early return; the loop walks every bit 1..64.
// Obligation machine-checked: the loop computes the plain model
// clmul64_bits(lhs0, rhs0, 64) for EVERY input.
// ===========================================================================

pub exec fn u128_clmul_64(lhs0: u128, rhs0: u128) -> (res: u128)
    ensures
        res == clmul64_bits(lhs0, rhs0, 64nat),
{
    let mut lhs: u128 = lhs0;
    let mut rhs: u128 = rhs0;
    proof {
        lemma_clmul64_bits_unfold(lhs0, rhs0, 64nat);
    }
    let sel0: u128 = if rhs & 1 == 1 { lhs } else { 0u128 };
    let mut res: u128 = sel0;
    proof {
        assert(sel0 == (if rhs0 & 1 == 1 { lhs0 } else { 0u128 }));
        let tail0: u128 = clmul64_bits(lhs0 << 1, rhs0 >> 1, 63nat);
        assert(clmul64_bits(lhs0, rhs0, 64nat)
            == sel0 ^ tail0);
        bv_xor_comm128(tail0, sel0);
        assert((tail0 ^ sel0) == (sel0 ^ tail0));
        assert(res == sel0);
        assert((tail0 ^ res) == clmul64_bits(lhs0, rhs0, 64nat));
    }
    let mut i: usize = 1;
    while i < 64
        invariant
            1 <= i <= 64,
            (clmul64_bits(lhs << 1, rhs >> 1, (64 - i) as nat) ^ res)
                == clmul64_bits(lhs0, rhs0, 64nat),
        decreases 64 - i,
    {
        let lhs_o: u128 = lhs;
        let rhs_o: u128 = rhs;
        let res_o: u128 = res;
        lhs = lhs_o << 1;
        rhs = rhs_o >> 1;
        proof {
            lemma_clmul64_bits_unfold(lhs, rhs, (64 - i) as nat);
        }
        let sel: u128 = if rhs & 1 == 1 { lhs } else { 0u128 };
        res = res_o ^ sel;
        proof {
            let w: nat = (64 - i) as nat;
            let spec: u128 = clmul64_bits(lhs0, rhs0, 64nat);
            let tail_old: u128 = clmul64_bits(lhs, rhs, w);
            let tail_new: u128 = clmul64_bits(lhs << 1, rhs >> 1, (w - 1) as nat);
            assert((tail_old ^ res_o) == spec);
            assert(tail_old == (if rhs & 1 == 1 { lhs } else { 0u128 }) ^ tail_new);
            assert(sel == (if rhs & 1 == 1 { lhs } else { 0u128 }));
            assert(spec == (sel ^ tail_new) ^ res_o);
            bv_xor_comm128(sel, tail_new);
            assert((sel ^ tail_new) ^ res_o == (tail_new ^ sel) ^ res_o);
            bv_xor_ac128(tail_new, sel, res_o);
            assert((tail_new ^ sel) ^ res_o == tail_new ^ (sel ^ res_o));
            assert(res == res_o ^ sel);
            bv_xor_comm128(res_o, sel);
            assert(res_o ^ sel == sel ^ res_o);
            assert(tail_new ^ res == tail_new ^ (sel ^ res_o));
            assert(tail_new ^ (sel ^ res_o) == tail_new ^ (res_o ^ sel));
            assert(tail_new ^ res == spec);
        }
        i += 1;
    }
    proof {
        assert(clmul64_bits(lhs << 1, rhs >> 1, 0nat) == 0u128);
        assert((0u128 ^ res) == res) by (bit_vector);
    }
    res
}

/// Origin Rust (large_fields.rs :57-66):
///     /// Perform a carry-less multiplication of two 64-bit polynomials
///     /// over the finite field GF(2). This function takes the lower
///     /// halves of both lhs and rhs.
///     fn u128_clmul_ll(lhs: u128, rhs: u128) -> u128 {
///         let (lhs, rhs) = (lhs & U128_LOWER_MASK, rhs & U128_LOWER_MASK);
///         u128_clmul_64(lhs, rhs) }
#[inline]
pub exec fn u128_clmul_ll(lhs: u128, rhs: u128) -> (res: u128)
    ensures
        res == clmul64_bits(lhs & U128_LOWER_MASK, rhs & U128_LOWER_MASK, 64nat),
{
    u128_clmul_64(lhs & U128_LOWER_MASK, rhs & U128_LOWER_MASK)
}

/// Origin Rust (large_fields.rs :68-77, "takes the upper halves of
/// both lhs and rhs"): high-half selection then the shared core.
#[inline]
pub exec fn u128_clmul_hh(lhs: u128, rhs: u128) -> (res: u128)
    ensures
        res == clmul64_bits(lhs >> 64, rhs >> 64, 64nat),
{
    u128_clmul_64(lhs >> 64, rhs >> 64)
}

/// Origin Rust (large_fields.rs :79-88):
///     /// Perform a carry-less multiplication of two 64-bit
///     /// polynomials over the finite field GF(2). This function
///     /// takes the upper half of lhs and the lower half of rhs.
///     fn u128_clmul_lh(lhs: u128, rhs: u128) -> u128 {
///         let (lhs, rhs) = (lhs & U128_LOWER_MASK, rhs >> 64);   // doc/comment slip: "lower halves"
///         u128_clmul_64(lhs, rhs) }
/// (inside the body upstream's selection comment reads "// Select
/// lower 64 bits from lhs and rhs" while the code selects rhs's UPPER
/// half -- upstream comment slip recorded, body verbatim).
#[inline]
pub exec fn u128_clmul_lh(lhs: u128, rhs: u128) -> (res: u128)
    ensures
        res == clmul64_bits(lhs & U128_LOWER_MASK, rhs >> 64, 64nat),
{
    u128_clmul_64(lhs & U128_LOWER_MASK, rhs >> 64)
}

// ===========================================================================
// Karatsuba recombination (upstream large_fields.rs :101-146).
// ===========================================================================

/// Origin Rust (large_fields.rs :101-114):
///     /// Splits `lhs` and `rhs` into four 64-bit polynomials over
///     /// GF(2) and uses [`u128_clmul_64`] to perform karatsuba
///     /// multiplication.
///     /// Returns the resulting 256-bit polynomial `res` in
///     /// uncombined form (i.e., `lhs * rhs = res[0] + 2^64 * res[1]
///     /// + 2^128 * res[2]`).
///     fn karatsuba_mul_128_uncombined(lhs: u128, rhs: u128) -> [u128; 3] {
///         let lo = u128_clmul_ll(lhs, rhs);
///         let hi = u128_clmul_hh(lhs, rhs);
///         let lhs_sum = (lhs >> 64) ^ lhs & U128_LOWER_MASK;
///         let rhs_sum = (rhs >> 64) ^ rhs & U128_LOWER_MASK;
///         let mid = u128_clmul_ll(lhs_sum, rhs_sum) ^ lo ^ hi;
///         [lo, mid, hi] }
/// Note on the upstream sum lines: with Rust operator precedence
/// (`&` binds tighter than `^`), `x >> 64 ^ x & MASK` -- as written
/// upstream -- parses as `(x >> 64) ^ (x & MASK)`, the intended
/// cross-sum; the twin parenthesizes. GF256 consumes this face.
#[inline]
pub exec fn karatsuba_mul_128_uncombined(lhs: u128, rhs: u128) -> (out: [u128; 3])
    ensures
        out[0] == clmul64_bits(lhs & U128_LOWER_MASK, rhs & U128_LOWER_MASK, 64nat),
        out[2] == clmul64_bits(lhs >> 64, rhs >> 64, 64nat),
        out[1] == gf128_karatsuba_mid(lhs, rhs),
{
    proof {
        // ensure the ensures' spec side has an instantiated definition
        lemma_karatsuba_mid_def(lhs, rhs);
    }
    let lo: u128 = u128_clmul_ll(lhs, rhs);
    let hi: u128 = u128_clmul_hh(lhs, rhs);
    let lhs_sum: u128 = (lhs >> 64) ^ (lhs & U128_LOWER_MASK);
    let rhs_sum: u128 = (rhs >> 64) ^ (rhs & U128_LOWER_MASK);
    let mid: u128 = u128_clmul_ll(lhs_sum, rhs_sum) ^ lo ^ hi;
    proof {
        // the cross sums stay inside the low 64 bits, so the ll-face's
        // mask is a no-op on them (two single-machine blasts)
        assert((lhs_sum & U128_LOWER_MASK) == lhs_sum) by (bit_vector)
            requires
                lhs_sum == ((lhs >> 64) ^ (lhs & U128_LOWER_MASK)),
        ;
        assert((rhs_sum & U128_LOWER_MASK) == rhs_sum) by (bit_vector)
            requires
                rhs_sum == ((rhs >> 64) ^ (rhs & U128_LOWER_MASK)),
        ;
        assert(mid == clmul64_bits(lhs_sum, rhs_sum, 64nat) ^ lo ^ hi);
        assert(lo == clmul64_bits(lhs & U128_LOWER_MASK, rhs & U128_LOWER_MASK, 64nat));
        assert(hi == clmul64_bits(lhs >> 64, rhs >> 64, 64nat));
        assert(gf128_karatsuba_mid(lhs, rhs) == mid) by {
            lemma_karatsuba_mid_def(lhs, rhs);
        }
    }
    [lo, mid, hi]
}

/// Origin Rust (large_fields.rs :116-129):
///     /// ... Returns the resulting 256-bit polynomial `res`
///     /// (i.e., `lhs * rhs = res[0] + 2^128 * res[1]`).
///     fn karatsuba_mul_128(lhs: u128, rhs: u128) -> [u128; 2] {
///         let lo = u128_clmul_ll(lhs, rhs);
///         let hi = u128_clmul_hh(lhs, rhs);
///         let lhs_sum = ...; let rhs_sum = ...;
///         let mid = u128_clmul_ll(lhs_sum, rhs_sum) ^ lo ^ hi;
///         [lo ^ mid << 64, hi ^ mid >> 64] }
#[inline]
pub exec fn karatsuba_mul_128(lhs: u128, rhs: u128) -> (out: [u128; 2])
    ensures
        out[0] == gf128_karatsuba_lo(lhs, rhs),
        out[1] == gf128_karatsuba_hi(lhs, rhs),
{
    proof {
        lemma_karatsuba_mid_def(lhs, rhs);
        lemma_karatsuba_lo_def(lhs, rhs);
        lemma_karatsuba_hi_def(lhs, rhs);
    }
    let lo: u128 = u128_clmul_ll(lhs, rhs);
    let hi: u128 = u128_clmul_hh(lhs, rhs);
    let lhs_sum: u128 = (lhs >> 64) ^ (lhs & U128_LOWER_MASK);
    let rhs_sum: u128 = (rhs >> 64) ^ (rhs & U128_LOWER_MASK);
    let mid: u128 = u128_clmul_ll(lhs_sum, rhs_sum) ^ lo ^ hi;
    proof {
        assert((lhs_sum & U128_LOWER_MASK) == lhs_sum) by (bit_vector)
            requires
                lhs_sum == ((lhs >> 64) ^ (lhs & U128_LOWER_MASK)),
        ;
        assert((rhs_sum & U128_LOWER_MASK) == rhs_sum) by (bit_vector)
            requires
                rhs_sum == ((rhs >> 64) ^ (rhs & U128_LOWER_MASK)),
        ;
        assert(mid == clmul64_bits(lhs_sum, rhs_sum, 64nat) ^ lo ^ hi);
        assert(lo == clmul64_bits(lhs & U128_LOWER_MASK, rhs & U128_LOWER_MASK, 64nat));
        assert(hi == clmul64_bits(lhs >> 64, rhs >> 64, 64nat));
        assert(gf128_karatsuba_mid(lhs, rhs) == mid) by {
            lemma_karatsuba_mid_def(lhs, rhs);
        }
        assert(gf128_karatsuba_lo(lhs, rhs) == lo ^ (mid << 64)) by {
            lemma_karatsuba_lo_def(lhs, rhs);
        }
        assert(gf128_karatsuba_hi(lhs, rhs) == hi ^ (mid >> 64)) by {
            lemma_karatsuba_hi_def(lhs, rhs);
        }
    }
    [lo ^ (mid << 64), hi ^ (mid >> 64)]
}

// ===========================================================================
// GF128: the multiplication core (upstream large_fields.rs :858-916).
// Origin Rust (gf128_mul, docstring "Multiplies two 128-bit
// polynomials 'x', 'y' over the finite field GF(2). Stores the result
// in 'x'"):
//     fn gf128_mul(x: &mut u128, y: u128) {
//         let [lo, hi] = karatsuba_mul_128(*x, y);
//         // Reduction modulo x^128 + x^7 + x^2 + x + 1 as by page 16/17
//         // of <https://cdrdv2-public.intel.com/836172/
//         //        clmul-wp-rev-2-02-2014-04-20.pdf>
//         let x2 = hi & U128_LOWER_MASK;
//         let x3 = hi >> 64;
//         let a = x3 >> 63;
//         let b = x3 >> 62;
//         let c = x3 >> 57;
//         let x3_d = (x3 << 64) ^ x2 ^ a ^ b ^ c;
//         let e1_e0 = x3_d << 1;
//         let f1_f0 = x3_d << 2;
//         let g1_g0 = x3_d << 7;
//         let h1_h0 = x3_d ^ e1_e0 ^ f1_f0 ^ g1_g0;
//         *x = lo ^ h1_h0 }
// The twin returns the value (upstream mutates through the &mut);
// expression tree and step comments preserved verbatim; the only
// obligation discharged nontrivially is the clmul unfold (proven),
// everything else is plain congruence (probe2 green).
// ===========================================================================

/// The core (MulAssign<&Self> face, upstream :912-916:
/// `fn mul_assign(&mut self, rhs: &Self) { gf128_mul(&mut self.0[0],
/// rhs.0[0]) }`).
pub exec fn gf128_mul(x: u128, y: u128) -> (out: u128)
    ensures
        out == gf128_mul_spec(x, y),
{
    proof {
        lemma_mul128_spec_def(x, y);
    }
    let comb: [u128; 2] = karatsuba_mul_128(x, y);
    let lo: u128 = comb[0];
    let hi: u128 = comb[1];
    // Step 1
    let x2: u128 = hi & U128_LOWER_MASK;
    let x3: u128 = hi >> 64;
    let a: u128 = x3 >> 63;
    let b: u128 = x3 >> 62;
    let c: u128 = x3 >> 57;
    // Step 2
    let x3_d: u128 = (x3 << 64) ^ x2 ^ a ^ b ^ c;
    // Step 3
    let e1_e0: u128 = x3_d << 1;
    let f1_f0: u128 = x3_d << 2;
    let g1_g0: u128 = x3_d << 7;
    // Step 4
    let h1_h0: u128 = x3_d ^ e1_e0 ^ f1_f0 ^ g1_g0;
    lo ^ h1_h0
}

/// Origin Rust (large_fields.rs :888-895, Mul for GF128):
///     fn mul(mut self, rhs: Self) -> Self::Output {
///         self *= rhs;
///         self }
#[inline]
pub exec fn gf128_mul_self(x: u128, y: u128) -> (res: u128)
    ensures
        res == gf128_mul_spec(x, y),
{
    gf128_mul(x, y)
}

/// Origin Rust (large_fields.rs :906-910, MulAssign for GF128):
///     fn mul_assign(&mut self, rhs: Self) { *self *= &rhs; }
#[inline]
pub exec fn gf128_mul_assign(x: &mut u128, y: u128)
    ensures
        *final(x) == gf128_mul_spec(*old(x), y),
{
    *x = gf128_mul(*x, y);
}

// ===========================================================================
// Generic orbit machinery faces, specialized at GF128 (upstream
// large_fields.rs :557-803; the generic ToMask/ApplyMask/ShiftLeft1
// helpers are the single-limb selects at N == 1).
// ===========================================================================

/// Bit extraction face for the orbit loops (upstream ToMask<u128> for
/// BigGF<u128, 1, 128>, :803-809, inlined value face; the mask idiom
/// lowers to the 0/1 select).
#[inline]
pub exec fn gf128_bit_at(v: u128, bit: usize) -> (c: u8)
    requires
        bit < 128,
    ensures
        (c as u128) == ((v >> (bit as u64)) & 1),
        c <= 1u8,
{
    assert(((v >> (bit as u64)) & 1) == 0u128 || ((v >> (bit as u64)) & 1) == 1u128) by (bit_vector);
    (((v >> (bit as u64)) & 1) as u8) as u8
}

/// Origin Rust (large_fields.rs :746-762, Double for BigGF, the GF128
/// instantiation; the upstream generic double mutates through
/// to_mask/shift_left_1/modulus):
///     fn double(mut self) -> Self::Output {
///         let mask = self.to_mask();
///         self = self.shift_left_1();
///         self.0[0] ^= mask & Self::MODULUS;
///         self }
/// (upstream doc, fields/mod.rs:85-92: "This operation is not
/// equivalent to `self + self` but corresponds to a the multiplication
/// with the element representing `2`".) Proven equal to the xtime
/// orbit step and thence to the hmul model's doubling, every input.
pub exec fn gf128_double(v: u128) -> (res: u128)
    ensures
        res == gf128_xtime(v),
        res == gf128_hmul(v, 2u128),
{
    let m: u128 = if (v >> 127) & 1 == 1 { GF128_MODULUS } else { 0u128 };
    let out: u128 = (v << 1) ^ m;
    proof {
        // hmul(v, 2) at the model level: bit 0 of 2 is zero, bit 1 set
        assert((2u128 & 1) == 0u128) by (bit_vector);
        assert((2u128 >> 1) == 1u128) by (bit_vector);
        lemma_hmul128_bits_unfold(v, 2u128, 128nat);
        assert((if (2u128 & 1) == 1u128 { v } else { 0u128 }) == 0u128);
        let tail_after1: u128 = gf128_mul_bits(gf128_xtime(v), 1u128, 127nat);
        assert(gf128_mul_bits(v, 2u128, 128nat)
            == 0u128 ^ tail_after1);
        lemma_hmul128_one_tail(gf128_xtime(v), 127nat);
        bv_xor_zero128(tail_after1);
        assert(gf128_mul_bits(v, 2u128, 128nat) == gf128_xtime(v));
        assert(gf128_hmul(v, 2u128) == gf128_mul_bits(v, 2u128, 128nat));
    }
    out
}

/// Origin Rust (large_fields.rs :766-791, Square for BigGF, the GF128
/// instantiation):
///     fn square(self) -> Self::Output {
///         let mut other = self;
///         let mut result = other.copy_apply_mask(self.to_mask_bit(0));
///         for idx in 1..LENGTH {
///             let mask = other.to_mask();
///             other = other.shift_left_1();
///             other.0[0] ^= mask & Self::MODULUS;
///             result += other.copy_apply_mask(self.to_mask_bit(idx));
///         }
///         result }
/// Loop shape preserved (orbit register `other`, per-index select, no
/// early return, full 1..128 domain); twin proves
/// square(v) == gf128_hmul(v, v), every input.
pub exec fn gf128_square(v: u128) -> (res: u128)
    ensures
        res == gf128_hmul(v, v),
        res == gf128_mul_bits(v, v, 128nat),
{
    let mut other: u128 = v;
    let c0: u8 = gf128_bit_at(v, 0);
    let mut result: u128 = if (c0 as u128) != 0 { other } else { 0u128 };
    proof {
        assert((c0 as u128) == 1u128 <==> (v & 1) == 1u128) by (bit_vector)
            requires
                (c0 as u128) == ((v >> 0u64) & 1),
        ;
        let sel0: u128 = if (v & 1) == 1 { v } else { 0u128 };
        assert(result == sel0);
        lemma_hmul128_bits_unfold(v, v, 128nat);
        let tail0: u128 = gf128_mul_bits(gf128_xtime(v), v >> 1, 127nat);
        assert(gf128_mul_bits(v, v, 128nat) == sel0 ^ tail0);
        bv_xor_comm128(tail0, sel0);
        assert((tail0 ^ result) == gf128_mul_bits(v, v, 128nat));
    }
    let mut idx: usize = 1;
    while idx < 128
        invariant
            1 <= idx <= 128,
            idx < 128 ==>
                gf128_mul_bits(gf128_xtime(other), v >> (idx as u64), (128 - idx) as nat)
                    ^ result == gf128_mul_bits(v, v, 128nat),
            idx == 128 ==> result == gf128_mul_bits(v, v, 128nat),
        decreases 128 - idx,
    {
        let oold: u128 = other;
        let rold: u128 = result;
        let r_i: u128 = v >> (idx as u64);
        proof {
            // tail shift compose (or the 127-case zero fold)
            if (idx + 1) < 128 {
                let t = (v >> (idx as u64)) >> 1u64;
                let t2 = v >> ((idx + 1) as u64);
                assert(t == t2) by (bit_vector)
                    requires
                        (idx + 1) < 128,
                        t == (v >> (idx as u64)) >> 1u64,
                        t2 == v >> ((idx + 1) as u64),
                ;
            } else {
                let rv = (v >> (idx as u64)) >> 1u64;
                assert(rv == 0u128) by (bit_vector)
                    requires
                        idx == 127,
                        rv == (v >> (idx as u64)) >> 1u64,
                ;
            }
        }
        let mh: u8 = gf128_bit_at(oold, 127);
        let m: u128 = if (mh as u128) != 0 { GF128_MODULUS } else { 0u128 };
        other = (oold << 1) ^ m;
        let ci: u8 = gf128_bit_at(v, idx);
        let add: u128 = if (ci as u128) != 0 { other } else { 0u128 };
        result = rold ^ add;
        proof {
            let a1: u128 = gf128_xtime(oold);
            assert((mh as u128) == 1u128 <==> ((oold >> 127) & 1) == 1u128) by (bit_vector)
                requires
                    (mh as u128) == ((oold >> 127) & 1),
            ;
            assert(m == (if ((oold >> 127) & 1) == 1u128 { GF128_MODULUS } else { 0u128 }));
            assert(other == a1) by {
                assert(gf128_xtime(oold)
                    == ((oold << 1) ^ (if ((oold >> 127) & 1) == 1u128 { GF128_MODULUS } else { 0u128 })));
            }
            assert((ci as u128) == 1u128 <==> (r_i & 1) == 1u128) by (bit_vector)
                requires
                    (ci as u128) == ((v >> (idx as u64)) & 1),
                    r_i == v >> (idx as u64),
            ;
            assert(add == (if (r_i & 1) == 1u128 { other } else { 0u128 }));
            assert(((128 - idx) - 1) == 128 - (idx + 1));
            let w: nat = (128 - idx) as nat;
            lemma_hmul128_bits_unfold(a1, r_i, w);
            let contrib: u128 = if (r_i & 1) == 1u128 { other } else { 0u128 };
            let tailA: u128 = gf128_mul_bits(gf128_xtime(a1), (r_i) >> 1u64, (w - 1) as nat);
            let tailB: u128 = gf128_mul_bits(gf128_xtime(other), (r_i) >> 1u64, (w - 1) as nat);
            assert(tailA == tailB);
            assert(gf128_mul_bits(a1, r_i, w) == contrib ^ tailA);
            let jn: usize = (idx + 1) as usize;
            if (idx + 1) < 128 {
                assert((r_i) >> 1u64 == v >> (jn as u64));
                // re-group for the piecewise (<) case
                assert(rold ^ contrib == result);
                assert((contrib ^ tailB) ^ rold == gf128_mul_bits(v, v, 128nat));
                assert((contrib ^ tailB) ^ rold == tailB ^ (rold ^ contrib)) by {
                    bv_xor_ac128(contrib, tailB, rold);
                    bv_xor_comm128(contrib, rold);
                }
                assert(tailB ^ result == gf128_mul_bits(v, v, 128nat));
            } else {
                // idx == 127: fuel w == 1, the tail collapses and the exit
                // case of the piecewise invariant takes over
                assert(tailA == 0u128) by {
                    assert(gf128_mul_bits(gf128_xtime(a1), (r_i) >> 1u64, 0nat) == 0u128);
                }
                assert(gf128_mul_bits(a1, r_i, w) == contrib ^ 0u128);
                assert((contrib ^ 0u128) == contrib) by (bit_vector);
                assert(gf128_mul_bits(a1, r_i, w) == contrib);
                assert(rold ^ contrib == result);
                assert(result == gf128_mul_bits(v, v, 128nat)) by {
                    bv_xor_ac128(contrib, tailB, rold);
                    bv_xor_comm128(contrib, rold);
                    assert((contrib ^ tailB) ^ rold == tailB ^ (rold ^ contrib));
                    assert(tailB == 0u128);
                }
            }
        }
        idx += 1;
    }
    result
}

/// Origin Rust (large_fields.rs :680-705, Mul<GF64> for BigGF, the
/// GF128 instantiation -- the orbit loop over the 64 multiplier bits
/// of the GF64 operand, GF64 embedded base-first as upstream's
/// u64::to_mask_bit serves bit `idx` of the u64):
///     fn mul(mut self, rhs: GF64) -> Self::Output {
///         let rhs = u64::from(rhs);
///         let mut result = self.copy_apply_mask(rhs.to_mask_bit(0));
///         for idx in 1..64 { ...same orbit shape as square... }
///         result }
/// Twin proves == gf128_mul_bits(x, rhs, 64) (the textbook model over
/// the embedded multiplier), every input; upstream test
/// `assert_eq!(lhs * rhs_64, lhs * rhs_f)` pairs this face with the
/// full mul on the padded byte slice (harness closes the pair at the
/// sample level).
pub exec fn gf128_mul_gf64(x: u128, rhs: u64) -> (res: u128)
    ensures
        res == gf128_mul_bits(x, (rhs as u128), 64nat),
{
    let rhs_e: u128 = rhs as u128;
    proof {
        assert(rhs_e <= 0xFFFF_FFFF_FFFF_FFFFu128) by (bit_vector)
            requires
                rhs_e == (rhs as u128),
        ;
    }
    let mut lhs: u128 = x;
    let mut result: u128 = if rhs_e & 1 == 1 { lhs } else { 0u128 };
    proof {
        let sel0: u128 = if (rhs_e & 1) == 1 { x } else { 0u128 };
        assert(result == sel0);
        lemma_hmul128_bits_unfold(x, rhs_e, 64nat);
        let tail0: u128 = gf128_mul_bits(gf128_xtime(x), rhs_e >> 1, 63nat);
        assert(gf128_mul_bits(x, rhs_e, 64nat) == sel0 ^ tail0);
        bv_xor_comm128(tail0, sel0);
        assert((tail0 ^ result) == gf128_mul_bits(x, rhs_e, 64nat));
    }
    let mut idx: usize = 1;
    while idx < 64
        invariant
            1 <= idx <= 64,
            rhs_e <= 0xFFFF_FFFF_FFFF_FFFFu128,
            idx < 64 ==>
                gf128_mul_bits(gf128_xtime(lhs), rhs_e >> (idx as u64), (64 - idx) as nat)
                    ^ result == gf128_mul_bits(x, rhs_e, 64nat),
            idx == 64 ==> result == gf128_mul_bits(x, rhs_e, 64nat),
        decreases 64 - idx,
    {
        let lold: u128 = lhs;
        let rold: u128 = result;
        let r_i: u128 = rhs_e >> (idx as u64);
        proof {
            if (idx + 1) < 64 {
                let t = (rhs_e >> (idx as u64)) >> 1u64;
                let t2 = rhs_e >> ((idx + 1) as u64);
                assert(t == t2) by (bit_vector)
                    requires
                        (idx + 1) < 64,
                        t == (rhs_e >> (idx as u64)) >> 1u64,
                        t2 == rhs_e >> ((idx + 1) as u64),
                    ;
            } else {
                // idx == 63 boundary: rhs_e is the u64-embedded operand,
                // so its value stays below 2^64 and the last rung's
                // tail-shift folds to zero; the range fact is restated
                // in the fold's own scope first (blast premises are
                // strictly local, #FA2-3; the range fact rides the loop
                // invariant)
                let rv = (rhs_e >> (idx as u64)) >> 1u64;
                assert(rv == 0u128) by (bit_vector)
                    requires
                        idx == 63,
                        rv == (rhs_e >> (idx as u64)) >> 1u64,
                        rhs_e <= 0xFFFF_FFFF_FFFF_FFFFu128,
                ;
            }
        }
        let mh: u8 = gf128_bit_at(lold, 127);
        let m: u128 = if (mh as u128) != 0 { GF128_MODULUS } else { 0u128 };
        lhs = (lold << 1) ^ m;
        let ci: u8 = gf128_bit_at(rhs_e, idx);
        let add: u128 = if (ci as u128) != 0 { lhs } else { 0u128 };
        result = rold ^ add;
        proof {
            let a1: u128 = gf128_xtime(lold);
            assert((mh as u128) == 1u128 <==> ((lold >> 127) & 1) == 1u128) by (bit_vector)
                requires
                    (mh as u128) == ((lold >> 127) & 1),
            ;
            assert(m == (if ((lold >> 127) & 1) == 1u128 { GF128_MODULUS } else { 0u128 }));
            assert(lhs == a1) by {
                assert(gf128_xtime(lold)
                    == ((lold << 1) ^ (if ((lold >> 127) & 1) == 1u128 { GF128_MODULUS } else { 0u128 })));
            }
            assert((ci as u128) == 1u128 <==> (r_i & 1) == 1u128) by (bit_vector)
                requires
                    (ci as u128) == ((rhs_e >> (idx as u64)) & 1),
                    r_i == rhs_e >> (idx as u64),
            ;
            assert(add == (if (r_i & 1) == 1u128 { lhs } else { 0u128 }));
            assert(((64 - idx) - 1) == 64 - (idx + 1));
            let w: nat = (64 - idx) as nat;
            lemma_hmul128_bits_unfold(a1, r_i, w);
            let contrib: u128 = if (r_i & 1) == 1u128 { lhs } else { 0u128 };
            let tailA: u128 = gf128_mul_bits(gf128_xtime(a1), (r_i) >> 1u64, (w - 1) as nat);
            let tailB: u128 = gf128_mul_bits(gf128_xtime(lhs), (r_i) >> 1u64, (w - 1) as nat);
            assert(tailA == tailB);
            assert(gf128_mul_bits(a1, r_i, w) == contrib ^ tailA);
            let jn: usize = (idx + 1) as usize;
            if (idx + 1) < 64 {
                assert((r_i) >> 1u64 == rhs_e >> (jn as u64));
                assert(rold ^ contrib == result);
                assert((contrib ^ tailB) ^ rold == gf128_mul_bits(x, rhs_e, 64nat));
                assert((contrib ^ tailB) ^ rold == tailB ^ (rold ^ contrib)) by {
                    bv_xor_ac128(contrib, tailB, rold);
                    bv_xor_comm128(contrib, rold);
                }
                assert(tailB ^ result == gf128_mul_bits(x, rhs_e, 64nat));
            } else {
                assert(tailA == 0u128) by {
                    assert(gf128_mul_bits(gf128_xtime(a1), (r_i) >> 1u64, 0nat) == 0u128);
                }
                assert(gf128_mul_bits(a1, r_i, w) == contrib ^ 0u128);
                assert((contrib ^ 0u128) == contrib) by (bit_vector);
                assert(gf128_mul_bits(a1, r_i, w) == contrib);
                assert(rold ^ contrib == result);
                assert(result == gf128_mul_bits(x, rhs_e, 64nat)) by {
                    bv_xor_ac128(contrib, tailB, rold);
                    bv_xor_comm128(contrib, rold);
                    assert((contrib ^ tailB) ^ rold == tailB ^ (rold ^ contrib));
                    assert(tailB == 0u128);
                }
            }
        }
        idx += 1;
    }
    result
}

/// Origin Rust (large_fields.rs :668-678, Mul<u8> for BigGF, the GF128
/// instantiation):
///     fn mul(self, rhs: u8) -> Self::Output {
///         self.apply_mask(rhs.to_mask_bit(0)) }
/// (doc context: this multiplies by the BIT-0 element of rhs, not the
/// byte value; upstream's own test asserts `anything * 0u8 == ZERO`
/// and `anything * 1u8 == anything`, large_fields.rs:1609-1613).
pub exec fn gf128_mul_u8(x: u128, rhs: u8) -> (res: u128)
    ensures
        res == (if (rhs & 1) == 1 { x } else { 0u128 }),
        (rhs & 1) == 0 ==> res == 0u128,
        (rhs & 1) == 1 ==> res == x,
{
    if (rhs & 1) == 1 {
        x
    } else {
        0u128
    }
}

/// Origin Rust (large_fields.rs :315-319 with the generic BigGF body
/// :361-371, GF128 instantiation):
///     pub trait FromBit: Field {
///         /// Takes the first bit from the input byte `x`, and returns
///         /// the respective Field representation.
///         fn from_bit(x: u8) -> Self; }
///     impl FromBit for BigGF ... {
///         fn from_bit(x: u8) -> Self {
///             Self::ONE.apply_mask(x.to_mask_bit(0)) } }
pub exec fn gf128_from_bit(x: u8) -> (res: u128)
    ensures
        (x & 1) == 1 ==> res == GF128_ONE,
        (x & 1) == 0 ==> res == GF128_ZERO,
{
    if (x & 1) == 1 {
        GF128_ONE
    } else {
        GF128_ZERO
    }
}

// ===========================================================================
// ByteCombine for GF128 (upstream large_fields.rs :197-213 trait decl;
// the generic BigGF body :375-402; constant payload
// large_fields_constants.rs :11-21; ByteCombineConstants :929-932).
// Origin Rust (generic body):
///     fn byte_combine(x: &[Self; 8]) -> Self {
///         x.iter().skip(1).zip(Self::ALPHA).fold(x[0],
///             |sum, (xi, alphai)| sum + (alphai * xi)) }
///     fn byte_combine_slice(x: &[Self]) -> Self {
///         debug_assert_eq!(x.len(), 8);
///         let (x0, x) = x.split_at(1);
///         x.iter().zip(Self::ALPHA).fold(x0[0],
///             |sum, (xi, alphai)| sum + (alphai * xi)) }
///     fn byte_combine_bits(x: u8) -> Self {
///         Self::ALPHA.iter().enumerate().fold(
///             Self::ONE.apply_mask(x.to_mask_bit(0)),
///             |sum, (index, alpha)| sum + alpha.apply_mask(
///                 x.to_mask_bit(index + 1))) }
// ===========================================================================

/// Alphas::ALPHA for GF128 (upstream large_fields_constants.rs :11-21,
/// values verbatim).
pub const GF128_ALPHA: [u128; 7] = [
    0x053d8555a9979a1ca13fe8ac5560ce0d,
    0x4cf4b7439cbfbb84ec7759ca3488aee1,
    0x35ad604f7d51d2c6bfcf02ae363946a8,
    0x0dcb364640a222fe6b8330483c2e9849,
    0x549810e11a88dea5252b49277b1b82b4,
    0xd681a5686c0c1f75c72bf2ef2521ff22,
    0x0950311a4fb78fe07a7a8e94e136f9bc,
];

/// ByteCombineConstants for GF128 (upstream :929-932):
///     const BYTE_COMBINE_2: Self = Self::ALPHA[0];
///     const BYTE_COMBINE_3: Self = Self([Self::ALPHA[0].0[0] ^ Self::ONE.0[0]]);
/// ("Equivalent `ByteCombing::byte_combine_bits(2)` resp. `(3)`" --
/// the upstream doc Comment line above each const, recorded; the
/// upstream doc's `ByteCombing` is a doc-alias of ByteCombine).
pub const GF128_BYTE_COMBINE_2: u128 = 0x053d8555a9979a1ca13fe8ac5560ce0d;
pub const GF128_BYTE_COMBINE_3: u128 = 0x053d8555a9979a1ca13fe8ac5560ce0d ^ 1;

/// Spec face of byte_combine: x0 + sum_{i} ALPHA[i-1] * x_i, the
/// products by the field mul spec, the sums by characteristic-2 xor.
pub open spec fn gf128_byte_combine_spec(
    x0: u128,
    x1: u128,
    x2: u128,
    x3: u128,
    x4: u128,
    x5: u128,
    x6: u128,
    x7: u128,
) -> u128 {
    x0
        ^ gf128_mul_spec(GF128_ALPHA[0], x1)
        ^ gf128_mul_spec(GF128_ALPHA[1], x2)
        ^ gf128_mul_spec(GF128_ALPHA[2], x3)
        ^ gf128_mul_spec(GF128_ALPHA[3], x4)
        ^ gf128_mul_spec(GF128_ALPHA[4], x5)
        ^ gf128_mul_spec(GF128_ALPHA[5], x6)
        ^ gf128_mul_spec(GF128_ALPHA[6], x7)
}

/// byte_combine (upstream :381-385): the fold unrolled in the
/// upstream order (left-to-right over the seven alpha products).
pub exec fn gf128_byte_combine(
    x0: u128,
    x1: u128,
    x2: u128,
    x3: u128,
    x4: u128,
    x5: u128,
    x6: u128,
    x7: u128,
) -> (res: u128)
    ensures
        res == gf128_byte_combine_spec(x0, x1, x2, x3, x4, x5, x6, x7),
{
    let mut sum: u128 = x0;
    sum = sum ^ gf128_mul_self(GF128_ALPHA[0], x1);
    sum = sum ^ gf128_mul_self(GF128_ALPHA[1], x2);
    sum = sum ^ gf128_mul_self(GF128_ALPHA[2], x3);
    sum = sum ^ gf128_mul_self(GF128_ALPHA[3], x4);
    sum = sum ^ gf128_mul_self(GF128_ALPHA[4], x5);
    sum = sum ^ gf128_mul_self(GF128_ALPHA[5], x6);
    sum = sum ^ gf128_mul_self(GF128_ALPHA[6], x7);
    sum
}

/// Spec face of byte_combine_bits (upstream :396-401): the byte's
/// bits select ONE or ALPHA[i] by position (widened-view bit
/// projections for one canonical projection style across this face,
/// its partial-fold twin, and the exec selects).
pub open spec fn gf128_byte_combine_bits_spec(x: u8) -> u128 {
    (if ((x as u128) & 1) == 1 { GF128_ONE } else { 0u128 })
        ^ (if (((x as u128) >> 1) & 1) == 1 { GF128_ALPHA[0] } else { 0u128 })
        ^ (if (((x as u128) >> 2) & 1) == 1 { GF128_ALPHA[1] } else { 0u128 })
        ^ (if (((x as u128) >> 3) & 1) == 1 { GF128_ALPHA[2] } else { 0u128 })
        ^ (if (((x as u128) >> 4) & 1) == 1 { GF128_ALPHA[3] } else { 0u128 })
        ^ (if (((x as u128) >> 5) & 1) == 1 { GF128_ALPHA[4] } else { 0u128 })
        ^ (if (((x as u128) >> 6) & 1) == 1 { GF128_ALPHA[5] } else { 0u128 })
        ^ (if (((x as u128) >> 7) & 1) == 1 { GF128_ALPHA[6] } else { 0u128 })
}

/// byte_combine_bits (upstream :396-401): the enumerate-fold unrolled
/// in the upstream accumulation order (ONE.bit0 first, then the seven
/// alpha-bit selections); loop shape preserved (index run over the
/// ALPHA entries as upstream's enumerate does).
pub exec fn gf128_byte_combine_bits(x: u8) -> (res: u128)
    ensures
        res == gf128_byte_combine_bits_spec(x),
{
    let mut sum: u128 = if ((x as u128) & 1) == 1 { GF128_ONE } else { 0u128 };
    proof {
        assert(sum == partial_bits_sum128(x, 0nat));
    }
    let mut i: usize = 0;
    while i < 7
        invariant
            0 <= i <= 7,
            sum == partial_bits_sum128(x, i as nat),
        decreases 7 - i,
    {
        proof {
            unfold_bit_sum(x, (i + 1) as nat);
        }
        let c: u8 = gf128_bit_at(x as u128, (i + 1) as usize);
        let term: u128 = if (c as u128) == 1u128 {
            GF128_ALPHA[i]
        } else {
            0u128
        };
        proof {
            // the bit face IS the widened-view projection at i+1
            assert((c as u128) == (((x as u128) >> ((i + 1) as int)) & 1));
            // so the exec term is exactly the spec fold's next term
            assert(term
                == (if (((x as u128) >> ((i + 1) as int)) & 1) == 1 {
                    GF128_ALPHA[i as int]
                } else { 0u128 }));
        }
        sum = sum ^ term;
        i += 1;
    }
    proof {
        assert(sum == partial_bits_sum128(x, 7nat));
        assert(partial_bits_sum128(x, 7nat) == gf128_byte_combine_bits_spec(x)) by {
            // structural chain: unfold the helper down to its base and
            // match the spec's eight projections one by one; every
            // unfold carries the same condition text, so each step is
            // definitional identity
            assert(partial_bits_sum128(x, 0nat) == (if ((x as u128) & 1) == 1 { GF128_ONE } else { 0u128 }));
            assert(partial_bits_sum128(x, 1nat)
                == partial_bits_sum128(x, 0nat)
                    ^ (if (((x as u128) >> 1) & 1) == 1 { GF128_ALPHA[0] } else { 0u128 })) by {
                unfold_bit_sum(x, 1nat);
            }
            assert(partial_bits_sum128(x, 2nat)
                == partial_bits_sum128(x, 1nat)
                    ^ (if (((x as u128) >> 2) & 1) == 1 { GF128_ALPHA[1] } else { 0u128 })) by {
                unfold_bit_sum(x, 2nat);
            }
            assert(partial_bits_sum128(x, 3nat)
                == partial_bits_sum128(x, 2nat)
                    ^ (if (((x as u128) >> 3) & 1) == 1 { GF128_ALPHA[2] } else { 0u128 })) by {
                unfold_bit_sum(x, 3nat);
            }
            assert(partial_bits_sum128(x, 4nat)
                == partial_bits_sum128(x, 3nat)
                    ^ (if (((x as u128) >> 4) & 1) == 1 { GF128_ALPHA[3] } else { 0u128 })) by {
                unfold_bit_sum(x, 4nat);
            }
            assert(partial_bits_sum128(x, 5nat)
                == partial_bits_sum128(x, 4nat)
                    ^ (if (((x as u128) >> 5) & 1) == 1 { GF128_ALPHA[4] } else { 0u128 })) by {
                unfold_bit_sum(x, 5nat);
            }
            assert(partial_bits_sum128(x, 6nat)
                == partial_bits_sum128(x, 5nat)
                    ^ (if (((x as u128) >> 6) & 1) == 1 { GF128_ALPHA[5] } else { 0u128 })) by {
                unfold_bit_sum(x, 6nat);
            }
            assert(partial_bits_sum128(x, 7nat)
                == partial_bits_sum128(x, 6nat)
                    ^ (if (((x as u128) >> 7) & 1) == 1 { GF128_ALPHA[6] } else { 0u128 })) by {
                unfold_bit_sum(x, 7nat);
            }
        }
    }
    sum
}

/// Partial-accumulation spec fn for the byte_combine_bits fold
/// (private helper of the invariant; i counts the folded alpha terms;
/// same widened-view bit projections as the spec face).
spec fn partial_bits_sum128(x: u8, i: nat) -> u128
    decreases i,
{
    if i == 0 {
        (if ((x as u128) & 1) == 1 { GF128_ONE } else { 0u128 })
    } else {
        partial_bits_sum128(x, (i - 1) as nat)
            ^ (if (((x as u128) >> (i as int)) & 1) == 1 {
                GF128_ALPHA[(i - 1) as int]
            } else { 0u128 })
    }
}

/// Definitional unfold of the partial bit-sum at positive fold count.
proof fn unfold_bit_sum(x: u8, i: nat)
    requires
        0 < i <= 7,
    ensures
        partial_bits_sum128(x, i)
            == partial_bits_sum128(x, (i - 1) as nat)
                ^ (if (((x as u128) >> (i as int)) & 1) == 1 {
                    GF128_ALPHA[(i - 1) as int]
                } else { 0u128 }),
{
}

// ===========================================================================
// GF128 Field face: as_bytes / from_bytes (upstream large_fields.rs
// :923-926 resp. :934-941).
// Origin Rust:
//     fn as_bytes(&self) -> Array<u8, Self::Length> {
//         Array(self.0[0].to_le_bytes()) }
//     impl From<&[u8]> for BigGF<u128, 1, 128> {
//         fn from(value: &[u8]) -> Self {
//             debug_assert_eq!(value.len(), 16);
//             let mut array = [0u8; 16];
//             array.copy_from_slice(&value[..16]);
//             Self([u128::from_le_bytes(array)]) } }
// hybrid-array Array<u8, U16> lowers to [u8; 16]; to_le_bytes /
// from_le_bytes lower to per-byte shift/mask planes (FA2 GF64
// convention at the doubled width).
// ===========================================================================

/// The little-endian byte j of a u128 value (spec helper of the
/// byte faces).
pub open spec fn byte128(v: u128, j: int) -> u128 {
    (v >> ((8 * j) as u64)) & 0xFF
}

/// Field::as_bytes for GF128 (upstream :923-926), [u8; 16] lowered
/// face with the per-byte blast folds.
pub exec fn gf128_as_bytes(v: u128) -> (out: [u8; 16])
    ensures
        forall |j: int| 0 <= j < 16
            ==> out[j] == (byte128(v, j)),
{
    #[verifier::truncate] let b0: u8 = ((v >> 0u64) & 0xFF) as u8;
    #[verifier::truncate] let b1: u8 = ((v >> 8u64) & 0xFF) as u8;
    #[verifier::truncate] let b2: u8 = ((v >> 16u64) & 0xFF) as u8;
    #[verifier::truncate] let b3: u8 = ((v >> 24u64) & 0xFF) as u8;
    #[verifier::truncate] let b4: u8 = ((v >> 32u64) & 0xFF) as u8;
    #[verifier::truncate] let b5: u8 = ((v >> 40u64) & 0xFF) as u8;
    #[verifier::truncate] let b6: u8 = ((v >> 48u64) & 0xFF) as u8;
    #[verifier::truncate] let b7: u8 = ((v >> 56u64) & 0xFF) as u8;
    #[verifier::truncate] let b8: u8 = ((v >> 64u64) & 0xFF) as u8;
    #[verifier::truncate] let b9: u8 = ((v >> 72u64) & 0xFF) as u8;
    #[verifier::truncate] let b10: u8 = ((v >> 80u64) & 0xFF) as u8;
    #[verifier::truncate] let b11: u8 = ((v >> 88u64) & 0xFF) as u8;
    #[verifier::truncate] let b12: u8 = ((v >> 96u64) & 0xFF) as u8;
    #[verifier::truncate] let b13: u8 = ((v >> 104u64) & 0xFF) as u8;
    #[verifier::truncate] let b14: u8 = ((v >> 112u64) & 0xFF) as u8;
    #[verifier::truncate] let b15: u8 = ((v >> 120u64) & 0xFF) as u8;
    proof {
        // masked bytes stay in the u8 range (plain machine blasts)
        assert(((v >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 64u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 72u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 80u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 88u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 96u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 104u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 112u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((v >> 120u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        // truncated casts are value-exact, plain chains the rest
        assert((b0 as u128) == ((v >> 0u64) & 0xFF));
        assert((b1 as u128) == ((v >> 8u64) & 0xFF));
        assert((b2 as u128) == ((v >> 16u64) & 0xFF));
        assert((b3 as u128) == ((v >> 24u64) & 0xFF));
        assert((b4 as u128) == ((v >> 32u64) & 0xFF));
        assert((b5 as u128) == ((v >> 40u64) & 0xFF));
        assert((b6 as u128) == ((v >> 48u64) & 0xFF));
        assert((b7 as u128) == ((v >> 56u64) & 0xFF));
        assert((b8 as u128) == ((v >> 64u64) & 0xFF));
        assert((b9 as u128) == ((v >> 72u64) & 0xFF));
        assert((b10 as u128) == ((v >> 80u64) & 0xFF));
        assert((b11 as u128) == ((v >> 88u64) & 0xFF));
        assert((b12 as u128) == ((v >> 96u64) & 0xFF));
        assert((b13 as u128) == ((v >> 104u64) & 0xFF));
        assert((b14 as u128) == ((v >> 112u64) & 0xFF));
        assert((b15 as u128) == ((v >> 120u64) & 0xFF));
        // byte128 unfolds at the concrete byte indexes
        assert(byte128(v, 0) == ((v >> 0u64) & 0xFF));
        assert(byte128(v, 1) == ((v >> 8u64) & 0xFF));
        assert(byte128(v, 2) == ((v >> 16u64) & 0xFF));
        assert(byte128(v, 3) == ((v >> 24u64) & 0xFF));
        assert(byte128(v, 4) == ((v >> 32u64) & 0xFF));
        assert(byte128(v, 5) == ((v >> 40u64) & 0xFF));
        assert(byte128(v, 6) == ((v >> 48u64) & 0xFF));
        assert(byte128(v, 7) == ((v >> 56u64) & 0xFF));
        assert(byte128(v, 8) == ((v >> 64u64) & 0xFF));
        assert(byte128(v, 9) == ((v >> 72u64) & 0xFF));
        assert(byte128(v, 10) == ((v >> 80u64) & 0xFF));
        assert(byte128(v, 11) == ((v >> 88u64) & 0xFF));
        assert(byte128(v, 12) == ((v >> 96u64) & 0xFF));
        assert(byte128(v, 13) == ((v >> 104u64) & 0xFF));
        assert(byte128(v, 14) == ((v >> 112u64) & 0xFF));
        assert(byte128(v, 15) == ((v >> 120u64) & 0xFF));
    }
    [b0 as u8, b1 as u8, b2 as u8, b3 as u8, b4 as u8, b5 as u8, b6 as u8, b7 as u8,
        b8 as u8, b9 as u8, b10 as u8, b11 as u8, b12 as u8, b13 as u8, b14 as u8, b15 as u8]
}

/// From<&[u8]> for GF128 (upstream :934-941): the upstream
/// debug_assert_eq!(value.len(), 16) (absent in release builds)
/// re-erects as the twin's requires; from_le_bytes lowers to the
/// OR-of-shifted-bytes assembly.
pub exec fn gf128_from_bytes(value: &[u8]) -> (res: u128)
    requires
        value.len() == 16,
    ensures
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(res, j) == (value[j] as u128),
{
    let b0: u128 = value[0] as u128;
    let b1: u128 = value[1] as u128;
    let b2: u128 = value[2] as u128;
    let b3: u128 = value[3] as u128;
    let b4: u128 = value[4] as u128;
    let b5: u128 = value[5] as u128;
    let b6: u128 = value[6] as u128;
    let b7: u128 = value[7] as u128;
    let b8: u128 = value[8] as u128;
    let b9: u128 = value[9] as u128;
    let b10: u128 = value[10] as u128;
    let b11: u128 = value[11] as u128;
    let b12: u128 = value[12] as u128;
    let b13: u128 = value[13] as u128;
    let b14: u128 = value[14] as u128;
    let b15: u128 = value[15] as u128;
    let acc: u128 = (b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)
        | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))
        ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64)
        | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64));
    // the two OR-halves are disjoint in u128 (byte planes 0..8 vs
    // 8..16), so assembling by ^ equals assembling by |: one blast
    // per byte plane closes the value contract.
    proof {
        lemma_from_bytes_planes(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15);
        assert(byte128(acc, 0) == ((acc >> 0u64) & 0xFF));
        assert(byte128(acc, 1) == ((acc >> 8u64) & 0xFF));
        assert(byte128(acc, 2) == ((acc >> 16u64) & 0xFF));
        assert(byte128(acc, 3) == ((acc >> 24u64) & 0xFF));
        assert(byte128(acc, 4) == ((acc >> 32u64) & 0xFF));
        assert(byte128(acc, 5) == ((acc >> 40u64) & 0xFF));
        assert(byte128(acc, 6) == ((acc >> 48u64) & 0xFF));
        assert(byte128(acc, 7) == ((acc >> 56u64) & 0xFF));
        assert(byte128(acc, 8) == ((acc >> 64u64) & 0xFF));
        assert(byte128(acc, 9) == ((acc >> 72u64) & 0xFF));
        assert(byte128(acc, 10) == ((acc >> 80u64) & 0xFF));
        assert(byte128(acc, 11) == ((acc >> 88u64) & 0xFF));
        assert(byte128(acc, 12) == ((acc >> 96u64) & 0xFF));
        assert(byte128(acc, 13) == ((acc >> 104u64) & 0xFF));
        assert(byte128(acc, 14) == ((acc >> 112u64) & 0xFF));
        assert(byte128(acc, 15) == ((acc >> 120u64) & 0xFF));
    }
    acc
}

/// The 16 plane folds of the OR-assembled u128, lowered as one lemma
/// to keep the exec face readable (private; each is a plain machine
/// blast over the free byte symbols -- the FA2 from_bytes convention,
/// slices never enter blast contexts).
proof fn lemma_from_bytes_planes(
    b0: u128,
    b1: u128,
    b2: u128,
    b3: u128,
    b4: u128,
    b5: u128,
    b6: u128,
    b7: u128,
    b8: u128,
    b9: u128,
    b10: u128,
    b11: u128,
    b12: u128,
    b13: u128,
    b14: u128,
    b15: u128
)
    requires
        b0 <= 0xFF,
        b1 <= 0xFF,
        b2 <= 0xFF,
        b3 <= 0xFF,
        b4 <= 0xFF,
        b5 <= 0xFF,
        b6 <= 0xFF,
        b7 <= 0xFF,
        b8 <= 0xFF,
        b9 <= 0xFF,
        b10 <= 0xFF,
        b11 <= 0xFF,
        b12 <= 0xFF,
        b13 <= 0xFF,
        b14 <= 0xFF,
        b15 <= 0xFF,
    ensures
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 0u64) & 0xFF) == b0),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 8u64) & 0xFF) == b1),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 16u64) & 0xFF) == b2),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 24u64) & 0xFF) == b3),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 32u64) & 0xFF) == b4),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 40u64) & 0xFF) == b5),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 48u64) & 0xFF) == b6),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 56u64) & 0xFF) == b7),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 64u64) & 0xFF) == b8),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 72u64) & 0xFF) == b9),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 80u64) & 0xFF) == b10),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 88u64) & 0xFF) == b11),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 96u64) & 0xFF) == b12),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 104u64) & 0xFF) == b13),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 112u64) & 0xFF) == b14),
        (((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 120u64) & 0xFF) == b15),
{
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 0u64) & 0xFF) == b0)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 8u64) & 0xFF) == b1)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 16u64) & 0xFF) == b2)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 24u64) & 0xFF) == b3)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 32u64) & 0xFF) == b4)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 40u64) & 0xFF) == b5)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 48u64) & 0xFF) == b6)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 56u64) & 0xFF) == b7)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 64u64) & 0xFF) == b8)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 72u64) & 0xFF) == b9)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 80u64) & 0xFF) == b10)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 88u64) & 0xFF) == b11)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 96u64) & 0xFF) == b12)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 104u64) & 0xFF) == b13)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 112u64) & 0xFF) == b14)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
    assert((((((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64)))) >> 120u64) & 0xFF) == b15)) by (bit_vector)
        requires
            b0 <= 0xFF,
            b1 <= 0xFF,
            b2 <= 0xFF,
            b3 <= 0xFF,
            b4 <= 0xFF,
            b5 <= 0xFF,
            b6 <= 0xFF,
            b7 <= 0xFF,
            b8 <= 0xFF,
            b9 <= 0xFF,
            b10 <= 0xFF,
            b11 <= 0xFF,
            b12 <= 0xFF,
            b13 <= 0xFF,
            b14 <= 0xFF,
            b15 <= 0xFF,
    ;
}

/// Definitional bridge of gf128_byte_combine_spec (the open spec fn's
/// definition needs an instantiated call site in dependent proofs --
// probe8 finding: plain encoding does not substitute value-equal
// arguments into spec-fn applications, so consumers restate their
/// spec facts through an explicit def bridge).
pub proof fn lemma_byte_combine_spec_def(
    x0: u128,
    x1: u128,
    x2: u128,
    x3: u128,
    x4: u128,
    x5: u128,
    x6: u128,
    x7: u128,
)
    ensures
        gf128_byte_combine_spec(x0, x1, x2, x3, x4, x5, x6, x7)
            == x0
                ^ gf128_mul_spec(GF128_ALPHA[0], x1)
                ^ gf128_mul_spec(GF128_ALPHA[1], x2)
                ^ gf128_mul_spec(GF128_ALPHA[2], x3)
                ^ gf128_mul_spec(GF128_ALPHA[3], x4)
                ^ gf128_mul_spec(GF128_ALPHA[4], x5)
                ^ gf128_mul_spec(GF128_ALPHA[5], x6)
                ^ gf128_mul_spec(GF128_ALPHA[6], x7),
{
}

/// Definitional bridge of gf128_byte_combine_bits_spec.
pub proof fn lemma_byte_combine_bits_spec_def(x: u8)
    ensures
        gf128_byte_combine_bits_spec(x)
            == (if ((x as u128) & 1) == 1 { GF128_ONE } else { 0u128 })
                ^ (if (((x as u128) >> 1) & 1) == 1 { GF128_ALPHA[0] } else { 0u128 })
                ^ (if (((x as u128) >> 2) & 1) == 1 { GF128_ALPHA[1] } else { 0u128 })
                ^ (if (((x as u128) >> 3) & 1) == 1 { GF128_ALPHA[2] } else { 0u128 })
                ^ (if (((x as u128) >> 4) & 1) == 1 { GF128_ALPHA[3] } else { 0u128 })
                ^ (if (((x as u128) >> 5) & 1) == 1 { GF128_ALPHA[4] } else { 0u128 })
                ^ (if (((x as u128) >> 6) & 1) == 1 { GF128_ALPHA[5] } else { 0u128 })
                ^ (if (((x as u128) >> 7) & 1) == 1 { GF128_ALPHA[6] } else { 0u128 }),
{
}

/// Byte-value equality of two u128s with all sixteen byte slots given
/// as machine values (the FA2 lemma_u64_bytes_eq shape).
pub proof fn lemma_u128_bytes_eq(
    a: u128,
    b: u128,
    e0: u128,
    e1: u128,
    e2: u128,
    e3: u128,
    e4: u128,
    e5: u128,
    e6: u128,
    e7: u128,
    e8: u128,
    e9: u128,
    e10: u128,
    e11: u128,
    e12: u128,
    e13: u128,
    e14: u128,
    e15: u128,
)
    requires
        e0 <= 0xFF,
        e1 <= 0xFF,
        e2 <= 0xFF,
        e3 <= 0xFF,
        e4 <= 0xFF,
        e5 <= 0xFF,
        e6 <= 0xFF,
        e7 <= 0xFF,
        e8 <= 0xFF,
        e9 <= 0xFF,
        e10 <= 0xFF,
        e11 <= 0xFF,
        e12 <= 0xFF,
        e13 <= 0xFF,
        e14 <= 0xFF,
        e15 <= 0xFF,
        ((a >> 0u64) & 0xFF) == e0,
        ((a >> 8u64) & 0xFF) == e1,
        ((a >> 16u64) & 0xFF) == e2,
        ((a >> 24u64) & 0xFF) == e3,
        ((a >> 32u64) & 0xFF) == e4,
        ((a >> 40u64) & 0xFF) == e5,
        ((a >> 48u64) & 0xFF) == e6,
        ((a >> 56u64) & 0xFF) == e7,
        ((a >> 64u64) & 0xFF) == e8,
        ((a >> 72u64) & 0xFF) == e9,
        ((a >> 80u64) & 0xFF) == e10,
        ((a >> 88u64) & 0xFF) == e11,
        ((a >> 96u64) & 0xFF) == e12,
        ((a >> 104u64) & 0xFF) == e13,
        ((a >> 112u64) & 0xFF) == e14,
        ((a >> 120u64) & 0xFF) == e15,
        ((b >> 0u64) & 0xFF) == e0,
        ((b >> 8u64) & 0xFF) == e1,
        ((b >> 16u64) & 0xFF) == e2,
        ((b >> 24u64) & 0xFF) == e3,
        ((b >> 32u64) & 0xFF) == e4,
        ((b >> 40u64) & 0xFF) == e5,
        ((b >> 48u64) & 0xFF) == e6,
        ((b >> 56u64) & 0xFF) == e7,
        ((b >> 64u64) & 0xFF) == e8,
        ((b >> 72u64) & 0xFF) == e9,
        ((b >> 80u64) & 0xFF) == e10,
        ((b >> 88u64) & 0xFF) == e11,
        ((b >> 96u64) & 0xFF) == e12,
        ((b >> 104u64) & 0xFF) == e13,
        ((b >> 112u64) & 0xFF) == e14,
        ((b >> 120u64) & 0xFF) == e15,
    ensures
        a == b,
{
    assert(a == (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64)
        | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64)
        | (e8 << 64u64) | (e9 << 72u64) | (e10 << 80u64) | (e11 << 88u64)
        | (e12 << 96u64) | (e13 << 104u64) | (e14 << 112u64) | (e15 << 120u64))) by (bit_vector)
        requires
            e0 <= 0xFF,
            e1 <= 0xFF,
            e2 <= 0xFF,
            e3 <= 0xFF,
            e4 <= 0xFF,
            e5 <= 0xFF,
            e6 <= 0xFF,
            e7 <= 0xFF,
            e8 <= 0xFF,
            e9 <= 0xFF,
            e10 <= 0xFF,
            e11 <= 0xFF,
            e12 <= 0xFF,
            e13 <= 0xFF,
            e14 <= 0xFF,
            e15 <= 0xFF,
            ((a >> 0u64) & 0xFF) == e0,
            ((a >> 8u64) & 0xFF) == e1,
            ((a >> 16u64) & 0xFF) == e2,
            ((a >> 24u64) & 0xFF) == e3,
            ((a >> 32u64) & 0xFF) == e4,
            ((a >> 40u64) & 0xFF) == e5,
            ((a >> 48u64) & 0xFF) == e6,
            ((a >> 56u64) & 0xFF) == e7,
            ((a >> 64u64) & 0xFF) == e8,
            ((a >> 72u64) & 0xFF) == e9,
            ((a >> 80u64) & 0xFF) == e10,
            ((a >> 88u64) & 0xFF) == e11,
            ((a >> 96u64) & 0xFF) == e12,
            ((a >> 104u64) & 0xFF) == e13,
            ((a >> 112u64) & 0xFF) == e14,
            ((a >> 120u64) & 0xFF) == e15,
    ;
    assert(b == (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64)
        | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64)
        | (e8 << 64u64) | (e9 << 72u64) | (e10 << 80u64) | (e11 << 88u64)
        | (e12 << 96u64) | (e13 << 104u64) | (e14 << 112u64) | (e15 << 120u64))) by (bit_vector)
        requires
            e0 <= 0xFF,
            e1 <= 0xFF,
            e2 <= 0xFF,
            e3 <= 0xFF,
            e4 <= 0xFF,
            e5 <= 0xFF,
            e6 <= 0xFF,
            e7 <= 0xFF,
            e8 <= 0xFF,
            e9 <= 0xFF,
            e10 <= 0xFF,
            e11 <= 0xFF,
            e12 <= 0xFF,
            e13 <= 0xFF,
            e14 <= 0xFF,
            e15 <= 0xFF,
            ((b >> 0u64) & 0xFF) == e0,
            ((b >> 8u64) & 0xFF) == e1,
            ((b >> 16u64) & 0xFF) == e2,
            ((b >> 24u64) & 0xFF) == e3,
            ((b >> 32u64) & 0xFF) == e4,
            ((b >> 40u64) & 0xFF) == e5,
            ((b >> 48u64) & 0xFF) == e6,
            ((b >> 56u64) & 0xFF) == e7,
            ((b >> 64u64) & 0xFF) == e8,
            ((b >> 72u64) & 0xFF) == e9,
            ((b >> 80u64) & 0xFF) == e10,
            ((b >> 88u64) & 0xFF) == e11,
            ((b >> 96u64) & 0xFF) == e12,
            ((b >> 104u64) & 0xFF) == e13,
            ((b >> 112u64) & 0xFF) == e14,
            ((b >> 120u64) & 0xFF) == e15,
    ;
}

// ===========================================================================
// ByteCombine payloads for GF192/GF256 (upstream
// large_fields_constants.rs :73-104 resp. :247-278 -- Alphas::ALPHA;
// both values transcribed verbatim from the pinned upstream), wave 3.
// The ByteCombine traits' declaration syntax drops at the trait
// boundary (the FA2/FA3 convention); the payloads ride as const faces
// so the FA6 hashers can consume them per-domain.
// ===========================================================================

/// Alphas::ALPHA for GF192 (upstream large_fields_constants.rs
/// :73-104, values verbatim; each element is the limb pair).
pub const GF192_ALPHA: [(u128, u128); 7] = [
    (0xe665d76c966ebdeaccc8a3d56f389763, 0x310bc8140e6b3662),
    (0x7bf61f19d5633f26b233619e7cf450bb, 0xda933726d491db34),
    (0x8232e37706328d199c6d2c13f5398a0d, 0x0c3b0d703c754ef6),
    (0x7a5542ab0058d22edd20747cbd2bf75d, 0x45ec519c94bc1251),
    (0x08168cb767debe84d8d50ce28ace2bf8, 0xd67d146a4ba67045),
    (0xf3eaf7ae5fd72048970f9c76eed5e1ba, 0x29a6bd5f696cea43),
    (0x6019fd623906e9d3f5945dc265068571, 0xc77c56540f87c4b0),
];

/// ByteCombineConstants for GF192 (upstream :229-243):
///     const BYTE_COMBINE_2: Self = Self::ALPHA[0];
///     const BYTE_COMBINE_3: Self = Self([ALPHA[0] ^ ONE, ...]);
/// ONE is the value pair (1, 0), so the per-limb xor is on limb 0.
pub const GF192_BYTE_COMBINE_2: (u128, u128) = (0xe665d76c966ebdeaccc8a3d56f389763, 0x310bc8140e6b3662);
pub const GF192_BYTE_COMBINE_3: (u128, u128) = (0xe665d76c966ebdeaccc8a3d56f389762, 0x310bc8140e6b3662);

/// Alphas::ALPHA for GF256 (upstream :247-278, values verbatim).
pub const GF256_ALPHA: [(u128, u128); 7] = [
    (0xbed68d38a0474e67969788420bdefee7, 0x04c9a8cf20c95833df229845f8f1e16a),
    (0x2ba5c48d2c42072fa95af52ad52289c1, 0x064e4d699c5b4af1d14a0d376c00b0ea),
    (0x1771831e533b0f5755dab3833f809d1d, 0x6195e3db7011f68dfb96573fad3fac10),
    (0x752758911a30e3f6de010519b01bcdd5, 0x56c24fd64f7688382a0778b6489ea03f),
    (0x1bc4dbd440f1848298c2f529e98a30b6, 0x22270b6d71574ffc2fbe09947d49a981),
    (0xaced66c666f1afbc9e75afb9de44670b, 0xc03d372fd1fa29f3f001253ff2991f7e),
    (0x5237c4d625b86f0dba43b698b332e88b, 0x133eea09d26b7bb82f652b2af4e81545),
];

/// ByteCombineConstants for GF256 (upstream :402-416).
pub const GF256_BYTE_COMBINE_2: (u128, u128) = (0xbed68d38a0474e67969788420bdefee7, 0x04c9a8cf20c95833df229845f8f1e16a);
pub const GF256_BYTE_COMBINE_3: (u128, u128) = (0xbed68d38a0474e67969788420bdefee6, 0x04c9a8cf20c95833df229845f8f1e16a);

// ===========================================================================
// GF192 (upstream large_fields.rs :979-1109, wave 2): the [u128; 2]
// plane. BigGF<u128, 2, 192> lowers to a u128 pair; the Field constants
// (:1084-1087), the Length = U24 byte count, the From<&[u8]> split
// (:1100-1109), as_bytes (:1090-1095), the Modulus (:979-981) and the
// ClearHighBits limb-1 mask (:983-989) all lower to the faces below.
// Origin Rust (gf192_mul, :998-1052, docstring "Multiplies two 192-bit
// polynomials 'x', 'y' over the finite field GF(2). Stores the result
// in 'x'"):
//     fn gf192_mul(x: &mut [u128; 2], y: &[u128; 2]) {
//         let xlow_ylow = u128_clmul_ll(x[0], y[0]);
//         let xhigh_yhigh = u128_clmul_ll(x[1], y[1]);
//         let x1_cat_y0_plus_y2 = allignr_8bytes(y[0] ^ y[1], x[0]);
//         let xsum = x[0] ^ x[1] ^ x1_cat_y0_plus_y2; // Result in low.
//         let ysum = y[0] ^ x1_cat_y0_plus_y2;        // Result in high.
//         let xsum_ysum = u128_clmul_lh(xsum, ysum);
//         let xa = x[0] ^ (x[1] ^ (x[1] & U128_LOWER_MASK) << 64);
//         let ya = y[0] ^ (y[1] ^ (y[1] & U128_LOWER_MASK) << 64);
//         let karatsuba_out =
//             karatsuba_mul_128_uninterpolated_other_sum(xa, ya, x[0], y[0]);
//         let xya0 = karatsuba_out[0] ^ karatsuba_out[2];
//         let xya1 = karatsuba_out[0] ^ karatsuba_out[1];
//         let xya0_plus_xsum_ysum = xya0 ^ xsum_ysum;
//         let combined = combine_poly128s_5(&[
//             xlow_ylow,
//             xya0_plus_xsum_ysum ^ xhigh_yhigh,
//             xya0_plus_xsum_ysum ^ xya1,
//             xlow_ylow ^ xsum_ysum ^ xya1,
//             xhigh_yhigh,
//         ]);
//         // Reduction modulo x^192 + x^7 + x^2 + x^1 + 1 (Intel wp p.16/17)
//         let x2 = combined[1] >> 64 ^ combined[2] << 64;
//         let x3 = combined[2] >> 64;
//         let a = x3 >> 63; let b = x3 >> 62; let c = x3 >> 57;
//         let d = x2 ^ a ^ b ^ c;
//         let e1_e0 = [d << 1, x3 << 1 ^ d >> 127];
//         let f1_f0 = [d << 2, x3 << 2 ^ d >> 126];
//         let g1_g0 = [d << 7, x3 << 7 ^ d >> 121];
//         let h1_h0 = [
//             d ^ e1_e0[0] ^ f1_f0[0] ^ g1_g0[0],
//             x3 ^ e1_e0[1] ^ f1_f0[1] ^ g1_g0[1],
//         ];
//         x[0] = combined[0] ^ h1_h0[0];
//         x[1] = (combined[1] ^ h1_h0[1]) & U128_LOWER_MASK; }
// The combine_poly128s_5 body (:39-45) inlines below (its upstream form
// is [x[0] ^ x[1] << 64, x[2] ^ allignr_8bytes(x[3], x[1]),
// x[3] >> 64 ^ x[4]]).
//
// Representation fiducials: the two-limb sum lines preserve upstream
// operator precedence ((x[1] & MASK) << 64 binds as written); the
// exec twin returns the pair instead of mutating through x.
// ===========================================================================

/// Reduction-polynomial low half for GF(2^192) (upstream `MODULUS`,
/// large_fields.rs :980: 0b10000111 -- same low half as GF128).
pub const GF192_MODULUS: u128 = 0x87;

/// Field::Length of GF192 (U24) at the byte-count lowering.
pub const GF192_LENGTH_BYTES: usize = 24;

/// Field::ZERO for GF192 (upstream :1085, Self([0, 0])), value pair.
pub const GF192_ZERO: (u128, u128) = (0, 0);

/// Field::ONE for GF192 (upstream :1086, Self([1, 0])), value pair.
pub const GF192_ONE: (u128, u128) = (1, 0);

/// The GF(2^192) multiplication spec face: the upstream algorithm's
/// own composition (three clmuls over 64-bit halves plus the
/// uninterpolated-other-sum karatsuba route and the Intel-paper
/// 192-bit reduction), as a pure spec expression over the lowered
/// two-limb pair. Returns the result limbs (lo, hi-64).
pub open spec fn gf192_mul_spec(x0: u128, x1: u128, y0: u128, y1: u128) -> (u128, u128)
{
    let xl_yl = clmul64_bits(x0 & U128_LOWER_MASK, y0 & U128_LOWER_MASK, 64nat);
    let xh_yh = clmul64_bits(x1 & U128_LOWER_MASK, y1 & U128_LOWER_MASK, 64nat);
    let cat = allignr_8bytes(y0 ^ y1, x0);
    let xsum = x0 ^ x1 ^ cat;
    let ysum = y0 ^ cat;
    let xs_ys = clmul64_bits(xsum & U128_LOWER_MASK, ysum >> 64, 64nat);
    let xa = x0 ^ (x1 ^ ((x1 & U128_LOWER_MASK) << 64));
    let ya = y0 ^ (y1 ^ ((y1 & U128_LOWER_MASK) << 64));
    // karatsuba_mul_128_uninterpolated_other_sum(xa, ya, x0, y0), body
    // large_fields.rs :132-146 -- with x_for_sum = x0, y_for_sum = y0 the
    // cat inside is allignr_8bytes(y0, x0)
    let x0y0 = clmul64_bits(xa & U128_LOWER_MASK, ya & U128_LOWER_MASK, 64nat);
    let x1y1 = clmul64_bits(xa >> 64, ya >> 64, 64nat);
    let cat2 = allignr_8bytes(y0, x0);
    let xsum2 = x0 ^ cat2;
    let ysum2 = y0 ^ cat2;
    let xs2_ys2 = clmul64_bits(xsum2 & U128_LOWER_MASK, ysum2 >> 64, 64nat);
    let xya0 = x0y0 ^ x1y1;
    let xya1 = x0y0 ^ xs2_ys2;
    let s = xya0 ^ xs_ys;
    // combine_poly128s_5
    let in0 = xl_yl;
    let in1 = s ^ xh_yh;
    let in2 = s ^ xya1;
    let in3 = xl_yl ^ xs_ys ^ xya1;
    let in4 = xh_yh;
    let c0 = in0 ^ (in1 << 64);
    let c1 = in2 ^ (allignr_8bytes(in3, in1));
    let c2 = (in3 >> 64) ^ in4;
    // Intel reduction, verbatim
    let x2 = (c1 >> 64) ^ (c2 << 64);
    let x3 = c2 >> 64;
    let a = x3 >> 63;
    let b = x3 >> 62;
    let c = x3 >> 57;
    let d = x2 ^ a ^ b ^ c;
    let e1 = d << 1;
    let e0 = (x3 << 1) ^ (d >> 127);
    let f1 = d << 2;
    let f0 = (x3 << 2) ^ (d >> 126);
    let g1 = d << 7;
    let g0 = (x3 << 7) ^ (d >> 121);
    let h0 = d ^ e1 ^ f1 ^ g1;
    let h1 = x3 ^ e0 ^ f0 ^ g0;
    let out0 = c0 ^ h0;
    let out1 = (c1 ^ h1) & U128_LOWER_MASK;
    (out0, out1)
}

/// The MulAssign<&Self> face for GF192 (upstream :1078-1082:
/// `fn mul_assign(&mut self, rhs: &Self) { gf192_mul(&mut self.0,
/// &rhs.0) }`). The exec twin keeps the upstream expression tree
/// verbatim (the value-returning resyntax of the mutating core);
/// every clmul site is the shared verified core face, so the equality
/// to the spec face is plain congruence (the probe2 route).
pub exec fn gf192_mul(x0: u128, x1: u128, y0: u128, y1: u128) -> (out: (u128, u128))
    ensures
        out == gf192_mul_spec(x0, x1, y0, y1),
{
    let xl_yl: u128 = u128_clmul_ll(x0, y0);
    let xh_yh: u128 = u128_clmul_ll(x1, y1);
    let cat: u128 = allignr_exec8(y0 ^ y1, x0);
    let xsum: u128 = x0 ^ x1 ^ cat;
    let ysum: u128 = y0 ^ cat;
    let xs_ys: u128 = u128_clmul_lh(xsum, ysum);
    let xa: u128 = x0 ^ (x1 ^ ((x1 & U128_LOWER_MASK) << 64));
    let ya: u128 = y0 ^ (y1 ^ ((y1 & U128_LOWER_MASK) << 64));
    let kout: [u128; 3] = karatsuba_128_uninterpolated_other_sum(xa, ya, x0, y0);
    let xya0: u128 = kout[0] ^ kout[2];
    let xya1: u128 = kout[0] ^ kout[1];
    let s: u128 = xya0 ^ xs_ys;
    let in0: u128 = xl_yl;
    let in1: u128 = s ^ xh_yh;
    let in2: u128 = s ^ xya1;
    let in3: u128 = xl_yl ^ xs_ys ^ xya1;
    let in4: u128 = xh_yh;
    let c0: u128 = in0 ^ (in1 << 64);
    let c1: u128 = in2 ^ (allignr_exec8(in3, in1));
    let c2: u128 = (in3 >> 64) ^ in4;
    // Step 1
    let x2: u128 = (c1 >> 64) ^ (c2 << 64);
    let x3: u128 = c2 >> 64;
    let a: u128 = x3 >> 63;
    let b: u128 = x3 >> 62;
    let c: u128 = x3 >> 57;
    // Step 2
    let d: u128 = x2 ^ a ^ b ^ c;
    // Step 3
    let e1: u128 = d << 1;
    let e0: u128 = (x3 << 1) ^ (d >> 127);
    let f1: u128 = d << 2;
    let f0: u128 = (x3 << 2) ^ (d >> 126);
    let g1: u128 = d << 7;
    let g0: u128 = (x3 << 7) ^ (d >> 121);
    // Step 4
    let h0: u128 = d ^ e1 ^ f1 ^ g1;
    let h1: u128 = x3 ^ e0 ^ f0 ^ g0;
    let out0: u128 = c0 ^ h0;
    let out1: u128 = (c1 ^ h1) & U128_LOWER_MASK;
    (out0, out1)
}

/// exec value face of allignr_8bytes (upstream :34-36), used at the
/// GF192/256 combiner sites; the spec twin is allignr_8bytes.
#[inline]
pub exec fn allignr_exec8(x: u128, y: u128) -> (res: u128)
    ensures
        res == allignr_8bytes(x, y),
{
    (x << 64) ^ (y >> 64)
}

/// The upstream karatsuba_mul_128_uninterpolated_other_sum body
/// (:132-146 verbatim; doc: gf192 consumes it), exec twin with the
/// per-site clmul ensures.
#[inline]
pub exec fn karatsuba_128_uninterpolated_other_sum(
    x: u128,
    y: u128,
    x_for_sum: u128,
    y_for_sum: u128,
) -> (out: [u128; 3])
    ensures
        out[0] == clmul64_bits(x & U128_LOWER_MASK, y & U128_LOWER_MASK, 64nat),
        out[2] == clmul64_bits(x >> 64, y >> 64, 64nat),
        out[1] == clmul64_bits(
            (x_for_sum ^ (allignr_8bytes(y_for_sum, x_for_sum))) & U128_LOWER_MASK,
            (y_for_sum ^ (allignr_8bytes(y_for_sum, x_for_sum))) >> 64,
            64nat,
        ),
{
    let x0y0: u128 = u128_clmul_ll(x, y);
    let x1y1: u128 = u128_clmul_hh(x, y);
    let x1_cat_y0: u128 = allignr_exec8(y_for_sum, x_for_sum);
    let xsum: u128 = x_for_sum ^ x1_cat_y0;
    let ysum: u128 = y_for_sum ^ x1_cat_y0;
    let xs_ys: u128 = u128_clmul_lh(xsum, ysum);
    [x0y0, xs_ys, x1y1]
}

// ===========================================================================
// GF256 (upstream large_fields.rs :1134-1292): the [u128; 2] plane,
// Field Length U32, Modulus 0b10000100101 (:1226-1228), from/as_bytes
// (:1243-1259). Origin gf256_mul (:1148-1194, karatsuba via
// karatsuba_mul_128_uncombined + combine_poly128s_7 + the Intel
// 256-bit reduction modulo x^256 + x^10 + x^5 + x^2 + 1).
// ===========================================================================

/// Reduction-polynomial low half for GF(2^256) (upstream :1227:
/// 0b10000100101).
pub const GF256_MODULUS: u128 = 0x425;

/// Field::Length of GF256 (U32) at the byte-count lowering.
pub const GF256_LENGTH_BYTES: usize = 32;

/// Field::ZERO for GF256 (upstream :1238), value pair.
pub const GF256_ZERO: (u128, u128) = (0, 0);

/// Field::ONE for GF256 (upstream :1239), value pair.
pub const GF256_ONE: (u128, u128) = (1, 0);

/// The GF(2^256) multiplication spec face: the upstream composition
/// (three karatsuba_mul_128_uncombined products + the combine_poly128s_7
/// recombination + the Intel 256-bit reduction) as a pure expression.
pub open spec fn gf256_mul_spec(x0: u128, x1: u128, y0: u128, y1: u128) -> (u128, u128)
{
    // karatsuba_mul_128_uncombined(x0, y0), spec
    let l0 = clmul64_bits(x0 & U128_LOWER_MASK, y0 & U128_LOWER_MASK, 64nat);
    let h0 = clmul64_bits(x0 >> 64, y0 >> 64, 64nat);
    let m0 = clmul64_bits(
        (x0 >> 64) ^ (x0 & U128_LOWER_MASK),
        (y0 >> 64) ^ (y0 & U128_LOWER_MASK), 64nat) ^ l0 ^ h0;
    let j0 = [l0, m0, h0];
    // karatsuba_mul_128_uncombined(x1, y1), spec
    let l1 = clmul64_bits(x1 & U128_LOWER_MASK, y1 & U128_LOWER_MASK, 64nat);
    let h1 = clmul64_bits(x1 >> 64, y1 >> 64, 64nat);
    let m1 = clmul64_bits(
        (x1 >> 64) ^ (x1 & U128_LOWER_MASK),
        (y1 >> 64) ^ (y1 & U128_LOWER_MASK), 64nat) ^ l1 ^ h1;
    let j1 = [l1, m1, h1];
    // karatsuba_mul_128_uncombined(x0 ^ x1, y0 ^ y1), spec
    let la = clmul64_bits((x0 ^ x1) & U128_LOWER_MASK, (y0 ^ y1) & U128_LOWER_MASK, 64nat);
    let ha = clmul64_bits((x0 ^ x1) >> 64, (y0 ^ y1) >> 64, 64nat);
    let ma = clmul64_bits(
        ((x0 ^ x1) >> 64) ^ ((x0 ^ x1) & U128_LOWER_MASK),
        ((y0 ^ y1) >> 64) ^ ((y0 ^ y1) & U128_LOWER_MASK), 64nat) ^ la ^ ha;
    let ja = [la, ma, ha];
    // gf256_mul body
    let cross = j0[2] ^ j1[0];
    let in0 = j0[0];
    let in1 = j0[1];
    let in2 = ja[0] ^ j0[0] ^ cross;
    let in3 = ja[1] ^ j0[1] ^ j1[1];
    let in4 = ja[2] ^ j1[2] ^ cross;
    let in5 = j1[1];
    let in6 = j1[2];
    // combine_poly128s_7 (:48-55)
    let c0 = in0 ^ (in1 << 64);
    let c1 = in2 ^ (allignr_8bytes(in3, in1));
    let c2 = in4 ^ (allignr_8bytes(in5, in3));
    let c3 = (in5 >> 64) ^ in6;
    // Intel reduction modulo x^256 + x^10 + x^5 + x^2 + 1
    let x2 = c2;
    let x3 = c3;
    let a = x3 >> 126;
    let b = x3 >> 123;
    let c = x3 >> 118;
    let d = x2 ^ a ^ b ^ c;
    let e1 = d << 2;
    let e0 = (x3 << 2) ^ (d >> 126);
    let f1 = d << 5;
    let f0 = (x3 << 5) ^ (d >> 123);
    let g1 = d << 10;
    let g0 = (x3 << 10) ^ (d >> 118);
    let h0 = d ^ e1 ^ f1 ^ g1;
    let h1 = x3 ^ e0 ^ f0 ^ g0;
    (c0 ^ h0, c1 ^ h1)
}

/// The MulAssign<&Self> face for GF256 (upstream :1220-1224 + core
/// :1149-1194 verbatim resyntax).
pub exec fn gf256_mul(x0: u128, x1: u128, y0: u128, y1: u128) -> (out: (u128, u128))
    ensures
        out == gf256_mul_spec(x0, x1, y0, y1),
{
    proof {
        // the uncombined face's mid slot is the karatsuba_mid spec
        // application; its definition needs instantiated call sites
        // (#FA3-1 def-bridge convention) -- one per inner product
        lemma_karatsuba_mid_def(x0, y0);
        lemma_karatsuba_mid_def(x1, y1);
        lemma_karatsuba_mid_def(x0 ^ x1, y0 ^ y1);
    }
    let j0: [u128; 3] = karatsuba_mul_128_uncombined(x0, y0);
    let j1: [u128; 3] = karatsuba_mul_128_uncombined(x1, y1);
    let ja: [u128; 3] = karatsuba_mul_128_uncombined(x0 ^ x1, y0 ^ y1);
    let cross: u128 = j0[2] ^ j1[0];
    let in0: u128 = j0[0];
    let in1: u128 = j0[1];
    let in2: u128 = ja[0] ^ j0[0] ^ cross;
    let in3: u128 = ja[1] ^ j0[1] ^ j1[1];
    let in4: u128 = ja[2] ^ j1[2] ^ cross;
    let in5: u128 = j1[1];
    let in6: u128 = j1[2];
    let c0: u128 = in0 ^ (in1 << 64);
    let c1: u128 = in2 ^ (allignr_exec8(in3, in1));
    let c2: u128 = in4 ^ (allignr_exec8(in5, in3));
    let c3: u128 = (in5 >> 64) ^ in6;
    // Step 1
    let x2: u128 = c2;
    let x3: u128 = c3;
    let a: u128 = x3 >> 126;
    let b: u128 = x3 >> 123;
    let c: u128 = x3 >> 118;
    // Step 2
    let d: u128 = x2 ^ a ^ b ^ c;
    // Step 3
    let e1: u128 = d << 2;
    let e0: u128 = (x3 << 2) ^ (d >> 126);
    let f1: u128 = d << 5;
    let f0: u128 = (x3 << 5) ^ (d >> 123);
    let g1: u128 = d << 10;
    let g0: u128 = (x3 << 10) ^ (d >> 118);
    // Step 4
    let h0: u128 = d ^ e1 ^ f1 ^ g1;
    let h1: u128 = x3 ^ e0 ^ f0 ^ g0;
    let out0: u128 = c0 ^ h0;
    let out1: u128 = c1 ^ h1;
    (out0, out1)
}

// ===========================================================================
// GF384 / GF576 / GF768 (upstream large_fields.rs :1294-1493, wave 2's
// byte-plane and constants section): the extension fields carry the
// BaseField security relation (fields/mod.rs:78-79: "For security,
// FAEST requires the extension field to have 3x the length of the
// base field"), their moduli, byte faces, and the ExtensionField
// trait records. The Mul<BaseField> orbit loops (:518-542 at the
// consumers) remain wave-3 scope (D-FA3-3's execution half); the
// constants below pin the security invariant now -- each extension
// length is exactly 3x its base's byte length.
// ===========================================================================

/// Reduction-polynomial low half for GF(2^384) (upstream :1298,
/// 0b1000000001101).
pub const GF384_MODULUS: u128 = 0x100D;

/// Reduction-polynomial low half for GF(2^576) (upstream :1359:
/// 0b10000000011001 == 0x2019, bits 13/4/3 -- x^13 + x^4 + x^3 + 1
/// over the 576-bit plane).
pub const GF576_MODULUS: u128 = 0x2019;

/// Reduction-polynomial low half for GF(2^768) (upstream :1433,
/// 0b10100000000000010001).
pub const GF768_MODULUS: u128 = 0xA0011;

/// Field::Length of GF384 (U48) at the byte-count lowering.
pub const GF384_LENGTH_BYTES: usize = 48;

/// Field::Length of GF576 (U72) at the byte-count lowering.
pub const GF576_LENGTH_BYTES: usize = 72;

/// Field::Length of GF768 (U96) at the byte-count lowering.
pub const GF768_LENGTH_BYTES: usize = 96;

/// BaseField security pin (upstream fields/mod.rs:78-79): the
/// extension field carries exactly 3x the byte length of its base
/// field. One theorem per pairing, checked at const level.
/// The tuple is (GF128, GF192, GF256) bases to (GF384, GF576, GF768).
pub proof fn lemma_extension_length_pin_128()
    ensures
        GF384_LENGTH_BYTES == 3 * GF128_LENGTH_BYTES,
{
    // 48 == 3 * 16, plain const arithmetic
}

pub proof fn lemma_extension_length_pin_192()
    ensures
        GF576_LENGTH_BYTES == 3 * GF192_LENGTH_BYTES,
{
    // 72 == 3 * 24
}

pub proof fn lemma_extension_length_pin_256()
    ensures
        GF768_LENGTH_BYTES == 3 * GF256_LENGTH_BYTES,
{
    // 96 == 3 * 32
}

// ===========================================================================
// SumPoly (upstream large_fields.rs :224-246 with the blanket impl
// :329-346, GF128 instantiation), wave 2.
// Origin Rust:
///     pub trait SumPoly: Field {
///         /// Compute polynomial sum
///         fn sum_poly(v: &[Self]) -> Self;
///         fn sum_poly_bits(v: &[u8]) -> Self; }
///     impl<T> SumPoly for T where ... {
///         fn sum_poly(v: &[Self]) -> Self {
///             v.iter().rev().skip(1)
///                 .fold(v[v.len() - 1], |sum, val| sum.double() + val) }
///         fn sum_poly_bits(v: &[u8]) -> Self {
///             let init = Self::from_bit(v[v.len() - 1] >> 7);
///             (0..v.len() * 8).rev().skip(1).fold(init, |sum, i| {
///                 sum.double() + Self::from_bit(v[i / 8] >> (i % 8))
///             }) } }
// The sum is the MSB-first Horner over the field's characteristic
// orbit: acc <- acc*2 + term.
// ===========================================================================

/// The GF128 sum_poly exec face for an eight-element slice (the byte
/// face upstream consumers use; the v[v.len()-1]-first, then reverse
/// fold). The value contract: the fold result is (v7.first), and the
/// reverse accumulation applies double-then-add for each v6..v0 term.
/// The upstream iteration order and term selection are preserved
/// (rev().skip(1) over the slice = indices len-1 alone seeded, then
/// len-2 ..= 0 consumed by the running sum).
pub open spec fn gf128_sum_poly8_spec(
    v0: u128,
    v1: u128,
    v2: u128,
    v3: u128,
    v4: u128,
    v5: u128,
    v6: u128,
    v7: u128,
) -> u128 {
    // seed with v7, then double-and-add v6, v5, ..., v0
    let s0 = v7;
    let s1 = gf128_xtime(s0) ^ v6;
    let s2 = gf128_xtime(s1) ^ v5;
    let s3 = gf128_xtime(s2) ^ v4;
    let s4 = gf128_xtime(s3) ^ v3;
    let s5 = gf128_xtime(s4) ^ v2;
    let s6 = gf128_xtime(s5) ^ v1;
    let s7 = gf128_xtime(s6) ^ v0;
    s7
}

/// The GF128 sum_poly exec face (upstream :333-338 instantiated at
/// eight elements, the byte-block shape FAEST consumes).
pub exec fn gf128_sum_poly8(
    v0: u128,
    v1: u128,
    v2: u128,
    v3: u128,
    v4: u128,
    v5: u128,
    v6: u128,
    v7: u128,
) -> (res: u128)
    ensures
        res == gf128_sum_poly8_spec(v0, v1, v2, v3, v4, v5, v6, v7),
{
    let s0: u128 = v7;
    let s1: u128 = gf128_double(s0) ^ v6;
    let s2: u128 = gf128_double(s1) ^ v5;
    let s3: u128 = gf128_double(s2) ^ v4;
    let s4: u128 = gf128_double(s3) ^ v3;
    let s5: u128 = gf128_double(s4) ^ v2;
    let s6: u128 = gf128_double(s5) ^ v1;
    let s7: u128 = gf128_double(s6) ^ v0;
    s7
}

/// The MSB-projection spec face of sum_poly_bits for one byte (the
/// upstream v[i/8] >> (i % 8) at bit index i): bit i of the byte in
/// the field's 0/1 element.
pub open spec fn gf128_sum_poly_bits1_spec(x: u8) -> u128 {
    // byte consumed MSB-first: from_bit(bit 7) doubles into the low
    // positions; the pairs (position, value):
    // sum = ((((((((b7)d + b6)d + b5)d + b4)d + b3)d + b2)d + b1)d + b0
    // where d = double and bk = from_bit((x >> k) & 1)
    let b0 = if x & 1 == 1 { GF128_ONE } else { 0u128 };
    let b1 = if (x >> 1) & 1 == 1 { GF128_ONE } else { 0u128 };
    let b2 = if (x >> 2) & 1 == 1 { GF128_ONE } else { 0u128 };
    let b3 = if (x >> 3) & 1 == 1 { GF128_ONE } else { 0u128 };
    let b4 = if (x >> 4) & 1 == 1 { GF128_ONE } else { 0u128 };
    let b5 = if (x >> 5) & 1 == 1 { GF128_ONE } else { 0u128 };
    let b6 = if (x >> 6) & 1 == 1 { GF128_ONE } else { 0u128 };
    let b7 = if (x >> 7) & 1 == 1 { GF128_ONE } else { 0u128 };
    let s1 = b7;
    let s2 = gf128_xtime(s1) ^ b6;
    let s3 = gf128_xtime(s2) ^ b5;
    let s4 = gf128_xtime(s3) ^ b4;
    let s5 = gf128_xtime(s4) ^ b3;
    let s6 = gf128_xtime(s5) ^ b2;
    let s7 = gf128_xtime(s6) ^ b1;
    let s8 = gf128_xtime(s7) ^ b0;
    s8
}

/// The GF128 sum_poly_bits exec face for one byte (upstream :340-345
/// instantiated at len == 1: the single byte, MSB-first).
pub exec fn gf128_sum_poly_bits1(x: u8) -> (res: u128)
    ensures
        res == gf128_sum_poly_bits1_spec(x),
{
    // fold order: bit 7 doubles into position 0 ...
    let init: u128 = if (x >> 7) & 1 == 1 { GF128_ONE } else { 0u128 };
    let s1: u128 = gf128_double(init) ^ (if (x >> 6) & 1 == 1 { GF128_ONE } else { 0u128 });
    let s2: u128 = gf128_double(s1) ^ (if (x >> 5) & 1 == 1 { GF128_ONE } else { 0u128 });
    let s3: u128 = gf128_double(s2) ^ (if (x >> 4) & 1 == 1 { GF128_ONE } else { 0u128 });
    let s4: u128 = gf128_double(s3) ^ (if (x >> 3) & 1 == 1 { GF128_ONE } else { 0u128 });
    let s5: u128 = gf128_double(s4) ^ (if (x >> 2) & 1 == 1 { GF128_ONE } else { 0u128 });
    let s6: u128 = gf128_double(s5) ^ (if (x >> 1) & 1 == 1 { GF128_ONE } else { 0u128 });
    let s7: u128 = gf128_double(s6) ^ (if x & 1 == 1 { GF128_ONE } else { 0u128 });
    s7
}

// ===========================================================================
// byte_combine_slice (upstream large_fields.rs :388-394, D-FA3-5):
//     fn byte_combine_slice(x: &[Self]) -> Self {
//         debug_assert_eq!(x.len(), 8);
//         let (x0, x) = x.split_at(1);
//         x.iter().zip(Self::ALPHA).fold(x0[0], ...) }
// The slice form is byte_combine's expression over a len-8 slice; the
// debug assert re-erects as the requires (the FA2/FA3 convention).
// ===========================================================================

/// Zero-orbit stationarity: xtime(0) == 0 (one concrete blast plus
/// the definitional fold; #FA3-3 restated premises).
pub proof fn lemma_xtime128_zero()
    ensures
        gf128_xtime(0u128) == 0u128,
{
    assert((0u128 >> 127) & 1 == 0) by (bit_vector);
    assert((((0u128 << 1) ^ (if ((0u128 >> 127) & 1) == 1u128 { GF128_MODULUS } else { 0u128 }))) == 0u128) by (bit_vector);
}

/// The upstream sum_poly zero row, generically at the 8-element byte
/// block: folding eight zero elements through the double-and-add
/// chain yields the field zero (each step folds through xtime(0)==0
/// and 0^0 == 0, with the zero-literal application repeated).
pub proof fn lemma_sum_poly8_zero()
    ensures
        gf128_sum_poly8_spec(0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128)
            == 0u128,
{
    lemma_xtime128_zero();
    let s1: u128 = gf128_xtime(0u128) ^ 0u128;
    let s2: u128 = gf128_xtime(s1) ^ 0u128;
    let s3: u128 = gf128_xtime(s2) ^ 0u128;
    let s4: u128 = gf128_xtime(s3) ^ 0u128;
    let s5: u128 = gf128_xtime(s4) ^ 0u128;
    let s6: u128 = gf128_xtime(s5) ^ 0u128;
    let s7: u128 = gf128_xtime(s6) ^ 0u128;
    assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    assert(s1 == 0u128);
    assert(gf128_xtime(s1) == gf128_xtime(0u128));
    assert(s2 == 0u128);
    assert(gf128_xtime(s2) == gf128_xtime(0u128));
    assert(s3 == 0u128);
    assert(gf128_xtime(s3) == gf128_xtime(0u128));
    assert(s4 == 0u128);
    assert(s5 == 0u128);
    assert(s6 == 0u128);
    assert(s7 == 0u128);
    assert(gf128_sum_poly8_spec(0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128, 0u128)
        == s7);
}

/// The upstream sum_poly_bits zero row at the single-byte face.
pub proof fn lemma_sum_poly_bits1_zero()
    ensures
        gf128_sum_poly_bits1_spec(0u8) == 0u128,
{
    lemma_xtime128_zero();
    // all eight bit projections of x = 0 are zero (nonnegated and
    // negated forms, so every spec-side select folds)
    assert(((0u8 >> 7) & 1) == 0u8) by (bit_vector);
    assert(!(((0u8 >> 7) & 1) == 1u8));
    assert(((0u8 >> 6) & 1) == 0u8) by (bit_vector);
    assert(!(((0u8 >> 6) & 1) == 1u8));
    assert(((0u8 >> 5) & 1) == 0u8) by (bit_vector);
    assert(!(((0u8 >> 5) & 1) == 1u8));
    assert(((0u8 >> 4) & 1) == 0u8) by (bit_vector);
    assert(!(((0u8 >> 4) & 1) == 1u8));
    assert(((0u8 >> 3) & 1) == 0u8) by (bit_vector);
    assert(!(((0u8 >> 3) & 1) == 1u8));
    assert(((0u8 >> 2) & 1) == 0u8) by (bit_vector);
    assert(!(((0u8 >> 2) & 1) == 1u8));
    assert(((0u8 >> 1) & 1) == 0u8) by (bit_vector);
    assert(!(((0u8 >> 1) & 1) == 1u8));
    assert(((0u8 & 1) == 0u8)) by (bit_vector);
    assert(!((0u8 & 1) == 1u8));
    let s1: u128 = 0u128;
    let s2: u128 = gf128_xtime(s1) ^ 0u128;
    let s3: u128 = gf128_xtime(s2) ^ 0u128;
    let s4: u128 = gf128_xtime(s3) ^ 0u128;
    let s5: u128 = gf128_xtime(s4) ^ 0u128;
    let s6: u128 = gf128_xtime(s5) ^ 0u128;
    let s7: u128 = gf128_xtime(s6) ^ 0u128;
    let s8: u128 = gf128_xtime(s7) ^ 0u128;
    assert((0u128 ^ 0u128) == 0u128) by (bit_vector);
    assert(s2 == 0u128);
    assert(gf128_xtime(s2) == gf128_xtime(0u128));
    assert(s3 == 0u128);
    assert(gf128_xtime(s3) == gf128_xtime(0u128));
    assert(s4 == 0u128);
    assert(gf128_xtime(s4) == gf128_xtime(0u128));
    assert(s5 == 0u128);
    assert(gf128_xtime(s5) == gf128_xtime(0u128));
    assert(s6 == 0u128);
    assert(gf128_xtime(s6) == gf128_xtime(0u128));
    assert(s7 == 0u128);
    assert(gf128_xtime(s7) == gf128_xtime(0u128));
    assert(s8 == 0u128);
    assert(gf128_sum_poly_bits1_spec(0u8) == s8);
}

/// The GF128 byte_combine_slice exec face (upstream :388-394). The
/// value contract is byte_combine's, index-aligned: slice element j
/// pairs with ALPHA[j-1] for j >= 1.
pub exec fn gf128_byte_combine_slice(x: &[u128]) -> (res: u128)
    requires
        x.len() == 8,
    ensures
        res == gf128_byte_combine_spec(
            x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7],
        ),
{
    gf128_byte_combine(
        x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7],
    )
}

// ===========================================================================
// GF576 / GF768 multiplication cores (wave 3). The 576 = 4.5*128 plane
// masks its top limb (limb 4) to the low 64 bits every orbit step
// (upstream ClearHighBits :1362-1368); the domain MSB is bit 575 =
// limb-4 bit 63. GF768 is the full six-limb plane with MSB at limb-5
// bit 127. The base multipliers: GF192 pairs (192 bits) resp. GF256
// pairs (256 bits), consumed LSB-first per the upstream to_mask_bit.
// ===========================================================================

/// Orbit step of GF(2^384): limb cascade shift; limb-2's old bit 127
/// (the domain MSB, bit 383) reduces limb 0 by the modulus 0x100D.
pub open spec fn gf384_xtime_lo(v0: u128, v1: u128, v2: u128) -> u128 {
    ((v0 << 1) ^ (if (v2 >> 127) & 1 == 1 { GF384_MODULUS } else { 0u128 }))
}

pub open spec fn gf384_xtime_mid(v0: u128, v1: u128) -> u128 {
    ((v1 << 1) | (v0 >> 127))
}

pub open spec fn gf384_xtime_hi(v1: u128, v2: u128) -> u128 {
    ((v2 << 1) | (v1 >> 127))
}

/// Spec helper: per-limb xor of two orbit triples.
pub open spec fn xor3(
    a: (u128, u128, u128),
    b: (u128, u128, u128),
) -> (u128, u128, u128) {
    (a.0 ^ b.0, a.1 ^ b.1, a.2 ^ b.2)
}

/// Definitional bridge of xor3 (the open spec fn needs instantiated
/// call sites at its consumers, #FA3-1).
pub proof fn lemma_xor3_def(
    a: (u128, u128, u128),
    b: (u128, u128, u128),
)
    ensures
        xor3(a, b) == (a.0 ^ b.0, a.1 ^ b.1, a.2 ^ b.2),
{
}


/// low-bit Horner over the base multiplier with the 3-limb orbit.
pub open spec fn gf384_mul_bits(orbit0: u128, orbit1: u128, orbit2: u128, r: u128, w: nat)
    -> (u128, u128, u128)
    decreases w,
{
    if w == 0 {
        (0u128, 0u128, 0u128)
    } else {
        let t0 = gf384_xtime_lo(orbit0, orbit1, orbit2);
        let t1 = gf384_xtime_mid(orbit0, orbit1);
        let t2 = gf384_xtime_hi(orbit1, orbit2);
        let tail = gf384_mul_bits(t0, t1, t2, r >> 1, (w - 1) as nat);
        let s0 = if r & 1 == 1 { orbit0 } else { 0u128 };
        let s1 = if r & 1 == 1 { orbit1 } else { 0u128 };
        let s2 = if r & 1 == 1 { orbit2 } else { 0u128 };
        (s0 ^ tail.0, s1 ^ tail.1, s2 ^ tail.2)
    }
}

/// Definitional one-level unfold of the GF384 model at non-zero fuel.
pub proof fn lemma_mul384_bits_unfold(o0: u128, o1: u128, o2: u128, r: u128, w: nat)
    requires
        0 < w,
    ensures
        gf384_mul_bits(o0, o1, o2, r, w)
            == xor3(
                (if r & 1 == 1 { o0 } else { 0u128 },
                 if r & 1 == 1 { o1 } else { 0u128 },
                 if r & 1 == 1 { o2 } else { 0u128 }),
                gf384_mul_bits(
                    gf384_xtime_lo(o0, o1, o2),
                    gf384_xtime_mid(o0, o1),
                    gf384_xtime_hi(o1, o2),
                    r >> 1, (w - 1) as nat),
            ),
{
}

/// The GF384 Mul<GF128> face (upstream gf_mul :518-542 at the GF384
/// instantiation: 128 orbit steps over the base multiplier bits).
pub exec fn gf384_mul_gf128(x0: u128, x1: u128, x2: u128, y: u128) -> (res: (u128, u128, u128))
    ensures
        res == gf384_mul_bits(x0, x1, x2, y, 128nat),
{
    let mut l0: u128 = x0;
    let mut l1: u128 = x1;
    let mut l2: u128 = x2;
    let mut r0: u128 = if y & 1 == 1 { x0 } else { 0u128 };
    let mut r1: u128 = if y & 1 == 1 { x1 } else { 0u128 };
    let mut r2: u128 = if y & 1 == 1 { x2 } else { 0u128 };
    proof {
        lemma_mul384_bits_unfold(x0, x1, x2, y, 128nat);
        let t0 = gf384_xtime_lo(x0, x1, x2);
        let t1 = gf384_xtime_mid(x0, x1);
        let t2 = gf384_xtime_hi(x1, x2);
        let tail = gf384_mul_bits(t0, t1, t2, y >> 1, 127nat);
        bv_xor_comm128(tail.0, r0);
        bv_xor_comm128(tail.1, r1);
        bv_xor_comm128(tail.2, r2);
    }
    let mut idx: usize = 1;
    while idx < 128
        invariant
            1 <= idx <= 128,
            xor3(gf384_mul_bits(
                gf384_xtime_lo(l0, l1, l2),
                gf384_xtime_mid(l0, l1),
                gf384_xtime_hi(l1, l2),
                y >> (idx as u64), (128 - idx) as nat,
            ), (r0, r1, r2)) == gf384_mul_bits(x0, x1, x2, y, 128nat),
        decreases 128 - idx,
    {
        let o0: u128 = l0;
        let o1: u128 = l1;
        let o2: u128 = l2;
        let s0: u128 = r0;
        let s1: u128 = r1;
        let s2: u128 = r2;
        let y_i: u128 = y >> (idx as u64);
        proof {
            if (idx + 1) < 128 {
                assert((y_i >> 1) == (y >> ((idx + 1) as u64))) by (bit_vector)
                    requires
                        (idx + 1) < 128,
                        y_i == y >> (idx as u64),
                ;
            } else {
                assert((y >> 127) >> 1 == 0u128) by (bit_vector);
                assert(y_i == (y >> 127)) by (bit_vector)
                    requires
                        idx == 127,
                        y_i == y >> (idx as u64),
                ;
                assert((y_i >> 1) == 0u128);
            }
            lemma_mul384_bits_unfold(o0, o1, o2, y_i, (128 - idx) as nat);
        }
        let mh: u8 = gf128_bit_at(o2, 127);
        let m: u128 = if (mh as u128) != 0 { GF384_MODULUS } else { 0u128 };
        l2 = (o2 << 1) | (o1 >> 127);
        l1 = (o1 << 1) | (o0 >> 127);
        l0 = (o0 << 1) ^ m;
        proof {
            assert((mh as u128) == ((o2 >> 127) & 1));
            assert(m == (if ((o2 >> 127) & 1) == 1u128 { GF384_MODULUS } else { 0u128 }));
            assert(l0 == gf384_xtime_lo(o0, o1, o2));
            assert(l1 == gf384_xtime_mid(o0, o1));
            assert(l2 == gf384_xtime_hi(o1, o2));
        }
        r0 = s0 ^ (if y_i & 1 == 1 { l0 } else { 0u128 });
        r1 = s1 ^ (if y_i & 1 == 1 { l1 } else { 0u128 });
        r2 = s2 ^ (if y_i & 1 == 1 { l2 } else { 0u128 });
        proof {
            let c0 = if y_i & 1 == 1u128 { l0 } else { 0u128 };
            let c1 = if y_i & 1 == 1u128 { l1 } else { 0u128 };
            let c2 = if y_i & 1 == 1u128 { l2 } else { 0u128 };
            let n0 = gf384_xtime_lo(l0, l1, l2);
            let n1 = gf384_xtime_mid(l0, l1);
            let n2 = gf384_xtime_hi(l1, l2);
            let tail_old = gf384_mul_bits(l0, l1, l2, y_i, (128 - idx) as nat);
            let tail_new = gf384_mul_bits(n0, n1, n2, y_i >> 1, (128 - idx - 1) as nat);
            assert(xor3(tail_old, (s0, s1, s2)) == gf384_mul_bits(x0, x1, x2, y, 128nat));
            assert(tail_old == xor3((c0, c1, c2), tail_new));
            assert(tail_new.0 ^ r0 == tail_old.0 ^ s0) by {
                bv_xor_ac128(c0, tail_new.0, s0);
                bv_xor_comm128(c0, s0);
                assert((c0 ^ tail_new.0) ^ s0 == tail_new.0 ^ (s0 ^ c0));
                assert(tail_old.0 == c0 ^ tail_new.0);
            }
            assert(tail_new.1 ^ r1 == tail_old.1 ^ s1) by {
                bv_xor_ac128(c1, tail_new.1, s1);
                bv_xor_comm128(c1, s1);
                assert((c1 ^ tail_new.1) ^ s1 == tail_new.1 ^ (s1 ^ c1));
                assert(tail_old.1 == c1 ^ tail_new.1);
            }
            assert(tail_new.2 ^ r2 == tail_old.2 ^ s2) by {
                bv_xor_ac128(c2, tail_new.2, s2);
                bv_xor_comm128(c2, s2);
                assert((c2 ^ tail_new.2) ^ s2 == tail_new.2 ^ (s2 ^ c2));
                assert(tail_old.2 == c2 ^ tail_new.2);
            }
        }
        idx += 1;
    }
    proof {
        let n0 = gf384_xtime_lo(l0, l1, l2);
        let n1 = gf384_xtime_mid(l0, l1);
        let n2 = gf384_xtime_hi(l1, l2);
        assert(gf384_mul_bits(n0, n1, n2, y >> 128u64, 0nat) == (0u128, 0u128, 0u128));
        assert((y >> 128u64) == 0u128) by (bit_vector);
        assert((0u128 ^ r0) == r0) by (bit_vector);
        assert((0u128 ^ r1) == r1) by (bit_vector);
        assert((0u128 ^ r2) == r2) by (bit_vector);
    }
    (r0, r1, r2)
}

/// Orbit step spec faces of GF(2^576). The 576 = 4.5*128 plane masks
/// its top limb (limb 4) to the low 64 bits each step (upstream
/// ClearHighBits :1362-1368); the domain MSB is bit 575 = limb-4's
/// bit 63, and the reduction bit feeds limb 0.
pub open spec fn gf576_xtime_l0(v0: u128, v4lo: u128) -> u128 {
    ((v0 << 1) ^ (if (v4lo >> 63) & 1 == 1 { GF576_MODULUS } else { 0u128 }))
}

pub open spec fn gf576_xtime_l1(v0: u128, v1: u128) -> u128 {
    ((v1 << 1) | (v0 >> 127))
}

pub open spec fn gf576_xtime_lm(vlo: u128, vhi: u128) -> u128 {
    ((vhi << 1) | (vlo >> 127))
}

pub open spec fn gf576_xtime_l4(v3: u128, v4: u128) -> u128 {
    (((v4 << 1) | (v3 >> 127)) & U128_LOWER_MASK)
}

/// Spec helper: per-limb xor of two 5-tuples.
pub open spec fn xor5(
    a: (u128, u128, u128, u128, u128),
    b: (u128, u128, u128, u128, u128),
) -> (u128, u128, u128, u128, u128) {
    (a.0 ^ b.0, a.1 ^ b.1, a.2 ^ b.2, a.3 ^ b.3, a.4 ^ b.4)
}

/// Definitional bridge of xor5.
pub proof fn lemma_xor5_def(
    a: (u128, u128, u128, u128, u128),
    b: (u128, u128, u128, u128, u128),
)
    ensures
        xor5(a, b) == (a.0 ^ b.0, a.1 ^ b.1, a.2 ^ b.2, a.3 ^ b.3, a.4 ^ b.4),
{
}

/// The GF(2^576) * embedded-GF(2^192) multiplication model: the
/// low-bit Horner over the multiplier pair consumed LSB-first (the
/// pair shifts: low <- low >> 1 | (high & 1) << 127, high <- high >> 1,
/// matching the upstream to_mask_bit(idx) sequence).
pub open spec fn gf576_mul_bits(
    o0: u128, o1: u128, o2: u128, o3: u128, o4: u128,
    r: (u128, u128), w: nat,
) -> (u128, u128, u128, u128, u128)
    decreases w,
{
    if w == 0 {
        (0u128, 0u128, 0u128, 0u128, 0u128)
    } else {
        let t0 = gf576_xtime_l0(o0, o4);
        let t1 = gf576_xtime_l1(o0, o1);
        let t2 = gf576_xtime_lm(o1, o2);
        let t3 = gf576_xtime_lm(o2, o3);
        let t4 = gf576_xtime_l4(o3, o4);
        let tail = gf576_mul_bits(t0, t1, t2, t3, t4,
            ((r.0 >> 1) | ((r.1 & 1) << 127), r.1 >> 1), (w - 1) as nat);
        let s0 = if r.0 & 1 == 1 { o0 } else { 0u128 };
        let s1 = if r.0 & 1 == 1 { o1 } else { 0u128 };
        let s2 = if r.0 & 1 == 1 { o2 } else { 0u128 };
        let s3 = if r.0 & 1 == 1 { o3 } else { 0u128 };
        let s4 = if r.0 & 1 == 1 { o4 } else { 0u128 };
        (s0 ^ tail.0, s1 ^ tail.1, s2 ^ tail.2, s3 ^ tail.3, s4 ^ tail.4)
    }
}

/// Definitional unfold of the GF576 model at non-zero fuel.
pub proof fn lemma_mul576_bits_unfold(
    o0: u128, o1: u128, o2: u128, o3: u128, o4: u128,
    ra: u128, rb: u128, w: nat,
)
    requires
        0 < w,
    ensures
        gf576_mul_bits(o0, o1, o2, o3, o4, (ra, rb), w)
            == xor5(
                (if ra & 1 == 1 { o0 } else { 0u128 },
                 if ra & 1 == 1 { o1 } else { 0u128 },
                 if ra & 1 == 1 { o2 } else { 0u128 },
                 if ra & 1 == 1 { o3 } else { 0u128 },
                 if ra & 1 == 1 { o4 } else { 0u128 }),
                gf576_mul_bits(
                    gf576_xtime_l0(o0, o4),
                    gf576_xtime_l1(o0, o1),
                    gf576_xtime_lm(o1, o2),
                    gf576_xtime_lm(o2, o3),
                    gf576_xtime_l4(o3, o4),
                    ((ra >> 1) | ((rb & 1) << 127), rb >> 1), (w - 1) as nat),
            ),
{
}

/// The GF576 Mul<GF192> face (upstream gf_mul at the GF576
/// instantiation: 192 orbit steps). The loop keeps the upstream shape
/// (MSB mask at limb-4's bit 63, the five-limb cascade shift with the
/// top-limb 64-bit mask, limb-0 reduction, per-rung select-and-xor);
/// the multiplier pair is shifted LSB-first per rung, matching the
/// model's transition, so rung idx consumes the upstream
/// to_mask_bit(idx) bit.
pub exec fn gf576_mul_gf192(
    x0: u128, x1: u128, x2: u128, x3: u128, x4: u128,
    y0: u128, y1: u128,
) -> (res: (u128, u128, u128, u128, u128))
    ensures
        res == gf576_mul_bits(x0, x1, x2, x3, x4 & U128_LOWER_MASK, (y0, y1), 192nat),
{
    let mut l0: u128 = x0;
    let mut l1: u128 = x1;
    let mut l2: u128 = x2;
    let mut l3: u128 = x3;
    let mut l4: u128 = x4 & U128_LOWER_MASK;
    let mut ra: u128 = y0;
    let mut rb: u128 = y1;
    let mut r0: u128 = if ra & 1 == 1 { l0 } else { 0u128 };
    let mut r1: u128 = if ra & 1 == 1 { l1 } else { 0u128 };
    let mut r2: u128 = if ra & 1 == 1 { l2 } else { 0u128 };
    let mut r3: u128 = if ra & 1 == 1 { l3 } else { 0u128 };
    let mut r4: u128 = if ra & 1 == 1 { l4 } else { 0u128 };
    proof {
        lemma_mul576_bits_unfold(x0, x1, x2, x3, x4 & U128_LOWER_MASK, y0, y1, 192nat);
        // entry regroup per limb: contribution ^ tail ^ result == spec
        let t0 = gf576_xtime_l0(x0, x4 & U128_LOWER_MASK);
        let t1 = gf576_xtime_l1(x0, x1);
        let t2 = gf576_xtime_lm(x1, x2);
        let t3 = gf576_xtime_lm(x2, x3);
        let t4 = gf576_xtime_l4(x3, x4 & U128_LOWER_MASK);
        let tail = gf576_mul_bits(t0, t1, t2, t3, t4,
            ((y0 >> 1) | ((y1 & 1) << 127), y1 >> 1), 191nat);
        bv_xor_comm128(tail.0, r0);
        bv_xor_comm128(tail.1, r1);
        bv_xor_comm128(tail.2, r2);
        bv_xor_comm128(tail.3, r3);
        bv_xor_comm128(tail.4, r4);
    }
    // the entry seed consumed bit 0; the pair state moves one step
    // so the loop's remaining-tail invariant aligns with the model
    ra = (y0 >> 1) | ((y1 & 1) << 127);
    rb = y1 >> 1;
    let mut steps: usize = 1;
    while steps < 192
        invariant
            1 <= steps <= 192,
            steps < 192 ==>
                xor5(gf576_mul_bits(
                    gf576_xtime_l0(l0, l4),
                    gf576_xtime_l1(l0, l1),
                    gf576_xtime_lm(l1, l2),
                    gf576_xtime_lm(l2, l3),
                    gf576_xtime_l4(l3, l4),
                    (ra, rb), (192 - steps) as nat,
                ), (r0, r1, r2, r3, r4))
                    == gf576_mul_bits(x0, x1, x2, x3, x4 & U128_LOWER_MASK, (y0, y1), 192nat),
            steps == 192 ==>
                (r0, r1, r2, r3, r4) == gf576_mul_bits(x0, x1, x2, x3, x4 & U128_LOWER_MASK, (y0, y1), 192nat),
        decreases 192 - steps,
    {
        let o0: u128 = l0;
        let o1: u128 = l1;
        let o2: u128 = l2;
        let o3: u128 = l3;
        let o4: u128 = l4;
        let oa: u128 = ra;
        let ob: u128 = rb;
        let s0: u128 = r0;
        let s1: u128 = r1;
        let s2: u128 = r2;
        let s3: u128 = r3;
        let s4: u128 = r4;
        proof {
            lemma_mul576_bits_unfold(o0, o1, o2, o3, o4, oa, ob, (192 - steps) as nat);
        }
        let bh: u8 = gf128_bit_at(o4, 63);
        let m: u128 = if (bh as u128) != 0 { GF576_MODULUS } else { 0u128 };
        l4 = ((o4 << 1) | (o3 >> 127)) & U128_LOWER_MASK;
        l3 = (o3 << 1) | (o2 >> 127);
        l2 = (o2 << 1) | (o1 >> 127);
        l1 = (o1 << 1) | (o0 >> 127);
        l0 = (o0 << 1) ^ m;
        proof {
            assert((bh as u128) == ((o4 >> 63) & 1));
            assert(m == (if ((o4 >> 63) & 1) == 1u128 { GF576_MODULUS } else { 0u128 }));
            assert(l0 == gf576_xtime_l0(o0, o4));
            assert(l1 == gf576_xtime_l1(o0, o1));
            assert(l2 == gf576_xtime_lm(o1, o2));
            assert(l3 == gf576_xtime_lm(o2, o3));
            assert(l4 == gf576_xtime_l4(o3, o4));
        }
        // contribution select at the current LSB of the pair
        r0 = s0 ^ (if oa & 1 == 1 { l0 } else { 0u128 });
        r1 = s1 ^ (if oa & 1 == 1 { l1 } else { 0u128 });
        r2 = s2 ^ (if oa & 1 == 1 { l2 } else { 0u128 });
        r3 = s3 ^ (if oa & 1 == 1 { l3 } else { 0u128 });
        r4 = s4 ^ (if oa & 1 == 1 { l4 } else { 0u128 });
        ra = (oa >> 1) | ((ob & 1) << 127);
        rb = ob >> 1;
        proof {
            let c0 = if oa & 1 == 1u128 { l0 } else { 0u128 };
            let c1 = if oa & 1 == 1u128 { l1 } else { 0u128 };
            let c2 = if oa & 1 == 1u128 { l2 } else { 0u128 };
            let c3 = if oa & 1 == 1u128 { l3 } else { 0u128 };
            let c4 = if oa & 1 == 1u128 { l4 } else { 0u128 };
            let n0 = gf576_xtime_l0(l0, l4);
            let n1 = gf576_xtime_l1(l0, l1);
            let n2 = gf576_xtime_lm(l1, l2);
            let n3 = gf576_xtime_lm(l2, l3);
            let n4 = gf576_xtime_l4(l3, l4);
            let tail_old = gf576_mul_bits(l0, l1, l2, l3, l4, (oa, ob), (192 - steps) as nat);
            let tail_new = gf576_mul_bits(n0, n1, n2, n3, n4, (ra, rb), (192 - steps - 1) as nat);
            // second unfold: over the POST-STEP orbit and the PRE-SHIFT
            // pair -- this peels the rung's contribution off tail_old
            lemma_mul576_bits_unfold(l0, l1, l2, l3, l4, oa, ob, (192 - steps) as nat);
            assert(tail_old == xor5((c0, c1, c2, c3, c4), tail_new));
            let spec = gf576_mul_bits(x0, x1, x2, x3, x4 & U128_LOWER_MASK, (y0, y1), 192nat);
            // per limb: tail_old.0 ^ s0 == spec.0 and the c-contribution
            // lampshades: tail_new.0 ^ (s0 ^ c0) == tail_old.0 ^ s0
            assert(tail_new.0 ^ r0 == tail_old.0 ^ s0) by {
                bv_xor_ac128(c0, tail_new.0, s0);
                bv_xor_comm128(c0, s0);
                assert((c0 ^ tail_new.0) ^ s0 == tail_new.0 ^ (s0 ^ c0));
                assert(tail_old.0 == c0 ^ tail_new.0);
            }
            assert(tail_new.1 ^ r1 == tail_old.1 ^ s1) by {
                bv_xor_ac128(c1, tail_new.1, s1);
                bv_xor_comm128(c1, s1);
                assert((c1 ^ tail_new.1) ^ s1 == tail_new.1 ^ (s1 ^ c1));
                assert(tail_old.1 == c1 ^ tail_new.1);
            }
            assert(tail_new.2 ^ r2 == tail_old.2 ^ s2) by {
                bv_xor_ac128(c2, tail_new.2, s2);
                bv_xor_comm128(c2, s2);
                assert((c2 ^ tail_new.2) ^ s2 == tail_new.2 ^ (s2 ^ c2));
                assert(tail_old.2 == c2 ^ tail_new.2);
            }
            assert(tail_new.3 ^ r3 == tail_old.3 ^ s3) by {
                bv_xor_ac128(c3, tail_new.3, s3);
                bv_xor_comm128(c3, s3);
                assert((c3 ^ tail_new.3) ^ s3 == tail_new.3 ^ (s3 ^ c3));
                assert(tail_old.3 == c3 ^ tail_new.3);
            }
            assert(tail_new.4 ^ r4 == tail_old.4 ^ s4) by {
                bv_xor_ac128(c4, tail_new.4, s4);
                bv_xor_comm128(c4, s4);
                assert((c4 ^ tail_new.4) ^ s4 == tail_new.4 ^ (s4 ^ c4));
                assert(tail_old.4 == c4 ^ tail_new.4);
            }
            // the boundary rung: the remaining fuel runs out and the
            // piecewise branch takes over -- the zero-fuel tail is the
            // zero tuple (definition) and zero-xor folds away
            if (steps + 1) == 192 {
                assert(tail_old == xor5((c0, c1, c2, c3, c4), tail_new));
                lemma_xor5_def((c0, c1, c2, c3, c4), tail_new);
                assert(tail_new == (0u128, 0u128, 0u128, 0u128, 0u128)) by {
                    assert(gf576_mul_bits(n0, n1, n2, n3, n4, (ra, rb), 0nat)
                        == (0u128, 0u128, 0u128, 0u128, 0u128));
                }
                assert(tail_new.0 == 0u128);
                assert(tail_new.1 == 0u128);
                assert(tail_new.2 == 0u128);
                assert(tail_new.3 == 0u128);
                assert(tail_new.4 == 0u128);
                bv_xor_zero128(tail_new.0);
                bv_xor_zero128(tail_new.1);
                bv_xor_zero128(tail_new.2);
                bv_xor_zero128(tail_new.3);
                bv_xor_zero128(tail_new.4);
                assert(tail_old.0 == (c0 ^ tail_new.0));
                let tz0: u128 = tail_new.0;
                assert((c0 ^ tz0) == c0) by (bit_vector)
                    requires
                        tz0 == 0u128,
                ;
                assert(tail_old.1 == (c1 ^ tail_new.1));
                let tz1: u128 = tail_new.1;
                assert((c1 ^ tz1) == c1) by (bit_vector)
                    requires
                        tz1 == 0u128,
                ;
                assert(tail_old.2 == (c2 ^ tail_new.2));
                let tz2: u128 = tail_new.2;
                assert((c2 ^ tz2) == c2) by (bit_vector)
                    requires
                        tz2 == 0u128,
                ;
                assert(tail_old.3 == (c3 ^ tail_new.3));
                let tz3: u128 = tail_new.3;
                assert((c3 ^ tz3) == c3) by (bit_vector)
                    requires
                        tz3 == 0u128,
                ;
                assert(tail_old.4 == (c4 ^ tail_new.4));
                let tz4: u128 = tail_new.4;
                assert((c4 ^ tz4) == c4) by (bit_vector)
                    requires
                        tz4 == 0u128,
                ;
                // boundary close: tail_old collapses to the contribution
                // tuple, so the accumulated r (s ^ c) IS the spec
                assert(tail_old == (c0, c1, c2, c3, c4));
                assert((r0, r1, r2, r3, r4) == (s0 ^ c0, s1 ^ c1, s2 ^ c2, s3 ^ c3, s4 ^ c4));
                bv_xor_comm128(s0, c0);
                bv_xor_comm128(s1, c1);
                bv_xor_comm128(s2, c2);
                bv_xor_comm128(s3, c3);
                bv_xor_comm128(s4, c4);
                assert(xor5(tail_old, (s0, s1, s2, s3, s4))
                    == gf576_mul_bits(x0, x1, x2, x3, x4 & U128_LOWER_MASK, (y0, y1), 192nat));
                assert((r0, r1, r2, r3, r4)
                    == gf576_mul_bits(x0, x1, x2, x3, x4 & U128_LOWER_MASK, (y0, y1), 192nat));
            }
        }
        steps += 1;
    }
    proof {
        // exit: remaining fuel 0 -> tail triple zero; zeros fold away
        assert((192 - 192) == 0);
        let n0 = gf576_xtime_l0(l0, l4);
        let n1 = gf576_xtime_l1(l0, l1);
        let n2 = gf576_xtime_lm(l1, l2);
        let n3 = gf576_xtime_lm(l2, l3);
        let n4 = gf576_xtime_l4(l3, l4);
        assert(gf576_mul_bits(n0, n1, n2, n3, n4, (ra, rb), 0nat)
            == (0u128, 0u128, 0u128, 0u128, 0u128));
        assert((0u128 ^ r0) == r0) by (bit_vector);
        assert((0u128 ^ r1) == r1) by (bit_vector);
        assert((0u128 ^ r2) == r2) by (bit_vector);
        assert((0u128 ^ r3) == r3) by (bit_vector);
        assert((0u128 ^ r4) == r4) by (bit_vector);
    }
    (r0, r1, r2, r3, r4)
}

/// Orbit step spec faces of GF(2^768): the full six-limb cascade;
/// the domain MSB (bit 767 = limb-5 bit 127) reduces limb 0 by
/// 0xA0011 (upstream MODULUS :1433:
/// 0b10100000000000010001, bits 19/17/4/0 -- X^768+X^19+X^17+X^4+1;
/// no ClearHighBits mask). Erratum: the wave-3 transcription wrote
/// 0x140011 here (a hand-decode of the binary literal that added a
/// 21st leading bit); the interop-probe wave-2 seven-way check
/// (faest-rs portable/SIMD, in-tree JSON/KAT, faest-ref v2.0,
/// regenerated KAT, official vectors) re-decoded the literal as
/// 0xA0011 and the in-tree data agrees; the constant was corrected
/// accordingly (see the FA6 notes erratum section).
pub open spec fn gf768_xtime_l0(v0: u128, v5: u128) -> u128 {
    ((v0 << 1) ^ (if (v5 >> 127) & 1 == 1 { GF768_MODULUS } else { 0u128 }))
}

pub open spec fn gf768_xtime_lc(vlo: u128, vhi: u128) -> u128 {
    ((vhi << 1) | (vlo >> 127))
}

/// Spec helper: per-limb xor of two 6-tuples.
pub open spec fn xor6(
    a: (u128, u128, u128, u128, u128, u128),
    b: (u128, u128, u128, u128, u128, u128),
) -> (u128, u128, u128, u128, u128, u128) {
    (a.0 ^ b.0, a.1 ^ b.1, a.2 ^ b.2, a.3 ^ b.3, a.4 ^ b.4, a.5 ^ b.5)
}

/// The GF(2^768) * embedded-GF(2^256) multiplication model (the
/// low-bit Horner over the multiplier pair consumed LSB-first).
pub open spec fn gf768_mul_bits(
    o0: u128, o1: u128, o2: u128, o3: u128, o4: u128, o5: u128,
    r: (u128, u128), w: nat,
) -> (u128, u128, u128, u128, u128, u128)
    decreases w,
{
    if w == 0 {
        (0u128, 0u128, 0u128, 0u128, 0u128, 0u128)
    } else {
        let t0 = gf768_xtime_l0(o0, o5);
        let t1 = gf768_xtime_lc(o0, o1);
        let t2 = gf768_xtime_lc(o1, o2);
        let t3 = gf768_xtime_lc(o2, o3);
        let t4 = gf768_xtime_lc(o3, o4);
        let t5 = gf768_xtime_lc(o4, o5);
        let tail = gf768_mul_bits(t0, t1, t2, t3, t4, t5,
            ((r.0 >> 1) | ((r.1 & 1) << 127), r.1 >> 1), (w - 1) as nat);
        let s0 = if r.0 & 1 == 1 { o0 } else { 0u128 };
        let s1 = if r.0 & 1 == 1 { o1 } else { 0u128 };
        let s2 = if r.0 & 1 == 1 { o2 } else { 0u128 };
        let s3 = if r.0 & 1 == 1 { o3 } else { 0u128 };
        let s4 = if r.0 & 1 == 1 { o4 } else { 0u128 };
        let s5 = if r.0 & 1 == 1 { o5 } else { 0u128 };
        (s0 ^ tail.0, s1 ^ tail.1, s2 ^ tail.2, s3 ^ tail.3, s4 ^ tail.4, s5 ^ tail.5)
    }
}

/// Definitional bridge of xor6.
pub proof fn lemma_xor6_def(
    a: (u128, u128, u128, u128, u128, u128),
    b: (u128, u128, u128, u128, u128, u128),
)
    ensures
        xor6(a, b) == (a.0 ^ b.0, a.1 ^ b.1, a.2 ^ b.2, a.3 ^ b.3, a.4 ^ b.4, a.5 ^ b.5),
{
}

/// Definitional unfold of the GF768 model at non-zero fuel.
pub proof fn lemma_mul768_bits_unfold(
    o0: u128, o1: u128, o2: u128, o3: u128, o4: u128, o5: u128,
    ra: u128, rb: u128, w: nat,
)
    requires
        0 < w,
    ensures
        gf768_mul_bits(o0, o1, o2, o3, o4, o5, (ra, rb), w)
            == xor6(
                (if ra & 1 == 1 { o0 } else { 0u128 },
                 if ra & 1 == 1 { o1 } else { 0u128 },
                 if ra & 1 == 1 { o2 } else { 0u128 },
                 if ra & 1 == 1 { o3 } else { 0u128 },
                 if ra & 1 == 1 { o4 } else { 0u128 },
                 if ra & 1 == 1 { o5 } else { 0u128 }),
                gf768_mul_bits(
                    gf768_xtime_l0(o0, o5),
                    gf768_xtime_lc(o0, o1),
                    gf768_xtime_lc(o1, o2),
                    gf768_xtime_lc(o2, o3),
                    gf768_xtime_lc(o3, o4),
                    gf768_xtime_lc(o4, o5),
                    ((ra >> 1) | ((rb & 1) << 127), rb >> 1), (w - 1) as nat),
            ),
{
}

/// The GF768 Mul<GF256> face (upstream gf_mul at the GF768
/// instantiation: 256 orbit steps; the loop shape is the GF576 twin
/// without the top-limb mask -- the 768 domain is a whole 6*128).
pub exec fn gf768_mul_gf256(
    x0: u128, x1: u128, x2: u128, x3: u128, x4: u128, x5: u128,
    y0: u128, y1: u128,
) -> (res: (u128, u128, u128, u128, u128, u128))
    ensures
        res == gf768_mul_bits(x0, x1, x2, x3, x4, x5, (y0, y1), 256nat),
{
    let mut l0: u128 = x0;
    let mut l1: u128 = x1;
    let mut l2: u128 = x2;
    let mut l3: u128 = x3;
    let mut l4: u128 = x4;
    let mut l5: u128 = x5;
    let mut ra: u128 = y0;
    let mut rb: u128 = y1;
    let mut r0: u128 = if ra & 1 == 1 { l0 } else { 0u128 };
    let mut r1: u128 = if ra & 1 == 1 { l1 } else { 0u128 };
    let mut r2: u128 = if ra & 1 == 1 { l2 } else { 0u128 };
    let mut r3: u128 = if ra & 1 == 1 { l3 } else { 0u128 };
    let mut r4: u128 = if ra & 1 == 1 { l4 } else { 0u128 };
    let mut r5: u128 = if ra & 1 == 1 { l5 } else { 0u128 };
    proof {
        lemma_mul768_bits_unfold(x0, x1, x2, x3, x4, x5, y0, y1, 256nat);
        let t0 = gf768_xtime_l0(x0, x5);
        let t1 = gf768_xtime_lc(x0, x1);
        let t2 = gf768_xtime_lc(x1, x2);
        let t3 = gf768_xtime_lc(x2, x3);
        let t4 = gf768_xtime_lc(x3, x4);
        let t5 = gf768_xtime_lc(x4, x5);
        let tail = gf768_mul_bits(t0, t1, t2, t3, t4, t5,
            ((y0 >> 1) | ((y1 & 1) << 127), y1 >> 1), 255nat);
        bv_xor_comm128(tail.0, r0);
        bv_xor_comm128(tail.1, r1);
        bv_xor_comm128(tail.2, r2);
        bv_xor_comm128(tail.3, r3);
        bv_xor_comm128(tail.4, r4);
        bv_xor_comm128(tail.5, r5);
    }
    // the entry seed consumed bit 0; shift the pair state once
    ra = (y0 >> 1) | ((y1 & 1) << 127);
    rb = y1 >> 1;
    let mut steps: usize = 1;
    while steps < 256
        invariant
            1 <= steps <= 256,
            steps < 256 ==>
                xor6(gf768_mul_bits(
                    gf768_xtime_l0(l0, l5),
                    gf768_xtime_lc(l0, l1),
                    gf768_xtime_lc(l1, l2),
                    gf768_xtime_lc(l2, l3),
                    gf768_xtime_lc(l3, l4),
                    gf768_xtime_lc(l4, l5),
                    (ra, rb), (256 - steps) as nat,
                ), (r0, r1, r2, r3, r4, r5))
                    == gf768_mul_bits(x0, x1, x2, x3, x4, x5, (y0, y1), 256nat),
            steps == 256 ==>
                (r0, r1, r2, r3, r4, r5) == gf768_mul_bits(x0, x1, x2, x3, x4, x5, (y0, y1), 256nat),
        decreases 256 - steps,
    {
        let o0: u128 = l0;
        let o1: u128 = l1;
        let o2: u128 = l2;
        let o3: u128 = l3;
        let o4: u128 = l4;
        let o5: u128 = l5;
        let oa: u128 = ra;
        let ob: u128 = rb;
        let s0: u128 = r0;
        let s1: u128 = r1;
        let s2: u128 = r2;
        let s3: u128 = r3;
        let s4: u128 = r4;
        let s5: u128 = r5;
        proof {
            lemma_mul768_bits_unfold(o0, o1, o2, o3, o4, o5, oa, ob, (256 - steps) as nat);
        }
        let bh: u8 = gf128_bit_at(o5, 127);
        let m: u128 = if (bh as u128) != 0 { GF768_MODULUS } else { 0u128 };
        l5 = (o5 << 1) | (o4 >> 127);
        l4 = (o4 << 1) | (o3 >> 127);
        l3 = (o3 << 1) | (o2 >> 127);
        l2 = (o2 << 1) | (o1 >> 127);
        l1 = (o1 << 1) | (o0 >> 127);
        l0 = (o0 << 1) ^ m;
        proof {
            assert((bh as u128) == ((o5 >> 127) & 1));
            assert(m == (if ((o5 >> 127) & 1) == 1u128 { GF768_MODULUS } else { 0u128 }));
            assert(l0 == gf768_xtime_l0(o0, o5));
            assert(l1 == gf768_xtime_lc(o0, o1));
            assert(l2 == gf768_xtime_lc(o1, o2));
            assert(l3 == gf768_xtime_lc(o2, o3));
            assert(l4 == gf768_xtime_lc(o3, o4));
            assert(l5 == gf768_xtime_lc(o4, o5));
        }
        r0 = s0 ^ (if oa & 1 == 1 { l0 } else { 0u128 });
        r1 = s1 ^ (if oa & 1 == 1 { l1 } else { 0u128 });
        r2 = s2 ^ (if oa & 1 == 1 { l2 } else { 0u128 });
        r3 = s3 ^ (if oa & 1 == 1 { l3 } else { 0u128 });
        r4 = s4 ^ (if oa & 1 == 1 { l4 } else { 0u128 });
        r5 = s5 ^ (if oa & 1 == 1 { l5 } else { 0u128 });
        ra = (oa >> 1) | ((ob & 1) << 127);
        rb = ob >> 1;
        proof {
            let c0 = if oa & 1 == 1u128 { l0 } else { 0u128 };
            let c1 = if oa & 1 == 1u128 { l1 } else { 0u128 };
            let c2 = if oa & 1 == 1u128 { l2 } else { 0u128 };
            let c3 = if oa & 1 == 1u128 { l3 } else { 0u128 };
            let c4 = if oa & 1 == 1u128 { l4 } else { 0u128 };
            let c5 = if oa & 1 == 1u128 { l5 } else { 0u128 };
            let n0 = gf768_xtime_l0(l0, l5);
            let n1 = gf768_xtime_lc(l0, l1);
            let n2 = gf768_xtime_lc(l1, l2);
            let n3 = gf768_xtime_lc(l2, l3);
            let n4 = gf768_xtime_lc(l3, l4);
            let n5 = gf768_xtime_lc(l4, l5);
            let tail_old = gf768_mul_bits(l0, l1, l2, l3, l4, l5, (oa, ob), (256 - steps) as nat);
            let tail_new = gf768_mul_bits(n0, n1, n2, n3, n4, n5, (ra, rb), (256 - steps - 1) as nat);
            lemma_mul768_bits_unfold(l0, l1, l2, l3, l4, l5, oa, ob, (256 - steps) as nat);
            assert(tail_old == xor6((c0, c1, c2, c3, c4, c5), tail_new));
            assert(tail_new.0 ^ r0 == tail_old.0 ^ s0) by {
                bv_xor_ac128(c0, tail_new.0, s0);
                bv_xor_comm128(c0, s0);
                assert((c0 ^ tail_new.0) ^ s0 == tail_new.0 ^ (s0 ^ c0));
                assert(tail_old.0 == c0 ^ tail_new.0);
            }
            assert(tail_new.1 ^ r1 == tail_old.1 ^ s1) by {
                bv_xor_ac128(c1, tail_new.1, s1);
                bv_xor_comm128(c1, s1);
                assert((c1 ^ tail_new.1) ^ s1 == tail_new.1 ^ (s1 ^ c1));
                assert(tail_old.1 == c1 ^ tail_new.1);
            }
            assert(tail_new.2 ^ r2 == tail_old.2 ^ s2) by {
                bv_xor_ac128(c2, tail_new.2, s2);
                bv_xor_comm128(c2, s2);
                assert((c2 ^ tail_new.2) ^ s2 == tail_new.2 ^ (s2 ^ c2));
                assert(tail_old.2 == c2 ^ tail_new.2);
            }
            assert(tail_new.3 ^ r3 == tail_old.3 ^ s3) by {
                bv_xor_ac128(c3, tail_new.3, s3);
                bv_xor_comm128(c3, s3);
                assert((c3 ^ tail_new.3) ^ s3 == tail_new.3 ^ (s3 ^ c3));
                assert(tail_old.3 == c3 ^ tail_new.3);
            }
            assert(tail_new.4 ^ r4 == tail_old.4 ^ s4) by {
                bv_xor_ac128(c4, tail_new.4, s4);
                bv_xor_comm128(c4, s4);
                assert((c4 ^ tail_new.4) ^ s4 == tail_new.4 ^ (s4 ^ c4));
                assert(tail_old.4 == c4 ^ tail_new.4);
            }
            assert(tail_new.5 ^ r5 == tail_old.5 ^ s5) by {
                bv_xor_ac128(c5, tail_new.5, s5);
                bv_xor_comm128(c5, s5);
                assert((c5 ^ tail_new.5) ^ s5 == tail_new.5 ^ (s5 ^ c5));
                assert(tail_old.5 == c5 ^ tail_new.5);
            }
            if (steps + 1) == 256 {
                assert(tail_old == xor6((c0, c1, c2, c3, c4, c5), tail_new));
                lemma_xor6_def((c0, c1, c2, c3, c4, c5), tail_new);
                assert(tail_new == (0u128, 0u128, 0u128, 0u128, 0u128, 0u128)) by {
                    assert(gf768_mul_bits(n0, n1, n2, n3, n4, n5, (ra, rb), 0nat)
                        == (0u128, 0u128, 0u128, 0u128, 0u128, 0u128));
                }
                assert(tail_new.0 == 0u128);
                assert(tail_new.1 == 0u128);
                assert(tail_new.2 == 0u128);
                assert(tail_new.3 == 0u128);
                assert(tail_new.4 == 0u128);
                assert(tail_new.5 == 0u128);
                bv_xor_zero128(tail_new.0);
                bv_xor_zero128(tail_new.1);
                bv_xor_zero128(tail_new.2);
                bv_xor_zero128(tail_new.3);
                bv_xor_zero128(tail_new.4);
                bv_xor_zero128(tail_new.5);
                assert(tail_old.0 == (c0 ^ tail_new.0));
                let tz0: u128 = tail_new.0;
                assert((c0 ^ tz0) == c0) by (bit_vector)
                    requires
                        tz0 == 0u128,
                ;
                assert(tail_old.1 == (c1 ^ tail_new.1));
                let tz1: u128 = tail_new.1;
                assert((c1 ^ tz1) == c1) by (bit_vector)
                    requires
                        tz1 == 0u128,
                ;
                assert(tail_old.2 == (c2 ^ tail_new.2));
                let tz2: u128 = tail_new.2;
                assert((c2 ^ tz2) == c2) by (bit_vector)
                    requires
                        tz2 == 0u128,
                ;
                assert(tail_old.3 == (c3 ^ tail_new.3));
                let tz3: u128 = tail_new.3;
                assert((c3 ^ tz3) == c3) by (bit_vector)
                    requires
                        tz3 == 0u128,
                ;
                assert(tail_old.4 == (c4 ^ tail_new.4));
                let tz4: u128 = tail_new.4;
                assert((c4 ^ tz4) == c4) by (bit_vector)
                    requires
                        tz4 == 0u128,
                ;
                assert(tail_old.5 == (c5 ^ tail_new.5));
                let tz5: u128 = tail_new.5;
                assert((c5 ^ tz5) == c5) by (bit_vector)
                    requires
                        tz5 == 0u128,
                ;
                assert(tail_old == (c0, c1, c2, c3, c4, c5));
                assert((r0, r1, r2, r3, r4, r5)
                    == (s0 ^ c0, s1 ^ c1, s2 ^ c2, s3 ^ c3, s4 ^ c4, s5 ^ c5));
                bv_xor_comm128(s0, c0);
                bv_xor_comm128(s1, c1);
                bv_xor_comm128(s2, c2);
                bv_xor_comm128(s3, c3);
                bv_xor_comm128(s4, c4);
                bv_xor_comm128(s5, c5);
                assert(xor6(tail_old, (s0, s1, s2, s3, s4, s5))
                    == gf768_mul_bits(x0, x1, x2, x3, x4, x5, (y0, y1), 256nat));
                assert((r0, r1, r2, r3, r4, r5)
                    == gf768_mul_bits(x0, x1, x2, x3, x4, x5, (y0, y1), 256nat));
            }
        }
        steps += 1;
    }
    proof {
        assert((256 - 256) == 0);
        let n0 = gf768_xtime_l0(l0, l5);
        let n1 = gf768_xtime_lc(l0, l1);
        let n2 = gf768_xtime_lc(l1, l2);
        let n3 = gf768_xtime_lc(l2, l3);
        let n4 = gf768_xtime_lc(l3, l4);
        let n5 = gf768_xtime_lc(l4, l5);
        assert(gf768_mul_bits(n0, n1, n2, n3, n4, n5, (ra, rb), 0nat)
            == (0u128, 0u128, 0u128, 0u128, 0u128, 0u128));
        assert((0u128 ^ r0) == r0) by (bit_vector);
        assert((0u128 ^ r1) == r1) by (bit_vector);
        assert((0u128 ^ r2) == r2) by (bit_vector);
        assert((0u128 ^ r3) == r3) by (bit_vector);
        assert((0u128 ^ r4) == r4) by (bit_vector);
        assert((0u128 ^ r5) == r5) by (bit_vector);
    }
    (r0, r1, r2, r3, r4, r5)
}

// Records (upstream surfaces outside this wave\'s lowered scope).
//   - combine_poly128s_5 / combine_poly128s_7 (:39-55): pure
//     composition constants over allignr_8bytes; value-level spec
//     twins mount with the GF192/GF256 wave (second wave).
//   - SquareBytes::square_byte / square_byte_inplace (:236-276): the
//     generic 8-sum formula; trait blankets drop at the BigGaloisField
//     tower; second wave.
//   - ByteCombineSquared blanket (:302-313) and SumPoly (:329-346):
//     build on ByteCombine + square_bits + Double; second wave.
//   - No inverse surface exists (upstream Field doc, fields/mod.rs
//     :43-44): large_fields.rs defines no inversion anywhere; the
//     batch's inverse item is record-only.
// ===========================================================================

// ===========================================================================
// GF384 Field byte face: as_bytes / From<&[u8]>
// (upstream large_fields.rs ExtensionField impls, per-limb
// ===========================================================================

/// The little-endian byte j of a GF384 element, per-limb
/// conversion mirror of byte128.
pub open spec fn byte384(v: [u128; 3], j: int) -> u128 {
    if 0 <= j < 48 { byte128(v[j / 16], j % 16) } else { 0 }
}

/// Field::as_bytes for GF384 ([u8; 48] lowered face).
pub exec fn gf384_as_bytes(v: [u128; 3]) -> (out: [u8; 48])
    ensures
        forall |j: int| 0 <= j < 48 ==> #[trigger] out[j] == (byte384(v, j)),
{
    let p0 = gf128_as_bytes(v[0]);
    let p1 = gf128_as_bytes(v[1]);
    let p2 = gf128_as_bytes(v[2]);
    [p0[0], p0[1], p0[2], p0[3], p0[4], p0[5], p0[6], p0[7], p0[8], p0[9], p0[10], p0[11], p0[12], p0[13], p0[14], p0[15], p1[0], p1[1], p1[2], p1[3], p1[4], p1[5], p1[6], p1[7], p1[8], p1[9], p1[10], p1[11], p1[12], p1[13], p1[14], p1[15], p2[0], p2[1], p2[2], p2[3], p2[4], p2[5], p2[6], p2[7], p2[8], p2[9], p2[10], p2[11], p2[12], p2[13], p2[14], p2[15]]
}

/// From<&[u8]> for GF384: the upstream debug-length or partial-block
/// copy re-erects as the requires; per-limb assembly mirrors
/// gf128_from_bytes.
pub exec fn gf384_from_bytes(value: &[u8]) -> (res: [u128; 3])
    requires
        value.len() == 48,
    ensures
        res.len() == 3,
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[0], k) == (value[0 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[1], k) == (value[16 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[2], k) == (value[32 + k] as u128),
{
    let b0: u128 = value[0] as u128;
    let b1: u128 = value[1] as u128;
    let b2: u128 = value[2] as u128;
    let b3: u128 = value[3] as u128;
    let b4: u128 = value[4] as u128;
    let b5: u128 = value[5] as u128;
    let b6: u128 = value[6] as u128;
    let b7: u128 = value[7] as u128;
    let b8: u128 = value[8] as u128;
    let b9: u128 = value[9] as u128;
    let b10: u128 = value[10] as u128;
    let b11: u128 = value[11] as u128;
    let b12: u128 = value[12] as u128;
    let b13: u128 = value[13] as u128;
    let b14: u128 = value[14] as u128;
    let b15: u128 = value[15] as u128;
    let b16: u128 = value[16] as u128;
    let b17: u128 = value[17] as u128;
    let b18: u128 = value[18] as u128;
    let b19: u128 = value[19] as u128;
    let b20: u128 = value[20] as u128;
    let b21: u128 = value[21] as u128;
    let b22: u128 = value[22] as u128;
    let b23: u128 = value[23] as u128;
    let b24: u128 = value[24] as u128;
    let b25: u128 = value[25] as u128;
    let b26: u128 = value[26] as u128;
    let b27: u128 = value[27] as u128;
    let b28: u128 = value[28] as u128;
    let b29: u128 = value[29] as u128;
    let b30: u128 = value[30] as u128;
    let b31: u128 = value[31] as u128;
    let b32: u128 = value[32] as u128;
    let b33: u128 = value[33] as u128;
    let b34: u128 = value[34] as u128;
    let b35: u128 = value[35] as u128;
    let b36: u128 = value[36] as u128;
    let b37: u128 = value[37] as u128;
    let b38: u128 = value[38] as u128;
    let b39: u128 = value[39] as u128;
    let b40: u128 = value[40] as u128;
    let b41: u128 = value[41] as u128;
    let b42: u128 = value[42] as u128;
    let b43: u128 = value[43] as u128;
    let b44: u128 = value[44] as u128;
    let b45: u128 = value[45] as u128;
    let b46: u128 = value[46] as u128;
    let b47: u128 = value[47] as u128;
    let l0: u128 = ((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))
        ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64));
    let l1: u128 = ((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64))
        ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64));
    let l2: u128 = ((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64))
        ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64));
    proof {
        lemma_from_bytes_planes(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15);
        lemma_from_bytes_planes(b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31);
        lemma_from_bytes_planes(b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47);
        assert(byte128(l0, 0) == ((l0 >> 0u64) & 0xFF));
        assert(byte128(l0, 1) == ((l0 >> 8u64) & 0xFF));
        assert(byte128(l0, 2) == ((l0 >> 16u64) & 0xFF));
        assert(byte128(l0, 3) == ((l0 >> 24u64) & 0xFF));
        assert(byte128(l0, 4) == ((l0 >> 32u64) & 0xFF));
        assert(byte128(l0, 5) == ((l0 >> 40u64) & 0xFF));
        assert(byte128(l0, 6) == ((l0 >> 48u64) & 0xFF));
        assert(byte128(l0, 7) == ((l0 >> 56u64) & 0xFF));
        assert(byte128(l0, 8) == ((l0 >> 64u64) & 0xFF));
        assert(byte128(l0, 9) == ((l0 >> 72u64) & 0xFF));
        assert(byte128(l0, 10) == ((l0 >> 80u64) & 0xFF));
        assert(byte128(l0, 11) == ((l0 >> 88u64) & 0xFF));
        assert(byte128(l0, 12) == ((l0 >> 96u64) & 0xFF));
        assert(byte128(l0, 13) == ((l0 >> 104u64) & 0xFF));
        assert(byte128(l0, 14) == ((l0 >> 112u64) & 0xFF));
        assert(byte128(l0, 15) == ((l0 >> 120u64) & 0xFF));
        assert(byte128(l1, 0) == ((l1 >> 0u64) & 0xFF));
        assert(byte128(l1, 1) == ((l1 >> 8u64) & 0xFF));
        assert(byte128(l1, 2) == ((l1 >> 16u64) & 0xFF));
        assert(byte128(l1, 3) == ((l1 >> 24u64) & 0xFF));
        assert(byte128(l1, 4) == ((l1 >> 32u64) & 0xFF));
        assert(byte128(l1, 5) == ((l1 >> 40u64) & 0xFF));
        assert(byte128(l1, 6) == ((l1 >> 48u64) & 0xFF));
        assert(byte128(l1, 7) == ((l1 >> 56u64) & 0xFF));
        assert(byte128(l1, 8) == ((l1 >> 64u64) & 0xFF));
        assert(byte128(l1, 9) == ((l1 >> 72u64) & 0xFF));
        assert(byte128(l1, 10) == ((l1 >> 80u64) & 0xFF));
        assert(byte128(l1, 11) == ((l1 >> 88u64) & 0xFF));
        assert(byte128(l1, 12) == ((l1 >> 96u64) & 0xFF));
        assert(byte128(l1, 13) == ((l1 >> 104u64) & 0xFF));
        assert(byte128(l1, 14) == ((l1 >> 112u64) & 0xFF));
        assert(byte128(l1, 15) == ((l1 >> 120u64) & 0xFF));
        assert(byte128(l2, 0) == ((l2 >> 0u64) & 0xFF));
        assert(byte128(l2, 1) == ((l2 >> 8u64) & 0xFF));
        assert(byte128(l2, 2) == ((l2 >> 16u64) & 0xFF));
        assert(byte128(l2, 3) == ((l2 >> 24u64) & 0xFF));
        assert(byte128(l2, 4) == ((l2 >> 32u64) & 0xFF));
        assert(byte128(l2, 5) == ((l2 >> 40u64) & 0xFF));
        assert(byte128(l2, 6) == ((l2 >> 48u64) & 0xFF));
        assert(byte128(l2, 7) == ((l2 >> 56u64) & 0xFF));
        assert(byte128(l2, 8) == ((l2 >> 64u64) & 0xFF));
        assert(byte128(l2, 9) == ((l2 >> 72u64) & 0xFF));
        assert(byte128(l2, 10) == ((l2 >> 80u64) & 0xFF));
        assert(byte128(l2, 11) == ((l2 >> 88u64) & 0xFF));
        assert(byte128(l2, 12) == ((l2 >> 96u64) & 0xFF));
        assert(byte128(l2, 13) == ((l2 >> 104u64) & 0xFF));
        assert(byte128(l2, 14) == ((l2 >> 112u64) & 0xFF));
        assert(byte128(l2, 15) == ((l2 >> 120u64) & 0xFF));
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l0, k) == (value[0 + k] as u128)
        by {
                if k == 0 {
                    let z: u128 = value[0 as int] as u128;
                    assert(byte128(l0, 0) == z) by (bit_vector)
                        requires
                            z == b0,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 1 {
                    let z: u128 = value[1 as int] as u128;
                    assert(byte128(l0, 1) == z) by (bit_vector)
                        requires
                            z == b1,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 2 {
                    let z: u128 = value[2 as int] as u128;
                    assert(byte128(l0, 2) == z) by (bit_vector)
                        requires
                            z == b2,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 3 {
                    let z: u128 = value[3 as int] as u128;
                    assert(byte128(l0, 3) == z) by (bit_vector)
                        requires
                            z == b3,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 4 {
                    let z: u128 = value[4 as int] as u128;
                    assert(byte128(l0, 4) == z) by (bit_vector)
                        requires
                            z == b4,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 5 {
                    let z: u128 = value[5 as int] as u128;
                    assert(byte128(l0, 5) == z) by (bit_vector)
                        requires
                            z == b5,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 6 {
                    let z: u128 = value[6 as int] as u128;
                    assert(byte128(l0, 6) == z) by (bit_vector)
                        requires
                            z == b6,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 7 {
                    let z: u128 = value[7 as int] as u128;
                    assert(byte128(l0, 7) == z) by (bit_vector)
                        requires
                            z == b7,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 8 {
                    let z: u128 = value[8 as int] as u128;
                    assert(byte128(l0, 8) == z) by (bit_vector)
                        requires
                            z == b8,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 9 {
                    let z: u128 = value[9 as int] as u128;
                    assert(byte128(l0, 9) == z) by (bit_vector)
                        requires
                            z == b9,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 10 {
                    let z: u128 = value[10 as int] as u128;
                    assert(byte128(l0, 10) == z) by (bit_vector)
                        requires
                            z == b10,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 11 {
                    let z: u128 = value[11 as int] as u128;
                    assert(byte128(l0, 11) == z) by (bit_vector)
                        requires
                            z == b11,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 12 {
                    let z: u128 = value[12 as int] as u128;
                    assert(byte128(l0, 12) == z) by (bit_vector)
                        requires
                            z == b12,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 13 {
                    let z: u128 = value[13 as int] as u128;
                    assert(byte128(l0, 13) == z) by (bit_vector)
                        requires
                            z == b13,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 14 {
                    let z: u128 = value[14 as int] as u128;
                    assert(byte128(l0, 14) == z) by (bit_vector)
                        requires
                            z == b14,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else if k == 15 {
                    let z: u128 = value[15 as int] as u128;
                    assert(byte128(l0, 15) == z) by (bit_vector)
                        requires
                            z == b15,
                            l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                            b0 <= 0xFF,
                            b1 <= 0xFF,
                            b2 <= 0xFF,
                            b3 <= 0xFF,
                            b4 <= 0xFF,
                            b5 <= 0xFF,
                            b6 <= 0xFF,
                            b7 <= 0xFF,
                            b8 <= 0xFF,
                            b9 <= 0xFF,
                            b10 <= 0xFF,
                            b11 <= 0xFF,
                            b12 <= 0xFF,
                            b13 <= 0xFF,
                            b14 <= 0xFF,
                            b15 <= 0xFF,
                    ;
                } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l1, k) == (value[16 + k] as u128)
        by {
                if k == 0 {
                    let z: u128 = value[16 as int] as u128;
                    assert(byte128(l1, 0) == z) by (bit_vector)
                        requires
                            z == b16,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 1 {
                    let z: u128 = value[17 as int] as u128;
                    assert(byte128(l1, 1) == z) by (bit_vector)
                        requires
                            z == b17,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 2 {
                    let z: u128 = value[18 as int] as u128;
                    assert(byte128(l1, 2) == z) by (bit_vector)
                        requires
                            z == b18,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 3 {
                    let z: u128 = value[19 as int] as u128;
                    assert(byte128(l1, 3) == z) by (bit_vector)
                        requires
                            z == b19,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 4 {
                    let z: u128 = value[20 as int] as u128;
                    assert(byte128(l1, 4) == z) by (bit_vector)
                        requires
                            z == b20,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 5 {
                    let z: u128 = value[21 as int] as u128;
                    assert(byte128(l1, 5) == z) by (bit_vector)
                        requires
                            z == b21,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 6 {
                    let z: u128 = value[22 as int] as u128;
                    assert(byte128(l1, 6) == z) by (bit_vector)
                        requires
                            z == b22,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 7 {
                    let z: u128 = value[23 as int] as u128;
                    assert(byte128(l1, 7) == z) by (bit_vector)
                        requires
                            z == b23,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 8 {
                    let z: u128 = value[24 as int] as u128;
                    assert(byte128(l1, 8) == z) by (bit_vector)
                        requires
                            z == b24,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 9 {
                    let z: u128 = value[25 as int] as u128;
                    assert(byte128(l1, 9) == z) by (bit_vector)
                        requires
                            z == b25,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 10 {
                    let z: u128 = value[26 as int] as u128;
                    assert(byte128(l1, 10) == z) by (bit_vector)
                        requires
                            z == b26,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 11 {
                    let z: u128 = value[27 as int] as u128;
                    assert(byte128(l1, 11) == z) by (bit_vector)
                        requires
                            z == b27,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 12 {
                    let z: u128 = value[28 as int] as u128;
                    assert(byte128(l1, 12) == z) by (bit_vector)
                        requires
                            z == b28,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 13 {
                    let z: u128 = value[29 as int] as u128;
                    assert(byte128(l1, 13) == z) by (bit_vector)
                        requires
                            z == b29,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 14 {
                    let z: u128 = value[30 as int] as u128;
                    assert(byte128(l1, 14) == z) by (bit_vector)
                        requires
                            z == b30,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else if k == 15 {
                    let z: u128 = value[31 as int] as u128;
                    assert(byte128(l1, 15) == z) by (bit_vector)
                        requires
                            z == b31,
                            l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                            b16 <= 0xFF,
                            b17 <= 0xFF,
                            b18 <= 0xFF,
                            b19 <= 0xFF,
                            b20 <= 0xFF,
                            b21 <= 0xFF,
                            b22 <= 0xFF,
                            b23 <= 0xFF,
                            b24 <= 0xFF,
                            b25 <= 0xFF,
                            b26 <= 0xFF,
                            b27 <= 0xFF,
                            b28 <= 0xFF,
                            b29 <= 0xFF,
                            b30 <= 0xFF,
                            b31 <= 0xFF,
                    ;
                } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l2, k) == (value[32 + k] as u128)
        by {
                if k == 0 {
                    let z: u128 = value[32 as int] as u128;
                    assert(byte128(l2, 0) == z) by (bit_vector)
                        requires
                            z == b32,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 1 {
                    let z: u128 = value[33 as int] as u128;
                    assert(byte128(l2, 1) == z) by (bit_vector)
                        requires
                            z == b33,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 2 {
                    let z: u128 = value[34 as int] as u128;
                    assert(byte128(l2, 2) == z) by (bit_vector)
                        requires
                            z == b34,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 3 {
                    let z: u128 = value[35 as int] as u128;
                    assert(byte128(l2, 3) == z) by (bit_vector)
                        requires
                            z == b35,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 4 {
                    let z: u128 = value[36 as int] as u128;
                    assert(byte128(l2, 4) == z) by (bit_vector)
                        requires
                            z == b36,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 5 {
                    let z: u128 = value[37 as int] as u128;
                    assert(byte128(l2, 5) == z) by (bit_vector)
                        requires
                            z == b37,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 6 {
                    let z: u128 = value[38 as int] as u128;
                    assert(byte128(l2, 6) == z) by (bit_vector)
                        requires
                            z == b38,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 7 {
                    let z: u128 = value[39 as int] as u128;
                    assert(byte128(l2, 7) == z) by (bit_vector)
                        requires
                            z == b39,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 8 {
                    let z: u128 = value[40 as int] as u128;
                    assert(byte128(l2, 8) == z) by (bit_vector)
                        requires
                            z == b40,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 9 {
                    let z: u128 = value[41 as int] as u128;
                    assert(byte128(l2, 9) == z) by (bit_vector)
                        requires
                            z == b41,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 10 {
                    let z: u128 = value[42 as int] as u128;
                    assert(byte128(l2, 10) == z) by (bit_vector)
                        requires
                            z == b42,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 11 {
                    let z: u128 = value[43 as int] as u128;
                    assert(byte128(l2, 11) == z) by (bit_vector)
                        requires
                            z == b43,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 12 {
                    let z: u128 = value[44 as int] as u128;
                    assert(byte128(l2, 12) == z) by (bit_vector)
                        requires
                            z == b44,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 13 {
                    let z: u128 = value[45 as int] as u128;
                    assert(byte128(l2, 13) == z) by (bit_vector)
                        requires
                            z == b45,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 14 {
                    let z: u128 = value[46 as int] as u128;
                    assert(byte128(l2, 14) == z) by (bit_vector)
                        requires
                            z == b46,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else if k == 15 {
                    let z: u128 = value[47 as int] as u128;
                    assert(byte128(l2, 15) == z) by (bit_vector)
                        requires
                            z == b47,
                            l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                            b32 <= 0xFF,
                            b33 <= 0xFF,
                            b34 <= 0xFF,
                            b35 <= 0xFF,
                            b36 <= 0xFF,
                            b37 <= 0xFF,
                            b38 <= 0xFF,
                            b39 <= 0xFF,
                            b40 <= 0xFF,
                            b41 <= 0xFF,
                            b42 <= 0xFF,
                            b43 <= 0xFF,
                            b44 <= 0xFF,
                            b45 <= 0xFF,
                            b46 <= 0xFF,
                            b47 <= 0xFF,
                    ;
                } else { }
        }
    }
    [l0, l1, l2]
}

// ===========================================================================

// ===========================================================================
/// The little-endian byte j of a GF576 element, per-limb
/// conversion mirror of byte128 (wire-form top partial limb;
/// out-of-range j maps to 0).
pub open spec fn byte576(v: [u128; 5], j: int) -> u128 {
    if 0 <= j < 72 {
        if j < 64 { byte128(v[j / 16], j % 16) } else { byte128(v[4], j - 64) }
    } else { 0 }
}

/// Field::as_bytes for GF576 ([u8; 72] lowered face).
pub exec fn gf576_as_bytes(v: [u128; 5]) -> (out: [u8; 72])
    ensures
        forall |j: int| 0 <= j < 72 ==> #[trigger] out[j] == (byte576(v, j)),
{
    let p0 = gf128_as_bytes(v[0]);
    let p1 = gf128_as_bytes(v[1]);
    let p2 = gf128_as_bytes(v[2]);
    let p3 = gf128_as_bytes(v[3]);
    let top: u128 = v[4];
#[verifier::truncate] let q0: u8 = ((v[4] >> 0u64) & 0xFF) as u8;
    #[verifier::truncate] let q1: u8 = ((v[4] >> 8u64) & 0xFF) as u8;
    #[verifier::truncate] let q2: u8 = ((v[4] >> 16u64) & 0xFF) as u8;
    #[verifier::truncate] let q3: u8 = ((v[4] >> 24u64) & 0xFF) as u8;
    #[verifier::truncate] let q4: u8 = ((v[4] >> 32u64) & 0xFF) as u8;
    #[verifier::truncate] let q5: u8 = ((v[4] >> 40u64) & 0xFF) as u8;
    #[verifier::truncate] let q6: u8 = ((v[4] >> 48u64) & 0xFF) as u8;
    #[verifier::truncate] let q7: u8 = ((v[4] >> 56u64) & 0xFF) as u8;
    proof {
        assert(((top >> 0u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((top >> 8u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((top >> 16u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((top >> 24u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((top >> 32u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((top >> 40u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((top >> 48u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert(((top >> 56u64) & 0xFF) <= 0xFFu128) by (bit_vector);
        assert((q0 as u128) == ((top >> 0u64) & 0xFF));
        assert((q1 as u128) == ((top >> 8u64) & 0xFF));
        assert((q2 as u128) == ((top >> 16u64) & 0xFF));
        assert((q3 as u128) == ((top >> 24u64) & 0xFF));
        assert((q4 as u128) == ((top >> 32u64) & 0xFF));
        assert((q5 as u128) == ((top >> 40u64) & 0xFF));
        assert((q6 as u128) == ((top >> 48u64) & 0xFF));
        assert((q7 as u128) == ((top >> 56u64) & 0xFF));
        assert(byte128(top, 0) == ((top >> 0u64) & 0xFF));
        assert(byte128(top, 1) == ((top >> 8u64) & 0xFF));
        assert(byte128(top, 2) == ((top >> 16u64) & 0xFF));
        assert(byte128(top, 3) == ((top >> 24u64) & 0xFF));
        assert(byte128(top, 4) == ((top >> 32u64) & 0xFF));
        assert(byte128(top, 5) == ((top >> 40u64) & 0xFF));
        assert(byte128(top, 6) == ((top >> 48u64) & 0xFF));
        assert(byte128(top, 7) == ((top >> 56u64) & 0xFF));
    }
    [p0[0], p0[1], p0[2], p0[3], p0[4], p0[5], p0[6], p0[7], p0[8], p0[9], p0[10], p0[11], p0[12], p0[13], p0[14], p0[15], p1[0], p1[1], p1[2], p1[3], p1[4], p1[5], p1[6], p1[7], p1[8], p1[9], p1[10], p1[11], p1[12], p1[13], p1[14], p1[15], p2[0], p2[1], p2[2], p2[3], p2[4], p2[5], p2[6], p2[7], p2[8], p2[9], p2[10], p2[11], p2[12], p2[13], p2[14], p2[15], p3[0], p3[1], p3[2], p3[3], p3[4], p3[5], p3[6], p3[7], p3[8], p3[9], p3[10], p3[11], p3[12], p3[13], p3[14], p3[15], q0, q1, q2, q3, q4, q5, q6, q7]
}

/// From<&[u8]> for GF576: the upstream block copy re-erects as
/// the requires; the ensures are stated per limb byte plane (the
/// division-free shape; symbolic-index case splits ride the per-
/// case bit_vector bridges below, #FA3-4 lesson).
pub exec fn gf576_from_bytes(value: &[u8]) -> (res: [u128; 5])
    requires
        value.len() == 72,
    ensures
        res.len() == 5,
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[0], k) == (value[0 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[1], k) == (value[16 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[2], k) == (value[32 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[3], k) == (value[48 + k] as u128),
        forall |k: int| 0 <= k < 8 ==> #[trigger] byte128(res[4], k) == (value[64 + k] as u128),
        (res[4] >> 64) == 0,
{
    let b0: u128 = value[0] as u128;
    let b1: u128 = value[1] as u128;
    let b2: u128 = value[2] as u128;
    let b3: u128 = value[3] as u128;
    let b4: u128 = value[4] as u128;
    let b5: u128 = value[5] as u128;
    let b6: u128 = value[6] as u128;
    let b7: u128 = value[7] as u128;
    let b8: u128 = value[8] as u128;
    let b9: u128 = value[9] as u128;
    let b10: u128 = value[10] as u128;
    let b11: u128 = value[11] as u128;
    let b12: u128 = value[12] as u128;
    let b13: u128 = value[13] as u128;
    let b14: u128 = value[14] as u128;
    let b15: u128 = value[15] as u128;
    let b16: u128 = value[16] as u128;
    let b17: u128 = value[17] as u128;
    let b18: u128 = value[18] as u128;
    let b19: u128 = value[19] as u128;
    let b20: u128 = value[20] as u128;
    let b21: u128 = value[21] as u128;
    let b22: u128 = value[22] as u128;
    let b23: u128 = value[23] as u128;
    let b24: u128 = value[24] as u128;
    let b25: u128 = value[25] as u128;
    let b26: u128 = value[26] as u128;
    let b27: u128 = value[27] as u128;
    let b28: u128 = value[28] as u128;
    let b29: u128 = value[29] as u128;
    let b30: u128 = value[30] as u128;
    let b31: u128 = value[31] as u128;
    let b32: u128 = value[32] as u128;
    let b33: u128 = value[33] as u128;
    let b34: u128 = value[34] as u128;
    let b35: u128 = value[35] as u128;
    let b36: u128 = value[36] as u128;
    let b37: u128 = value[37] as u128;
    let b38: u128 = value[38] as u128;
    let b39: u128 = value[39] as u128;
    let b40: u128 = value[40] as u128;
    let b41: u128 = value[41] as u128;
    let b42: u128 = value[42] as u128;
    let b43: u128 = value[43] as u128;
    let b44: u128 = value[44] as u128;
    let b45: u128 = value[45] as u128;
    let b46: u128 = value[46] as u128;
    let b47: u128 = value[47] as u128;
    let b48: u128 = value[48] as u128;
    let b49: u128 = value[49] as u128;
    let b50: u128 = value[50] as u128;
    let b51: u128 = value[51] as u128;
    let b52: u128 = value[52] as u128;
    let b53: u128 = value[53] as u128;
    let b54: u128 = value[54] as u128;
    let b55: u128 = value[55] as u128;
    let b56: u128 = value[56] as u128;
    let b57: u128 = value[57] as u128;
    let b58: u128 = value[58] as u128;
    let b59: u128 = value[59] as u128;
    let b60: u128 = value[60] as u128;
    let b61: u128 = value[61] as u128;
    let b62: u128 = value[62] as u128;
    let b63: u128 = value[63] as u128;
    let b64: u128 = value[64] as u128;
    let b65: u128 = value[65] as u128;
    let b66: u128 = value[66] as u128;
    let b67: u128 = value[67] as u128;
    let b68: u128 = value[68] as u128;
    let b69: u128 = value[69] as u128;
    let b70: u128 = value[70] as u128;
    let b71: u128 = value[71] as u128;
    let l0: u128 = ((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))
        ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64));
    let l1: u128 = ((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64))
        ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64));
    let l2: u128 = ((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64))
        ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64));
    let l3: u128 = ((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64))
        ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64));
    let l4: u128 = (b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64);
    proof {
        lemma_from_bytes_planes(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15);
        lemma_from_bytes_planes(b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31);
        lemma_from_bytes_planes(b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47);
        lemma_from_bytes_planes(b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63);
        assert(l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)));
        assert((l4 >> 64) == 0) by (bit_vector)
            requires
                l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                b64 <= 0xFF,
                b65 <= 0xFF,
                b66 <= 0xFF,
                b67 <= 0xFF,
                b68 <= 0xFF,
                b69 <= 0xFF,
                b70 <= 0xFF,
                b71 <= 0xFF,
        ;
        assert(byte128(l0, 0) == ((l0 >> 0u64) & 0xFF));
        assert(byte128(l0, 1) == ((l0 >> 8u64) & 0xFF));
        assert(byte128(l0, 2) == ((l0 >> 16u64) & 0xFF));
        assert(byte128(l0, 3) == ((l0 >> 24u64) & 0xFF));
        assert(byte128(l0, 4) == ((l0 >> 32u64) & 0xFF));
        assert(byte128(l0, 5) == ((l0 >> 40u64) & 0xFF));
        assert(byte128(l0, 6) == ((l0 >> 48u64) & 0xFF));
        assert(byte128(l0, 7) == ((l0 >> 56u64) & 0xFF));
        assert(byte128(l0, 8) == ((l0 >> 64u64) & 0xFF));
        assert(byte128(l0, 9) == ((l0 >> 72u64) & 0xFF));
        assert(byte128(l0, 10) == ((l0 >> 80u64) & 0xFF));
        assert(byte128(l0, 11) == ((l0 >> 88u64) & 0xFF));
        assert(byte128(l0, 12) == ((l0 >> 96u64) & 0xFF));
        assert(byte128(l0, 13) == ((l0 >> 104u64) & 0xFF));
        assert(byte128(l0, 14) == ((l0 >> 112u64) & 0xFF));
        assert(byte128(l0, 15) == ((l0 >> 120u64) & 0xFF));
        assert(byte128(l1, 0) == ((l1 >> 0u64) & 0xFF));
        assert(byte128(l1, 1) == ((l1 >> 8u64) & 0xFF));
        assert(byte128(l1, 2) == ((l1 >> 16u64) & 0xFF));
        assert(byte128(l1, 3) == ((l1 >> 24u64) & 0xFF));
        assert(byte128(l1, 4) == ((l1 >> 32u64) & 0xFF));
        assert(byte128(l1, 5) == ((l1 >> 40u64) & 0xFF));
        assert(byte128(l1, 6) == ((l1 >> 48u64) & 0xFF));
        assert(byte128(l1, 7) == ((l1 >> 56u64) & 0xFF));
        assert(byte128(l1, 8) == ((l1 >> 64u64) & 0xFF));
        assert(byte128(l1, 9) == ((l1 >> 72u64) & 0xFF));
        assert(byte128(l1, 10) == ((l1 >> 80u64) & 0xFF));
        assert(byte128(l1, 11) == ((l1 >> 88u64) & 0xFF));
        assert(byte128(l1, 12) == ((l1 >> 96u64) & 0xFF));
        assert(byte128(l1, 13) == ((l1 >> 104u64) & 0xFF));
        assert(byte128(l1, 14) == ((l1 >> 112u64) & 0xFF));
        assert(byte128(l1, 15) == ((l1 >> 120u64) & 0xFF));
        assert(byte128(l2, 0) == ((l2 >> 0u64) & 0xFF));
        assert(byte128(l2, 1) == ((l2 >> 8u64) & 0xFF));
        assert(byte128(l2, 2) == ((l2 >> 16u64) & 0xFF));
        assert(byte128(l2, 3) == ((l2 >> 24u64) & 0xFF));
        assert(byte128(l2, 4) == ((l2 >> 32u64) & 0xFF));
        assert(byte128(l2, 5) == ((l2 >> 40u64) & 0xFF));
        assert(byte128(l2, 6) == ((l2 >> 48u64) & 0xFF));
        assert(byte128(l2, 7) == ((l2 >> 56u64) & 0xFF));
        assert(byte128(l2, 8) == ((l2 >> 64u64) & 0xFF));
        assert(byte128(l2, 9) == ((l2 >> 72u64) & 0xFF));
        assert(byte128(l2, 10) == ((l2 >> 80u64) & 0xFF));
        assert(byte128(l2, 11) == ((l2 >> 88u64) & 0xFF));
        assert(byte128(l2, 12) == ((l2 >> 96u64) & 0xFF));
        assert(byte128(l2, 13) == ((l2 >> 104u64) & 0xFF));
        assert(byte128(l2, 14) == ((l2 >> 112u64) & 0xFF));
        assert(byte128(l2, 15) == ((l2 >> 120u64) & 0xFF));
        assert(byte128(l3, 0) == ((l3 >> 0u64) & 0xFF));
        assert(byte128(l3, 1) == ((l3 >> 8u64) & 0xFF));
        assert(byte128(l3, 2) == ((l3 >> 16u64) & 0xFF));
        assert(byte128(l3, 3) == ((l3 >> 24u64) & 0xFF));
        assert(byte128(l3, 4) == ((l3 >> 32u64) & 0xFF));
        assert(byte128(l3, 5) == ((l3 >> 40u64) & 0xFF));
        assert(byte128(l3, 6) == ((l3 >> 48u64) & 0xFF));
        assert(byte128(l3, 7) == ((l3 >> 56u64) & 0xFF));
        assert(byte128(l3, 8) == ((l3 >> 64u64) & 0xFF));
        assert(byte128(l3, 9) == ((l3 >> 72u64) & 0xFF));
        assert(byte128(l3, 10) == ((l3 >> 80u64) & 0xFF));
        assert(byte128(l3, 11) == ((l3 >> 88u64) & 0xFF));
        assert(byte128(l3, 12) == ((l3 >> 96u64) & 0xFF));
        assert(byte128(l3, 13) == ((l3 >> 104u64) & 0xFF));
        assert(byte128(l3, 14) == ((l3 >> 112u64) & 0xFF));
        assert(byte128(l3, 15) == ((l3 >> 120u64) & 0xFF));
        assert(byte128(l4, 0) == ((l4 >> 0u64) & 0xFF));
        assert(byte128(l4, 1) == ((l4 >> 8u64) & 0xFF));
        assert(byte128(l4, 2) == ((l4 >> 16u64) & 0xFF));
        assert(byte128(l4, 3) == ((l4 >> 24u64) & 0xFF));
        assert(byte128(l4, 4) == ((l4 >> 32u64) & 0xFF));
        assert(byte128(l4, 5) == ((l4 >> 40u64) & 0xFF));
        assert(byte128(l4, 6) == ((l4 >> 48u64) & 0xFF));
        assert(byte128(l4, 7) == ((l4 >> 56u64) & 0xFF));
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l0, k) == (value[0 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[0 as int] as u128;
                assert(l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))));
                assert(z == b0);
                assert(byte128(l0, 0) == z) by (bit_vector)
                    requires
                        z == b0,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[1 as int] as u128;
                assert(byte128(l0, 1) == z) by (bit_vector)
                    requires
                        z == b1,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[2 as int] as u128;
                assert(byte128(l0, 2) == z) by (bit_vector)
                    requires
                        z == b2,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[3 as int] as u128;
                assert(byte128(l0, 3) == z) by (bit_vector)
                    requires
                        z == b3,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[4 as int] as u128;
                assert(byte128(l0, 4) == z) by (bit_vector)
                    requires
                        z == b4,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[5 as int] as u128;
                assert(byte128(l0, 5) == z) by (bit_vector)
                    requires
                        z == b5,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[6 as int] as u128;
                assert(byte128(l0, 6) == z) by (bit_vector)
                    requires
                        z == b6,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[7 as int] as u128;
                assert(byte128(l0, 7) == z) by (bit_vector)
                    requires
                        z == b7,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[8 as int] as u128;
                assert(byte128(l0, 8) == z) by (bit_vector)
                    requires
                        z == b8,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[9 as int] as u128;
                assert(byte128(l0, 9) == z) by (bit_vector)
                    requires
                        z == b9,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[10 as int] as u128;
                assert(byte128(l0, 10) == z) by (bit_vector)
                    requires
                        z == b10,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[11 as int] as u128;
                assert(byte128(l0, 11) == z) by (bit_vector)
                    requires
                        z == b11,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[12 as int] as u128;
                assert(byte128(l0, 12) == z) by (bit_vector)
                    requires
                        z == b12,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[13 as int] as u128;
                assert(byte128(l0, 13) == z) by (bit_vector)
                    requires
                        z == b13,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[14 as int] as u128;
                assert(byte128(l0, 14) == z) by (bit_vector)
                    requires
                        z == b14,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[15 as int] as u128;
                assert(byte128(l0, 15) == z) by (bit_vector)
                    requires
                        z == b15,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l1, k) == (value[16 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[16 as int] as u128;
                assert(byte128(l1, 0) == z) by (bit_vector)
                    requires
                        z == b16,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[17 as int] as u128;
                assert(byte128(l1, 1) == z) by (bit_vector)
                    requires
                        z == b17,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[18 as int] as u128;
                assert(byte128(l1, 2) == z) by (bit_vector)
                    requires
                        z == b18,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[19 as int] as u128;
                assert(byte128(l1, 3) == z) by (bit_vector)
                    requires
                        z == b19,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[20 as int] as u128;
                assert(byte128(l1, 4) == z) by (bit_vector)
                    requires
                        z == b20,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[21 as int] as u128;
                assert(byte128(l1, 5) == z) by (bit_vector)
                    requires
                        z == b21,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[22 as int] as u128;
                assert(byte128(l1, 6) == z) by (bit_vector)
                    requires
                        z == b22,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[23 as int] as u128;
                assert(byte128(l1, 7) == z) by (bit_vector)
                    requires
                        z == b23,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[24 as int] as u128;
                assert(byte128(l1, 8) == z) by (bit_vector)
                    requires
                        z == b24,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[25 as int] as u128;
                assert(byte128(l1, 9) == z) by (bit_vector)
                    requires
                        z == b25,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[26 as int] as u128;
                assert(byte128(l1, 10) == z) by (bit_vector)
                    requires
                        z == b26,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[27 as int] as u128;
                assert(byte128(l1, 11) == z) by (bit_vector)
                    requires
                        z == b27,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[28 as int] as u128;
                assert(byte128(l1, 12) == z) by (bit_vector)
                    requires
                        z == b28,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[29 as int] as u128;
                assert(byte128(l1, 13) == z) by (bit_vector)
                    requires
                        z == b29,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[30 as int] as u128;
                assert(byte128(l1, 14) == z) by (bit_vector)
                    requires
                        z == b30,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[31 as int] as u128;
                assert(byte128(l1, 15) == z) by (bit_vector)
                    requires
                        z == b31,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l2, k) == (value[32 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[32 as int] as u128;
                assert(byte128(l2, 0) == z) by (bit_vector)
                    requires
                        z == b32,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[33 as int] as u128;
                assert(byte128(l2, 1) == z) by (bit_vector)
                    requires
                        z == b33,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[34 as int] as u128;
                assert(byte128(l2, 2) == z) by (bit_vector)
                    requires
                        z == b34,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[35 as int] as u128;
                assert(byte128(l2, 3) == z) by (bit_vector)
                    requires
                        z == b35,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[36 as int] as u128;
                assert(byte128(l2, 4) == z) by (bit_vector)
                    requires
                        z == b36,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[37 as int] as u128;
                assert(byte128(l2, 5) == z) by (bit_vector)
                    requires
                        z == b37,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[38 as int] as u128;
                assert(byte128(l2, 6) == z) by (bit_vector)
                    requires
                        z == b38,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[39 as int] as u128;
                assert(byte128(l2, 7) == z) by (bit_vector)
                    requires
                        z == b39,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[40 as int] as u128;
                assert(byte128(l2, 8) == z) by (bit_vector)
                    requires
                        z == b40,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[41 as int] as u128;
                assert(byte128(l2, 9) == z) by (bit_vector)
                    requires
                        z == b41,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[42 as int] as u128;
                assert(byte128(l2, 10) == z) by (bit_vector)
                    requires
                        z == b42,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[43 as int] as u128;
                assert(byte128(l2, 11) == z) by (bit_vector)
                    requires
                        z == b43,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[44 as int] as u128;
                assert(byte128(l2, 12) == z) by (bit_vector)
                    requires
                        z == b44,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[45 as int] as u128;
                assert(byte128(l2, 13) == z) by (bit_vector)
                    requires
                        z == b45,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[46 as int] as u128;
                assert(byte128(l2, 14) == z) by (bit_vector)
                    requires
                        z == b46,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[47 as int] as u128;
                assert(byte128(l2, 15) == z) by (bit_vector)
                    requires
                        z == b47,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l3, k) == (value[48 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[48 as int] as u128;
                assert(byte128(l3, 0) == z) by (bit_vector)
                    requires
                        z == b48,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[49 as int] as u128;
                assert(byte128(l3, 1) == z) by (bit_vector)
                    requires
                        z == b49,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[50 as int] as u128;
                assert(byte128(l3, 2) == z) by (bit_vector)
                    requires
                        z == b50,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[51 as int] as u128;
                assert(byte128(l3, 3) == z) by (bit_vector)
                    requires
                        z == b51,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[52 as int] as u128;
                assert(byte128(l3, 4) == z) by (bit_vector)
                    requires
                        z == b52,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[53 as int] as u128;
                assert(byte128(l3, 5) == z) by (bit_vector)
                    requires
                        z == b53,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[54 as int] as u128;
                assert(byte128(l3, 6) == z) by (bit_vector)
                    requires
                        z == b54,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[55 as int] as u128;
                assert(byte128(l3, 7) == z) by (bit_vector)
                    requires
                        z == b55,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[56 as int] as u128;
                assert(byte128(l3, 8) == z) by (bit_vector)
                    requires
                        z == b56,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[57 as int] as u128;
                assert(byte128(l3, 9) == z) by (bit_vector)
                    requires
                        z == b57,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[58 as int] as u128;
                assert(byte128(l3, 10) == z) by (bit_vector)
                    requires
                        z == b58,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[59 as int] as u128;
                assert(byte128(l3, 11) == z) by (bit_vector)
                    requires
                        z == b59,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[60 as int] as u128;
                assert(byte128(l3, 12) == z) by (bit_vector)
                    requires
                        z == b60,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[61 as int] as u128;
                assert(byte128(l3, 13) == z) by (bit_vector)
                    requires
                        z == b61,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[62 as int] as u128;
                assert(byte128(l3, 14) == z) by (bit_vector)
                    requires
                        z == b62,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[63 as int] as u128;
                assert(byte128(l3, 15) == z) by (bit_vector)
                    requires
                        z == b63,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 8 implies
            #[trigger] byte128(l4, k) == (value[64 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[64 as int] as u128;
                assert(byte128(l4, 0) == z) by (bit_vector)
                    requires
                        z == b64,
                        l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[65 as int] as u128;
                assert(byte128(l4, 1) == z) by (bit_vector)
                    requires
                        z == b65,
                        l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[66 as int] as u128;
                assert(byte128(l4, 2) == z) by (bit_vector)
                    requires
                        z == b66,
                        l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[67 as int] as u128;
                assert(byte128(l4, 3) == z) by (bit_vector)
                    requires
                        z == b67,
                        l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[68 as int] as u128;
                assert(byte128(l4, 4) == z) by (bit_vector)
                    requires
                        z == b68,
                        l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[69 as int] as u128;
                assert(byte128(l4, 5) == z) by (bit_vector)
                    requires
                        z == b69,
                        l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[70 as int] as u128;
                assert(byte128(l4, 6) == z) by (bit_vector)
                    requires
                        z == b70,
                        l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[71 as int] as u128;
                assert(byte128(l4, 7) == z) by (bit_vector)
                    requires
                        z == b71,
                        l4 == ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                ;
            } else { }
        }
    }
    [l0, l1, l2, l3, l4]
}

// ===========================================================================
/// The little-endian byte j of a GF768 element, per-limb
/// conversion mirror of byte128 (out-of-range j maps to 0).
pub open spec fn byte768(v: [u128; 6], j: int) -> u128 {
    if 0 <= j < 96 { byte128(v[j / 16], j % 16) } else { 0 }
}

/// Field::as_bytes for GF768 ([u8; 96] lowered face).
pub exec fn gf768_as_bytes(v: [u128; 6]) -> (out: [u8; 96])
    ensures
        forall |j: int| 0 <= j < 96 ==> #[trigger] out[j] == (byte768(v, j)),
{
    let p0 = gf128_as_bytes(v[0]);
    let p1 = gf128_as_bytes(v[1]);
    let p2 = gf128_as_bytes(v[2]);
    let p3 = gf128_as_bytes(v[3]);
    let p4 = gf128_as_bytes(v[4]);
    let p5 = gf128_as_bytes(v[5]);
    [p0[0], p0[1], p0[2], p0[3], p0[4], p0[5], p0[6], p0[7], p0[8], p0[9], p0[10], p0[11], p0[12], p0[13], p0[14], p0[15], p1[0], p1[1], p1[2], p1[3], p1[4], p1[5], p1[6], p1[7], p1[8], p1[9], p1[10], p1[11], p1[12], p1[13], p1[14], p1[15], p2[0], p2[1], p2[2], p2[3], p2[4], p2[5], p2[6], p2[7], p2[8], p2[9], p2[10], p2[11], p2[12], p2[13], p2[14], p2[15], p3[0], p3[1], p3[2], p3[3], p3[4], p3[5], p3[6], p3[7], p3[8], p3[9], p3[10], p3[11], p3[12], p3[13], p3[14], p3[15], p4[0], p4[1], p4[2], p4[3], p4[4], p4[5], p4[6], p4[7], p4[8], p4[9], p4[10], p4[11], p4[12], p4[13], p4[14], p4[15], p5[0], p5[1], p5[2], p5[3], p5[4], p5[5], p5[6], p5[7], p5[8], p5[9], p5[10], p5[11], p5[12], p5[13], p5[14], p5[15]]
}

/// From<&[u8]> for GF768: the upstream block copy re-erects as
/// the requires; the ensures are stated per limb byte plane (the
/// division-free shape; symbolic-index case splits ride the per-
/// case bit_vector bridges below, #FA3-4 lesson).
pub exec fn gf768_from_bytes(value: &[u8]) -> (res: [u128; 6])
    requires
        value.len() == 96,
    ensures
        res.len() == 6,
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[0], k) == (value[0 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[1], k) == (value[16 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[2], k) == (value[32 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[3], k) == (value[48 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[4], k) == (value[64 + k] as u128),
        forall |k: int| 0 <= k < 16 ==> #[trigger] byte128(res[5], k) == (value[80 + k] as u128),
{
    let b0: u128 = value[0] as u128;
    let b1: u128 = value[1] as u128;
    let b2: u128 = value[2] as u128;
    let b3: u128 = value[3] as u128;
    let b4: u128 = value[4] as u128;
    let b5: u128 = value[5] as u128;
    let b6: u128 = value[6] as u128;
    let b7: u128 = value[7] as u128;
    let b8: u128 = value[8] as u128;
    let b9: u128 = value[9] as u128;
    let b10: u128 = value[10] as u128;
    let b11: u128 = value[11] as u128;
    let b12: u128 = value[12] as u128;
    let b13: u128 = value[13] as u128;
    let b14: u128 = value[14] as u128;
    let b15: u128 = value[15] as u128;
    let b16: u128 = value[16] as u128;
    let b17: u128 = value[17] as u128;
    let b18: u128 = value[18] as u128;
    let b19: u128 = value[19] as u128;
    let b20: u128 = value[20] as u128;
    let b21: u128 = value[21] as u128;
    let b22: u128 = value[22] as u128;
    let b23: u128 = value[23] as u128;
    let b24: u128 = value[24] as u128;
    let b25: u128 = value[25] as u128;
    let b26: u128 = value[26] as u128;
    let b27: u128 = value[27] as u128;
    let b28: u128 = value[28] as u128;
    let b29: u128 = value[29] as u128;
    let b30: u128 = value[30] as u128;
    let b31: u128 = value[31] as u128;
    let b32: u128 = value[32] as u128;
    let b33: u128 = value[33] as u128;
    let b34: u128 = value[34] as u128;
    let b35: u128 = value[35] as u128;
    let b36: u128 = value[36] as u128;
    let b37: u128 = value[37] as u128;
    let b38: u128 = value[38] as u128;
    let b39: u128 = value[39] as u128;
    let b40: u128 = value[40] as u128;
    let b41: u128 = value[41] as u128;
    let b42: u128 = value[42] as u128;
    let b43: u128 = value[43] as u128;
    let b44: u128 = value[44] as u128;
    let b45: u128 = value[45] as u128;
    let b46: u128 = value[46] as u128;
    let b47: u128 = value[47] as u128;
    let b48: u128 = value[48] as u128;
    let b49: u128 = value[49] as u128;
    let b50: u128 = value[50] as u128;
    let b51: u128 = value[51] as u128;
    let b52: u128 = value[52] as u128;
    let b53: u128 = value[53] as u128;
    let b54: u128 = value[54] as u128;
    let b55: u128 = value[55] as u128;
    let b56: u128 = value[56] as u128;
    let b57: u128 = value[57] as u128;
    let b58: u128 = value[58] as u128;
    let b59: u128 = value[59] as u128;
    let b60: u128 = value[60] as u128;
    let b61: u128 = value[61] as u128;
    let b62: u128 = value[62] as u128;
    let b63: u128 = value[63] as u128;
    let b64: u128 = value[64] as u128;
    let b65: u128 = value[65] as u128;
    let b66: u128 = value[66] as u128;
    let b67: u128 = value[67] as u128;
    let b68: u128 = value[68] as u128;
    let b69: u128 = value[69] as u128;
    let b70: u128 = value[70] as u128;
    let b71: u128 = value[71] as u128;
    let b72: u128 = value[72] as u128;
    let b73: u128 = value[73] as u128;
    let b74: u128 = value[74] as u128;
    let b75: u128 = value[75] as u128;
    let b76: u128 = value[76] as u128;
    let b77: u128 = value[77] as u128;
    let b78: u128 = value[78] as u128;
    let b79: u128 = value[79] as u128;
    let b80: u128 = value[80] as u128;
    let b81: u128 = value[81] as u128;
    let b82: u128 = value[82] as u128;
    let b83: u128 = value[83] as u128;
    let b84: u128 = value[84] as u128;
    let b85: u128 = value[85] as u128;
    let b86: u128 = value[86] as u128;
    let b87: u128 = value[87] as u128;
    let b88: u128 = value[88] as u128;
    let b89: u128 = value[89] as u128;
    let b90: u128 = value[90] as u128;
    let b91: u128 = value[91] as u128;
    let b92: u128 = value[92] as u128;
    let b93: u128 = value[93] as u128;
    let b94: u128 = value[94] as u128;
    let b95: u128 = value[95] as u128;
    let l0: u128 = ((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))
        ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64));
    let l1: u128 = ((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64))
        ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64));
    let l2: u128 = ((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64))
        ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64));
    let l3: u128 = ((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64))
        ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64));
    let l4: u128 = ((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64))
        ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64));
    let l5: u128 = ((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64))
        ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64));
    proof {
        lemma_from_bytes_planes(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15);
        lemma_from_bytes_planes(b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31);
        lemma_from_bytes_planes(b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47);
        lemma_from_bytes_planes(b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63);
        lemma_from_bytes_planes(b64, b65, b66, b67, b68, b69, b70, b71, b72, b73, b74, b75, b76, b77, b78, b79);
        lemma_from_bytes_planes(b80, b81, b82, b83, b84, b85, b86, b87, b88, b89, b90, b91, b92, b93, b94, b95);
        assert(byte128(l0, 0) == ((l0 >> 0u64) & 0xFF));
        assert(byte128(l0, 1) == ((l0 >> 8u64) & 0xFF));
        assert(byte128(l0, 2) == ((l0 >> 16u64) & 0xFF));
        assert(byte128(l0, 3) == ((l0 >> 24u64) & 0xFF));
        assert(byte128(l0, 4) == ((l0 >> 32u64) & 0xFF));
        assert(byte128(l0, 5) == ((l0 >> 40u64) & 0xFF));
        assert(byte128(l0, 6) == ((l0 >> 48u64) & 0xFF));
        assert(byte128(l0, 7) == ((l0 >> 56u64) & 0xFF));
        assert(byte128(l0, 8) == ((l0 >> 64u64) & 0xFF));
        assert(byte128(l0, 9) == ((l0 >> 72u64) & 0xFF));
        assert(byte128(l0, 10) == ((l0 >> 80u64) & 0xFF));
        assert(byte128(l0, 11) == ((l0 >> 88u64) & 0xFF));
        assert(byte128(l0, 12) == ((l0 >> 96u64) & 0xFF));
        assert(byte128(l0, 13) == ((l0 >> 104u64) & 0xFF));
        assert(byte128(l0, 14) == ((l0 >> 112u64) & 0xFF));
        assert(byte128(l0, 15) == ((l0 >> 120u64) & 0xFF));
        assert(byte128(l1, 0) == ((l1 >> 0u64) & 0xFF));
        assert(byte128(l1, 1) == ((l1 >> 8u64) & 0xFF));
        assert(byte128(l1, 2) == ((l1 >> 16u64) & 0xFF));
        assert(byte128(l1, 3) == ((l1 >> 24u64) & 0xFF));
        assert(byte128(l1, 4) == ((l1 >> 32u64) & 0xFF));
        assert(byte128(l1, 5) == ((l1 >> 40u64) & 0xFF));
        assert(byte128(l1, 6) == ((l1 >> 48u64) & 0xFF));
        assert(byte128(l1, 7) == ((l1 >> 56u64) & 0xFF));
        assert(byte128(l1, 8) == ((l1 >> 64u64) & 0xFF));
        assert(byte128(l1, 9) == ((l1 >> 72u64) & 0xFF));
        assert(byte128(l1, 10) == ((l1 >> 80u64) & 0xFF));
        assert(byte128(l1, 11) == ((l1 >> 88u64) & 0xFF));
        assert(byte128(l1, 12) == ((l1 >> 96u64) & 0xFF));
        assert(byte128(l1, 13) == ((l1 >> 104u64) & 0xFF));
        assert(byte128(l1, 14) == ((l1 >> 112u64) & 0xFF));
        assert(byte128(l1, 15) == ((l1 >> 120u64) & 0xFF));
        assert(byte128(l2, 0) == ((l2 >> 0u64) & 0xFF));
        assert(byte128(l2, 1) == ((l2 >> 8u64) & 0xFF));
        assert(byte128(l2, 2) == ((l2 >> 16u64) & 0xFF));
        assert(byte128(l2, 3) == ((l2 >> 24u64) & 0xFF));
        assert(byte128(l2, 4) == ((l2 >> 32u64) & 0xFF));
        assert(byte128(l2, 5) == ((l2 >> 40u64) & 0xFF));
        assert(byte128(l2, 6) == ((l2 >> 48u64) & 0xFF));
        assert(byte128(l2, 7) == ((l2 >> 56u64) & 0xFF));
        assert(byte128(l2, 8) == ((l2 >> 64u64) & 0xFF));
        assert(byte128(l2, 9) == ((l2 >> 72u64) & 0xFF));
        assert(byte128(l2, 10) == ((l2 >> 80u64) & 0xFF));
        assert(byte128(l2, 11) == ((l2 >> 88u64) & 0xFF));
        assert(byte128(l2, 12) == ((l2 >> 96u64) & 0xFF));
        assert(byte128(l2, 13) == ((l2 >> 104u64) & 0xFF));
        assert(byte128(l2, 14) == ((l2 >> 112u64) & 0xFF));
        assert(byte128(l2, 15) == ((l2 >> 120u64) & 0xFF));
        assert(byte128(l3, 0) == ((l3 >> 0u64) & 0xFF));
        assert(byte128(l3, 1) == ((l3 >> 8u64) & 0xFF));
        assert(byte128(l3, 2) == ((l3 >> 16u64) & 0xFF));
        assert(byte128(l3, 3) == ((l3 >> 24u64) & 0xFF));
        assert(byte128(l3, 4) == ((l3 >> 32u64) & 0xFF));
        assert(byte128(l3, 5) == ((l3 >> 40u64) & 0xFF));
        assert(byte128(l3, 6) == ((l3 >> 48u64) & 0xFF));
        assert(byte128(l3, 7) == ((l3 >> 56u64) & 0xFF));
        assert(byte128(l3, 8) == ((l3 >> 64u64) & 0xFF));
        assert(byte128(l3, 9) == ((l3 >> 72u64) & 0xFF));
        assert(byte128(l3, 10) == ((l3 >> 80u64) & 0xFF));
        assert(byte128(l3, 11) == ((l3 >> 88u64) & 0xFF));
        assert(byte128(l3, 12) == ((l3 >> 96u64) & 0xFF));
        assert(byte128(l3, 13) == ((l3 >> 104u64) & 0xFF));
        assert(byte128(l3, 14) == ((l3 >> 112u64) & 0xFF));
        assert(byte128(l3, 15) == ((l3 >> 120u64) & 0xFF));
        assert(byte128(l4, 0) == ((l4 >> 0u64) & 0xFF));
        assert(byte128(l4, 1) == ((l4 >> 8u64) & 0xFF));
        assert(byte128(l4, 2) == ((l4 >> 16u64) & 0xFF));
        assert(byte128(l4, 3) == ((l4 >> 24u64) & 0xFF));
        assert(byte128(l4, 4) == ((l4 >> 32u64) & 0xFF));
        assert(byte128(l4, 5) == ((l4 >> 40u64) & 0xFF));
        assert(byte128(l4, 6) == ((l4 >> 48u64) & 0xFF));
        assert(byte128(l4, 7) == ((l4 >> 56u64) & 0xFF));
        assert(byte128(l4, 8) == ((l4 >> 64u64) & 0xFF));
        assert(byte128(l4, 9) == ((l4 >> 72u64) & 0xFF));
        assert(byte128(l4, 10) == ((l4 >> 80u64) & 0xFF));
        assert(byte128(l4, 11) == ((l4 >> 88u64) & 0xFF));
        assert(byte128(l4, 12) == ((l4 >> 96u64) & 0xFF));
        assert(byte128(l4, 13) == ((l4 >> 104u64) & 0xFF));
        assert(byte128(l4, 14) == ((l4 >> 112u64) & 0xFF));
        assert(byte128(l4, 15) == ((l4 >> 120u64) & 0xFF));
        assert(byte128(l5, 0) == ((l5 >> 0u64) & 0xFF));
        assert(byte128(l5, 1) == ((l5 >> 8u64) & 0xFF));
        assert(byte128(l5, 2) == ((l5 >> 16u64) & 0xFF));
        assert(byte128(l5, 3) == ((l5 >> 24u64) & 0xFF));
        assert(byte128(l5, 4) == ((l5 >> 32u64) & 0xFF));
        assert(byte128(l5, 5) == ((l5 >> 40u64) & 0xFF));
        assert(byte128(l5, 6) == ((l5 >> 48u64) & 0xFF));
        assert(byte128(l5, 7) == ((l5 >> 56u64) & 0xFF));
        assert(byte128(l5, 8) == ((l5 >> 64u64) & 0xFF));
        assert(byte128(l5, 9) == ((l5 >> 72u64) & 0xFF));
        assert(byte128(l5, 10) == ((l5 >> 80u64) & 0xFF));
        assert(byte128(l5, 11) == ((l5 >> 88u64) & 0xFF));
        assert(byte128(l5, 12) == ((l5 >> 96u64) & 0xFF));
        assert(byte128(l5, 13) == ((l5 >> 104u64) & 0xFF));
        assert(byte128(l5, 14) == ((l5 >> 112u64) & 0xFF));
        assert(byte128(l5, 15) == ((l5 >> 120u64) & 0xFF));
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l0, k) == (value[0 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[0 as int] as u128;
                assert(l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))));
                assert(z == b0);
                assert(byte128(l0, 0) == z) by (bit_vector)
                    requires
                        z == b0,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[1 as int] as u128;
                assert(byte128(l0, 1) == z) by (bit_vector)
                    requires
                        z == b1,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[2 as int] as u128;
                assert(byte128(l0, 2) == z) by (bit_vector)
                    requires
                        z == b2,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[3 as int] as u128;
                assert(byte128(l0, 3) == z) by (bit_vector)
                    requires
                        z == b3,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[4 as int] as u128;
                assert(byte128(l0, 4) == z) by (bit_vector)
                    requires
                        z == b4,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[5 as int] as u128;
                assert(byte128(l0, 5) == z) by (bit_vector)
                    requires
                        z == b5,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[6 as int] as u128;
                assert(byte128(l0, 6) == z) by (bit_vector)
                    requires
                        z == b6,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[7 as int] as u128;
                assert(byte128(l0, 7) == z) by (bit_vector)
                    requires
                        z == b7,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[8 as int] as u128;
                assert(byte128(l0, 8) == z) by (bit_vector)
                    requires
                        z == b8,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[9 as int] as u128;
                assert(byte128(l0, 9) == z) by (bit_vector)
                    requires
                        z == b9,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[10 as int] as u128;
                assert(byte128(l0, 10) == z) by (bit_vector)
                    requires
                        z == b10,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[11 as int] as u128;
                assert(byte128(l0, 11) == z) by (bit_vector)
                    requires
                        z == b11,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[12 as int] as u128;
                assert(byte128(l0, 12) == z) by (bit_vector)
                    requires
                        z == b12,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[13 as int] as u128;
                assert(byte128(l0, 13) == z) by (bit_vector)
                    requires
                        z == b13,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[14 as int] as u128;
                assert(byte128(l0, 14) == z) by (bit_vector)
                    requires
                        z == b14,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[15 as int] as u128;
                assert(byte128(l0, 15) == z) by (bit_vector)
                    requires
                        z == b15,
                        l0 == (((b0 << 0u64) | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64) | (b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64)) ^ ((b8 << 64u64) | (b9 << 72u64) | (b10 << 80u64) | (b11 << 88u64) | (b12 << 96u64) | (b13 << 104u64) | (b14 << 112u64) | (b15 << 120u64))),
                        b0 <= 0xFF,
                        b1 <= 0xFF,
                        b2 <= 0xFF,
                        b3 <= 0xFF,
                        b4 <= 0xFF,
                        b5 <= 0xFF,
                        b6 <= 0xFF,
                        b7 <= 0xFF,
                        b8 <= 0xFF,
                        b9 <= 0xFF,
                        b10 <= 0xFF,
                        b11 <= 0xFF,
                        b12 <= 0xFF,
                        b13 <= 0xFF,
                        b14 <= 0xFF,
                        b15 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l1, k) == (value[16 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[16 as int] as u128;
                assert(byte128(l1, 0) == z) by (bit_vector)
                    requires
                        z == b16,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[17 as int] as u128;
                assert(byte128(l1, 1) == z) by (bit_vector)
                    requires
                        z == b17,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[18 as int] as u128;
                assert(byte128(l1, 2) == z) by (bit_vector)
                    requires
                        z == b18,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[19 as int] as u128;
                assert(byte128(l1, 3) == z) by (bit_vector)
                    requires
                        z == b19,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[20 as int] as u128;
                assert(byte128(l1, 4) == z) by (bit_vector)
                    requires
                        z == b20,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[21 as int] as u128;
                assert(byte128(l1, 5) == z) by (bit_vector)
                    requires
                        z == b21,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[22 as int] as u128;
                assert(byte128(l1, 6) == z) by (bit_vector)
                    requires
                        z == b22,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[23 as int] as u128;
                assert(byte128(l1, 7) == z) by (bit_vector)
                    requires
                        z == b23,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[24 as int] as u128;
                assert(byte128(l1, 8) == z) by (bit_vector)
                    requires
                        z == b24,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[25 as int] as u128;
                assert(byte128(l1, 9) == z) by (bit_vector)
                    requires
                        z == b25,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[26 as int] as u128;
                assert(byte128(l1, 10) == z) by (bit_vector)
                    requires
                        z == b26,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[27 as int] as u128;
                assert(byte128(l1, 11) == z) by (bit_vector)
                    requires
                        z == b27,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[28 as int] as u128;
                assert(byte128(l1, 12) == z) by (bit_vector)
                    requires
                        z == b28,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[29 as int] as u128;
                assert(byte128(l1, 13) == z) by (bit_vector)
                    requires
                        z == b29,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[30 as int] as u128;
                assert(byte128(l1, 14) == z) by (bit_vector)
                    requires
                        z == b30,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[31 as int] as u128;
                assert(byte128(l1, 15) == z) by (bit_vector)
                    requires
                        z == b31,
                        l1 == (((b16 << 0u64) | (b17 << 8u64) | (b18 << 16u64) | (b19 << 24u64) | (b20 << 32u64) | (b21 << 40u64) | (b22 << 48u64) | (b23 << 56u64)) ^ ((b24 << 64u64) | (b25 << 72u64) | (b26 << 80u64) | (b27 << 88u64) | (b28 << 96u64) | (b29 << 104u64) | (b30 << 112u64) | (b31 << 120u64))),
                        b16 <= 0xFF,
                        b17 <= 0xFF,
                        b18 <= 0xFF,
                        b19 <= 0xFF,
                        b20 <= 0xFF,
                        b21 <= 0xFF,
                        b22 <= 0xFF,
                        b23 <= 0xFF,
                        b24 <= 0xFF,
                        b25 <= 0xFF,
                        b26 <= 0xFF,
                        b27 <= 0xFF,
                        b28 <= 0xFF,
                        b29 <= 0xFF,
                        b30 <= 0xFF,
                        b31 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l2, k) == (value[32 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[32 as int] as u128;
                assert(byte128(l2, 0) == z) by (bit_vector)
                    requires
                        z == b32,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[33 as int] as u128;
                assert(byte128(l2, 1) == z) by (bit_vector)
                    requires
                        z == b33,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[34 as int] as u128;
                assert(byte128(l2, 2) == z) by (bit_vector)
                    requires
                        z == b34,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[35 as int] as u128;
                assert(byte128(l2, 3) == z) by (bit_vector)
                    requires
                        z == b35,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[36 as int] as u128;
                assert(byte128(l2, 4) == z) by (bit_vector)
                    requires
                        z == b36,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[37 as int] as u128;
                assert(byte128(l2, 5) == z) by (bit_vector)
                    requires
                        z == b37,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[38 as int] as u128;
                assert(byte128(l2, 6) == z) by (bit_vector)
                    requires
                        z == b38,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[39 as int] as u128;
                assert(byte128(l2, 7) == z) by (bit_vector)
                    requires
                        z == b39,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[40 as int] as u128;
                assert(byte128(l2, 8) == z) by (bit_vector)
                    requires
                        z == b40,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[41 as int] as u128;
                assert(byte128(l2, 9) == z) by (bit_vector)
                    requires
                        z == b41,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[42 as int] as u128;
                assert(byte128(l2, 10) == z) by (bit_vector)
                    requires
                        z == b42,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[43 as int] as u128;
                assert(byte128(l2, 11) == z) by (bit_vector)
                    requires
                        z == b43,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[44 as int] as u128;
                assert(byte128(l2, 12) == z) by (bit_vector)
                    requires
                        z == b44,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[45 as int] as u128;
                assert(byte128(l2, 13) == z) by (bit_vector)
                    requires
                        z == b45,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[46 as int] as u128;
                assert(byte128(l2, 14) == z) by (bit_vector)
                    requires
                        z == b46,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[47 as int] as u128;
                assert(byte128(l2, 15) == z) by (bit_vector)
                    requires
                        z == b47,
                        l2 == (((b32 << 0u64) | (b33 << 8u64) | (b34 << 16u64) | (b35 << 24u64) | (b36 << 32u64) | (b37 << 40u64) | (b38 << 48u64) | (b39 << 56u64)) ^ ((b40 << 64u64) | (b41 << 72u64) | (b42 << 80u64) | (b43 << 88u64) | (b44 << 96u64) | (b45 << 104u64) | (b46 << 112u64) | (b47 << 120u64))),
                        b32 <= 0xFF,
                        b33 <= 0xFF,
                        b34 <= 0xFF,
                        b35 <= 0xFF,
                        b36 <= 0xFF,
                        b37 <= 0xFF,
                        b38 <= 0xFF,
                        b39 <= 0xFF,
                        b40 <= 0xFF,
                        b41 <= 0xFF,
                        b42 <= 0xFF,
                        b43 <= 0xFF,
                        b44 <= 0xFF,
                        b45 <= 0xFF,
                        b46 <= 0xFF,
                        b47 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l3, k) == (value[48 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[48 as int] as u128;
                assert(byte128(l3, 0) == z) by (bit_vector)
                    requires
                        z == b48,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[49 as int] as u128;
                assert(byte128(l3, 1) == z) by (bit_vector)
                    requires
                        z == b49,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[50 as int] as u128;
                assert(byte128(l3, 2) == z) by (bit_vector)
                    requires
                        z == b50,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[51 as int] as u128;
                assert(byte128(l3, 3) == z) by (bit_vector)
                    requires
                        z == b51,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[52 as int] as u128;
                assert(byte128(l3, 4) == z) by (bit_vector)
                    requires
                        z == b52,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[53 as int] as u128;
                assert(byte128(l3, 5) == z) by (bit_vector)
                    requires
                        z == b53,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[54 as int] as u128;
                assert(byte128(l3, 6) == z) by (bit_vector)
                    requires
                        z == b54,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[55 as int] as u128;
                assert(byte128(l3, 7) == z) by (bit_vector)
                    requires
                        z == b55,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[56 as int] as u128;
                assert(byte128(l3, 8) == z) by (bit_vector)
                    requires
                        z == b56,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[57 as int] as u128;
                assert(byte128(l3, 9) == z) by (bit_vector)
                    requires
                        z == b57,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[58 as int] as u128;
                assert(byte128(l3, 10) == z) by (bit_vector)
                    requires
                        z == b58,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[59 as int] as u128;
                assert(byte128(l3, 11) == z) by (bit_vector)
                    requires
                        z == b59,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[60 as int] as u128;
                assert(byte128(l3, 12) == z) by (bit_vector)
                    requires
                        z == b60,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[61 as int] as u128;
                assert(byte128(l3, 13) == z) by (bit_vector)
                    requires
                        z == b61,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[62 as int] as u128;
                assert(byte128(l3, 14) == z) by (bit_vector)
                    requires
                        z == b62,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[63 as int] as u128;
                assert(byte128(l3, 15) == z) by (bit_vector)
                    requires
                        z == b63,
                        l3 == (((b48 << 0u64) | (b49 << 8u64) | (b50 << 16u64) | (b51 << 24u64) | (b52 << 32u64) | (b53 << 40u64) | (b54 << 48u64) | (b55 << 56u64)) ^ ((b56 << 64u64) | (b57 << 72u64) | (b58 << 80u64) | (b59 << 88u64) | (b60 << 96u64) | (b61 << 104u64) | (b62 << 112u64) | (b63 << 120u64))),
                        b48 <= 0xFF,
                        b49 <= 0xFF,
                        b50 <= 0xFF,
                        b51 <= 0xFF,
                        b52 <= 0xFF,
                        b53 <= 0xFF,
                        b54 <= 0xFF,
                        b55 <= 0xFF,
                        b56 <= 0xFF,
                        b57 <= 0xFF,
                        b58 <= 0xFF,
                        b59 <= 0xFF,
                        b60 <= 0xFF,
                        b61 <= 0xFF,
                        b62 <= 0xFF,
                        b63 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l4, k) == (value[64 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[64 as int] as u128;
                assert(byte128(l4, 0) == z) by (bit_vector)
                    requires
                        z == b64,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[65 as int] as u128;
                assert(byte128(l4, 1) == z) by (bit_vector)
                    requires
                        z == b65,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[66 as int] as u128;
                assert(byte128(l4, 2) == z) by (bit_vector)
                    requires
                        z == b66,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[67 as int] as u128;
                assert(byte128(l4, 3) == z) by (bit_vector)
                    requires
                        z == b67,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[68 as int] as u128;
                assert(byte128(l4, 4) == z) by (bit_vector)
                    requires
                        z == b68,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[69 as int] as u128;
                assert(byte128(l4, 5) == z) by (bit_vector)
                    requires
                        z == b69,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[70 as int] as u128;
                assert(byte128(l4, 6) == z) by (bit_vector)
                    requires
                        z == b70,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[71 as int] as u128;
                assert(byte128(l4, 7) == z) by (bit_vector)
                    requires
                        z == b71,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[72 as int] as u128;
                assert(byte128(l4, 8) == z) by (bit_vector)
                    requires
                        z == b72,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[73 as int] as u128;
                assert(byte128(l4, 9) == z) by (bit_vector)
                    requires
                        z == b73,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[74 as int] as u128;
                assert(byte128(l4, 10) == z) by (bit_vector)
                    requires
                        z == b74,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[75 as int] as u128;
                assert(byte128(l4, 11) == z) by (bit_vector)
                    requires
                        z == b75,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[76 as int] as u128;
                assert(byte128(l4, 12) == z) by (bit_vector)
                    requires
                        z == b76,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[77 as int] as u128;
                assert(byte128(l4, 13) == z) by (bit_vector)
                    requires
                        z == b77,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[78 as int] as u128;
                assert(byte128(l4, 14) == z) by (bit_vector)
                    requires
                        z == b78,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[79 as int] as u128;
                assert(byte128(l4, 15) == z) by (bit_vector)
                    requires
                        z == b79,
                        l4 == (((b64 << 0u64) | (b65 << 8u64) | (b66 << 16u64) | (b67 << 24u64) | (b68 << 32u64) | (b69 << 40u64) | (b70 << 48u64) | (b71 << 56u64)) ^ ((b72 << 64u64) | (b73 << 72u64) | (b74 << 80u64) | (b75 << 88u64) | (b76 << 96u64) | (b77 << 104u64) | (b78 << 112u64) | (b79 << 120u64))),
                        b64 <= 0xFF,
                        b65 <= 0xFF,
                        b66 <= 0xFF,
                        b67 <= 0xFF,
                        b68 <= 0xFF,
                        b69 <= 0xFF,
                        b70 <= 0xFF,
                        b71 <= 0xFF,
                        b72 <= 0xFF,
                        b73 <= 0xFF,
                        b74 <= 0xFF,
                        b75 <= 0xFF,
                        b76 <= 0xFF,
                        b77 <= 0xFF,
                        b78 <= 0xFF,
                        b79 <= 0xFF,
                ;
            } else { }
        }
        assert forall |k: int| 0 <= k < 16 implies
            #[trigger] byte128(l5, k) == (value[80 + k] as u128)
        by {
            if k == 0 {
                let z: u128 = value[80 as int] as u128;
                assert(byte128(l5, 0) == z) by (bit_vector)
                    requires
                        z == b80,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 1 {
                let z: u128 = value[81 as int] as u128;
                assert(byte128(l5, 1) == z) by (bit_vector)
                    requires
                        z == b81,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 2 {
                let z: u128 = value[82 as int] as u128;
                assert(byte128(l5, 2) == z) by (bit_vector)
                    requires
                        z == b82,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 3 {
                let z: u128 = value[83 as int] as u128;
                assert(byte128(l5, 3) == z) by (bit_vector)
                    requires
                        z == b83,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 4 {
                let z: u128 = value[84 as int] as u128;
                assert(byte128(l5, 4) == z) by (bit_vector)
                    requires
                        z == b84,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 5 {
                let z: u128 = value[85 as int] as u128;
                assert(byte128(l5, 5) == z) by (bit_vector)
                    requires
                        z == b85,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 6 {
                let z: u128 = value[86 as int] as u128;
                assert(byte128(l5, 6) == z) by (bit_vector)
                    requires
                        z == b86,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 7 {
                let z: u128 = value[87 as int] as u128;
                assert(byte128(l5, 7) == z) by (bit_vector)
                    requires
                        z == b87,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 8 {
                let z: u128 = value[88 as int] as u128;
                assert(byte128(l5, 8) == z) by (bit_vector)
                    requires
                        z == b88,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 9 {
                let z: u128 = value[89 as int] as u128;
                assert(byte128(l5, 9) == z) by (bit_vector)
                    requires
                        z == b89,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 10 {
                let z: u128 = value[90 as int] as u128;
                assert(byte128(l5, 10) == z) by (bit_vector)
                    requires
                        z == b90,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 11 {
                let z: u128 = value[91 as int] as u128;
                assert(byte128(l5, 11) == z) by (bit_vector)
                    requires
                        z == b91,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 12 {
                let z: u128 = value[92 as int] as u128;
                assert(byte128(l5, 12) == z) by (bit_vector)
                    requires
                        z == b92,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 13 {
                let z: u128 = value[93 as int] as u128;
                assert(byte128(l5, 13) == z) by (bit_vector)
                    requires
                        z == b93,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 14 {
                let z: u128 = value[94 as int] as u128;
                assert(byte128(l5, 14) == z) by (bit_vector)
                    requires
                        z == b94,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else if k == 15 {
                let z: u128 = value[95 as int] as u128;
                assert(byte128(l5, 15) == z) by (bit_vector)
                    requires
                        z == b95,
                        l5 == (((b80 << 0u64) | (b81 << 8u64) | (b82 << 16u64) | (b83 << 24u64) | (b84 << 32u64) | (b85 << 40u64) | (b86 << 48u64) | (b87 << 56u64)) ^ ((b88 << 64u64) | (b89 << 72u64) | (b90 << 80u64) | (b91 << 88u64) | (b92 << 96u64) | (b93 << 104u64) | (b94 << 112u64) | (b95 << 120u64))),
                        b80 <= 0xFF,
                        b81 <= 0xFF,
                        b82 <= 0xFF,
                        b83 <= 0xFF,
                        b84 <= 0xFF,
                        b85 <= 0xFF,
                        b86 <= 0xFF,
                        b87 <= 0xFF,
                        b88 <= 0xFF,
                        b89 <= 0xFF,
                        b90 <= 0xFF,
                        b91 <= 0xFF,
                        b92 <= 0xFF,
                        b93 <= 0xFF,
                        b94 <= 0xFF,
                        b95 <= 0xFF,
                ;
            } else { }
        }
    }
    [l0, l1, l2, l3, l4, l5]
}

// ===========================================================================
// FA11-beta (the six-item fields supplement, batch 2026-11). Upstream
// anchors: fields/large_fields.rs traits -- Alphas (:148-151), Betas
// (:153-157), Sigmas (:159-162), ByteCombineConstants (:215-221),
// SquareBytes (:230-234 with the blanket impl :236-276),
// ByteCombineSquared (:278-298 with the blanket impl :300-313),
// FromBit (:315-319), ByteCombineSquaredConstants (:321-327), and the
// generic BigGF bodies -- FromBit (:363-371), ByteCombine (:375-402),
// SquareBytes :236-276, ByteCombineSquared :302-313. Values:
// fields/large_fields_constants.rs :9-416, transcribed script-exact
// (out/kverus-run/FA11-beta/extract_constants.py, int() evaluator,
// the #FA3-9 discipline) and cross-checked against the oracle run
// (out/kverus-run/FA11-beta/oracle-run.txt).
//
// This batch lands:
//   (1) ByteCombineSquaredConstants BYTE_COMBINE_SQ_2/SQ_3 at all
//       three axes (consumers: prover/aes.rs :239-247 + verifier/
//       aes.rs :386-387 MixColumns over squared commitments),
//   (2) Sigmas' SIGMA / SIGMA_SQUARES sets at all three axes
//       (consumers: prover/aes.rs :333-356 + verifier/aes.rs
//       :304-306 s_box_affine),
//   (3) Betas' BETA_SQUARES / BETA_CUBES sets at all three axes
//       (consumers: prover/encryption.rs :161-179 + verifier/
//       encryption.rs :153-159 invnorm_to_conjugates),
//   (4) the SquareBytes family at the GF192/GF256 pair axes
//       (square_byte / square_byte_inplace; consumer: verifier/
//       encryption.rs :179-192 f256_f2_conjugates),
//   (5) the ByteCombineSquared family at the pair axes (byte_
//       combine_bits_sq / byte_combine_sq_slice via the ByteCombine
//       blanket body :381-401 re-erected as gf* byte_combine /
//       byte_combine_slice / byte_combine_bits -- the carriers, a
//       this-batch dependency closure of combine_sq; consumer:
//       prover/byte_commitments.rs get_field_commit_sq at the pair
//       axes, plus from_bit for prover/encryption.rs :167),
//   (6) the re-homing of the FA6-pre prover-subtree patch faces
//       (SQ_COLS / sqb_slot8 / gf128_square_byte8 / gf128_square_
//       byte_inplace / the GF8-orbit lemma bank / gf8_sq_bits_u8 /
//       gf128_byte_combine_bits_sq / gf128_byte_combine_sq_slice)
//       from src/prover/byte_commitments.rs to THIS seat -- the
//       byte_commitments twin now re-exports them (same names, same
//       slot contracts; the FA6-pre re-homing note is discharged
//       here, single source of truth in the fields tree).
// ===========================================================================


// ---------------------------------------------------------------------------
// (2) Sigmas + (3) Betas for GF128 (upstream impls for GF128,
// large_fields_constants.rs :23-64, values verbatim; index 5 of each
// SIGMA set is Field::ONE, and the first-hand value observations
// BETA_SQUARES[4] == BETA_SQUARES[0] resp. BETA_CUBES[0] ==
// BETA_SQUARES[3] are upstream value facts, transcribed as-is).
// ---------------------------------------------------------------------------

/// Sigmas::SIGMA for GF128 (the s_box_affine base rows).
pub const GF128_SIGMA: [u128; 9] = [
    0x4cf4b7439cbfbb84ec7759ca3488aee0,
    0x35ad604f7d51d2c6bfcf02ae363946a9,
    0xb32fd29a04c0be084c3607bab51b5aca,
    0x186ca7a286376521c95c10ed4f932c54,
    0xca760596e52ed74a1f8e5cdeb7aab282,
    0x00000000000000000000000000000001,
    0x1cf7a0fe8922c83fd8a5ae31928b4da1,
    0x7534634307ce7cbe88fd3d5cb6e7dff9,
    0x872430dcdf135bcc433f53640b5ab39a,
];

/// Sigmas::SIGMA_SQUARES for GF128 (the sq=true affine rows).
pub const GF128_SIGMA_SQUARES: [u128; 9] = [
    0x0dcb364640a222fe6b8330483c2e9848,
    0xd681a5686c0c1f75c72bf2ef2521ff23,
    0x49c93216352821984d48b16661e860ed,
    0xf68b54c3d7c88a6cda3bd0e460a50d97,
    0x9283a13819861c13e1e073c178e70787,
    0x00000000000000000000000000000001,
    0xffdb65d9987f058ca0415e708193f42a,
    0xa3b5c62b6bc263cb4fd6cfb393c620db,
    0xdaec11278a2c0a891c6e94d79177c893,
];

/// Betas::BETA_SQUARES for GF128 (the F2-conjugate squares).
pub const GF128_BETA_SQUARES: [u128; 5] = [
    0xdb4a932e2cae3d8baca8c2a7190f676b,
    0x500317bd159d73bb34d2f7fba603e341,
    0xf210539fd8dd2772cbc26e38bdbd6c62,
    0x7959d70ce1ee694253b85b6402b1e849,
    0xdb4a932e2cae3d8baca8c2a7190f676b,
];

/// Betas::BETA_CUBES for GF128.
pub const GF128_BETA_CUBES: [u128; 4] = [
    0x7959d70ce1ee694253b85b6402b1e849,
    0xdb4a932e2cae3d8baca8c2a7190f676b,
    0x500317bd159d73bb34d2f7fba603e341,
    0xf210539fd8dd2772cbc26e38bdbd6c62,
];

// ---------------------------------------------------------------------------
// (1) ByteCombineSquaredConstants for GF128 (upstream
// large_fields_constants.rs :66-69):
//     impl ByteCombineSquaredConstants for BigGF<u128, 1, 128> {
//         const BYTE_COMBINE_SQ_2: Self = Self::ALPHA[1];
//         const BYTE_COMBINE_SQ_3: Self =
//             Self([Self::ALPHA[1].0[0] ^ Self::ONE.0[0]]); }
// ("Equivalent `ByteCombing::byte_combine_bits_sq(2)` resp. `(3)`" --
// the upstream doc line above each const, recorded; the upstream
// doc's `ByteCombing` is a doc-alias of ByteCombineSquared).
// ---------------------------------------------------------------------------

/// BYTE_COMBINE_SQ_2 for GF128 == ALPHA[1] (upstream derivation:
/// byte_combine_bits_sq(2) == byte_combine_bits(GF8::square_bits(2)
/// == 0x04) == ALPHA[1]; the FA6-pre 256-row CSV pins the k=04 row at
/// this exact constant).
pub const GF128_BYTE_COMBINE_SQ_2: u128 = 0x4cf4b7439cbfbb84ec7759ca3488aee1;

/// BYTE_COMBINE_SQ_3 for GF128 == ALPHA[1] ^ ONE (the ONE-carrying
/// limb is the low limb; expression form follows the upstream RHS,
/// the GF128_BYTE_COMBINE_3 twin convention).
pub const GF128_BYTE_COMBINE_SQ_3: u128 = 0x4cf4b7439cbfbb84ec7759ca3488aee1 ^ 1;


// ---------------------------------------------------------------------------
// (2) Sigmas + (3) Betas for GF192 (upstream large_fields_constants.rs
// :150-227, values verbatim; index 5 of each SIGMA set is Field::ONE
// pair note: Field::ONE (1, 0) sits at each SIGMA index 5.
// ---------------------------------------------------------------------------

/// Sigmas::SIGMA for GF192 (the s_box_affine base rows).
pub const GF192_SIGMA: [(u128, u128); 9] = [
    (0x7bf61f19d5633f26b233619e7cf450ba, 0x0000000000000000da933726d491db34),
    (0x8232e37706328d199c6d2c13f5398a0c, 0x00000000000000000c3b0d703c754ef6),
    (0x638227a707652828fb039539490f3262, 0x00000000000000007170a38d85840211),
    (0x73e093aeb2bd81a26ae66d7cf63a7b42, 0x00000000000000000cee234c9f37ab71),
    (0x9a46dbc9d4349a17d55dd8b4c0c2e8d5, 0x0000000000000000a7d899db6d6097d3),
    (0x00000000000000000000000000000001, 0x00000000000000000000000000000000),
    (0x69ac2c678be3ba5f425244c22e17096e, 0x00000000000000008e7e2484040c7d90),
    (0x7fb8d6607c39e6061702b39a83f3c8a5, 0x000000000000000020dfa416e9086710),
    (0x1d99ac75ae672326831233410b235d20, 0x0000000000000000ced061212ca1ac64),
];

/// Sigmas::SIGMA_SQUARES for GF192 (the sq=true affine rows).
pub const GF192_SIGMA_SQUARES: [(u128, u128); 9] = [
    (0x7a5542ab0058d22edd20747cbd2bf75c, 0x000000000000000045ec519c94bc1251),
    (0xf3eaf7ae5fd72048970f9c76eed5e1bb, 0x000000000000000029a6bd5f696cea43),
    (0x9d93c875430d82cc7efbc24b13ccc7d9, 0x0000000000000000eb98ff32dafaed56),
    (0x786dc5dceb00feddbca4a96550fde7a8, 0x00000000000000006c9fc2ff5e921d95),
    (0x142c7d701c8270aa34d42a414032d13f, 0x000000000000000087d213f1272a1544),
    (0x00000000000000000000000000000001, 0x00000000000000000000000000000000),
    (0x187438bed206170e4930f4a735fb62d8, 0x0000000000000000abe394ab5115d925),
    (0x8c5221ce23eec64e800d2fec6d26291f, 0x00000000000000000979194980648d53),
    (0x7596dda0f0bf7471ae536261e4ebf3a8, 0x0000000000000000dfd1231f68801891),
];

/// Betas::BETA_SQUARES for GF192 ([Self; 5], value pairs; the
// BETA_SQUARES[4] == BETA_SQUARES[0] wraparound is an upstream value
// fact, transcribed verbatim).
pub const GF192_BETA_SQUARES: [(u128, u128); 5] = [
    (0x89bfb5055f8ff2664a2fe80a53fe16e7, 0x00000000000000006c4aecc3fdd0f812),
    (0x125a337e5e808579f061255c52e359d4, 0x000000000000000054ed13a2d09da6a4),
    (0x62217a15d25ec520941080db88d09584, 0x0000000000000000ee0fc537c5a9cb74),
    (0xf9c4fc6ed351b23f2e5e4d8d89cddab6, 0x0000000000000000d6a83a56e8e495c2),
    (0x89bfb5055f8ff2664a2fe80a53fe16e7, 0x00000000000000006c4aecc3fdd0f812),
];

/// Betas::BETA_CUBES for GF192 ([Self; 4], value pairs).
pub const GF192_BETA_CUBES: [(u128, u128); 4] = [
    (0xf9c4fc6ed351b23f2e5e4d8d89cddab6, 0x0000000000000000d6a83a56e8e495c2),
    (0x89bfb5055f8ff2664a2fe80a53fe16e7, 0x00000000000000006c4aecc3fdd0f812),
    (0x125a337e5e808579f061255c52e359d4, 0x000000000000000054ed13a2d09da6a4),
    (0x62217a15d25ec520941080db88d09584, 0x0000000000000000ee0fc537c5a9cb74),
];

// ---------------------------------------------------------------------------
// (1) ByteCombineSquaredConstants for GF192 (upstream
// large_fields_constants.rs :237-243):
//     const BYTE_COMBINE_SQ_2: Self = Self::ALPHA[1];
//     const BYTE_COMBINE_SQ_3: Self = Self([
//         Self::ALPHA[1].0[0] ^ Self::ONE.0[0],
//         Self::ALPHA[1].0[1] ^ Self::ONE.0[1]]);
// ONE is the pair (1, 0), so the limb-1 xor is the identity; the
// value-literal form follows the GF192_BYTE_COMBINE_2/3 wave-3 twin
// convention (the XOR folded into the limb-0 literal).
// ---------------------------------------------------------------------------

/// BYTE_COMBINE_SQ_2 for GF192 == ALPHA[1] (upstream derivation:
/// byte_combine_bits_sq(2) == byte_combine_bits(0x04) == ALPHA[1]).
pub const GF192_BYTE_COMBINE_SQ_2: (u128, u128) = (0x7bf61f19d5633f26b233619e7cf450bb, 0x0000000000000000da933726d491db34);

/// BYTE_COMBINE_SQ_3 for GF192 == ALPHA[1] ^ ONE (low limb only).
pub const GF192_BYTE_COMBINE_SQ_3: (u128, u128) = (0x7bf61f19d5633f26b233619e7cf450ba, 0x0000000000000000da933726d491db34);


// ---------------------------------------------------------------------------
// (2) Sigmas + (3) Betas for GF256 (upstream large_fields_constants.rs
// :280-400, values verbatim; index 5 of each SIGMA set is Field::ONE
// pair note: Field::ONE (1, 0) sits at each SIGMA index 5.
// ---------------------------------------------------------------------------

/// Sigmas::SIGMA for GF256 (the s_box_affine base rows).
pub const GF256_SIGMA: [(u128, u128); 9] = [
    (0x2ba5c48d2c42072fa95af52ad52289c0, 0x064e4d699c5b4af1d14a0d376c00b0ea),
    (0x1771831e533b0f5755dab3833f809d1c, 0x6195e3db7011f68dfb96573fad3fac10),
    (0x8748a24b4ab3a892372f5a920b67efff, 0xc6737a464da16302214b28089e99af95),
    (0x30611f596cb383ad319800033ca8b976, 0x24694604ed0c050dfef404a31149196b),
    (0xbb9ce5d835caa0eacbaf1c3be1c5fb22, 0xa1a8d4f4a1ebdf7e0b9772005fa6b36f),
    (0x00000000000000000000000000000001, 0x00000000000000000000000000000000),
    (0x1771831e533b0f5655dab3823f819c28, 0x6195e3db7011f68dfb96573fad3fac11),
    (0xd0350e7dfa862912d0547873524e02b1, 0x702cec741ee89ff7da9be967cd26e8d5),
    (0x09ff302a864765599020d2d23c10a95b, 0xe6d3948d80643e3c009db4ee77215795),
];

/// Sigmas::SIGMA_SQUARES for GF256 (the sq=true affine rows).
pub const GF256_SIGMA_SQUARES: [(u128, u128); 9] = [
    (0x752758911a30e3f6de010519b01bcdd4, 0x56c24fd64f7688382a0778b6489ea03f),
    (0xaced66c666f1afbc9e75afb9de44670a, 0xc03d372fd1fa29f3f001253ff2991f7e),
    (0x957349b58c0549483fcd7d68defc7727, 0x0287e5a6bc9212c20e68957294f15180),
    (0xfedaa2104349c0b0243619206d778eb5, 0xd303dd260391524bdf640e1506710a3a),
    (0x4cb977e2f0c405027fb9d7c8b0a3ddf8, 0x94789d5f221eb309d46ec8fb2ef6eec1),
    (0x00000000000000000000000000000001, 0x00000000000000000000000000000000),
    (0xaced66c666f1afbd9e75afb8de45663f, 0xc03d372fd1fa29f3f001253ff2991f7f),
    (0x7cd868bb9c7786ae4e21d7ca8c0a65ba, 0xb011db5bcf12b6042a9acc583fbff7ab),
    (0x400c2f28e30e8ed6b2a1916366a87167, 0xd7ca75e923580a7800469650fe80eb51),
];

/// Betas::BETA_SQUARES for GF256 ([Self; 5], value pairs; the
// BETA_SQUARES[4] == BETA_SQUARES[0] wraparound is an upstream value
// fact, transcribed verbatim).
pub const GF256_BETA_SQUARES: [(u128, u128); 5] = [
    (0xd9ca3e577cc14c4a4074aaa06e5faade, 0x96ff78f99e8ca1cbda065d89ba07bf41),
    (0x3cd447937f790879fc8046a8eaa315e8, 0x67dbaeb2ec4abc7c2adc5a08c13f1cfb),
    (0xd9ca3e577cc14c4b4074aaa16e5eabeb, 0x96ff78f99e8ca1cbda065d89ba07bf40),
    (0x3cd447937f790878fc8046a9eaa214dc, 0x67dbaeb2ec4abc7c2adc5a08c13f1cfa),
    (0xd9ca3e577cc14c4a4074aaa06e5faade, 0x96ff78f99e8ca1cbda065d89ba07bf41),
];

/// Betas::BETA_CUBES for GF256 ([Self; 4], value pairs).
pub const GF256_BETA_CUBES: [(u128, u128); 4] = [
    (0x3cd447937f790878fc8046a9eaa214dc, 0x67dbaeb2ec4abc7c2adc5a08c13f1cfa),
    (0xd9ca3e577cc14c4a4074aaa06e5faade, 0x96ff78f99e8ca1cbda065d89ba07bf41),
    (0x3cd447937f790879fc8046a8eaa315e8, 0x67dbaeb2ec4abc7c2adc5a08c13f1cfb),
    (0xd9ca3e577cc14c4b4074aaa16e5eabeb, 0x96ff78f99e8ca1cbda065d89ba07bf40),
];

// ---------------------------------------------------------------------------
// (1) ByteCombineSquaredConstants for GF256 (upstream
// large_fields_constants.rs :410-416):
//     const BYTE_COMBINE_SQ_2: Self = Self::ALPHA[1];
//     const BYTE_COMBINE_SQ_3: Self = Self([
//         Self::ALPHA[1].0[0] ^ Self::ONE.0[0],
//         Self::ALPHA[1].0[1] ^ Self::ONE.0[1]]);
// ONE is the pair (1, 0), so the limb-1 xor is the identity; the
// value-literal form follows the GF256_BYTE_COMBINE_2/3 wave-3 twin
// convention (the XOR folded into the limb-0 literal).
// ---------------------------------------------------------------------------

/// BYTE_COMBINE_SQ_2 for GF256 == ALPHA[1] (upstream derivation:
/// byte_combine_bits_sq(2) == byte_combine_bits(0x04) == ALPHA[1]).
pub const GF256_BYTE_COMBINE_SQ_2: (u128, u128) = (0x2ba5c48d2c42072fa95af52ad52289c1, 0x064e4d699c5b4af1d14a0d376c00b0ea);

/// BYTE_COMBINE_SQ_3 for GF256 == ALPHA[1] ^ ONE (low limb only).
pub const GF256_BYTE_COMBINE_SQ_3: (u128, u128) = (0x2ba5c48d2c42072fa95af52ad52289c0, 0x064e4d699c5b4af1d14a0d376c00b0ea);


// ===========================================================================
// (6) Re-homed FA6-pre block (batch FA11-beta): the SquareBytes /
// ByteCombineSquared GF128-axis faces + the GF8-orbit lemma bank,
// moved VERBATIM from src/prover/byte_commitments.rs (the FA6-pre
// twin's local patch; the file header there records the discharge).
// The upstream anchors live in the block comments below; the faces
// are the fields tree's canonical seat now (single source).
// ===========================================================================

// ===========================================================================
// SquareBytes (upstream fields/large_fields.rs :215-276, blanket impl
// at the BigGaloisField tower; derived GF128-axis face):
//     fn square_byte(x: &[Self]) -> [Self; 8] {
//         let mut sq = [<Self as Field>::ZERO; 8];
//         sq[0] = x[0] + x[4] + x[6];
//         sq[2] = x[1] + x[5];
//         sq[4] = x[2] + x[4] + x[7];
//         sq[5] = x[5] + x[6];
//         sq[6] = x[3] + x[5];
//         sq[7] = x[6] + x[7];
//         sq[1] = x[4] + sq[7];
//         sq[3] = x[5] + sq[1];
//         sq }
// The eight formulas are the GF(2)-coordinate squaring matrix of
// GF(2^8) (modulus x^8+x^4+x^3+x+1, the GF8_MODULUS 0x1B of
// small_fields.rs:76) applied slot-wise over the 8 tag slots; `+` on
// the big field lowers to `^` (characteristic 2, the FA3 record).
// ===========================================================================

/// The square matrix columns as BYTES: SQ_COLS[j] is the GF8 square
/// of the basis byte 1<<j (the FA2 gf8_ref_square_spread model value;
/// proven per-column in lemma_sq_cols_basis). Bit i of SQ_COLS[j]
/// selects x[j] into output slot i.
pub const SQ_COLS: [u8; 8] = [0x01, 0x04, 0x10, 0x40, 0x1b, 0x6c, 0xab, 0x9a];

/// Spec face of the SquareBytes slot map over eight scalar slots.
pub open spec fn sqb_slot8(
    i: int,
    x0: u128,
    x1: u128,
    x2: u128,
    x3: u128,
    x4: u128,
    x5: u128,
    x6: u128,
    x7: u128,
) -> u128 {
    // column 0, byte 0x01 -- slot 0
    (if i == 0 { x0 } else { 0u128 })
        // column 1, byte 0x04 -- slot 2
        ^ (if i == 2 { x1 } else { 0u128 })
        // column 2, byte 0x10 -- slot 4
        ^ (if i == 4 { x2 } else { 0u128 })
        // column 3, byte 0x40 -- slot 6
        ^ (if i == 6 { x3 } else { 0u128 })
        // column 4, byte 0x1b -- slots 0, 1, 3, 4
        ^ (if i == 0 || i == 1 || i == 3 || i == 4 { x4 } else { 0u128 })
        // column 5, byte 0x6c -- slots 2, 3, 5, 6
        ^ (if i == 2 || i == 3 || i == 5 || i == 6 { x5 } else { 0u128 })
        // column 6, byte 0xab -- slots 0, 1, 3, 5, 7
        ^ (if i == 0 || i == 1 || i == 3 || i == 5 || i == 7 { x6 } else { 0u128 })
        // column 7, byte 0x9a -- slots 1, 3, 4, 7
        ^ (if i == 1 || i == 3 || i == 4 || i == 7 { x7 } else { 0u128 })
}

/// The pure square_byte twin (upstream :240-251), scalar-slot form.
/// Body order preserved: slots 0/2/4/5/6/7 first, then 1 and 3 off
/// the provisional sq[7] / sq[1] values.
pub exec fn gf128_square_byte8(
    x0: u128,
    x1: u128,
    x2: u128,
    x3: u128,
    x4: u128,
    x5: u128,
    x6: u128,
    x7: u128,
) -> (sq: [u128; 8])
    ensures
        sq[0] == sqb_slot8(0, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[1] == sqb_slot8(1, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[2] == sqb_slot8(2, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[3] == sqb_slot8(3, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[4] == sqb_slot8(4, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[5] == sqb_slot8(5, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[6] == sqb_slot8(6, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[7] == sqb_slot8(7, x0, x1, x2, x3, x4, x5, x6, x7),
{
    // the two-stage build mirrors the upstream's two-stage writes
    // (slots 0/2/4/5/6/7 off the inputs, then 1 / 3 off the
    // provisional sq[7] / sq[1]); the y-locals are the scalar
    // provable column of each slot (bv-friendly -- no mutated array
    // free var enters the bv asserts)
    let y0 = x0 ^ x4 ^ x6;
    let y2 = x1 ^ x5;
    let y4 = x2 ^ x4 ^ x7;
    let y5 = x5 ^ x6;
    let y6 = x3 ^ x5;
    let y7 = x6 ^ x7;
    let y1 = x4 ^ y7;
    let y3 = x5 ^ y1;
    proof {
        // bv sees let-locals as free vars (probe2 f1/f6 pin): each
        // y-slot gets its machine expression re-tied by requires
        assert(y0 == sqb_slot8(0, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires y0 == (x0 ^ x4 ^ x6),
        ;
        assert(y2 == sqb_slot8(2, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires y2 == (x1 ^ x5),
        ;
        assert(y4 == sqb_slot8(4, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires y4 == (x2 ^ x4 ^ x7),
        ;
        assert(y5 == sqb_slot8(5, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires y5 == (x5 ^ x6),
        ;
        assert(y6 == sqb_slot8(6, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires y6 == (x3 ^ x5),
        ;
        assert(y7 == sqb_slot8(7, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires y7 == (x6 ^ x7),
        ;
        assert(y1 == sqb_slot8(1, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires y1 == (x4 ^ (x6 ^ x7)),
        ;
        assert(y3 == sqb_slot8(3, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires y3 == (x5 ^ (x4 ^ (x6 ^ x7))),
        ;
    }
    [y0, y1, y2, y3, y4, y5, y6, y7]
}

/// The in-place SquareBytes twin (upstream :252-265), verbatim body
/// over the &mut slice:
///     let (i2, i4, i5, i6) = (x[2], x[4], x[5], x[6]);
///     x[0] += x[4] + x[6];
///     x[2] = x[1] + x[5];
///     x[4] += i2 + x[7];
///     x[5] += x[6];
///     x[6] = x[3] + i5;
///     x[7] += i6;
///     x[1] = i4 + x[7];
///     x[3] = i5 + x[1];
/// (the field `+=` lowers to `^`). The slot contract is the same
/// sqb_slot8 face as the pure twin -- the two upstream bodies of the
/// same SquareBytes trait verify against one spec.
pub exec fn gf128_square_byte_inplace(x: &mut [u128])
    requires
        old(x).len() == 8,
    ensures
        final(x)[0] == sqb_slot8(0, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[1] == sqb_slot8(1, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[2] == sqb_slot8(2, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[3] == sqb_slot8(3, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[4] == sqb_slot8(4, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[5] == sqb_slot8(5, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[6] == sqb_slot8(6, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[7] == sqb_slot8(7, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
{
    let x0 = x[0];
    let x1 = x[1];
    let x2 = x[2];
    let x3 = x[3];
    let x4 = x[4];
    let x5 = x[5];
    let x6 = x[6];
    let x7 = x[7];
    proof {
        assert(x0 == old(x)[0]);
        assert(x1 == old(x)[1]);
        assert(x2 == old(x)[2]);
        assert(x3 == old(x)[3]);
        assert(x4 == old(x)[4]);
        assert(x5 == old(x)[5]);
        assert(x6 == old(x)[6]);
        assert(x7 == old(x)[7]);
    }
    let i2 = x[2];
    let i4 = x[4];
    let i5 = x[5];
    let i6 = x[6];
    x[0] = x[0] ^ x[4] ^ x[6];
    x[2] = x[1] ^ x[5];
    x[4] = x[4] ^ i2 ^ x[7];
    x[5] = x[5] ^ x[6];
    x[6] = x[3] ^ i5;
    x[7] = x[7] ^ i6;
    x[1] = i4 ^ x[7];
    x[3] = i5 ^ x[1];
    proof {
        // the post-state slot values in terms of the pinned pre-state
        // locals (plain asserts; the mutation chain is straight-line;
        // the i-temporaries are pre-mutation reads of the same slots)
        assert(i2 == x2);
        assert(i4 == x4);
        assert(i5 == x5);
        assert(i6 == x6);
        let x7_n = x7 ^ i6;
        let x1_n = i4 ^ x7_n;
        assert(final(x)[7] == x7_n);
        assert(final(x)[1] == x1_n);
        assert(final(x)[3] == i5 ^ x1_n);
        // each slot against the column spec (the SQ_COLS byte bits
        // select exactly the local XOR terms; bv per slot)
        assert((x0 ^ x4 ^ x6) == sqb_slot8(0, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector);
        assert((i4 ^ x7_n) == sqb_slot8(1, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires (i4 ^ x7_n) == (x4 ^ (x7 ^ x6)),
        ;
        assert((x1 ^ x5) == sqb_slot8(2, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector);
        assert((i5 ^ x1_n) == sqb_slot8(3, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires (i5 ^ x1_n) == (x5 ^ (x4 ^ (x7 ^ x6))),
        ;
        assert((x4 ^ i2 ^ x7) == sqb_slot8(4, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires (x4 ^ i2 ^ x7) == (x4 ^ x2 ^ x7) && i2 == x2,
        ;
        assert((x5 ^ x6) == sqb_slot8(5, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector);
        assert((x3 ^ x5) == sqb_slot8(6, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector);
        assert((x7_n) == sqb_slot8(7, x0, x1, x2, x3, x4, x5, x6, x7)) by (bit_vector)
            requires x7_n == (x7 ^ x6),
        ;
        // slot-value plumbing:
        // x[0] new == x0^x4^x6, x[2] new == x1^x5, x[4] new == x4^i2^x7,
        // x[5] new == x5^x6, x[6] new == x3^x5 -- each of the
        // asserted spec equalities carries through
        let _ : () = ();
    }
}

// ===========================================================================
// GF8-orbit obligation 1 (per-column): SQ_COLS[j] == the FA2 spread
// model of the basis byte 1<<j.
// ===========================================================================

/// Per-column basis facts (eight columns; concrete u16 models, one
/// bv blast per column). This is the tag-plane / key-plane duality at
/// the coordinate level: the SquareBytes column j IS the GF8 square
/// byte of basis bit j.
pub proof fn lemma_sq_cols_basis()
    ensures
        gf8_ref_square_spread(0x0001u16) == 0x0001u16,
        gf8_ref_square_spread(0x0002u16) == 0x0004u16,
        gf8_ref_square_spread(0x0004u16) == 0x0010u16,
        gf8_ref_square_spread(0x0008u16) == 0x0040u16,
        gf8_ref_square_spread(0x0010u16) == 0x001bu16,
        gf8_ref_square_spread(0x0020u16) == 0x006cu16,
        gf8_ref_square_spread(0x0040u16) == 0x00abu16,
        gf8_ref_square_spread(0x0080u16) == 0x009au16,
{
    assert(gf8_ref_square_spread(0x0001u16) == 0x0001u16) by (bit_vector);
    assert(gf8_ref_square_spread(0x0002u16) == 0x0004u16) by (bit_vector);
    assert(gf8_ref_square_spread(0x0004u16) == 0x0010u16) by (bit_vector);
    assert(gf8_ref_square_spread(0x0008u16) == 0x0040u16) by (bit_vector);
    assert(gf8_ref_square_spread(0x0010u16) == 0x001bu16) by (bit_vector);
    assert(gf8_ref_square_spread(0x0020u16) == 0x006cu16) by (bit_vector);
    assert(gf8_ref_square_spread(0x0040u16) == 0x00abu16) by (bit_vector);
    assert(gf8_ref_square_spread(0x0080u16) == 0x009au16) by (bit_vector);
}

// ===========================================================================
// GF8-orbit obligation 2 (byte level): the spread model is
// XOR-homomorphic and equals the column-XOR linear face on every
// byte; the model stays in byte range.
// ===========================================================================

/// The column-XOR linear face of the GF8 square: XOR of SQ_COLS[j]
/// over the set bits j of k.
pub open spec fn gf8_sq_linear_spec(k: u8) -> u8 {
    (if k & 1 == 1 { SQ_COLS[0] } else { 0u8 })
        ^ (if ((k >> 1) & 1) == 1 { SQ_COLS[1] } else { 0u8 })
        ^ (if ((k >> 2) & 1) == 1 { SQ_COLS[2] } else { 0u8 })
        ^ (if ((k >> 3) & 1) == 1 { SQ_COLS[3] } else { 0u8 })
        ^ (if ((k >> 4) & 1) == 1 { SQ_COLS[4] } else { 0u8 })
        ^ (if ((k >> 5) & 1) == 1 { SQ_COLS[5] } else { 0u8 })
        ^ (if ((k >> 6) & 1) == 1 { SQ_COLS[6] } else { 0u8 })
        ^ (if ((k >> 7) & 1) == 1 { SQ_COLS[7] } else { 0u8 })
}

/// The spread model lands in byte range on every byte input (the two
/// fold tails close inside the low byte).
pub proof fn lemma_spread_byte_range(x: u8)
    ensures
        gf8_ref_square_spread(x as u16) < 0x100,
{
    assert(gf8_ref_square_spread(x as u16) < 0x100) by (bit_vector);
}

/// Spread-model GF2-linearity over byte XOR (the Morton spread's OR
/// masks hit disjoint positions on the u16 domain, so every output
/// bit is a single-position XOR of input bits).
pub proof fn lemma_spread_xor_hom(a: u8, b: u8)
    ensures
        gf8_ref_square_spread((a ^ b) as u16)
            == gf8_ref_square_spread(a as u16) ^ gf8_ref_square_spread(b as u16),
{
    assert(gf8_ref_square_spread((a ^ b) as u16)
        == gf8_ref_square_spread(a as u16) ^ gf8_ref_square_spread(b as u16)) by (bit_vector);
}

/// Column-face GF2-linearity over byte XOR (definitional selects).
pub proof fn lemma_sq_linear_xor_hom(a: u8, b: u8)
    ensures
        gf8_sq_linear_spec(a ^ b) == gf8_sq_linear_spec(a) ^ gf8_sq_linear_spec(b),
{
    assert(gf8_sq_linear_spec(a ^ b)
        == gf8_sq_linear_spec(a) ^ gf8_sq_linear_spec(b)) by (bit_vector);
}

/// Byte-level GF8-orbit theorem: on every byte, the FA2 spread model
/// of GF8::square_bits equals the column-XOR linear face of the tag
/// matrix. Both maps are GF2-linear (the two hom lemmas); the byte
/// splits lo ^ (hi << 4); each nibble voice's image is bv-pinned
/// (the low voice over the four low basis bytes, the high voice over
/// the four high ones -- the spread writes each basis bit into its
/// doubled position and folds it back).
pub proof fn lemma_gf8_sq_linear(k: u8)
    ensures
        gf8_ref_square_spread(k as u16) == (gf8_sq_linear_spec(k) as u16),
{
    assert((k & 0x0f) ^ ((k >> 4) << 4) == k) by (bit_vector);
    lemma_spread_xor_hom(k & 0x0f, (k >> 4) << 4);
    lemma_sq_linear_xor_hom(k & 0x0f, (k >> 4) << 4);
    lemma_sq_cols_basis();

    // low voice: the four low basis images (the spread model at
    // 1<<j is SQ_COLS[j], per-column above), combined by the
    // linearity lemma over the nibble's own bits
    assert(gf8_ref_square_spread((k & 0x0f) as u16) == (if (k & 0x01) == 0x01 { 0x0001u16 } else { 0x0000u16 })
        ^ (if (k & 0x02) == 0x02 { 0x0004u16 } else { 0x0000u16 })
        ^ (if (k & 0x04) == 0x04 { 0x0010u16 } else { 0x0000u16 })
        ^ (if (k & 0x08) == 0x08 { 0x0040u16 } else { 0x0000u16 })) by (bit_vector);
    assert(gf8_sq_linear_spec(k & 0x0f) == (if (k & 0x01) == 0x01 { 0x01u8 } else { 0u8 })
        ^ (if (k & 0x02) == 0x02 { 0x04u8 } else { 0u8 })
        ^ (if (k & 0x04) == 0x04 { 0x10u8 } else { 0u8 })
        ^ (if (k & 0x08) == 0x08 { 0x40u8 } else { 0u8 })) by (bit_vector);

    // high voice: the four high basis images (bits 4..7 spread into
    // positions 8..14 and the fold tails close back into the byte;
    // one bv blast pins the whole voice shape)
    assert(gf8_ref_square_spread((((k >> 4) << 4) as u16)) == (if (k & 0x10) == 0x10 { 0x001bu16 } else { 0x0000u16 })
        ^ (if (k & 0x20) == 0x20 { 0x006cu16 } else { 0x0000u16 })
        ^ (if (k & 0x40) == 0x40 { 0x00abu16 } else { 0x0000u16 })
        ^ (if (k & 0x80) == 0x80 { 0x009au16 } else { 0x0000u16 })) by (bit_vector);
    assert(gf8_sq_linear_spec((k >> 4) << 4) == (if (k & 0x10) == 0x10 { 0x1bu8 } else { 0u8 })
        ^ (if (k & 0x20) == 0x20 { 0x6cu8 } else { 0u8 })
        ^ (if (k & 0x40) == 0x40 { 0xabu8 } else { 0u8 })
        ^ (if (k & 0x80) == 0x80 { 0x9au8 } else { 0u8 })) by (bit_vector);
}

// ===========================================================================
// ByteCombineSquared (upstream fields/large_fields.rs :283-313,
// blanket impl):
//     fn byte_combine_sq_slice(x: &[Self]) -> Self {
//         Self::byte_combine(&Self::square_byte(x)) }
//     fn byte_combine_bits_sq(x: u8) -> Self {
//         Self::byte_combine_bits(GF8::square_bits(x)) }
// Derived GF128-axis faces, composed over the FA3 combine twins and
// (for the bits face) the FA2 GF8 square exec.
// ===========================================================================

/// Byte-level spec face of GF8::square_bits (the FA2 spread model,
/// byte-truncated; the truncation is lossless by
/// lemma_spread_byte_range).
pub open spec fn gf8_sq_bits_u8(x: u8) -> u8 {
    gf8_ref_square_spread(x as u16) as u8
}

/// ByteCombineSquared::byte_combine_bits_sq (upstream :302-313, the
/// bits arm).
pub exec fn gf128_byte_combine_bits_sq(x: u8) -> (res: u128)
    ensures
        res == gf128_byte_combine_bits_spec(gf8_sq_bits_u8(x)),
{
    proof {
        lemma_gf8_sq_linear(x);
        lemma_spread_byte_range(x);
    }
    let sq: u8 = gf8_square_bits(x);
    let res: u128 = gf128_byte_combine_bits(sq);
    res
}

/// ByteCombineSquared::byte_combine_sq_slice (upstream :302-305, the
/// slice arm: byte_combine of the squared tag vector).
pub exec fn gf128_byte_combine_sq_slice(x: &[u128]) -> (res: u128)
    requires
        x.len() == 8,
    ensures
        res == gf128_byte_combine_spec(
            sqb_slot8(0, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot8(1, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot8(2, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot8(3, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot8(4, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot8(5, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot8(6, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot8(7, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
        ),
{
    let x0 = x[0];
    let x1 = x[1];
    let x2 = x[2];
    let x3 = x[3];
    let x4 = x[4];
    let x5 = x[5];
    let x6 = x[6];
    let x7 = x[7];
    let sq: [u128; 8] = gf128_square_byte8(x0, x1, x2, x3, x4, x5, x6, x7);
    gf128_byte_combine(
        sq[0], sq[1], sq[2], sq[3], sq[4], sq[5], sq[6], sq[7],
    )
}


// ===========================================================================
// (4)(5) the GF192 pair axis: SquareBytes + ByteCombineSquared with
// their ByteCombine carriers and from_bit. Upstream bodies: the
// generic BigGF ByteCombine (:375-402), FromBit (:363-371),
// SquareBytes (:236-276) and ByteCombineSquared (:300-313) blankets
// -- identical per-axis shapes; the pair-plane lowering is the
// limb-wise reading of every element operation (Field::ZERO is the
// pair (0, 0), Field::ONE the pair (1, 0), `+` the limb xor; the
// GF256 twin below is the mirrored face set).
// ===========================================================================

/// Pair-plane spec face of the SquareBytes slot map (the upstream
/// square matrix of GF(2^8) applied per field element; the Square-
/// Bytes blanket :240-251 spelled slot by slot. On the pair axes the
/// element adds decompose into the same column expression per limb).
/// Used by both GF192 and GF256.
pub open spec fn sqb_slot_pair(
    i: int,
    x0: (u128, u128),
    x1: (u128, u128),
    x2: (u128, u128),
    x3: (u128, u128),
    x4: (u128, u128),
    x5: (u128, u128),
    x6: (u128, u128),
    x7: (u128, u128),
) -> (u128, u128) {
    (
        sqb_slot8(i, x0.0, x1.0, x2.0, x3.0, x4.0, x5.0, x6.0, x7.0),
        sqb_slot8(i, x0.1, x1.1, x2.1, x3.1, x4.1, x5.1, x6.1, x7.1),
    )
}


// ===========================================================================

/// FromBit for GF192 (upstream trait :315-319 + generic BigGF body
/// :361-371): the bit-0 masked ONE (the element (1, 0)); consumed by
/// prover/encryption.rs :167 invnorm_to_conjugates at the pair axes.
pub exec fn gf192_from_bit(x: u8) -> (res: (u128, u128))
    ensures
        (x & 1) == 1 ==> res == GF192_ONE,
        (x & 1) == 0 ==> res == GF192_ZERO,
{
    if (x & 1) == 1 {
        GF192_ONE
    } else {
        GF192_ZERO
    }
}

// ---------------------------------------------------------------------------
// GF192 ByteCombine carriers (the combine_sq dependency closure).
// ---------------------------------------------------------------------------

/// Spec face of byte_combine for GF192 (upstream generic body
/// :381-385): x0 ^ mul(ALPHA[0], x1) ^ ... ^ mul(ALPHA[6], x7), the
/// products by gf192_mul_spec over the pair limbs, the sums by the
/// limb-wise xor.
pub open spec fn gf192_byte_combine_spec(
    x0: (u128, u128),
    x1: (u128, u128),
    x2: (u128, u128),
    x3: (u128, u128),
    x4: (u128, u128),
    x5: (u128, u128),
    x6: (u128, u128),
    x7: (u128, u128),
) -> (u128, u128) {
    let a0 = GF192_ALPHA[0];
    let a1 = GF192_ALPHA[1];
    let a2 = GF192_ALPHA[2];
    let a3 = GF192_ALPHA[3];
    let a4 = GF192_ALPHA[4];
    let a5 = GF192_ALPHA[5];
    let a6 = GF192_ALPHA[6];
    let m1 = gf192_mul_spec(a0.0, a0.1, x1.0, x1.1);
    let m2 = gf192_mul_spec(a1.0, a1.1, x2.0, x2.1);
    let m3 = gf192_mul_spec(a2.0, a2.1, x3.0, x3.1);
    let m4 = gf192_mul_spec(a3.0, a3.1, x4.0, x4.1);
    let m5 = gf192_mul_spec(a4.0, a4.1, x5.0, x5.1);
    let m6 = gf192_mul_spec(a5.0, a5.1, x6.0, x6.1);
    let m7 = gf192_mul_spec(a6.0, a6.1, x7.0, x7.1);
    (
        x0.0 ^ m1.0 ^ m2.0 ^ m3.0 ^ m4.0 ^ m5.0 ^ m6.0 ^ m7.0,
        x0.1 ^ m1.1 ^ m2.1 ^ m3.1 ^ m4.1 ^ m5.1 ^ m6.1 ^ m7.1,
    )
}

/// byte_combine (upstream :381-385) at the GF192 axis: the fold
/// unrolled in the upstream accumulation order (x0 first, then the
/// seven alpha products left to right).
pub exec fn gf192_byte_combine(
    x0: (u128, u128),
    x1: (u128, u128),
    x2: (u128, u128),
    x3: (u128, u128),
    x4: (u128, u128),
    x5: (u128, u128),
    x6: (u128, u128),
    x7: (u128, u128),
) -> (res: (u128, u128))
    ensures
        res == gf192_byte_combine_spec(x0, x1, x2, x3, x4, x5, x6, x7),
{
    let (x0l, x0h) = x0;
    let (x1l, x1h) = x1;
    let (x2l, x2h) = x2;
    let (x3l, x3h) = x3;
    let (x4l, x4h) = x4;
    let (x5l, x5h) = x5;
    let (x6l, x6h) = x6;
    let (x7l, x7h) = x7;
    let (a0l, a0h) = GF192_ALPHA[0];
    let (a1l, a1h) = GF192_ALPHA[1];
    let (a2l, a2h) = GF192_ALPHA[2];
    let (a3l, a3h) = GF192_ALPHA[3];
    let (a4l, a4h) = GF192_ALPHA[4];
    let (a5l, a5h) = GF192_ALPHA[5];
    let (a6l, a6h) = GF192_ALPHA[6];
    let (m1l, m1h) = gf192_mul(a0l, a0h, x1l, x1h);
    let (m2l, m2h) = gf192_mul(a1l, a1h, x2l, x2h);
    let (m3l, m3h) = gf192_mul(a2l, a2h, x3l, x3h);
    let (m4l, m4h) = gf192_mul(a3l, a3h, x4l, x4h);
    let (m5l, m5h) = gf192_mul(a4l, a4h, x5l, x5h);
    let (m6l, m6h) = gf192_mul(a5l, a5h, x6l, x6h);
    let (m7l, m7h) = gf192_mul(a6l, a6h, x7l, x7h);
    (
        x0l ^ m1l ^ m2l ^ m3l ^ m4l ^ m5l ^ m6l ^ m7l,
        x0h ^ m1h ^ m2h ^ m3h ^ m4h ^ m5h ^ m6h ^ m7h,
    )
}

/// GF192 byte_combine_slice (upstream :388-394): the slice form of
/// the canonical face (the upstream debug_assert lowers to the
/// requires; the value contract is byte_combine's, slice-index
/// aligned).
pub exec fn gf192_byte_combine_slice(x: &[(u128, u128)]) -> (res: (u128, u128))
    requires
        x.len() == 8,
    ensures
        res == gf192_byte_combine_spec(
            x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7],
        ),
{
    gf192_byte_combine(
        x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7],
    )
}

/// Spec face of byte_combine_bits for GF192 (upstream :396-401): the
/// bits select ONE or ALPHA[i-1] by position (the same widened-view
/// bit projections as the GF128 spec face; ONE is the pair (1, 0),
/// so the whole bit-0 selection lives in the low limb).
pub open spec fn gf192_byte_combine_bits_spec(x: u8) -> (u128, u128) {
    let a0 = GF192_ALPHA[0];
    let a1 = GF192_ALPHA[1];
    let a2 = GF192_ALPHA[2];
    let a3 = GF192_ALPHA[3];
    let a4 = GF192_ALPHA[4];
    let a5 = GF192_ALPHA[5];
    let a6 = GF192_ALPHA[6];
    (
        (if ((x as u128) & 1) == 1 { GF192_ONE.0 } else { 0u128 })
            ^ (if ((x as u128) >> 1) & 1 == 1 { a0.0 } else { 0u128 })
            ^ (if ((x as u128) >> 2) & 1 == 1 { a1.0 } else { 0u128 })
            ^ (if ((x as u128) >> 3) & 1 == 1 { a2.0 } else { 0u128 })
            ^ (if ((x as u128) >> 4) & 1 == 1 { a3.0 } else { 0u128 })
            ^ (if ((x as u128) >> 5) & 1 == 1 { a4.0 } else { 0u128 })
            ^ (if ((x as u128) >> 6) & 1 == 1 { a5.0 } else { 0u128 })
            ^ (if ((x as u128) >> 7) & 1 == 1 { a6.0 } else { 0u128 }),
        (if ((x as u128) & 1) == 1 { GF192_ONE.1 } else { 0u128 })
            ^ (if ((x as u128) >> 1) & 1 == 1 { a0.1 } else { 0u128 })
            ^ (if ((x as u128) >> 2) & 1 == 1 { a1.1 } else { 0u128 })
            ^ (if ((x as u128) >> 3) & 1 == 1 { a2.1 } else { 0u128 })
            ^ (if ((x as u128) >> 4) & 1 == 1 { a3.1 } else { 0u128 })
            ^ (if ((x as u128) >> 5) & 1 == 1 { a4.1 } else { 0u128 })
            ^ (if ((x as u128) >> 6) & 1 == 1 { a5.1 } else { 0u128 })
            ^ (if ((x as u128) >> 7) & 1 == 1 { a6.1 } else { 0u128 }),
    )
}

/// Partial-accumulation spec fn for the gf192 bit fold (private
/// helper of the exec invariant; i counts the folded alpha terms;
/// same widened-view bit projections as the spec face).
spec fn partial_bits_sum_gf192(x: u8, i: nat) -> (u128, u128)
    decreases i,
{
    if i == 0 {
        (if ((x as u128) & 1) == 1 { 1u128 } else { 0u128 }, 0u128)
    } else {
        let prev = partial_bits_sum_gf192(x, (i - 1) as nat);
        (
            prev.0
                ^ (if ((x as u128) >> (i as int)) & 1 == 1 {
                    GF192_ALPHA[(i - 1) as int].0
                } else { 0u128 }),
            prev.1
                ^ (if ((x as u128) >> (i as int)) & 1 == 1 {
                    GF192_ALPHA[(i - 1) as int].1
                } else { 0u128 }),
        )
    }
}

/// Definitional unfold of the gf192 partial pair fold at positive
/// fold count (limb-wise conjuncts).
proof fn unfold_bits_sum_gf192(x: u8, i: nat)
    requires
        0 < i <= 7,
    ensures
        partial_bits_sum_gf192(x, i).0
            == partial_bits_sum_gf192(x, (i - 1) as nat).0
                ^ (if ((x as u128) >> (i as int)) & 1 == 1 {
                    GF192_ALPHA[(i - 1) as int].0
                } else { 0u128 }),
        partial_bits_sum_gf192(x, i).1
            == partial_bits_sum_gf192(x, (i - 1) as nat).1
                ^ (if ((x as u128) >> (i as int)) & 1 == 1 {
                    GF192_ALPHA[(i - 1) as int].1
                } else { 0u128 }),
{
}

/// byte_combine_bits (upstream :396-401) at the GF192 axis: the
/// enumerate-fold as the GF128 twin's loop shape (index run over the
/// ALPHA entries; ONE.bit0 selection first, then the seven alpha
/// selections in accumulation order).
pub exec fn gf192_byte_combine_bits(x: u8) -> (res: (u128, u128))
    ensures
        res == gf192_byte_combine_bits_spec(x),
{
    let mut s0: u128 = if ((x as u128) & 1) == 1 { 1u128 } else { 0u128 };
    let mut s1: u128 = 0u128;
    proof {
        assert((s0, s1) == partial_bits_sum_gf192(x, 0nat));
    }
    let mut i: usize = 0;
    while i < 7
        invariant
            0 <= i <= 7,
            (s0, s1) == partial_bits_sum_gf192(x, i as nat),
        decreases 7 - i,
    {
        proof {
            unfold_bits_sum_gf192(x, (i + 1) as nat);
        }
        let c: u128 = ((x as u128) >> (i + 1)) & 1;
        let (al, ah) = GF192_ALPHA[i];
        let term0: u128 = if c == 1 {
            al
        } else {
            0u128
        };
        let term1: u128 = if c == 1 {
            ah
        } else {
            0u128
        };
        proof {
            assert(al == GF192_ALPHA[i as int].0);
            assert(ah == GF192_ALPHA[i as int].1);
            assert(term0
                == (if ((x as u128) >> ((i + 1) as int)) & 1 == 1 {
                    GF192_ALPHA[i as int].0
                } else { 0u128 }));
            assert(term1
                == (if ((x as u128) >> ((i + 1) as int)) & 1 == 1 {
                    GF192_ALPHA[i as int].1
                } else { 0u128 }));
        }
        s0 = s0 ^ term0;
        s1 = s1 ^ term1;
        i += 1;
    }
    proof {
        assert((s0, s1) == partial_bits_sum_gf192(x, 7nat));
        // structural chain: the partial fold unfolds to its base and
        // matches the spec projections one by one (the GF128 twin's
        // end-of-loop ladder; every unfold is definitional)
        assert(partial_bits_sum_gf192(x, 1nat).0
            == partial_bits_sum_gf192(x, 0nat).0
                ^ (if ((x as u128) >> 1) & 1 == 1 { GF192_ALPHA[0].0 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 1nat);
        }
        assert(partial_bits_sum_gf192(x, 1nat).1
            == partial_bits_sum_gf192(x, 0nat).1
                ^ (if ((x as u128) >> 1) & 1 == 1 { GF192_ALPHA[0].1 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 1nat);
        }
        assert(partial_bits_sum_gf192(x, 2nat).0
            == partial_bits_sum_gf192(x, 1nat).0
                ^ (if ((x as u128) >> 2) & 1 == 1 { GF192_ALPHA[1].0 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 2nat);
        }
        assert(partial_bits_sum_gf192(x, 2nat).1
            == partial_bits_sum_gf192(x, 1nat).1
                ^ (if ((x as u128) >> 2) & 1 == 1 { GF192_ALPHA[1].1 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 2nat);
        }
        assert(partial_bits_sum_gf192(x, 3nat).0
            == partial_bits_sum_gf192(x, 2nat).0
                ^ (if ((x as u128) >> 3) & 1 == 1 { GF192_ALPHA[2].0 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 3nat);
        }
        assert(partial_bits_sum_gf192(x, 3nat).1
            == partial_bits_sum_gf192(x, 2nat).1
                ^ (if ((x as u128) >> 3) & 1 == 1 { GF192_ALPHA[2].1 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 3nat);
        }
        assert(partial_bits_sum_gf192(x, 4nat).0
            == partial_bits_sum_gf192(x, 3nat).0
                ^ (if ((x as u128) >> 4) & 1 == 1 { GF192_ALPHA[3].0 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 4nat);
        }
        assert(partial_bits_sum_gf192(x, 4nat).1
            == partial_bits_sum_gf192(x, 3nat).1
                ^ (if ((x as u128) >> 4) & 1 == 1 { GF192_ALPHA[3].1 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 4nat);
        }
        assert(partial_bits_sum_gf192(x, 5nat).0
            == partial_bits_sum_gf192(x, 4nat).0
                ^ (if ((x as u128) >> 5) & 1 == 1 { GF192_ALPHA[4].0 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 5nat);
        }
        assert(partial_bits_sum_gf192(x, 5nat).1
            == partial_bits_sum_gf192(x, 4nat).1
                ^ (if ((x as u128) >> 5) & 1 == 1 { GF192_ALPHA[4].1 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 5nat);
        }
        assert(partial_bits_sum_gf192(x, 6nat).0
            == partial_bits_sum_gf192(x, 5nat).0
                ^ (if ((x as u128) >> 6) & 1 == 1 { GF192_ALPHA[5].0 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 6nat);
        }
        assert(partial_bits_sum_gf192(x, 6nat).1
            == partial_bits_sum_gf192(x, 5nat).1
                ^ (if ((x as u128) >> 6) & 1 == 1 { GF192_ALPHA[5].1 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 6nat);
        }
        assert(partial_bits_sum_gf192(x, 7nat).0
            == partial_bits_sum_gf192(x, 6nat).0
                ^ (if ((x as u128) >> 7) & 1 == 1 { GF192_ALPHA[6].0 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 7nat);
        }
        assert(partial_bits_sum_gf192(x, 7nat).1
            == partial_bits_sum_gf192(x, 6nat).1
                ^ (if ((x as u128) >> 7) & 1 == 1 { GF192_ALPHA[6].1 } else { 0u128 })) by {
            unfold_bits_sum_gf192(x, 7nat);
        }
        assert(partial_bits_sum_gf192(x, 7nat)
            == gf192_byte_combine_bits_spec(x));
    }
    (s0, s1)
}

// ---------------------------------------------------------------------------
// GF192 SquareBytes + ByteCombineSquared (the family items 4/5).
// ---------------------------------------------------------------------------

/// GF192 SquareBytes::square_byte (upstream :240-251), scalar-slot
/// form at the pair axis: the same eight column formulas per element,
/// composed limb-wise through the verified pure GF128 twin (value-
/// identical: the pair-plane element add is the limb xor).
pub exec fn gf192_square_byte8(
    x0: (u128, u128),
    x1: (u128, u128),
    x2: (u128, u128),
    x3: (u128, u128),
    x4: (u128, u128),
    x5: (u128, u128),
    x6: (u128, u128),
    x7: (u128, u128),
) -> (sq: [(u128, u128); 8])
    ensures
        sq[0] == sqb_slot_pair(0, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[1] == sqb_slot_pair(1, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[2] == sqb_slot_pair(2, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[3] == sqb_slot_pair(3, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[4] == sqb_slot_pair(4, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[5] == sqb_slot_pair(5, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[6] == sqb_slot_pair(6, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[7] == sqb_slot_pair(7, x0, x1, x2, x3, x4, x5, x6, x7),
{
    let (x0l, x0h) = x0;
    let (x1l, x1h) = x1;
    let (x2l, x2h) = x2;
    let (x3l, x3h) = x3;
    let (x4l, x4h) = x4;
    let (x5l, x5h) = x5;
    let (x6l, x6h) = x6;
    let (x7l, x7h) = x7;
    proof {
        assert(x0l == x0.0);
        assert(x0h == x0.1);
        assert(x1l == x1.0);
        assert(x1h == x1.1);
        assert(x2l == x2.0);
        assert(x2h == x2.1);
        assert(x3l == x3.0);
        assert(x3h == x3.1);
        assert(x4l == x4.0);
        assert(x4h == x4.1);
        assert(x5l == x5.0);
        assert(x5h == x5.1);
        assert(x6l == x6.0);
        assert(x6h == x6.1);
        assert(x7l == x7.0);
        assert(x7h == x7.1);
    }
    let lo = gf128_square_byte8(x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l);
    let hi = gf128_square_byte8(x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h);
    proof {
        assert(lo[0] == sqb_slot8(0, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[1] == sqb_slot8(1, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[2] == sqb_slot8(2, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[3] == sqb_slot8(3, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[4] == sqb_slot8(4, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[5] == sqb_slot8(5, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[6] == sqb_slot8(6, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[7] == sqb_slot8(7, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(hi[0] == sqb_slot8(0, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[1] == sqb_slot8(1, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[2] == sqb_slot8(2, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[3] == sqb_slot8(3, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[4] == sqb_slot8(4, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[5] == sqb_slot8(5, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[6] == sqb_slot8(6, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[7] == sqb_slot8(7, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
    }
    [
        (lo[0], hi[0]),
        (lo[1], hi[1]),
        (lo[2], hi[2]),
        (lo[3], hi[3]),
        (lo[4], hi[4]),
        (lo[5], hi[5]),
        (lo[6], hi[6]),
        (lo[7], hi[7]),
    ]
}

/// GF192 SquareBytes::square_byte_inplace (upstream :252-275),
/// read-compute-write lowering: the upstream body juggles the
/// in-place mutation chain with the (i2,i4,i5,i6) snapshot reads; the
/// twin reads the eight elements, applies the pure square map limb-
/// wise and writes the slots back -- the slot contract is the same
/// sqb_slot_pair face (value-identical; the deviation trades the
/// mutation-chain re-derivation for the verified pure faces, the
/// FA6-pre ByteCommitment::square_inplace tag-slice precedent).
pub exec fn gf192_square_byte_inplace(x: &mut [(u128, u128)])
    requires
        old(x).len() == 8,
    ensures
        final(x)[0] == sqb_slot_pair(0, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[1] == sqb_slot_pair(1, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[2] == sqb_slot_pair(2, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[3] == sqb_slot_pair(3, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[4] == sqb_slot_pair(4, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[5] == sqb_slot_pair(5, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[6] == sqb_slot_pair(6, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[7] == sqb_slot_pair(7, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
{
    let x0 = x[0];
    let x1 = x[1];
    let x2 = x[2];
    let x3 = x[3];
    let x4 = x[4];
    let x5 = x[5];
    let x6 = x[6];
    let x7 = x[7];
    proof {
        assert(x0 == old(x)[0]);
        assert(x1 == old(x)[1]);
        assert(x2 == old(x)[2]);
        assert(x3 == old(x)[3]);
        assert(x4 == old(x)[4]);
        assert(x5 == old(x)[5]);
        assert(x6 == old(x)[6]);
        assert(x7 == old(x)[7]);
    }
    let lo_arr = gf128_square_byte8(x0.0, x1.0, x2.0, x3.0, x4.0, x5.0, x6.0, x7.0);
    let hi_arr = gf128_square_byte8(x0.1, x1.1, x2.1, x3.1, x4.1, x5.1, x6.1, x7.1);
    x[0] = (lo_arr[0], hi_arr[0]);
    x[1] = (lo_arr[1], hi_arr[1]);
    x[2] = (lo_arr[2], hi_arr[2]);
    x[3] = (lo_arr[3], hi_arr[3]);
    x[4] = (lo_arr[4], hi_arr[4]);
    x[5] = (lo_arr[5], hi_arr[5]);
    x[6] = (lo_arr[6], hi_arr[6]);
    x[7] = (lo_arr[7], hi_arr[7]);
    proof {
        assert(final(x)[0] == sqb_slot_pair(0, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[1] == sqb_slot_pair(1, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[2] == sqb_slot_pair(2, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[3] == sqb_slot_pair(3, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[4] == sqb_slot_pair(4, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[5] == sqb_slot_pair(5, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[6] == sqb_slot_pair(6, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[7] == sqb_slot_pair(7, x0, x1, x2, x3, x4, x5, x6, x7));
    }
}

/// GF192 ByteCombineSquared::byte_combine_bits_sq (upstream blanket
/// :310-312, the bits arm): byte_combine_bits(GF8::square_bits(x)).
pub exec fn gf192_byte_combine_bits_sq(x: u8) -> (res: (u128, u128))
    ensures
        res == gf192_byte_combine_bits_spec(gf8_sq_bits_u8(x)),
{
    proof {
        lemma_gf8_sq_linear(x);
        lemma_spread_byte_range(x);
    }
    gf192_byte_combine_bits(gf8_square_bits(x))
}

/// GF192 ByteCombineSquared::byte_combine_sq_slice (upstream blanket
/// :306-308, the slice arm): byte_combine of the squared element
/// vector.
pub exec fn gf192_byte_combine_sq_slice(x: &[(u128, u128)]) -> (res: (u128, u128))
    requires
        x.len() == 8,
    ensures
        res == gf192_byte_combine_spec(
            sqb_slot_pair(0, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(1, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(2, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(3, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(4, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(5, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(6, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(7, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
        ),
{
    let x0 = x[0];
    let x1 = x[1];
    let x2 = x[2];
    let x3 = x[3];
    let x4 = x[4];
    let x5 = x[5];
    let x6 = x[6];
    let x7 = x[7];
    let s = gf192_square_byte8(x0, x1, x2, x3, x4, x5, x6, x7);
    gf192_byte_combine(s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7])
}

// ===========================================================================
// (4)(5) the GF256 pair axis (the mirrored face set of the GF192 half
// above; upstream anchors identical -- the blankets are axis-blind).
// ===========================================================================

/// FromBit for GF256 (upstream trait :315-319 + generic BigGF body
/// :361-371): the bit-0 masked ONE (the element (1, 0)); consumed by
/// prover/encryption.rs :167 invnorm_to_conjugates at the pair axes.
pub exec fn gf256_from_bit(x: u8) -> (res: (u128, u128))
    ensures
        (x & 1) == 1 ==> res == GF256_ONE,
        (x & 1) == 0 ==> res == GF256_ZERO,
{
    if (x & 1) == 1 {
        GF256_ONE
    } else {
        GF256_ZERO
    }
}

// ---------------------------------------------------------------------------
// GF256 ByteCombine carriers (the combine_sq dependency closure).
// ---------------------------------------------------------------------------

/// Spec face of byte_combine for GF256 (upstream generic body
/// :381-385): x0 ^ mul(ALPHA[0], x1) ^ ... ^ mul(ALPHA[6], x7), the
/// products by gf256_mul_spec over the pair limbs, the sums by the
/// limb-wise xor.
pub open spec fn gf256_byte_combine_spec(
    x0: (u128, u128),
    x1: (u128, u128),
    x2: (u128, u128),
    x3: (u128, u128),
    x4: (u128, u128),
    x5: (u128, u128),
    x6: (u128, u128),
    x7: (u128, u128),
) -> (u128, u128) {
    let a0 = GF256_ALPHA[0];
    let a1 = GF256_ALPHA[1];
    let a2 = GF256_ALPHA[2];
    let a3 = GF256_ALPHA[3];
    let a4 = GF256_ALPHA[4];
    let a5 = GF256_ALPHA[5];
    let a6 = GF256_ALPHA[6];
    let m1 = gf256_mul_spec(a0.0, a0.1, x1.0, x1.1);
    let m2 = gf256_mul_spec(a1.0, a1.1, x2.0, x2.1);
    let m3 = gf256_mul_spec(a2.0, a2.1, x3.0, x3.1);
    let m4 = gf256_mul_spec(a3.0, a3.1, x4.0, x4.1);
    let m5 = gf256_mul_spec(a4.0, a4.1, x5.0, x5.1);
    let m6 = gf256_mul_spec(a5.0, a5.1, x6.0, x6.1);
    let m7 = gf256_mul_spec(a6.0, a6.1, x7.0, x7.1);
    (
        x0.0 ^ m1.0 ^ m2.0 ^ m3.0 ^ m4.0 ^ m5.0 ^ m6.0 ^ m7.0,
        x0.1 ^ m1.1 ^ m2.1 ^ m3.1 ^ m4.1 ^ m5.1 ^ m6.1 ^ m7.1,
    )
}

/// byte_combine (upstream :381-385) at the GF256 axis: the fold
/// unrolled in the upstream accumulation order (x0 first, then the
/// seven alpha products left to right).
pub exec fn gf256_byte_combine(
    x0: (u128, u128),
    x1: (u128, u128),
    x2: (u128, u128),
    x3: (u128, u128),
    x4: (u128, u128),
    x5: (u128, u128),
    x6: (u128, u128),
    x7: (u128, u128),
) -> (res: (u128, u128))
    ensures
        res == gf256_byte_combine_spec(x0, x1, x2, x3, x4, x5, x6, x7),
{
    let (x0l, x0h) = x0;
    let (x1l, x1h) = x1;
    let (x2l, x2h) = x2;
    let (x3l, x3h) = x3;
    let (x4l, x4h) = x4;
    let (x5l, x5h) = x5;
    let (x6l, x6h) = x6;
    let (x7l, x7h) = x7;
    let (a0l, a0h) = GF256_ALPHA[0];
    let (a1l, a1h) = GF256_ALPHA[1];
    let (a2l, a2h) = GF256_ALPHA[2];
    let (a3l, a3h) = GF256_ALPHA[3];
    let (a4l, a4h) = GF256_ALPHA[4];
    let (a5l, a5h) = GF256_ALPHA[5];
    let (a6l, a6h) = GF256_ALPHA[6];
    let (m1l, m1h) = gf256_mul(a0l, a0h, x1l, x1h);
    let (m2l, m2h) = gf256_mul(a1l, a1h, x2l, x2h);
    let (m3l, m3h) = gf256_mul(a2l, a2h, x3l, x3h);
    let (m4l, m4h) = gf256_mul(a3l, a3h, x4l, x4h);
    let (m5l, m5h) = gf256_mul(a4l, a4h, x5l, x5h);
    let (m6l, m6h) = gf256_mul(a5l, a5h, x6l, x6h);
    let (m7l, m7h) = gf256_mul(a6l, a6h, x7l, x7h);
    (
        x0l ^ m1l ^ m2l ^ m3l ^ m4l ^ m5l ^ m6l ^ m7l,
        x0h ^ m1h ^ m2h ^ m3h ^ m4h ^ m5h ^ m6h ^ m7h,
    )
}

/// GF256 byte_combine_slice (upstream :388-394): the slice form of
/// the canonical face (the upstream debug_assert lowers to the
/// requires; the value contract is byte_combine's, slice-index
/// aligned).
pub exec fn gf256_byte_combine_slice(x: &[(u128, u128)]) -> (res: (u128, u128))
    requires
        x.len() == 8,
    ensures
        res == gf256_byte_combine_spec(
            x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7],
        ),
{
    gf256_byte_combine(
        x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7],
    )
}

/// Spec face of byte_combine_bits for GF256 (upstream :396-401): the
/// bits select ONE or ALPHA[i-1] by position (the same widened-view
/// bit projections as the GF128 spec face; ONE is the pair (1, 0),
/// so the whole bit-0 selection lives in the low limb).
pub open spec fn gf256_byte_combine_bits_spec(x: u8) -> (u128, u128) {
    let a0 = GF256_ALPHA[0];
    let a1 = GF256_ALPHA[1];
    let a2 = GF256_ALPHA[2];
    let a3 = GF256_ALPHA[3];
    let a4 = GF256_ALPHA[4];
    let a5 = GF256_ALPHA[5];
    let a6 = GF256_ALPHA[6];
    (
        (if ((x as u128) & 1) == 1 { GF256_ONE.0 } else { 0u128 })
            ^ (if ((x as u128) >> 1) & 1 == 1 { a0.0 } else { 0u128 })
            ^ (if ((x as u128) >> 2) & 1 == 1 { a1.0 } else { 0u128 })
            ^ (if ((x as u128) >> 3) & 1 == 1 { a2.0 } else { 0u128 })
            ^ (if ((x as u128) >> 4) & 1 == 1 { a3.0 } else { 0u128 })
            ^ (if ((x as u128) >> 5) & 1 == 1 { a4.0 } else { 0u128 })
            ^ (if ((x as u128) >> 6) & 1 == 1 { a5.0 } else { 0u128 })
            ^ (if ((x as u128) >> 7) & 1 == 1 { a6.0 } else { 0u128 }),
        (if ((x as u128) & 1) == 1 { GF256_ONE.1 } else { 0u128 })
            ^ (if ((x as u128) >> 1) & 1 == 1 { a0.1 } else { 0u128 })
            ^ (if ((x as u128) >> 2) & 1 == 1 { a1.1 } else { 0u128 })
            ^ (if ((x as u128) >> 3) & 1 == 1 { a2.1 } else { 0u128 })
            ^ (if ((x as u128) >> 4) & 1 == 1 { a3.1 } else { 0u128 })
            ^ (if ((x as u128) >> 5) & 1 == 1 { a4.1 } else { 0u128 })
            ^ (if ((x as u128) >> 6) & 1 == 1 { a5.1 } else { 0u128 })
            ^ (if ((x as u128) >> 7) & 1 == 1 { a6.1 } else { 0u128 }),
    )
}

/// Partial-accumulation spec fn for the gf256 bit fold (private
/// helper of the exec invariant; i counts the folded alpha terms;
/// same widened-view bit projections as the spec face).
spec fn partial_bits_sum_gf256(x: u8, i: nat) -> (u128, u128)
    decreases i,
{
    if i == 0 {
        (if ((x as u128) & 1) == 1 { 1u128 } else { 0u128 }, 0u128)
    } else {
        let prev = partial_bits_sum_gf256(x, (i - 1) as nat);
        (
            prev.0
                ^ (if ((x as u128) >> (i as int)) & 1 == 1 {
                    GF256_ALPHA[(i - 1) as int].0
                } else { 0u128 }),
            prev.1
                ^ (if ((x as u128) >> (i as int)) & 1 == 1 {
                    GF256_ALPHA[(i - 1) as int].1
                } else { 0u128 }),
        )
    }
}

/// Definitional unfold of the gf256 partial pair fold at positive
/// fold count (limb-wise conjuncts).
proof fn unfold_bits_sum_gf256(x: u8, i: nat)
    requires
        0 < i <= 7,
    ensures
        partial_bits_sum_gf256(x, i).0
            == partial_bits_sum_gf256(x, (i - 1) as nat).0
                ^ (if ((x as u128) >> (i as int)) & 1 == 1 {
                    GF256_ALPHA[(i - 1) as int].0
                } else { 0u128 }),
        partial_bits_sum_gf256(x, i).1
            == partial_bits_sum_gf256(x, (i - 1) as nat).1
                ^ (if ((x as u128) >> (i as int)) & 1 == 1 {
                    GF256_ALPHA[(i - 1) as int].1
                } else { 0u128 }),
{
}

/// byte_combine_bits (upstream :396-401) at the GF256 axis: the
/// enumerate-fold as the GF128 twin's loop shape (index run over the
/// ALPHA entries; ONE.bit0 selection first, then the seven alpha
/// selections in accumulation order).
pub exec fn gf256_byte_combine_bits(x: u8) -> (res: (u128, u128))
    ensures
        res == gf256_byte_combine_bits_spec(x),
{
    let mut s0: u128 = if ((x as u128) & 1) == 1 { 1u128 } else { 0u128 };
    let mut s1: u128 = 0u128;
    proof {
        assert((s0, s1) == partial_bits_sum_gf256(x, 0nat));
    }
    let mut i: usize = 0;
    while i < 7
        invariant
            0 <= i <= 7,
            (s0, s1) == partial_bits_sum_gf256(x, i as nat),
        decreases 7 - i,
    {
        proof {
            unfold_bits_sum_gf256(x, (i + 1) as nat);
        }
        let c: u128 = ((x as u128) >> (i + 1)) & 1;
        let (al, ah) = GF256_ALPHA[i];
        let term0: u128 = if c == 1 {
            al
        } else {
            0u128
        };
        let term1: u128 = if c == 1 {
            ah
        } else {
            0u128
        };
        proof {
            assert(al == GF256_ALPHA[i as int].0);
            assert(ah == GF256_ALPHA[i as int].1);
            assert(term0
                == (if ((x as u128) >> ((i + 1) as int)) & 1 == 1 {
                    GF256_ALPHA[i as int].0
                } else { 0u128 }));
            assert(term1
                == (if ((x as u128) >> ((i + 1) as int)) & 1 == 1 {
                    GF256_ALPHA[i as int].1
                } else { 0u128 }));
        }
        s0 = s0 ^ term0;
        s1 = s1 ^ term1;
        i += 1;
    }
    proof {
        assert((s0, s1) == partial_bits_sum_gf256(x, 7nat));
        // structural chain: the partial fold unfolds to its base and
        // matches the spec projections one by one (the GF128 twin's
        // end-of-loop ladder; every unfold is definitional)
        assert(partial_bits_sum_gf256(x, 1nat).0
            == partial_bits_sum_gf256(x, 0nat).0
                ^ (if ((x as u128) >> 1) & 1 == 1 { GF256_ALPHA[0].0 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 1nat);
        }
        assert(partial_bits_sum_gf256(x, 1nat).1
            == partial_bits_sum_gf256(x, 0nat).1
                ^ (if ((x as u128) >> 1) & 1 == 1 { GF256_ALPHA[0].1 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 1nat);
        }
        assert(partial_bits_sum_gf256(x, 2nat).0
            == partial_bits_sum_gf256(x, 1nat).0
                ^ (if ((x as u128) >> 2) & 1 == 1 { GF256_ALPHA[1].0 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 2nat);
        }
        assert(partial_bits_sum_gf256(x, 2nat).1
            == partial_bits_sum_gf256(x, 1nat).1
                ^ (if ((x as u128) >> 2) & 1 == 1 { GF256_ALPHA[1].1 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 2nat);
        }
        assert(partial_bits_sum_gf256(x, 3nat).0
            == partial_bits_sum_gf256(x, 2nat).0
                ^ (if ((x as u128) >> 3) & 1 == 1 { GF256_ALPHA[2].0 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 3nat);
        }
        assert(partial_bits_sum_gf256(x, 3nat).1
            == partial_bits_sum_gf256(x, 2nat).1
                ^ (if ((x as u128) >> 3) & 1 == 1 { GF256_ALPHA[2].1 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 3nat);
        }
        assert(partial_bits_sum_gf256(x, 4nat).0
            == partial_bits_sum_gf256(x, 3nat).0
                ^ (if ((x as u128) >> 4) & 1 == 1 { GF256_ALPHA[3].0 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 4nat);
        }
        assert(partial_bits_sum_gf256(x, 4nat).1
            == partial_bits_sum_gf256(x, 3nat).1
                ^ (if ((x as u128) >> 4) & 1 == 1 { GF256_ALPHA[3].1 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 4nat);
        }
        assert(partial_bits_sum_gf256(x, 5nat).0
            == partial_bits_sum_gf256(x, 4nat).0
                ^ (if ((x as u128) >> 5) & 1 == 1 { GF256_ALPHA[4].0 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 5nat);
        }
        assert(partial_bits_sum_gf256(x, 5nat).1
            == partial_bits_sum_gf256(x, 4nat).1
                ^ (if ((x as u128) >> 5) & 1 == 1 { GF256_ALPHA[4].1 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 5nat);
        }
        assert(partial_bits_sum_gf256(x, 6nat).0
            == partial_bits_sum_gf256(x, 5nat).0
                ^ (if ((x as u128) >> 6) & 1 == 1 { GF256_ALPHA[5].0 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 6nat);
        }
        assert(partial_bits_sum_gf256(x, 6nat).1
            == partial_bits_sum_gf256(x, 5nat).1
                ^ (if ((x as u128) >> 6) & 1 == 1 { GF256_ALPHA[5].1 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 6nat);
        }
        assert(partial_bits_sum_gf256(x, 7nat).0
            == partial_bits_sum_gf256(x, 6nat).0
                ^ (if ((x as u128) >> 7) & 1 == 1 { GF256_ALPHA[6].0 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 7nat);
        }
        assert(partial_bits_sum_gf256(x, 7nat).1
            == partial_bits_sum_gf256(x, 6nat).1
                ^ (if ((x as u128) >> 7) & 1 == 1 { GF256_ALPHA[6].1 } else { 0u128 })) by {
            unfold_bits_sum_gf256(x, 7nat);
        }
        assert(partial_bits_sum_gf256(x, 7nat)
            == gf256_byte_combine_bits_spec(x));
    }
    (s0, s1)
}

// ---------------------------------------------------------------------------
// GF256 SquareBytes + ByteCombineSquared (the family items 4/5).
// ---------------------------------------------------------------------------

/// GF256 SquareBytes::square_byte (upstream :240-251), scalar-slot
/// form at the pair axis: the same eight column formulas per element,
/// composed limb-wise through the verified pure GF128 twin (value-
/// identical: the pair-plane element add is the limb xor).
pub exec fn gf256_square_byte8(
    x0: (u128, u128),
    x1: (u128, u128),
    x2: (u128, u128),
    x3: (u128, u128),
    x4: (u128, u128),
    x5: (u128, u128),
    x6: (u128, u128),
    x7: (u128, u128),
) -> (sq: [(u128, u128); 8])
    ensures
        sq[0] == sqb_slot_pair(0, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[1] == sqb_slot_pair(1, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[2] == sqb_slot_pair(2, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[3] == sqb_slot_pair(3, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[4] == sqb_slot_pair(4, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[5] == sqb_slot_pair(5, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[6] == sqb_slot_pair(6, x0, x1, x2, x3, x4, x5, x6, x7),
        sq[7] == sqb_slot_pair(7, x0, x1, x2, x3, x4, x5, x6, x7),
{
    let (x0l, x0h) = x0;
    let (x1l, x1h) = x1;
    let (x2l, x2h) = x2;
    let (x3l, x3h) = x3;
    let (x4l, x4h) = x4;
    let (x5l, x5h) = x5;
    let (x6l, x6h) = x6;
    let (x7l, x7h) = x7;
    proof {
        assert(x0l == x0.0);
        assert(x0h == x0.1);
        assert(x1l == x1.0);
        assert(x1h == x1.1);
        assert(x2l == x2.0);
        assert(x2h == x2.1);
        assert(x3l == x3.0);
        assert(x3h == x3.1);
        assert(x4l == x4.0);
        assert(x4h == x4.1);
        assert(x5l == x5.0);
        assert(x5h == x5.1);
        assert(x6l == x6.0);
        assert(x6h == x6.1);
        assert(x7l == x7.0);
        assert(x7h == x7.1);
    }
    let lo = gf128_square_byte8(x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l);
    let hi = gf128_square_byte8(x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h);
    proof {
        assert(lo[0] == sqb_slot8(0, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[1] == sqb_slot8(1, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[2] == sqb_slot8(2, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[3] == sqb_slot8(3, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[4] == sqb_slot8(4, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[5] == sqb_slot8(5, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[6] == sqb_slot8(6, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(lo[7] == sqb_slot8(7, x0l, x1l, x2l, x3l, x4l, x5l, x6l, x7l));
        assert(hi[0] == sqb_slot8(0, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[1] == sqb_slot8(1, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[2] == sqb_slot8(2, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[3] == sqb_slot8(3, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[4] == sqb_slot8(4, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[5] == sqb_slot8(5, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[6] == sqb_slot8(6, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
        assert(hi[7] == sqb_slot8(7, x0h, x1h, x2h, x3h, x4h, x5h, x6h, x7h));
    }
    [
        (lo[0], hi[0]),
        (lo[1], hi[1]),
        (lo[2], hi[2]),
        (lo[3], hi[3]),
        (lo[4], hi[4]),
        (lo[5], hi[5]),
        (lo[6], hi[6]),
        (lo[7], hi[7]),
    ]
}

/// GF256 SquareBytes::square_byte_inplace (upstream :252-275),
/// read-compute-write lowering: the upstream body juggles the
/// in-place mutation chain with the (i2,i4,i5,i6) snapshot reads; the
/// twin reads the eight elements, applies the pure square map limb-
/// wise and writes the slots back -- the slot contract is the same
/// sqb_slot_pair face (value-identical; the deviation trades the
/// mutation-chain re-derivation for the verified pure faces, the
/// FA6-pre ByteCommitment::square_inplace tag-slice precedent).
pub exec fn gf256_square_byte_inplace(x: &mut [(u128, u128)])
    requires
        old(x).len() == 8,
    ensures
        final(x)[0] == sqb_slot_pair(0, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[1] == sqb_slot_pair(1, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[2] == sqb_slot_pair(2, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[3] == sqb_slot_pair(3, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[4] == sqb_slot_pair(4, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[5] == sqb_slot_pair(5, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[6] == sqb_slot_pair(6, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
        final(x)[7] == sqb_slot_pair(7, old(x)[0], old(x)[1], old(x)[2], old(x)[3], old(x)[4], old(x)[5], old(x)[6], old(x)[7]),
{
    let x0 = x[0];
    let x1 = x[1];
    let x2 = x[2];
    let x3 = x[3];
    let x4 = x[4];
    let x5 = x[5];
    let x6 = x[6];
    let x7 = x[7];
    proof {
        assert(x0 == old(x)[0]);
        assert(x1 == old(x)[1]);
        assert(x2 == old(x)[2]);
        assert(x3 == old(x)[3]);
        assert(x4 == old(x)[4]);
        assert(x5 == old(x)[5]);
        assert(x6 == old(x)[6]);
        assert(x7 == old(x)[7]);
    }
    let lo_arr = gf128_square_byte8(x0.0, x1.0, x2.0, x3.0, x4.0, x5.0, x6.0, x7.0);
    let hi_arr = gf128_square_byte8(x0.1, x1.1, x2.1, x3.1, x4.1, x5.1, x6.1, x7.1);
    x[0] = (lo_arr[0], hi_arr[0]);
    x[1] = (lo_arr[1], hi_arr[1]);
    x[2] = (lo_arr[2], hi_arr[2]);
    x[3] = (lo_arr[3], hi_arr[3]);
    x[4] = (lo_arr[4], hi_arr[4]);
    x[5] = (lo_arr[5], hi_arr[5]);
    x[6] = (lo_arr[6], hi_arr[6]);
    x[7] = (lo_arr[7], hi_arr[7]);
    proof {
        assert(final(x)[0] == sqb_slot_pair(0, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[1] == sqb_slot_pair(1, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[2] == sqb_slot_pair(2, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[3] == sqb_slot_pair(3, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[4] == sqb_slot_pair(4, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[5] == sqb_slot_pair(5, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[6] == sqb_slot_pair(6, x0, x1, x2, x3, x4, x5, x6, x7));
        assert(final(x)[7] == sqb_slot_pair(7, x0, x1, x2, x3, x4, x5, x6, x7));
    }
}

/// GF256 ByteCombineSquared::byte_combine_bits_sq (upstream blanket
/// :310-312, the bits arm): byte_combine_bits(GF8::square_bits(x)).
pub exec fn gf256_byte_combine_bits_sq(x: u8) -> (res: (u128, u128))
    ensures
        res == gf256_byte_combine_bits_spec(gf8_sq_bits_u8(x)),
{
    proof {
        lemma_gf8_sq_linear(x);
        lemma_spread_byte_range(x);
    }
    gf256_byte_combine_bits(gf8_square_bits(x))
}

/// GF256 ByteCombineSquared::byte_combine_sq_slice (upstream blanket
/// :306-308, the slice arm): byte_combine of the squared element
/// vector.
pub exec fn gf256_byte_combine_sq_slice(x: &[(u128, u128)]) -> (res: (u128, u128))
    requires
        x.len() == 8,
    ensures
        res == gf256_byte_combine_spec(
            sqb_slot_pair(0, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(1, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(2, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(3, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(4, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(5, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(6, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
            sqb_slot_pair(7, x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7]),
        ),
{
    let x0 = x[0];
    let x1 = x[1];
    let x2 = x[2];
    let x3 = x[3];
    let x4 = x[4];
    let x5 = x[5];
    let x6 = x[6];
    let x7 = x[7];
    let s = gf256_square_byte8(x0, x1, x2, x3, x4, x5, x6, x7);
    gf256_byte_combine(s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7])
}

} // verus!
