//! faest 0.3.0 -- Verus transcription of src/universal_hashing.rs,
//! batch FA6 (the leaf hash / VOLE hash / ZK hash / constraint-side
//! proof hasher family).
//!
//! Upstream: universal_hashing.rs (625 lines, pin 9ccc68c0):
//!   - the VOLE hasher family: VoleHasherInit (:25-43),
//!     VoleHasherProcess (:45-62), VoleHasher (:64-140);
//!   - the ZK hasher family: ZKHasherInit (:142-175), ZKHasherProcess
//!     (:177-186), ZKHasher (:188-222), ZKProofHasher (:224-305),
//!     ZKVerifyHasher (:307-356);
//!   - the leaf hasher: the LeafHasher trait (:358-373) and its three
//!     security-parameter instantiations LeafHasher128/192/256
//!     (:377-456);
//!   - the in-file test module (:458-625) rides the FA6 harness
//!     (verified/harness/ut_fa6.rs), not this twin.
//!
//! Representation lowering (trust boundary, FA2/FA3/FA6p
//! conventions; every deviation is anchored and classified):
//!   - The generic<F: BigGaloisField> trait faces instantiate at the
//!     three lambda axes GF128/GF192/GF256; each lambda gets concrete
//!     per-axis faces (the big-Galois-field values lower to u128 at
//!     lambda 128 and to the (u128, u128) limb pair at lambda 192/256
//!     -- the FA3 fields twin's plane). The trait declaration syntax
//!     drops at the trait boundary; the associated-type algebra
//!     (SDLength = Prod<Length, U5> + GF64::Length etc.) lowers to
//!     the concrete byte counts: VOLE sd 88/128/168, ZK sd 56/80/104,
//!     output Length+B = 18/26/34 (records at each site).
//!   - The Array<u8, N> carriers lower to [u8; N] / &[u8] (FA1
//!     convention); typenum BBits = U16 / B = U2 (upstream :20-23)
//!     record as the extra 2 output bytes of the VOLE hash.
//!   - The std ops dispatch lowers to the named fields twins' exec
//!     faces: F * F -> gf{128,192,256}_mul (verified == the FA3
//!     composition specs), F * GF64 -> the Mul<GF64> orbit faces
//!     gf128_mul_gf64 (FA3) and gf192/gf256_mul_gf64 (this twin,
//!     re-erected: the FA3 tree never landed the [u128; 2]-plane
//!     orbit; re-homing note in the file's orbit section), field add
//!     -> limb xor (characteristic 2, the FA3 Add record).
//!
//! The GF384/576/768 extension faces consumed by LeafHasher are the
//! FA3 wave-3 twins (exec == orbit models, every input). GF768
//! modulus note: the wave-3 transcription's literal 0x140011 was a
//! hand-decode slip of the upstream binary literal
//! 0b10100000000000010001 (== 0xA0011); corrected in the fields twin
//! (the interop-probe wave-2 seven-way cross-check), so the
//! leafhash_256 evidence pins carry directly.

use vstd::prelude::*;
use vstd::seq::Seq;

use crate::large_fields::{
    byte128, byte384, byte576, byte768, gf128_as_bytes, gf128_from_bytes, gf128_hmul,
    gf128_mul, gf128_mul_bits, gf128_mul_gf64, gf128_mul_spec, gf128_square, gf384_as_bytes,
    gf384_from_bytes, gf384_mul_bits, gf384_mul_gf128, gf192_mul, gf192_mul_spec, gf256_mul,
    gf256_mul_spec, gf576_as_bytes, gf576_from_bytes, gf576_mul_bits, gf576_mul_gf192,
    gf768_as_bytes, gf768_from_bytes, gf768_mul_bits, gf768_mul_gf256, lemma_u128_bytes_eq,
    GF128_LENGTH_BYTES, GF128_MODULUS, GF128_ZERO, GF192_LENGTH_BYTES, GF192_MODULUS,
    GF192_ONE, GF192_ZERO, GF256_LENGTH_BYTES, GF256_MODULUS, GF256_ONE, GF256_ZERO,
    U128_LOWER_MASK,
};
use crate::small_fields::{
    byte64, gf64_from_bytes, gf64_mul, gf64_mul_spec, GF64_MODULUS, GF64_ZERO,
};
use crate::prover::field_commitment::{
    FieldCommitDegOne, FieldCommitDegThree, FieldCommitDegTwo,
};

verus! {

// ===========================================================================
// Byte-span assembly spec fns (the le-bytes carriers the fold specs
// consume; the plane-bridge lemmas below connect the FA3/FA2 exec
// from_bytes faces to them).
// ===========================================================================

/// The little-endian u128 value of the 8 bytes at bs[lo..lo+8].
pub open spec fn le128_8(bs: Seq<u8>, lo: int) -> u128 {
    (bs[lo] as u128)
    | ((bs[lo + 1] as u128) << 8u64)
    | ((bs[lo + 2] as u128) << 16u64)
    | ((bs[lo + 3] as u128) << 24u64)
    | ((bs[lo + 4] as u128) << 32u64)
    | ((bs[lo + 5] as u128) << 40u64)
    | ((bs[lo + 6] as u128) << 48u64)
    | ((bs[lo + 7] as u128) << 56u64)
}

/// The little-endian u128 value of the 16 bytes at bs[lo..lo+16].
pub open spec fn le16_u128(bs: Seq<u8>, lo: int) -> u128 {
    (bs[lo] as u128)
    | ((bs[lo + 1] as u128) << 8u64)
    | ((bs[lo + 2] as u128) << 16u64)
    | ((bs[lo + 3] as u128) << 24u64)
    | ((bs[lo + 4] as u128) << 32u64)
    | ((bs[lo + 5] as u128) << 40u64)
    | ((bs[lo + 6] as u128) << 48u64)
    | ((bs[lo + 7] as u128) << 56u64)
    | ((bs[lo + 8] as u128) << 64u64)
    | ((bs[lo + 9] as u128) << 72u64)
    | ((bs[lo + 10] as u128) << 80u64)
    | ((bs[lo + 11] as u128) << 88u64)
    | ((bs[lo + 12] as u128) << 96u64)
    | ((bs[lo + 13] as u128) << 104u64)
    | ((bs[lo + 14] as u128) << 112u64)
    | ((bs[lo + 15] as u128) << 120u64)
}

/// The little-endian u64 value of the 8 bytes at bs[lo..lo+8].
pub open spec fn le8_u64(bs: Seq<u8>, lo: int) -> u64 {
    (bs[lo] as u64)
    | ((bs[lo + 1] as u64) << 8u64)
    | ((bs[lo + 2] as u64) << 16u64)
    | ((bs[lo + 3] as u64) << 24u64)
    | ((bs[lo + 4] as u64) << 32u64)
    | ((bs[lo + 5] as u64) << 40u64)
    | ((bs[lo + 6] as u64) << 48u64)
    | ((bs[lo + 7] as u64) << 56u64)
}

// ===========================================================================
// Plane-bridge lemmas: value == the le-bytes assembly, given the
// per-byte plane facts (plain-stage Seq-index hoisting into scalar
// lets first; the blast holds only the scalar lets -- #FA2-3 / #FA6p
// conventions; seq indexes never enter blast contexts).
// ===========================================================================

/// A value whose 16 byte planes are the span bytes equals the le
/// assembly (the FA3 lemma_u128_bytes_eq consumption route).
/// Byte-plane rows to scalar high-half: given the eight high byte
/// planes of a u128 (the shape the conv/partial-limb parse ensures
/// emit), fold them into the single scalar clause the plane8 bridge
/// consumes. This is the one bridge the plain encoding refuses to
/// fold by itself (masked shifts of an opaque term never trigger).
pub proof fn lemma_hi8_zero(a: u128)
    requires
        forall |j: int| 8 <= j < 16 ==> #[trigger] byte128(a, j) == 0,
    ensures
        (a >> 64) == 0,
{
    assert(byte128(a, 8) == ((a >> 64u64) & 0xFF));
    assert(byte128(a, 9) == ((a >> 72u64) & 0xFF));
    assert(byte128(a, 10) == ((a >> 80u64) & 0xFF));
    assert(byte128(a, 11) == ((a >> 88u64) & 0xFF));
    assert(byte128(a, 12) == ((a >> 96u64) & 0xFF));
    assert(byte128(a, 13) == ((a >> 104u64) & 0xFF));
    assert(byte128(a, 14) == ((a >> 112u64) & 0xFF));
    assert(byte128(a, 15) == ((a >> 120u64) & 0xFF));
    assert((a >> 64) == 0) by (bit_vector)
        requires
            ((a >> 64) & 0xFF) == 0,
            ((a >> 72) & 0xFF) == 0,
            ((a >> 80) & 0xFF) == 0,
            ((a >> 88) & 0xFF) == 0,
            ((a >> 96) & 0xFF) == 0,
            ((a >> 104) & 0xFF) == 0,
            ((a >> 112) & 0xFF) == 0,
            ((a >> 120) & 0xFF) == 0,
    ;
}

/// U128 xor re-association (local blast; the plain encoding keeps
/// ^ trees opaque, three-and-more-term regroups need this).
proof fn xor_assoc3(a: u128, b: u128, c: u128)
    ensures
        (a ^ (b ^ c)) == ((a ^ b) ^ c),
{
    assert((a ^ (b ^ c)) == ((a ^ b) ^ c)) by (bit_vector);
}

pub proof fn lemma_plane16_le(bs: Seq<u8>, lo: int, a: u128)
    requires
        0 <= lo,
        lo + 16 <= bs.len(),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(a, j) == (bs[lo + j] as u128),
    ensures
        a == le16_u128(bs, lo),
{
    let e0: u128 = bs[lo] as u128;
    let e1: u128 = bs[lo + 1] as u128;
    let e2: u128 = bs[lo + 2] as u128;
    let e3: u128 = bs[lo + 3] as u128;
    let e4: u128 = bs[lo + 4] as u128;
    let e5: u128 = bs[lo + 5] as u128;
    let e6: u128 = bs[lo + 6] as u128;
    let e7: u128 = bs[lo + 7] as u128;
    let e8: u128 = bs[lo + 8] as u128;
    let e9: u128 = bs[lo + 9] as u128;
    let e10: u128 = bs[lo + 10] as u128;
    let e11: u128 = bs[lo + 11] as u128;
    let e12: u128 = bs[lo + 12] as u128;
    let e13: u128 = bs[lo + 13] as u128;
    let e14: u128 = bs[lo + 14] as u128;
    let e15: u128 = bs[lo + 15] as u128;
    assert(byte128(a, 0) == ((a >> 0u64) & 0xFF));
    assert(byte128(a, 1) == ((a >> 8u64) & 0xFF));
    assert(byte128(a, 2) == ((a >> 16u64) & 0xFF));
    assert(byte128(a, 3) == ((a >> 24u64) & 0xFF));
    assert(byte128(a, 4) == ((a >> 32u64) & 0xFF));
    assert(byte128(a, 5) == ((a >> 40u64) & 0xFF));
    assert(byte128(a, 6) == ((a >> 48u64) & 0xFF));
    assert(byte128(a, 7) == ((a >> 56u64) & 0xFF));
    assert(byte128(a, 8) == ((a >> 64u64) & 0xFF));
    assert(byte128(a, 9) == ((a >> 72u64) & 0xFF));
    assert(byte128(a, 10) == ((a >> 80u64) & 0xFF));
    assert(byte128(a, 11) == ((a >> 88u64) & 0xFF));
    assert(byte128(a, 12) == ((a >> 96u64) & 0xFF));
    assert(byte128(a, 13) == ((a >> 104u64) & 0xFF));
    assert(byte128(a, 14) == ((a >> 112u64) & 0xFF));
    assert(byte128(a, 15) == ((a >> 120u64) & 0xFF));
    let flat = (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64)
        | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64)
        | (e8 << 64u64) | (e9 << 72u64) | (e10 << 80u64) | (e11 << 88u64)
        | (e12 << 96u64) | (e13 << 104u64) | (e14 << 112u64) | (e15 << 120u64));
    assert(a == flat) by (bit_vector)
        requires
            flat == (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64)
                | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64)
                | (e8 << 64u64) | (e9 << 72u64) | (e10 << 80u64) | (e11 << 88u64)
                | (e12 << 96u64) | (e13 << 104u64) | (e14 << 112u64) | (e15 << 120u64)),
            e0 <= 0xFF, e1 <= 0xFF, e2 <= 0xFF, e3 <= 0xFF,
            e4 <= 0xFF, e5 <= 0xFF, e6 <= 0xFF, e7 <= 0xFF,
            e8 <= 0xFF, e9 <= 0xFF, e10 <= 0xFF, e11 <= 0xFF,
            e12 <= 0xFF, e13 <= 0xFF, e14 <= 0xFF, e15 <= 0xFF,
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
    assert(le16_u128(bs, lo) == flat);
}

/// The u64 8-byte plane bridge (the small-fields twin carries no
/// lemma_u64_bytes_eq face; same flat-assembly route, bv over scalar
/// lets only).
pub proof fn lemma_plane8_le64(bs: Seq<u8>, lo: int, a: u64)
    requires
        0 <= lo,
        lo + 8 <= bs.len(),
        forall |j: int| 0 <= j < 8 ==> #[trigger] byte64(a, j) == (bs[lo + j] as u64),
    ensures
        a == le8_u64(bs, lo),
{
    let e0: u64 = bs[lo] as u64;
    let e1: u64 = bs[lo + 1] as u64;
    let e2: u64 = bs[lo + 2] as u64;
    let e3: u64 = bs[lo + 3] as u64;
    let e4: u64 = bs[lo + 4] as u64;
    let e5: u64 = bs[lo + 5] as u64;
    let e6: u64 = bs[lo + 6] as u64;
    let e7: u64 = bs[lo + 7] as u64;
    assert(byte64(a, 0) == ((a >> 0u64) & 0xFF));
    assert(byte64(a, 1) == ((a >> 8u64) & 0xFF));
    assert(byte64(a, 2) == ((a >> 16u64) & 0xFF));
    assert(byte64(a, 3) == ((a >> 24u64) & 0xFF));
    assert(byte64(a, 4) == ((a >> 32u64) & 0xFF));
    assert(byte64(a, 5) == ((a >> 40u64) & 0xFF));
    assert(byte64(a, 6) == ((a >> 48u64) & 0xFF));
    assert(byte64(a, 7) == ((a >> 56u64) & 0xFF));
    let flat = (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64)
        | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64));
    assert(a == flat) by (bit_vector)
        requires
            flat == (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64)
                | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64)),
            e0 <= 0xFF, e1 <= 0xFF, e2 <= 0xFF, e3 <= 0xFF,
            e4 <= 0xFF, e5 <= 0xFF, e6 <= 0xFF, e7 <= 0xFF,
            ((a >> 0u64) & 0xFF) == e0,
            ((a >> 8u64) & 0xFF) == e1,
            ((a >> 16u64) & 0xFF) == e2,
            ((a >> 24u64) & 0xFF) == e3,
            ((a >> 32u64) & 0xFF) == e4,
            ((a >> 40u64) & 0xFF) == e5,
            ((a >> 48u64) & 0xFF) == e6,
            ((a >> 56u64) & 0xFF) == e7,
    ;
    assert(le8_u64(bs, lo) == flat);
}

/// The u128-valued 8-byte plane bridge (GF192's limb-1 wire tail).
/// The zero-upper premise is a caller fact of the GF192 wire form
/// (the limb-1 bytes above the wire plane are 0 by the from_bytes
/// zero-fill and by the mul tail's U64 mask).
pub proof fn lemma_plane8_le128(bs: Seq<u8>, lo: int, a: u128)
    requires
        0 <= lo,
        lo + 8 <= bs.len(),
        forall |j: int| 0 <= j < 8 ==> #[trigger] byte128(a, j) == (bs[lo + j] as u128),
        (a >> 64) == 0,
    ensures
        a == le128_8(bs, lo),
{
    let e0: u128 = bs[lo] as u128;
    let e1: u128 = bs[lo + 1] as u128;
    let e2: u128 = bs[lo + 2] as u128;
    let e3: u128 = bs[lo + 3] as u128;
    let e4: u128 = bs[lo + 4] as u128;
    let e5: u128 = bs[lo + 5] as u128;
    let e6: u128 = bs[lo + 6] as u128;
    let e7: u128 = bs[lo + 7] as u128;
    assert(byte128(a, 0) == ((a >> 0u64) & 0xFF));
    assert(byte128(a, 1) == ((a >> 8u64) & 0xFF));
    assert(byte128(a, 2) == ((a >> 16u64) & 0xFF));
    assert(byte128(a, 3) == ((a >> 24u64) & 0xFF));
    assert(byte128(a, 4) == ((a >> 32u64) & 0xFF));
    assert(byte128(a, 5) == ((a >> 40u64) & 0xFF));
    assert(byte128(a, 6) == ((a >> 48u64) & 0xFF));
    assert(byte128(a, 7) == ((a >> 56u64) & 0xFF));
    let flat = (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64)
        | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64));
    assert(a == flat) by (bit_vector)
        requires
            flat == (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64)
                | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64)),
            e0 <= 0xFF, e1 <= 0xFF, e2 <= 0xFF, e3 <= 0xFF,
            e4 <= 0xFF, e5 <= 0xFF, e6 <= 0xFF, e7 <= 0xFF,
            ((a >> 0u64) & 0xFF) == e0,
            ((a >> 8u64) & 0xFF) == e1,
            ((a >> 16u64) & 0xFF) == e2,
            ((a >> 24u64) & 0xFF) == e3,
            ((a >> 32u64) & 0xFF) == e4,
            ((a >> 40u64) & 0xFF) == e5,
            ((a >> 48u64) & 0xFF) == e6,
            ((a >> 56u64) & 0xFF) == e7,
            (a >> 64) == 0,
    ;
    assert(le128_8(bs, lo) == flat);
}


// ===========================================================================
// GF192 / GF256 Field byte planes (re-erected here; the FA3 waves
// covered the mul cores and the 48/72/96 extension planes, never the
// 24/32 base planes -- re-homing note to FA3 recorded in the batch
// notes).
// Origin Rust (large_fields.rs :1083-1107, Field for GF192):
//     fn as_bytes(&self) -> Array<u8, Self::Length> {
//         let mut ret = Array::default();
//         ret[..16].copy_from_slice(&self.0[0].to_le_bytes());
//         ret[16..].copy_from_slice(&self.0[1].to_le_bytes()[..8]);
//         ret }
//     impl From<&[u8]> for BigGF<u128, 2, 192> {
//         fn from(value: &[u8]) -> Self {
//             debug_assert_eq!(value.len(), 24);
//             let mut array_2 = [0u8; 16];
//             array_2[..8].copy_from_slice(&value[16..24]);
//             Self([...from_le_bytes(array_1),
//                   u128::from_le_bytes(array_2)]) } }
// The debug-length contract re-erects as the requires (S-FA3-2
// convention); the limb-1 zero-fill above the wire plane (bytes
// 8..16 zeroed, i.e. res.1's high bytes) is an explicit ensures
// clause (the twin's GF192 carrier keeps that plane fact for the
// orbit tail and the as_bytes consumer).
// ===========================================================================

pub exec fn gf192_from_bytes(value: &[u8]) -> (res: (u128, u128))
    requires
        value.len() == GF192_LENGTH_BYTES,
    ensures
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(res.0, j) == (value[j] as u128),
        forall |j: int| 0 <= j < 8 ==> #[trigger] byte128(res.1, j) == (value[16 + j] as u128),
        forall |j: int| 8 <= j < 16 ==> #[trigger] byte128(res.1, j) == 0,
{
    let l0: u128 = gf128_from_bytes(&value[0..16]);
    // upstream:
    //     let mut array_2 = [0u8; 16];
    //     array_2[..8].copy_from_slice(&value[16..24]);
    //     limb_1 = u128::from_le_bytes(array_2)
    // the copy_from_slice lowers to the eight index copies (FA1
    // convention); the zeroed upper half of the temp array carries
    // the wire-side partial-limb fact.
    let mut buf: [u8; 16] = [0; 16];
    let mut j: usize = 0;
    while j < 8
        invariant
            j <= 8,
            value.len() == 24,
            buf.len() == 16,
            forall |k: int| 0 <= k < j ==> buf[k] == value[16 + k],
            forall |k: int| j <= k < 16 ==> buf[k] == 0,
        decreases 8 - j,
    {
        buf[j] = value[16 + j];
        j += 1;
    }
    let l1: u128 = gf128_from_bytes(&buf[..]);
    (l0, l1)
}

/// Partial-limb GF128 parse over 8 wire bytes (the LeafHasher192
/// e4 lane and every partial-limb tail re-erected at the byte-plane
/// level; the upper half of the temp array is zeroed per the
/// upstream copy_from_slice lowering, and the high byte rows stay
/// byte-shaped -- consumers fold the scalar row via lemma_hi8_zero).
pub exec fn gf128_from_bytes8(value: &[u8]) -> (res: u128)
    requires
        value.len() == 8,
    ensures
        forall |j: int| 0 <= j < 8 ==> #[trigger] byte128(res, j) == (value[j] as u128),
        forall |j: int| 8 <= j < 16 ==> #[trigger] byte128(res, j) == 0,
{
    // upstream: array_2 = [0u8; 16]; array_2[..8].copy_from_slice(value)
    let mut buf: [u8; 16] = [0; 16];
    let mut j: usize = 0;
    while j < 8
        invariant
            j <= 8,
            value.len() == 8,
            buf.len() == 16,
            forall |k: int| 0 <= k < j ==> buf[k] == value[k],
            forall |k: int| j <= k < 16 ==> buf[k] == 0,
        decreases 8 - j,
    {
        buf[j] = value[j];
        j += 1;
    }
    let l0: u128 = gf128_from_bytes(&buf[..]);
    proof {
        assert forall |j: int| 0 <= j < 8 implies
            #[trigger] byte128(l0, j) == (value[j] as u128) by {
            assert forall |k: int| 0 <= k < 16 implies
                #[trigger] byte128(l0, k) == (buf[k] as u128) by {
            }
        }
        assert forall |j: int| 8 <= j < 16 implies
            #[trigger] byte128(l0, j) == 0 by {
            assert forall |k: int| 8 <= k < 16 implies
                #[trigger] byte128(l0, k) == (buf[k] as u128) by {
            }
        }
    }
    l0
}

pub exec fn gf192_as_bytes(v: (u128, u128)) -> (out: [u8; 24])
    ensures
        forall |j: int| 0 <= j < 16 ==> out[j] == (byte128(v.0, j) as u8),
        forall |j: int| 0 <= j < 8
            ==> out[16 + j] == (byte128(v.1, j) as u8),
{
    let hiv: u128 = v.1;
    let p0 = gf128_as_bytes(v.0);
    #[verifier::truncate] let q0: u8 = ((hiv >> 0u64) & 0xFFu128) as u8;
    #[verifier::truncate] let q1: u8 = ((hiv >> 8u64) & 0xFFu128) as u8;
    #[verifier::truncate] let q2: u8 = ((hiv >> 16u64) & 0xFFu128) as u8;
    #[verifier::truncate] let q3: u8 = ((hiv >> 24u64) & 0xFFu128) as u8;
    #[verifier::truncate] let q4: u8 = ((hiv >> 32u64) & 0xFFu128) as u8;
    #[verifier::truncate] let q5: u8 = ((hiv >> 40u64) & 0xFFu128) as u8;
    #[verifier::truncate] let q6: u8 = ((hiv >> 48u64) & 0xFFu128) as u8;
    #[verifier::truncate] let q7: u8 = ((hiv >> 56u64) & 0xFFu128) as u8;
    proof {
        assert(((hiv >> 0u64) & 0xFFu128) <= 0xFFu128) by (bit_vector);
        assert(((hiv >> 8u64) & 0xFFu128) <= 0xFFu128) by (bit_vector);
        assert(((hiv >> 16u64) & 0xFFu128) <= 0xFFu128) by (bit_vector);
        assert(((hiv >> 24u64) & 0xFFu128) <= 0xFFu128) by (bit_vector);
        assert(((hiv >> 32u64) & 0xFFu128) <= 0xFFu128) by (bit_vector);
        assert(((hiv >> 40u64) & 0xFFu128) <= 0xFFu128) by (bit_vector);
        assert(((hiv >> 48u64) & 0xFFu128) <= 0xFFu128) by (bit_vector);
        assert(((hiv >> 56u64) & 0xFFu128) <= 0xFFu128) by (bit_vector);
        assert((q0 as u128) == ((hiv >> 0u64) & 0xFFu128));
        assert((q1 as u128) == ((hiv >> 8u64) & 0xFFu128));
        assert((q2 as u128) == ((hiv >> 16u64) & 0xFFu128));
        assert((q3 as u128) == ((hiv >> 24u64) & 0xFFu128));
        assert((q4 as u128) == ((hiv >> 32u64) & 0xFFu128));
        assert((q5 as u128) == ((hiv >> 40u64) & 0xFFu128));
        assert((q6 as u128) == ((hiv >> 48u64) & 0xFFu128));
        assert((q7 as u128) == ((hiv >> 56u64) & 0xFFu128));
        assert(byte128(hiv, 0) == (q0 as u128));
        assert(byte128(hiv, 1) == (q1 as u128));
        assert(byte128(hiv, 2) == (q2 as u128));
        assert(byte128(hiv, 3) == (q3 as u128));
        assert(byte128(hiv, 4) == (q4 as u128));
        assert(byte128(hiv, 5) == (q5 as u128));
        assert(byte128(hiv, 6) == (q6 as u128));
        assert(byte128(hiv, 7) == (q7 as u128));
    }
    [p0[0], p0[1], p0[2], p0[3], p0[4], p0[5], p0[6], p0[7],
     p0[8], p0[9], p0[10], p0[11], p0[12], p0[13], p0[14], p0[15],
     q0, q1, q2, q3, q4, q5, q6, q7]
}

// Origin Rust (large_fields.rs :1243-1257, Field for GF256 /
// From<&[u8]>): both limbs are full 16-byte LE planes (no partial
// limb on this wire).
pub exec fn gf256_from_bytes(value: &[u8]) -> (res: (u128, u128))
    requires
        value.len() == GF256_LENGTH_BYTES,
    ensures
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(res.0, j) == (value[j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(res.1, j) == (value[16 + j] as u128),
{
    let l0: u128 = gf128_from_bytes(&value[0..16]);
    let l1: u128 = gf128_from_bytes(&value[16..32]);
    (l0, l1)
}

pub exec fn gf256_as_bytes(v: (u128, u128)) -> (out: [u8; 32])
    ensures
        forall |j: int| 0 <= j < 16 ==> #[trigger] out[j] == (byte128(v.0, j) as u8),
        forall |j: int| 0 <= j < 16 ==> #[trigger] out[16 + j] == (byte128(v.1, j) as u8),
{
    let p0 = gf128_as_bytes(v.0);
    let p1 = gf128_as_bytes(v.1);
    [p0[0], p0[1], p0[2], p0[3], p0[4], p0[5], p0[6], p0[7],
     p0[8], p0[9], p0[10], p0[11], p0[12], p0[13], p0[14], p0[15],
     p1[0], p1[1], p1[2], p1[3], p1[4], p1[5], p1[6], p1[7],
     p1[8], p1[9], p1[10], p1[11], p1[12], p1[13], p1[14], p1[15]]
}


// ===========================================================================
// Mul<GF64> for GF192/GF256 -- the generic 64-bit orbit upstream
// (large_fields.rs :680-705) at the [u128; 2] plane, re-erected here
// (the FA3 tree landed only the GF128 instantiation of this face;
// re-homing note to FA3 in the batch notes). Verified == the
// low-bit-Horner orbit model over the embedded GF64 multiplier,
// every input -- the FA3-w1 gf128_mul_gf64 recipe at two limbs.
// ===========================================================================

// local bv xor helpers (the large_fields twins are module-private)
proof fn bx_c128(a: u128, b: u128)
    ensures
        (a ^ b) == (b ^ a),
{
    assert((a ^ b) == (b ^ a)) by (bit_vector);
}

proof fn bx_a128(a: u128, b: u128, c: u128)
    ensures
        ((a ^ b) ^ c) == (a ^ (b ^ c)),
        ((a ^ b) ^ c) == (b ^ (c ^ a)),
{
    assert(((a ^ b) ^ c) == (a ^ (b ^ c))) by (bit_vector);
    assert(((a ^ b) ^ c) == (b ^ (c ^ a))) by (bit_vector);
}

/// Orbit step of GF(2^192): limb-1 is wire-confined to the low 64
/// bits (ClearHighBits: `self.0[1] &= u64::MAX as u128`); the domain
/// MSB (bit 191 = limb-1 bit 63) reduces limb 0 by the modulus 0x87.
pub open spec fn gf192_xt0(l0: u128, l1: u128) -> u128 {
    ((l0 << 1) ^ (if (l1 >> 63) & 1 == 1 { GF192_MODULUS } else { 0u128 }))
}

pub open spec fn gf192_xt1(l0: u128, l1: u128) -> u128 {
    (((l1 << 1) | (l0 >> 127)) & U128_LOWER_MASK)
}

/// Spec helper: per-limb xor of two orbit pairs.
pub open spec fn xor2(a: (u128, u128), b: (u128, u128)) -> (u128, u128) {
    (a.0 ^ b.0, a.1 ^ b.1)
}

pub proof fn lemma_xor2_def(a: (u128, u128), b: (u128, u128))
    ensures
        xor2(a, b) == (a.0 ^ b.0, a.1 ^ b.1),
{
}

/// low-bit Horner over the embedded GF64 multiplier with the
/// 2-limb GF192 orbit.
pub open spec fn gf192_mg64_bits(o0: u128, o1: u128, r: u128, w: nat) -> (u128, u128)
    decreases w,
{
    if w == 0 {
        (0u128, 0u128)
    } else {
        let t0 = gf192_xt0(o0, o1);
        let t1 = gf192_xt1(o0, o1);
        let tail = gf192_mg64_bits(t0, t1, r >> 1, (w - 1) as nat);
        (if r & 1 == 1 { o0 } else { 0u128 } ^ tail.0,
         if r & 1 == 1 { o1 } else { 0u128 } ^ tail.1)
    }
}

pub proof fn lemma_gf192_mg64_unfold(o0: u128, o1: u128, r: u128, w: nat)
    requires
        0 < w,
    ensures
        gf192_mg64_bits(o0, o1, r, w)
            == xor2(
                (if r & 1 == 1 { o0 } else { 0u128 },
                 if r & 1 == 1 { o1 } else { 0u128 }),
                gf192_mg64_bits(gf192_xt0(o0, o1), gf192_xt1(o0, o1), r >> 1, (w - 1) as nat),
            ),
{
}

/// The GF192 Mul<GF64> exec face (upstream :680-705 at N = 2,
/// LENGTH = 192): the 64-rung orbit over the embedded GF64 bits.
pub exec fn gf192_mul_gf64(x0: u128, x1: u128, rhs: u64) -> (res: (u128, u128))
    ensures
        res == gf192_mg64_bits(x0, x1, (rhs as u128), 64nat),
{
    let y: u128 = rhs as u128;
    proof {
        assert(y <= 0xFFFF_FFFF_FFFF_FFFFu128) by (bit_vector)
            requires
                y == (rhs as u128),
        ;
    }
    let mut l0: u128 = x0;
    let mut l1: u128 = x1;
    let mut r0: u128 = if y & 1 == 1 { x0 } else { 0u128 };
    let mut r1: u128 = if y & 1 == 1 { x1 } else { 0u128 };
    proof {
        lemma_gf192_mg64_unfold(x0, x1, y, 64nat);
        let tail = gf192_mg64_bits(gf192_xt0(x0, x1), gf192_xt1(x0, x1), y >> 1, 63nat);
        bx_c128(tail.0, r0);
        bx_c128(tail.1, r1);
    }
    let mut idx: usize = 1;
    while idx < 64
        invariant
            1 <= idx <= 64,
            y <= 0xFFFF_FFFF_FFFF_FFFFu128,
            xor2(gf192_mg64_bits(
                gf192_xt0(l0, l1), gf192_xt1(l0, l1),
                y >> (idx as u64), (64 - idx) as nat,
            ), (r0, r1)) == gf192_mg64_bits(x0, x1, y, 64nat),
        decreases 64 - idx,
    {
        let o0: u128 = l0;
        let o1: u128 = l1;
        let s0: u128 = r0;
        let s1: u128 = r1;
        let y_i: u128 = y >> (idx as u64);
        proof {
            if (idx + 1) < 64 {
                assert((y_i >> 1) == (y >> ((idx + 1) as u64))) by (bit_vector)
                    requires
                        (idx + 1) < 64,
                        y_i == y >> (idx as u64),
                ;
            } else {
                assert((y >> 63) >> 1 == 0u128) by (bit_vector)
                    requires
                        y <= 0xFFFF_FFFF_FFFF_FFFFu128,
                ;
                assert(y_i == (y >> 63)) by (bit_vector)
                    requires
                        idx == 63,
                        y_i == y >> (idx as u64),
                ;
                assert((y_i >> 1) == 0u128);
            }
            lemma_gf192_mg64_unfold(o0, o1, y_i, (64 - idx) as nat);
        }
        // the pre-shift MSB (bit 191 = limb-1 bit 63) drives the fold
        let m: u128 = if (o1 >> 63) & 1 == 1 { GF192_MODULUS } else { 0u128 };
        l1 = ((o1 << 1) | (o0 >> 127)) & U128_LOWER_MASK;
        l0 = (o0 << 1) ^ m;
        proof {
            assert(m == (if ((o1 >> 63) & 1) == 1u128 { GF192_MODULUS } else { 0u128 }));
            assert(l0 == gf192_xt0(o0, o1));
            assert(l1 == gf192_xt1(o0, o1));
        }
        r0 = s0 ^ (if y_i & 1 == 1 { l0 } else { 0u128 });
        r1 = s1 ^ (if y_i & 1 == 1 { l1 } else { 0u128 });
        proof {
            let c0 = if y_i & 1 == 1u128 { l0 } else { 0u128 };
            let c1 = if y_i & 1 == 1u128 { l1 } else { 0u128 };
            let n0 = gf192_xt0(l0, l1);
            let n1 = gf192_xt1(l0, l1);
            let tail_old = gf192_mg64_bits(l0, l1, y_i, (64 - idx) as nat);
            let tail_new = gf192_mg64_bits(n0, n1, y_i >> 1, (64 - idx - 1) as nat);
            assert(xor2(tail_old, (s0, s1)) == gf192_mg64_bits(x0, x1, y, 64nat));
            assert(tail_old == xor2((c0, c1), tail_new));
            assert(tail_new.0 ^ r0 == tail_old.0 ^ s0) by {
                bx_a128(c0, tail_new.0, s0);
                bx_c128(c0, s0);
                assert((c0 ^ tail_new.0) ^ s0 == tail_new.0 ^ (s0 ^ c0));
                assert(tail_old.0 == c0 ^ tail_new.0);
            }
            assert(tail_new.1 ^ r1 == tail_old.1 ^ s1) by {
                bx_a128(c1, tail_new.1, s1);
                bx_c128(c1, s1);
                assert((c1 ^ tail_new.1) ^ s1 == tail_new.1 ^ (s1 ^ c1));
                assert(tail_old.1 == c1 ^ tail_new.1);
            }
        }
        idx += 1;
    }
    proof {
        let n0 = gf192_xt0(l0, l1);
        let n1 = gf192_xt1(l0, l1);
        assert(gf192_mg64_bits(n0, n1, y >> 64u64, 0nat) == (0u128, 0u128));
        assert((y >> 64u64) == 0u128) by (bit_vector)
            requires
                y <= 0xFFFF_FFFF_FFFF_FFFFu128,
        ;
        assert((0u128 ^ r0) == r0) by (bit_vector);
        assert((0u128 ^ r1) == r1) by (bit_vector);
    }
    (r0, r1)
}

// GF256 twin of the orbit: 256-bit element on both limbs, no
// ClearHighBits mask; the domain MSB (bit 255 = limb-1 bit 127)
// reduces limb 0 by the modulus 0x425.
pub open spec fn gf256_xt0(l0: u128, l1: u128) -> u128 {
    ((l0 << 1) ^ (if (l1 >> 127) & 1 == 1 { GF256_MODULUS } else { 0u128 }))
}

pub open spec fn gf256_xt1(l0: u128, l1: u128) -> u128 {
    ((l1 << 1) | (l0 >> 127))
}

pub open spec fn gf256_mg64_bits(o0: u128, o1: u128, r: u128, w: nat) -> (u128, u128)
    decreases w,
{
    if w == 0 {
        (0u128, 0u128)
    } else {
        let t0 = gf256_xt0(o0, o1);
        let t1 = gf256_xt1(o0, o1);
        let tail = gf256_mg64_bits(t0, t1, r >> 1, (w - 1) as nat);
        (if r & 1 == 1 { o0 } else { 0u128 } ^ tail.0,
         if r & 1 == 1 { o1 } else { 0u128 } ^ tail.1)
    }
}

pub proof fn lemma_gf256_mg64_unfold(o0: u128, o1: u128, r: u128, w: nat)
    requires
        0 < w,
    ensures
        gf256_mg64_bits(o0, o1, r, w)
            == xor2(
                (if r & 1 == 1 { o0 } else { 0u128 },
                 if r & 1 == 1 { o1 } else { 0u128 }),
                gf256_mg64_bits(gf256_xt0(o0, o1), gf256_xt1(o0, o1), r >> 1, (w - 1) as nat),
            ),
{
}

pub exec fn gf256_mul_gf64(x0: u128, x1: u128, rhs: u64) -> (res: (u128, u128))
    ensures
        res == gf256_mg64_bits(x0, x1, (rhs as u128), 64nat),
{
    let y: u128 = rhs as u128;
    proof {
        assert(y <= 0xFFFF_FFFF_FFFF_FFFFu128) by (bit_vector)
            requires
                y == (rhs as u128),
        ;
    }
    let mut l0: u128 = x0;
    let mut l1: u128 = x1;
    let mut r0: u128 = if y & 1 == 1 { x0 } else { 0u128 };
    let mut r1: u128 = if y & 1 == 1 { x1 } else { 0u128 };
    proof {
        lemma_gf256_mg64_unfold(x0, x1, y, 64nat);
        let tail = gf256_mg64_bits(gf256_xt0(x0, x1), gf256_xt1(x0, x1), y >> 1, 63nat);
        bx_c128(tail.0, r0);
        bx_c128(tail.1, r1);
    }
    let mut idx: usize = 1;
    while idx < 64
        invariant
            1 <= idx <= 64,
            y <= 0xFFFF_FFFF_FFFF_FFFFu128,
            xor2(gf256_mg64_bits(
                gf256_xt0(l0, l1), gf256_xt1(l0, l1),
                y >> (idx as u64), (64 - idx) as nat,
            ), (r0, r1)) == gf256_mg64_bits(x0, x1, y, 64nat),
        decreases 64 - idx,
    {
        let o0: u128 = l0;
        let o1: u128 = l1;
        let s0: u128 = r0;
        let s1: u128 = r1;
        let y_i: u128 = y >> (idx as u64);
        proof {
            if (idx + 1) < 64 {
                assert((y_i >> 1) == (y >> ((idx + 1) as u64))) by (bit_vector)
                    requires
                        (idx + 1) < 64,
                        y_i == y >> (idx as u64),
                ;
            } else {
                assert((y >> 63) >> 1 == 0u128) by (bit_vector)
                    requires
                        y <= 0xFFFF_FFFF_FFFF_FFFFu128,
                ;
                assert(y_i == (y >> 63)) by (bit_vector)
                    requires
                        idx == 63,
                        y_i == y >> (idx as u64),
                ;
                assert((y_i >> 1) == 0u128);
            }
            lemma_gf256_mg64_unfold(o0, o1, y_i, (64 - idx) as nat);
        }
        let m: u128 = if (o1 >> 127) & 1 == 1 { GF256_MODULUS } else { 0u128 };
        l1 = (o1 << 1) | (o0 >> 127);
        l0 = (o0 << 1) ^ m;
        proof {
            assert(m == (if ((o1 >> 127) & 1) == 1u128 { GF256_MODULUS } else { 0u128 }));
            assert(l0 == gf256_xt0(o0, o1));
            assert(l1 == gf256_xt1(o0, o1));
        }
        r0 = s0 ^ (if y_i & 1 == 1 { l0 } else { 0u128 });
        r1 = s1 ^ (if y_i & 1 == 1 { l1 } else { 0u128 });
        proof {
            let c0 = if y_i & 1 == 1u128 { l0 } else { 0u128 };
            let c1 = if y_i & 1 == 1u128 { l1 } else { 0u128 };
            let n0 = gf256_xt0(l0, l1);
            let n1 = gf256_xt1(l0, l1);
            let tail_old = gf256_mg64_bits(l0, l1, y_i, (64 - idx) as nat);
            let tail_new = gf256_mg64_bits(n0, n1, y_i >> 1, (64 - idx - 1) as nat);
            assert(xor2(tail_old, (s0, s1)) == gf256_mg64_bits(x0, x1, y, 64nat));
            assert(tail_old == xor2((c0, c1), tail_new));
            assert(tail_new.0 ^ r0 == tail_old.0 ^ s0) by {
                bx_a128(c0, tail_new.0, s0);
                bx_c128(c0, s0);
                assert((c0 ^ tail_new.0) ^ s0 == tail_new.0 ^ (s0 ^ c0));
                assert(tail_old.0 == c0 ^ tail_new.0);
            }
            assert(tail_new.1 ^ r1 == tail_old.1 ^ s1) by {
                bx_a128(c1, tail_new.1, s1);
                bx_c128(c1, s1);
                assert((c1 ^ tail_new.1) ^ s1 == tail_new.1 ^ (s1 ^ c1));
                assert(tail_old.1 == c1 ^ tail_new.1);
            }
        }
        idx += 1;
    }
    proof {
        let n0 = gf256_xt0(l0, l1);
        let n1 = gf256_xt1(l0, l1);
        assert(gf256_mg64_bits(n0, n1, y >> 64u64, 0nat) == (0u128, 0u128));
        assert((y >> 64u64) == 0u128) by (bit_vector)
            requires
                y <= 0xFFFF_FFFF_FFFF_FFFFu128,
        ;
        assert((0u128 ^ r0) == r0) by (bit_vector);
        assert((0u128 ^ r1) == r1) by (bit_vector);
    }
    (r0, r1)
}

// ===========================================================================
// Fold spec faces for the iterated hashers (VoleHasher / ZKHasher
// common carrier: per-block update algebra as spec chains over the
// byte planes of the message prefix). Lambda-128 column.
// ===========================================================================

/// One F-pointer(v: u128) update step (:129 *h0 = *h0 * s + F).
pub open spec fn vstep128(s: u128, acc: u128, bs: Seq<u8>, lo: int) -> u128 {
    gf128_mul_spec(acc, s) ^ le16_u128(bs, lo)
}

/// One GF64 update step (:131 *h1 = *h1 * t + GF64).
pub open spec fn vstep64(t: u64, acc: u64, bs: Seq<u8>, lo: int) -> u64 {
    gf64_mul_spec(acc, t) ^ le8_u64(bs, lo)
}

/// The zero-padded 16-byte tail block value (upstream
/// process_unpadded_block's zero-filled F::Length buffer).
pub open spec fn le16_pad_u128(bs: Seq<u8>, lo: int, filled: int) -> u128 {
    (if 0 < filled { bs[lo] as u128 } else { 0u128 })
        | (if 1 < filled { (bs[lo + 1] as u128) << 8u64 } else { 0u128 })
        | (if 2 < filled { (bs[lo + 2] as u128) << 16u64 } else { 0u128 })
        | (if 3 < filled { (bs[lo + 3] as u128) << 24u64 } else { 0u128 })
        | (if 4 < filled { (bs[lo + 4] as u128) << 32u64 } else { 0u128 })
        | (if 5 < filled { (bs[lo + 5] as u128) << 40u64 } else { 0u128 })
        | (if 6 < filled { (bs[lo + 6] as u128) << 48u64 } else { 0u128 })
        | (if 7 < filled { (bs[lo + 7] as u128) << 56u64 } else { 0u128 })
        | (if 8 < filled { (bs[lo + 8] as u128) << 64u64 } else { 0u128 })
        | (if 9 < filled { (bs[lo + 9] as u128) << 72u64 } else { 0u128 })
        | (if 10 < filled { (bs[lo + 10] as u128) << 80u64 } else { 0u128 })
        | (if 11 < filled { (bs[lo + 11] as u128) << 88u64 } else { 0u128 })
        | (if 12 < filled { (bs[lo + 12] as u128) << 96u64 } else { 0u128 })
        | (if 13 < filled { (bs[lo + 13] as u128) << 104u64 } else { 0u128 })
        | (if 14 < filled { (bs[lo + 14] as u128) << 112u64 } else { 0u128 })
        | (if 15 < filled { (bs[lo + 15] as u128) << 120u64 } else { 0u128 })
}

/// The zero-padded 8-byte GF64 sub-chunk value.
pub open spec fn le8_pad_u64(bs: Seq<u8>, lo: int, filled: int) -> u64 {
    (if 0 < filled { bs[lo] as u64 } else { 0u64 })
        | (if 1 < filled { (bs[lo + 1] as u64) << 8u64 } else { 0u64 })
        | (if 2 < filled { (bs[lo + 2] as u64) << 16u64 } else { 0u64 })
        | (if 3 < filled { (bs[lo + 3] as u64) << 24u64 } else { 0u64 })
        | (if 4 < filled { (bs[lo + 4] as u64) << 32u64 } else { 0u64 })
        | (if 5 < filled { (bs[lo + 5] as u64) << 40u64 } else { 0u64 })
        | (if 6 < filled { (bs[lo + 6] as u64) << 48u64 } else { 0u64 })
        | (if 7 < filled { (bs[lo + 7] as u64) << 56u64 } else { 0u64 })
}

/// F-pointer fold over k full 16-byte blocks.
pub open spec fn vh0_128(s: u128, bs: Seq<u8>, k: nat, acc: u128) -> u128
    decreases k,
{
    if k == 0 {
        acc
    } else {
        vstep128(s, vh0_128(s, bs, (k - 1) as nat, acc), bs, ((k as int) - 1) * 16)
    }
}

/// GF64 fold over k full 16-byte blocks (two 8-byte sub-chunks per
/// F-block -- upstream process_block's chunks_exact(8) loop).
pub open spec fn vh1_128(t: u64, bs: Seq<u8>, k: nat, acc: u64) -> u64
    decreases k,
{
    if k == 0 {
        acc
    } else {
        vstep64(
            t,
            vstep64(t, vh1_128(t, bs, (k - 1) as nat, acc), bs, ((k as int) - 1) * 16),
            bs,
            ((k as int) - 1) * 16 + 8,
        )
    }
}

/// vstep128 spelled over the zero-padded tail block value.
pub open spec fn vstep128_pad(s: u128, acc: u128, bs: Seq<u8>, lo: int, filled: int) -> u128 {
    gf128_mul_spec(acc, s) ^ le16_pad_u128(bs, lo, filled)
}

/// vstep64 spelled over a zero-padded 8-byte sub-chunk.
pub open spec fn vstep64_pad(t: u64, acc: u64, bs: Seq<u8>, lo: int, filled: int) -> u64 {
    gf64_mul_spec(acc, t) ^ le8_pad_u64(bs, lo, filled)
}

/// Total F-pointer state after nb full blocks plus the optional
/// zero-padded tail block (upstream process_split's chunks_exact
/// loop + unpadded tail; rem = len % 16 < 16).
pub open spec fn vh0_total_128(s: u128, bs: Seq<u8>, nb: nat, rem: nat, acc: u128) -> u128 {
    if rem == 0 {
        vh0_128(s, bs, nb, acc)
    } else {
        vstep128_pad(s, vh0_128(s, bs, nb, acc), bs, (nb as int) * 16, (rem as int))
    }
}

/// Total GF64 state after nb full blocks plus the padded tail block.
/// Upstream always processes the FULL padded F-block, so both GF64
/// sub-chunks run (zero-filled counts clamp(rem,0,8) and
/// clamp(rem-8,0,8)).
pub open spec fn vh1_total_128(t: u64, bs: Seq<u8>, nb: nat, rem: nat, acc: u64) -> u64 {
    if rem == 0 {
        vh1_128(t, bs, nb, acc)
    } else {
        vstep64_pad(
            t,
            vstep64_pad(
                t,
                vh1_128(t, bs, nb, acc),
                bs,
                (nb as int) * 16,
                (if rem < 8 { rem as int } else { 8 }),
            ),
            bs,
            (nb as int) * 16 + 8,
            (if rem < 8 { 0 } else { (rem as int) - 8 }),
        )
    }
}

/// One-level unfold of the F-pointer fold (#FA3-1 def-bridge form).
pub proof fn lemma_vh0_128_unfold(s: u128, bs: Seq<u8>, k: nat, acc: u128)
    requires
        0 < k,
    ensures
        vh0_128(s, bs, k, acc)
            == vstep128(s, vh0_128(s, bs, (k - 1) as nat, acc), bs, ((k as int) - 1) * 16),
{
}

/// One-level unfold of the GF64 fold (the double sub-step form).
pub proof fn lemma_vh1_128_unfold(t: u64, bs: Seq<u8>, k: nat, acc: u64)
    requires
        0 < k,
    ensures
        vh1_128(t, bs, k, acc)
            == vstep64(
                t,
                vstep64(t, vh1_128(t, bs, (k - 1) as nat, acc), bs, ((k as int) - 1) * 16),
                bs,
                ((k as int) - 1) * 16 + 8,
            ),
{
}

/// Sub-block span bridge: the le16 of a 16-byte block Seq equals
/// the le16 of the parent at the block offset (per-byte plane
/// congruence over the two flat-OR unfoldings).
pub proof fn lemma_blk_span_le16(sub: Seq<u8>, bs: Seq<u8>, lo: int)
    requires
        0 <= lo,
        lo + 16 <= bs.len(),
        sub.len() == 16,
        forall |j: int| 0 <= j < 16 ==> #[trigger] sub[j] == bs[lo + j],
    ensures
        le16_u128(sub, 0) == le16_u128(bs, lo),
{
    assert(le16_u128(sub, 0) == (sub[0] as u128) | ((sub[1] as u128) << 8u64)
        | ((sub[2] as u128) << 16u64) | ((sub[3] as u128) << 24u64)
        | ((sub[4] as u128) << 32u64) | ((sub[5] as u128) << 40u64)
        | ((sub[6] as u128) << 48u64) | ((sub[7] as u128) << 56u64)
        | ((sub[8] as u128) << 64u64) | ((sub[9] as u128) << 72u64)
        | ((sub[10] as u128) << 80u64) | ((sub[11] as u128) << 88u64)
        | ((sub[12] as u128) << 96u64) | ((sub[13] as u128) << 104u64)
        | ((sub[14] as u128) << 112u64) | ((sub[15] as u128) << 120u64));
    assert(le16_u128(bs, lo) == (bs[lo] as u128) | ((bs[lo + 1] as u128) << 8u64)
        | ((bs[lo + 2] as u128) << 16u64) | ((bs[lo + 3] as u128) << 24u64)
        | ((bs[lo + 4] as u128) << 32u64) | ((bs[lo + 5] as u128) << 40u64)
        | ((bs[lo + 6] as u128) << 48u64) | ((bs[lo + 7] as u128) << 56u64)
        | ((bs[lo + 8] as u128) << 64u64) | ((bs[lo + 9] as u128) << 72u64)
        | ((bs[lo + 10] as u128) << 80u64) | ((bs[lo + 11] as u128) << 88u64)
        | ((bs[lo + 12] as u128) << 96u64) | ((bs[lo + 13] as u128) << 104u64)
        | ((bs[lo + 14] as u128) << 112u64) | ((bs[lo + 15] as u128) << 120u64));
}

/// Same bridge at the GF64 8-byte sub-chunk width.
pub proof fn lemma_blk_span_le8(sub: Seq<u8>, bs: Seq<u8>, lo: int)
    requires
        0 <= lo,
        lo + 8 <= bs.len(),
        sub.len() == 8,
        forall |j: int| 0 <= j < 8 ==> #[trigger] sub[j] == bs[lo + j],
    ensures
        le8_u64(sub, 0) == le8_u64(bs, lo),
{
    assert(le8_u64(sub, 0) == (sub[0] as u64) | ((sub[1] as u64) << 8u64)
        | ((sub[2] as u64) << 16u64) | ((sub[3] as u64) << 24u64)
        | ((sub[4] as u64) << 32u64) | ((sub[5] as u64) << 40u64)
        | ((sub[6] as u64) << 48u64) | ((sub[7] as u64) << 56u64));
    assert(le8_u64(bs, lo) == (bs[lo] as u64) | ((bs[lo + 1] as u64) << 8u64)
        | ((bs[lo + 2] as u64) << 16u64) | ((bs[lo + 3] as u64) << 24u64)
        | ((bs[lo + 4] as u64) << 32u64) | ((bs[lo + 5] as u64) << 40u64)
        | ((bs[lo + 6] as u64) << 48u64) | ((bs[lo + 7] as u64) << 56u64));
}

// ===========================================================================
//Scalar-assembly spec faces for the pad bridges (blast-practical:
// all arguments machine-typed; the Seq-typed equals are derived by
// the seq-flat lemmas below, the blast itself only ever sees
// machine scalar formals).
// ===========================================================================

/// flat OR-assembly of 16 scalar bytes (the le16 value form).
pub open spec fn flat16(
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8,
    b8: u8, b9: u8, b10: u8, b11: u8, b12: u8, b13: u8, b14: u8, b15: u8,
) -> u128 {
    (b0 as u128)
        | ((b1 as u128) << 8u64) | ((b2 as u128) << 16u64)
        | ((b3 as u128) << 24u64) | ((b4 as u128) << 32u64)
        | ((b5 as u128) << 40u64) | ((b6 as u128) << 48u64)
        | ((b7 as u128) << 56u64) | ((b8 as u128) << 64u64)
        | ((b9 as u128) << 72u64) | ((b10 as u128) << 80u64)
        | ((b11 as u128) << 88u64) | ((b12 as u128) << 96u64)
        | ((b13 as u128) << 104u64) | ((b14 as u128) << 112u64)
        | ((b15 as u128) << 120u64)
}

/// flat CP-zero-guarded pad assembly of 16 scalar source bytes.
pub open spec fn flatpad16(
    d0: u8, d1: u8, d2: u8, d3: u8, d4: u8, d5: u8, d6: u8, d7: u8,
    d8: u8, d9: u8, d10: u8, d11: u8, d12: u8, d13: u8, d14: u8, d15: u8,
    filled: usize,
) -> u128 {
    (if 0 < filled { d0 as u128 } else { 0u128 })
        | (if 1 < filled { (d1 as u128) << 8u64 } else { 0u128 })
        | (if 2 < filled { (d2 as u128) << 16u64 } else { 0u128 })
        | (if 3 < filled { (d3 as u128) << 24u64 } else { 0u128 })
        | (if 4 < filled { (d4 as u128) << 32u64 } else { 0u128 })
        | (if 5 < filled { (d5 as u128) << 40u64 } else { 0u128 })
        | (if 6 < filled { (d6 as u128) << 48u64 } else { 0u128 })
        | (if 7 < filled { (d7 as u128) << 56u64 } else { 0u128 })
        | (if 8 < filled { (d8 as u128) << 64u64 } else { 0u128 })
        | (if 9 < filled { (d9 as u128) << 72u64 } else { 0u128 })
        | (if 10 < filled { (d10 as u128) << 80u64 } else { 0u128 })
        | (if 11 < filled { (d11 as u128) << 88u64 } else { 0u128 })
        | (if 12 < filled { (d12 as u128) << 96u64 } else { 0u128 })
        | (if 13 < filled { (d13 as u128) << 104u64 } else { 0u128 })
        | (if 14 < filled { (d14 as u128) << 112u64 } else { 0u128 })
        | (if 15 < filled { (d15 as u128) << 120u64 } else { 0u128 })
}

/// flat OR-assembly of 8 scalar bytes (u64 plane).
pub open spec fn flat8(
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8,
) -> u64 {
    (b0 as u64)
        | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
        | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64)
        | ((b7 as u64) << 56u64)
}

/// flat pad assembly of 8 scalar source bytes with a zero-tail guard.
pub open spec fn flatpad8(
    d0: u8, d1: u8, d2: u8, d3: u8, d4: u8, d5: u8, d6: u8, d7: u8,
    filled: usize,
) -> u64 {
    (if 0 < filled { d0 as u64 } else { 0u64 })
        | (if 1 < filled { (d1 as u64) << 8u64 } else { 0u64 })
        | (if 2 < filled { (d2 as u64) << 16u64 } else { 0u64 })
        | (if 3 < filled { (d3 as u64) << 24u64 } else { 0u64 })
        | (if 4 < filled { (d4 as u64) << 32u64 } else { 0u64 })
        | (if 5 < filled { (d5 as u64) << 40u64 } else { 0u64 })
        | (if 6 < filled { (d6 as u64) << 48u64 } else { 0u64 })
        | (if 7 < filled { (d7 as u64) << 56u64 } else { 0u64 })
}

/// le16 of a Seq window == the scalar flat16 of its bytes.
pub proof fn lemma_seq_flat16(
    bs: Seq<u8>,
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8,
    b8: u8, b9: u8, b10: u8, b11: u8, b12: u8, b13: u8, b14: u8, b15: u8,
)
    requires
        bs.len() == 16,
        bs[0] == b0,
        bs[1] == b1,
        bs[2] == b2,
        bs[3] == b3,
        bs[4] == b4,
        bs[5] == b5,
        bs[6] == b6,
        bs[7] == b7,
        bs[8] == b8,
        bs[9] == b9,
        bs[10] == b10,
        bs[11] == b11,
        bs[12] == b12,
        bs[13] == b13,
        bs[14] == b14,
        bs[15] == b15,
    ensures
        le16_u128(bs, 0) == flat16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15),
{
    assert(le16_u128(bs, 0) == (bs[0] as u128) | ((bs[1] as u128) << 8u64)
        | ((bs[2] as u128) << 16u64) | ((bs[3] as u128) << 24u64)
        | ((bs[4] as u128) << 32u64) | ((bs[5] as u128) << 40u64)
        | ((bs[6] as u128) << 48u64) | ((bs[7] as u128) << 56u64)
        | ((bs[8] as u128) << 64u64) | ((bs[9] as u128) << 72u64)
        | ((bs[10] as u128) << 80u64) | ((bs[11] as u128) << 88u64)
        | ((bs[12] as u128) << 96u64) | ((bs[13] as u128) << 104u64)
        | ((bs[14] as u128) << 112u64) | ((bs[15] as u128) << 120u64));
    assert(flat16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
        == (b0 as u128) | ((b1 as u128) << 8u64) | ((b2 as u128) << 16u64)
        | ((b3 as u128) << 24u64) | ((b4 as u128) << 32u64) | ((b5 as u128) << 40u64)
        | ((b6 as u128) << 48u64) | ((b7 as u128) << 56u64) | ((b8 as u128) << 64u64)
        | ((b9 as u128) << 72u64) | ((b10 as u128) << 80u64) | ((b11 as u128) << 88u64)
        | ((b12 as u128) << 96u64) | ((b13 as u128) << 104u64) | ((b14 as u128) << 112u64)
        | ((b15 as u128) << 120u64));
}

/// le16_pad of a Seq window == the scalar flatpad16 of its bytes.
pub proof fn lemma_seq_flatpad16(
    bs: Seq<u8>,
    lo: int,
    filled: usize,
    d0: u8, d1: u8, d2: u8, d3: u8, d4: u8, d5: u8, d6: u8, d7: u8,
    d8: u8, d9: u8, d10: u8, d11: u8, d12: u8, d13: u8, d14: u8, d15: u8,
)
    requires
        0 <= lo,
        filled < 16,
        lo + (filled as int) <= bs.len(),
        (0 < (filled as int) ==> bs[lo] == d0),
        (1 < (filled as int) ==> bs[lo + 1] == d1),
        (2 < (filled as int) ==> bs[lo + 2] == d2),
        (3 < (filled as int) ==> bs[lo + 3] == d3),
        (4 < (filled as int) ==> bs[lo + 4] == d4),
        (5 < (filled as int) ==> bs[lo + 5] == d5),
        (6 < (filled as int) ==> bs[lo + 6] == d6),
        (7 < (filled as int) ==> bs[lo + 7] == d7),
        (8 < (filled as int) ==> bs[lo + 8] == d8),
        (9 < (filled as int) ==> bs[lo + 9] == d9),
        (10 < (filled as int) ==> bs[lo + 10] == d10),
        (11 < (filled as int) ==> bs[lo + 11] == d11),
        (12 < (filled as int) ==> bs[lo + 12] == d12),
        (13 < (filled as int) ==> bs[lo + 13] == d13),
        (14 < (filled as int) ==> bs[lo + 14] == d14),
        (15 < (filled as int) ==> bs[lo + 15] == d15),
    ensures
        le16_pad_u128(bs, lo, filled as int)
            == flatpad16(d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, filled),
{
    assert(le16_pad_u128(bs, lo, filled as int)
        == (if 0 < (filled as int) { bs[lo] as u128 } else { 0u128 })
        | (if 1 < (filled as int) { (bs[lo + 1] as u128) << 8u64 } else { 0u128 })
        | (if 2 < (filled as int) { (bs[lo + 2] as u128) << 16u64 } else { 0u128 })
        | (if 3 < (filled as int) { (bs[lo + 3] as u128) << 24u64 } else { 0u128 })
        | (if 4 < (filled as int) { (bs[lo + 4] as u128) << 32u64 } else { 0u128 })
        | (if 5 < (filled as int) { (bs[lo + 5] as u128) << 40u64 } else { 0u128 })
        | (if 6 < (filled as int) { (bs[lo + 6] as u128) << 48u64 } else { 0u128 })
        | (if 7 < (filled as int) { (bs[lo + 7] as u128) << 56u64 } else { 0u128 })
        | (if 8 < (filled as int) { (bs[lo + 8] as u128) << 64u64 } else { 0u128 })
        | (if 9 < (filled as int) { (bs[lo + 9] as u128) << 72u64 } else { 0u128 })
        | (if 10 < (filled as int) { (bs[lo + 10] as u128) << 80u64 } else { 0u128 })
        | (if 11 < (filled as int) { (bs[lo + 11] as u128) << 88u64 } else { 0u128 })
        | (if 12 < (filled as int) { (bs[lo + 12] as u128) << 96u64 } else { 0u128 })
        | (if 13 < (filled as int) { (bs[lo + 13] as u128) << 104u64 } else { 0u128 })
        | (if 14 < (filled as int) { (bs[lo + 14] as u128) << 112u64 } else { 0u128 })
        | (if 15 < (filled as int) { (bs[lo + 15] as u128) << 120u64 } else { 0u128 }));
}

/// le8 window == scalar flat8.
pub proof fn lemma_seq_flat8(
    bs: Seq<u8>,
    so: int,
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8,
)
    requires
        0 <= so,
        so + 8 <= bs.len(),
        bs[so] == b0,
        bs[so + 1] == b1,
        bs[so + 2] == b2,
        bs[so + 3] == b3,
        bs[so + 4] == b4,
        bs[so + 5] == b5,
        bs[so + 6] == b6,
        bs[so + 7] == b7,
    ensures
        le8_u64(bs, so) == flat8(b0, b1, b2, b3, b4, b5, b6, b7),
{
    assert(le8_u64(bs, so) == (bs[so] as u64) | ((bs[so + 1] as u64) << 8u64)
        | ((bs[so + 2] as u64) << 16u64) | ((bs[so + 3] as u64) << 24u64)
        | ((bs[so + 4] as u64) << 32u64) | ((bs[so + 5] as u64) << 40u64)
        | ((bs[so + 6] as u64) << 48u64) | ((bs[so + 7] as u64) << 56u64));
    assert(flat8(b0, b1, b2, b3, b4, b5, b6, b7)
        == (b0 as u64) | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64)
        | ((b3 as u64) << 24u64) | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64)
        | ((b6 as u64) << 48u64) | ((b7 as u64) << 56u64));
}

/// le8_pad window == scalar flatpad8.
pub proof fn lemma_seq_flatpad8(
    bs: Seq<u8>,
    so: int,
    filled: usize,
    d0: u8, d1: u8, d2: u8, d3: u8, d4: u8, d5: u8, d6: u8, d7: u8,
)
    requires
        0 <= so,
        (0 < (filled as int) ==> bs[so] == d0),
        (1 < (filled as int) ==> bs[so + 1] == d1),
        (2 < (filled as int) ==> bs[so + 2] == d2),
        (3 < (filled as int) ==> bs[so + 3] == d3),
        (4 < (filled as int) ==> bs[so + 4] == d4),
        (5 < (filled as int) ==> bs[so + 5] == d5),
        (6 < (filled as int) ==> bs[so + 6] == d6),
        (7 < (filled as int) ==> bs[so + 7] == d7),
        (filled as int) <= 8,
        so + (filled as int) <= bs.len(),
    ensures
        le8_pad_u64(bs, so, filled as int) == flatpad8(d0, d1, d2, d3, d4, d5, d6, d7, filled),
{
    assert(le8_pad_u64(bs, so, filled as int)
        == (if 0 < (filled as int) { bs[so] as u64 } else { 0u64 })
        | (if 1 < (filled as int) { (bs[so + 1] as u64) << 8u64 } else { 0u64 })
        | (if 2 < (filled as int) { (bs[so + 2] as u64) << 16u64 } else { 0u64 })
        | (if 3 < (filled as int) { (bs[so + 3] as u64) << 24u64 } else { 0u64 })
        | (if 4 < (filled as int) { (bs[so + 4] as u64) << 32u64 } else { 0u64 })
        | (if 5 < (filled as int) { (bs[so + 5] as u64) << 40u64 } else { 0u64 })
        | (if 6 < (filled as int) { (bs[so + 6] as u64) << 48u64 } else { 0u64 })
        | (if 7 < (filled as int) { (bs[so + 7] as u64) << 56u64 } else { 0u64 }));
}

/// The scalar-side pad bridge: flat16(b*) == flatpad16(d*, filled)
/// under the guarded-row hypotheses (one blast over machine
/// scalars; the Seq-index and Int-guard hazards never enter).
/// The scalar-side pad bridge at the 8-byte width.
pub proof fn lemma_scalars_pad8(
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8,
    d0: u8, d1: u8, d2: u8, d3: u8, d4: u8, d5: u8, d6: u8, d7: u8,
    filled: usize,
)
    requires
        filled <= 8,
        (0 < filled ==> b0 == d0),
        (1 < filled ==> b1 == d1),
        (2 < filled ==> b2 == d2),
        (3 < filled ==> b3 == d3),
        (4 < filled ==> b4 == d4),
        (5 < filled ==> b5 == d5),
        (6 < filled ==> b6 == d6),
        (7 < filled ==> b7 == d7),
        (0 < filled || b0 == 0u8),
        (1 < filled || b1 == 0u8),
        (2 < filled || b2 == 0u8),
        (3 < filled || b3 == 0u8),
        (4 < filled || b4 == 0u8),
        (5 < filled || b5 == 0u8),
        (6 < filled || b6 == 0u8),
        (7 < filled || b7 == 0u8),
    ensures
        flat8(b0, b1, b2, b3, b4, b5, b6, b7)
            == flatpad8(d0, d1, d2, d3, d4, d5, d6, d7, filled),
{
    assert((b0 as u64)
        | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
        | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64)
        | ((b7 as u64) << 56u64)
        == (if 0 < filled { d0 as u64 } else { 0u64 })
        | (if 1 < filled { (d1 as u64) << 8u64 } else { 0u64 })
        | (if 2 < filled { (d2 as u64) << 16u64 } else { 0u64 })
        | (if 3 < filled { (d3 as u64) << 24u64 } else { 0u64 })
        | (if 4 < filled { (d4 as u64) << 32u64 } else { 0u64 })
        | (if 5 < filled { (d5 as u64) << 40u64 } else { 0u64 })
        | (if 6 < filled { (d6 as u64) << 48u64 } else { 0u64 })
        | (if 7 < filled { (d7 as u64) << 56u64 } else { 0u64 })) by (bit_vector)
        requires
            (0 < filled ==> b0 == d0),
            (1 < filled ==> b1 == d1),
            (2 < filled ==> b2 == d2),
            (3 < filled ==> b3 == d3),
            (4 < filled ==> b4 == d4),
            (5 < filled ==> b5 == d5),
            (6 < filled ==> b6 == d6),
            (7 < filled ==> b7 == d7),
            (0 < filled || b0 == 0u8),
            (1 < filled || b1 == 0u8),
            (2 < filled || b2 == 0u8),
            (3 < filled || b3 == 0u8),
            (4 < filled || b4 == 0u8),
            (5 < filled || b5 == 0u8),
            (6 < filled || b6 == 0u8),
            (7 < filled || b7 == 0u8),
    ;
}

pub proof fn lemma_scalars_pad16(
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8,
    b8: u8, b9: u8, b10: u8, b11: u8, b12: u8, b13: u8, b14: u8, b15: u8,
    d0: u8, d1: u8, d2: u8, d3: u8, d4: u8, d5: u8, d6: u8, d7: u8,
    d8: u8, d9: u8, d10: u8, d11: u8, d12: u8, d13: u8, d14: u8, d15: u8,
    filled: usize,
)
    requires
        filled < 16,
        (0 < filled ==> b0 == d0),
        (1 < filled ==> b1 == d1),
        (2 < filled ==> b2 == d2),
        (3 < filled ==> b3 == d3),
        (4 < filled ==> b4 == d4),
        (5 < filled ==> b5 == d5),
        (6 < filled ==> b6 == d6),
        (7 < filled ==> b7 == d7),
        (8 < filled ==> b8 == d8),
        (9 < filled ==> b9 == d9),
        (10 < filled ==> b10 == d10),
        (11 < filled ==> b11 == d11),
        (12 < filled ==> b12 == d12),
        (13 < filled ==> b13 == d13),
        (14 < filled ==> b14 == d14),
        (15 < filled ==> b15 == d15),
        (0 < filled || b0 == 0u8),
        (1 < filled || b1 == 0u8),
        (2 < filled || b2 == 0u8),
        (3 < filled || b3 == 0u8),
        (4 < filled || b4 == 0u8),
        (5 < filled || b5 == 0u8),
        (6 < filled || b6 == 0u8),
        (7 < filled || b7 == 0u8),
        (8 < filled || b8 == 0u8),
        (9 < filled || b9 == 0u8),
        (10 < filled || b10 == 0u8),
        (11 < filled || b11 == 0u8),
        (12 < filled || b12 == 0u8),
        (13 < filled || b13 == 0u8),
        (14 < filled || b14 == 0u8),
        (15 < filled || b15 == 0u8),
    ensures
        flat16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15)
            == flatpad16(d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, filled),
{
    assert((b0 as u128)
        | ((b1 as u128) << 8u64) | ((b2 as u128) << 16u64) | ((b3 as u128) << 24u64)
        | ((b4 as u128) << 32u64) | ((b5 as u128) << 40u64) | ((b6 as u128) << 48u64)
        | ((b7 as u128) << 56u64) | ((b8 as u128) << 64u64) | ((b9 as u128) << 72u64)
        | ((b10 as u128) << 80u64) | ((b11 as u128) << 88u64) | ((b12 as u128) << 96u64)
        | ((b13 as u128) << 104u64) | ((b14 as u128) << 112u64)
        | ((b15 as u128) << 120u64)
        == (if 0 < filled { d0 as u128 } else { 0u128 })
        | (if 1 < filled { (d1 as u128) << 8u64 } else { 0u128 })
        | (if 2 < filled { (d2 as u128) << 16u64 } else { 0u128 })
        | (if 3 < filled { (d3 as u128) << 24u64 } else { 0u128 })
        | (if 4 < filled { (d4 as u128) << 32u64 } else { 0u128 })
        | (if 5 < filled { (d5 as u128) << 40u64 } else { 0u128 })
        | (if 6 < filled { (d6 as u128) << 48u64 } else { 0u128 })
        | (if 7 < filled { (d7 as u128) << 56u64 } else { 0u128 })
        | (if 8 < filled { (d8 as u128) << 64u64 } else { 0u128 })
        | (if 9 < filled { (d9 as u128) << 72u64 } else { 0u128 })
        | (if 10 < filled { (d10 as u128) << 80u64 } else { 0u128 })
        | (if 11 < filled { (d11 as u128) << 88u64 } else { 0u128 })
        | (if 12 < filled { (d12 as u128) << 96u64 } else { 0u128 })
        | (if 13 < filled { (d13 as u128) << 104u64 } else { 0u128 })
        | (if 14 < filled { (d14 as u128) << 112u64 } else { 0u128 })
        | (if 15 < filled { (d15 as u128) << 120u64 } else { 0u128 })) by (bit_vector)
        requires
            (0 < filled ==> b0 == d0),
            (1 < filled ==> b1 == d1),
            (2 < filled ==> b2 == d2),
            (3 < filled ==> b3 == d3),
            (4 < filled ==> b4 == d4),
            (5 < filled ==> b5 == d5),
            (6 < filled ==> b6 == d6),
            (7 < filled ==> b7 == d7),
            (8 < filled ==> b8 == d8),
            (9 < filled ==> b9 == d9),
            (10 < filled ==> b10 == d10),
            (11 < filled ==> b11 == d11),
            (12 < filled ==> b12 == d12),
            (13 < filled ==> b13 == d13),
            (14 < filled ==> b14 == d14),
            (15 < filled ==> b15 == d15),
            (0 < filled || b0 == 0u8),
            (1 < filled || b1 == 0u8),
            (2 < filled || b2 == 0u8),
            (3 < filled || b3 == 0u8),
            (4 < filled || b4 == 0u8),
            (5 < filled || b5 == 0u8),
            (6 < filled || b6 == 0u8),
            (7 < filled || b7 == 0u8),
            (8 < filled || b8 == 0u8),
            (9 < filled || b9 == 0u8),
            (10 < filled || b10 == 0u8),
            (11 < filled || b11 == 0u8),
            (12 < filled || b12 == 0u8),
            (13 < filled || b13 == 0u8),
            (14 < filled || b14 == 0u8),
            (15 < filled || b15 == 0u8),
    ;
}

// ===========================================================================
// VoleHasher at lambda 128 (upstream :64-140 at F = GF128;
// SDLength = 5*16+8 = 88 bytes, OutputLength = Sum<U16, B> = 18 bytes
// -- the typenum Sum/<Prod> algebra lowered to byte counts).
// ===========================================================================

pub struct VoleHasher128 {
    /// r: [F; 4] (upstream :70)
    pub r: [u128; 4],
    /// s: F
    pub s: u128,
    /// t: GF64
    pub t: u64,
}

impl VoleHasher128 {
    /// Origin Rust (:119-121, from_r_s_t): Self { r, s, t }.
    pub fn from_r_s_t(r: [u128; 4], s: u128, t: u64) -> (h: Self)
        ensures
            h.r == r,
            h.s == s,
            h.t == t,
    {
        VoleHasher128 { r, s, t }
    }

    /// Origin Rust (:34-42, VoleHasherInit::new_vole_hasher at
    /// GF128): array::from_fn over the four r blocks + s + t.
    pub fn new_vole_hasher(sd: &[u8]) -> (h: Self)
        requires
            sd.len() == 5 * GF128_LENGTH_BYTES + 8,
        ensures
            h.r[0] == le16_u128(sd@, 0),
            h.r[1] == le16_u128(sd@, 16),
            h.r[2] == le16_u128(sd@, 32),
            h.r[3] == le16_u128(sd@, 48),
            h.s == le16_u128(sd@, 64),
            h.t == le8_u64(sd@, 80),
    {
        let s0 = &sd[0..16];
        let s1 = &sd[16..32];
        let s2 = &sd[32..48];
        let s3 = &sd[48..64];
        let s4 = &sd[64..80];
        let s5 = &sd[80..88];
        let r0 = gf128_from_bytes(s0);
        let r1 = gf128_from_bytes(s1);
        let r2 = gf128_from_bytes(s2);
        let r3 = gf128_from_bytes(s3);
        let sv = gf128_from_bytes(s4);
        let tv = gf64_from_bytes(s5);
        proof {
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r0, j) == (s0[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r1, j) == (s1[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r2, j) == (s2[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r3, j) == (s3[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(sv, j) == (s4[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte64(tv, j) == (s5[j] as u64) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                s0[j] == sd[j] by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                s1[j] == sd[16 + j] by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                s2[j] == sd[32 + j] by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                s3[j] == sd[48 + j] by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                s4[j] == sd[64 + j] by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                s5[j] == sd[80 + j] by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r0, j) == (sd[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r1, j) == (sd[16 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r2, j) == (sd[32 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r3, j) == (sd[48 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(sv, j) == (sd[64 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte64(tv, j) == (sd[80 + j] as u64) by {
            }
            lemma_plane16_le(sd@, 0, r0);
            lemma_plane16_le(sd@, 16, r1);
            lemma_plane16_le(sd@, 32, r2);
            lemma_plane16_le(sd@, 48, r3);
            lemma_plane16_le(sd@, 64, sv);
            lemma_plane8_le64(sd@, 80, tv);
        }
        VoleHasher128 {
            r: [r0, r1, r2, r3],
            s: sv,
            t: tv,
        }
    }

    /// Origin Rust (:128-133, process_block):
    ///     fn process_block(&self, h0: &mut F, h1: &mut GF64,
    ///                      data: &[u8]) {
    ///         *h0 = *h0 * self.s + F::from(data);
    ///         for data in data.chunks_exact(8) {
    ///             *h1 = *h1 * self.t + GF64::from(data); } }
    /// The inner chunks_exact(8) loop keeps its while-loop shape
    /// (two GF64 substeps per F-block at this axis); F::from lowers
    /// to gf128_from_bytes, GF64::from to gf64_from_bytes.
    pub fn process_block(self: &Self, h0: &mut u128, h1: &mut u64, data: &[u8])
        requires
            data.len() == GF128_LENGTH_BYTES,
        ensures
            *final(h0) == gf128_mul_spec(*old(h0), self.s) ^ le16_u128(data@, 0),
            *final(h1)
                == gf64_mul_spec(
                    gf64_mul_spec(*old(h1), self.t) ^ le8_u64(data@, 0),
                    self.t,
                ) ^ le8_u64(data@, 8),
    {
        // *h0 = *h0 * self.s + F::from(data)
        let f0 = gf128_from_bytes(data);
        proof {
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(f0, j) == (data@[j] as u128) by {
            }
            lemma_plane16_le(data@, 0, f0);
        }
        let h0_pre = *h0;
        let m0 = gf128_mul(h0_pre, self.s);
        // for data in data.chunks_exact(8): *h1 = *h1 * t + GF64::from
        let mut h1w: u64 = *h1;
        let mut j: usize = 0;
        while j < 2
            invariant
                j <= 2,
                data.len() == GF128_LENGTH_BYTES,
                j == 0 ==> h1w == *old(h1),
                j == 1
                    ==> h1w == gf64_mul_spec(*old(h1), self.t) ^ le8_u64(data@, 0),
                j == 2
                    ==> h1w == gf64_mul_spec(
                        gf64_mul_spec(*old(h1), self.t) ^ le8_u64(data@, 0),
                        self.t,
                    ) ^ le8_u64(data@, 8),
            decreases 2 - j,
        {
            let sub = &data[j * 8..(j + 1) * 8];
            let fv = gf64_from_bytes(sub);
            proof {
                assert forall |k: int| 0 <= k < 8 implies
                    #[trigger]
                    byte64(fv, k) == (sub[k] as u64) by {
                }
                assert forall |k: int| 0 <= k < 8 implies
                    #[trigger]
                    sub[k] == data[(j * 8) as int + k] by {
                }
                lemma_plane8_le64(sub@, 0, fv);
                lemma_blk_span_le8(sub@, data@, (j * 8) as int);
            }
            let h1_old = h1w;
            h1w = gf64_mul(h1_old, self.t) ^ fv;
            proof {
                // the exec update equals the spec step at offset 8j
                assert(h1w == gf64_mul_spec(h1_old, self.t) ^ le8_u64(data@, (j * 8) as int));
            }
            j += 1;
        }
        *h0 = m0 ^ f0;
        proof {
            assert(*h0 == gf128_mul_spec(h0_pre, self.s) ^ le16_u128(data@, 0));
            assert(h0_pre == *old(h0));
        }
        *h1 = h1w;
    }
}







// ===========================================================================
// VoleHasher lambda-128 continued:: the padded tail face, the split
// driver and the process wrapper (upstream :91-117, :54-59).
// ===========================================================================


/// General-offset plain 8-byte span bridge (rows form).
pub proof fn lemma_span_le8_off(sub: Seq<u8>, so: int, bs: Seq<u8>, lo: int)
    requires
        0 <= so,
        0 <= lo,
        sub.len() == 16,
        so + 8 <= sub.len(),
        lo + 8 <= bs.len(),
        sub[so] == bs[lo],
        sub[so + 1] == bs[lo + 1],
        sub[so + 2] == bs[lo + 2],
        sub[so + 3] == bs[lo + 3],
        sub[so + 4] == bs[lo + 4],
        sub[so + 5] == bs[lo + 5],
        sub[so + 6] == bs[lo + 6],
        sub[so + 7] == bs[lo + 7],
    ensures
        le8_u64(sub, so) == le8_u64(bs, lo),
{
}



impl VoleHasher128 {
    /// Origin Rust (:135-139, process_unpadded_block):
    ///     fn process_unpadded_block(&self, h0: &mut F,
    ///                                h1: &mut GF64, data: &[u8]) {
    ///         let mut buf = Array::<u8, F::Length>::default();
    ///         buf[..data.len()].copy_from_slice(data);
    ///         self.process_block(h0, h1, &buf); }
    pub fn process_unpadded_block(self: &Self, h0: &mut u128, h1: &mut u64, data: &[u8])
        requires
            data.len() < GF128_LENGTH_BYTES,
        ensures
            *final(h0)
                == gf128_mul_spec(*old(h0), self.s) ^ le16_pad_u128(data@, 0, data.len() as int),
            *final(h1)
                == gf64_mul_spec(
                    gf64_mul_spec(*old(h1), self.t)
                        ^ le8_pad_u64(
                            data@,
                            0,
                            (if data.len() < 8 { data.len() as int } else { 8 }),
                        ),
                    self.t,
                ) ^ le8_pad_u64(
                    data@,
                    8,
                    (if data.len() < 8 { 0 } else { data.len() as int - 8 }),
                ),
    {
        let mut buf: [u8; 16] = [0; 16];
        let mut j: usize = 0;
        while j < data.len()
            invariant
                j <= data.len(),
                data.len() <= 16,
                buf.len() == 16,
                forall |k: int| 0 <= k < j ==> buf[k] == data[k],
                forall |k: int| j <= k < 16 ==> buf[k] == 0,
            decreases data.len() - j,
        {
            buf[j] = data[j];
            j += 1;
        }
        proof {
            assert forall |k: int| 0 <= k < 16 implies
                #[trigger]
                buf[k] == (if k < data.len() as int { data[k] } else { 0u8 }) by {
            }
            assert(buf@.len() == 16);
        }
        let bf = &buf[..];
        let bf0 = &buf[..];
        let fl: usize = data.len();
        let f0: usize = if fl < 8 { fl } else { 8 };
        let f1: usize = (fl - (if fl < 8 { fl } else { 8 }));
        self.process_block(h0, h1, bf0);
        proof {
            // scalar hoists: all 16 buffer bytes as machine
            // ghosts, the filled count, and the guarded rows
            // (the pad bridge runs entirely over machine scalar
            // formals; the le16/le8 sides enter only through
            // the seq-flat lemma pair)
            let b0: u8 = buf[0];
            let b1: u8 = buf[1];
            let b2: u8 = buf[2];
            let b3: u8 = buf[3];
            let b4: u8 = buf[4];
            let b5: u8 = buf[5];
            let b6: u8 = buf[6];
            let b7: u8 = buf[7];
            let b8: u8 = buf[8];
            let b9: u8 = buf[9];
            let b10: u8 = buf[10];
            let b11: u8 = buf[11];
            let b12: u8 = buf[12];
            let b13: u8 = buf[13];
            let b14: u8 = buf[14];
            let b15: u8 = buf[15];
            let fl: usize = data.len();
            assert(0 < fl ==> buf[0] == data[0]);
            assert(0 < fl || buf[0] == 0u8);
            assert(1 < fl ==> buf[1] == data[1]);
            assert(1 < fl || buf[1] == 0u8);
            assert(2 < fl ==> buf[2] == data[2]);
            assert(2 < fl || buf[2] == 0u8);
            assert(3 < fl ==> buf[3] == data[3]);
            assert(3 < fl || buf[3] == 0u8);
            assert(4 < fl ==> buf[4] == data[4]);
            assert(4 < fl || buf[4] == 0u8);
            assert(5 < fl ==> buf[5] == data[5]);
            assert(5 < fl || buf[5] == 0u8);
            assert(6 < fl ==> buf[6] == data[6]);
            assert(6 < fl || buf[6] == 0u8);
            assert(7 < fl ==> buf[7] == data[7]);
            assert(7 < fl || buf[7] == 0u8);
            assert(8 < fl ==> buf[8] == data[8]);
            assert(8 < fl || buf[8] == 0u8);
            assert(9 < fl ==> buf[9] == data[9]);
            assert(9 < fl || buf[9] == 0u8);
            assert(10 < fl ==> buf[10] == data[10]);
            assert(10 < fl || buf[10] == 0u8);
            assert(11 < fl ==> buf[11] == data[11]);
            assert(11 < fl || buf[11] == 0u8);
            assert(12 < fl ==> buf[12] == data[12]);
            assert(12 < fl || buf[12] == 0u8);
            assert(13 < fl ==> buf[13] == data[13]);
            assert(13 < fl || buf[13] == 0u8);
            assert(14 < fl ==> buf[14] == data[14]);
            assert(14 < fl || buf[14] == 0u8);
            assert(15 < fl ==> buf[15] == data[15]);
            assert(15 < fl || buf[15] == 0u8);
            let d0: u8 = if 0 < fl { data[0] } else { 0u8 };
            let d1: u8 = if 1 < fl { data[1] } else { 0u8 };
            let d2: u8 = if 2 < fl { data[2] } else { 0u8 };
            let d3: u8 = if 3 < fl { data[3] } else { 0u8 };
            let d4: u8 = if 4 < fl { data[4] } else { 0u8 };
            let d5: u8 = if 5 < fl { data[5] } else { 0u8 };
            let d6: u8 = if 6 < fl { data[6] } else { 0u8 };
            let d7: u8 = if 7 < fl { data[7] } else { 0u8 };
            let d8: u8 = if 8 < fl { data[8] } else { 0u8 };
            let d9: u8 = if 9 < fl { data[9] } else { 0u8 };
            let d10: u8 = if 10 < fl { data[10] } else { 0u8 };
            let d11: u8 = if 11 < fl { data[11] } else { 0u8 };
            let d12: u8 = if 12 < fl { data[12] } else { 0u8 };
            let d13: u8 = if 13 < fl { data[13] } else { 0u8 };
            let d14: u8 = if 14 < fl { data[14] } else { 0u8 };
            let d15: u8 = if 15 < fl { data[15] } else { 0u8 };
            assert(0 < fl ==> b0 == d0);
            assert(0 < fl || b0 == 0u8);
            assert(1 < fl ==> b1 == d1);
            assert(1 < fl || b1 == 0u8);
            assert(2 < fl ==> b2 == d2);
            assert(2 < fl || b2 == 0u8);
            assert(3 < fl ==> b3 == d3);
            assert(3 < fl || b3 == 0u8);
            assert(4 < fl ==> b4 == d4);
            assert(4 < fl || b4 == 0u8);
            assert(5 < fl ==> b5 == d5);
            assert(5 < fl || b5 == 0u8);
            assert(6 < fl ==> b6 == d6);
            assert(6 < fl || b6 == 0u8);
            assert(7 < fl ==> b7 == d7);
            assert(7 < fl || b7 == 0u8);
            assert(8 < fl ==> b8 == d8);
            assert(8 < fl || b8 == 0u8);
            assert(9 < fl ==> b9 == d9);
            assert(9 < fl || b9 == 0u8);
            assert(10 < fl ==> b10 == d10);
            assert(10 < fl || b10 == 0u8);
            assert(11 < fl ==> b11 == d11);
            assert(11 < fl || b11 == 0u8);
            assert(12 < fl ==> b12 == d12);
            assert(12 < fl || b12 == 0u8);
            assert(13 < fl ==> b13 == d13);
            assert(13 < fl || b13 == 0u8);
            assert(14 < fl ==> b14 == d14);
            assert(14 < fl || b14 == 0u8);
            assert(15 < fl ==> b15 == d15);
            assert(15 < fl || b15 == 0u8);
            lemma_seq_flat16(buf@, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15);
            lemma_seq_flatpad16(data@, 0, fl, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15);
            lemma_scalars_pad16(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, fl);
            lemma_seq_flat8(buf@, 0, b0, b1, b2, b3, b4, b5, b6, b7);
            lemma_seq_flatpad8(data@, 0, f0, d0, d1, d2, d3, d4, d5, d6, d7);
            lemma_scalars_pad8(b0, b1, b2, b3, b4, b5, b6, b7, d0, d1, d2, d3, d4, d5, d6, d7, f0);
            lemma_seq_flat8(buf@, 8, b8, b9, b10, b11, b12, b13, b14, b15);
            if fl > 8 {
                lemma_seq_flatpad8(data@, 8, f1, d8, d9, d10, d11, d12, d13, d14, d15);
            } else {
                assert(f1 == 0);
                assert(le8_pad_u64(data@, 8, 0)
                    == 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64);
                assert(0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 == 0u64) by (bit_vector);
                assert(le8_pad_u64(data@, 8, 0) == 0u64);
            }
            lemma_scalars_pad8(b8, b9, b10, b11, b12, b13, b14, b15, d8, d9, d10, d11, d12, d13, d14, d15, f1);
            assert(le16_u128(buf@, 0) == le16_pad_u128(data@, 0, fl as int));
            assert(le8_u64(buf@, 0) == le8_pad_u64(data@, 0, f0 as int));
            assert(le8_u64(buf@, 8) == le8_pad_u64(data@, 8, f1 as int));
        }
    }

    /// Origin Rust (:91-117, process_split): the chunks_exact block
    /// loop + the unpadded remainder + the h2/h3 recombination and
    /// the zip(chain(h2.as_bytes(), h3.take(2)), x1) xor output
    /// assembly (:99-116). The chunk parse (nb full blocks, rem
    /// tail bytes) rides as requires-checked parameters -- the
    /// value counterpart of the upstream chunks_exact/remainder
    /// iterator split (twin convention: explicit parsed-count args
    /// keep the ensures free of machine div/mod algebra).
    pub fn process_split(self: &Self, x0: &[u8], x1: &[u8], nb: usize, rem: usize) -> (out: [u8; 18])
        requires
            x1.len() == 18,
            nb == x0.len() / 16,
            rem == x0.len() % 16,
        ensures
            forall |j: int| 0 <= j < 18 ==> #[trigger] (out[j] as u128)
                == ((if j < 16 {
                    byte128(
                        gf128_mul_spec(
                            self.r[0],
                            vh0_total_128(self.s, x0@, nb as nat, rem as nat, 0),
                        ) ^ gf128_mul_bits(
                            self.r[1],
                            (vh1_total_128(self.t, x0@, nb as nat, rem as nat, 0) as u128),
                            64nat,
                        ),
                        j,
                    )
                } else {
                    byte128(
                        gf128_mul_spec(
                            self.r[2],
                            vh0_total_128(self.s, x0@, nb as nat, rem as nat, 0),
                        ) ^ gf128_mul_bits(
                            self.r[3],
                            (vh1_total_128(self.t, x0@, nb as nat, rem as nat, 0) as u128),
                            64nat,
                        ),
                        (j - 16),
                    )
                }) ^ (x1[j] as u128)),
    {
        let nbi: usize = nb;
        let remi: usize = rem;
        let mut h0: u128 = 0;
        let mut h1: u64 = 0;
        let mut i: usize = 0;
        while i < nbi
            invariant
                i <= nbi,
                nbi == nb,
                remi == rem,
                nb * 16 + rem == x0.len(),
                nb <= x0.len(),
                h0 == vh0_128(self.s, x0@, i as nat, 0),
                h1 == vh1_128(self.t, x0@, i as nat, 0),
            decreases nbi - i,
        {
            let blk = &x0[i * 16..(i + 1) * 16];
            self.process_block(&mut h0, &mut h1, blk);
            proof {
                lemma_vh0_128_unfold(self.s, x0@, (i + 1) as nat, 0);
                lemma_vh1_128_unfold(self.t, x0@, (i + 1) as nat, 0);
                assert(blk@ == x0@.subrange((i * 16) as int, ((i + 1) * 16) as int));
                assert forall |k: int| 0 <= k < 16 implies
                    #[trigger]
                    blk@[k] == x0@[(i * 16) as int + k] by {
                    vstd::seq::lemma_seq_subrange_index(
                        x0@,
                        (i * 16) as int,
                        ((i + 1) * 16) as int,
                        k,
                    );
                }
                // rows-form span callers (literal positions; the
                // buffer's pointwise facts instantiate the rows and
                // the unshifted-index forall triggers fire on the
                // flattened OR terms)
                assert(blk[0] == x0[(i * 16) as int]);
                assert(blk[1] == x0[((i * 16) as int) + 1]);
                assert(blk[2] == x0[((i * 16) as int) + 2]);
                assert(blk[3] == x0[((i * 16) as int) + 3]);
                assert(blk[4] == x0[((i * 16) as int) + 4]);
                assert(blk[5] == x0[((i * 16) as int) + 5]);
                assert(blk[6] == x0[((i * 16) as int) + 6]);
                assert(blk[7] == x0[((i * 16) as int) + 7]);
                assert(blk[8 as int] == x0[((i * 16) as int) + 8]);
                assert(blk[9 as int] == x0[((i * 16) as int) + 9]);
                assert(blk[10 as int] == x0[((i * 16) as int) + 10]);
                assert(blk[11 as int] == x0[((i * 16) as int) + 11]);
                assert(blk[12 as int] == x0[((i * 16) as int) + 12]);
                assert(blk[13 as int] == x0[((i * 16) as int) + 13]);
                assert(blk[14 as int] == x0[((i * 16) as int) + 14]);
                assert(blk[15 as int] == x0[((i * 16) as int) + 15]);
                lemma_blk_span_le16(blk@, x0@, (i * 16) as int);
                lemma_span_le8_off(blk@, 0, x0@, (i * 16) as int);
                lemma_span_le8_off(blk@, 8, x0@, ((i * 16) as int) + 8);
                assert(vstep128(
                    self.s,
                    vh0_128(self.s, x0@, i as nat, 0),
                    x0@,
                    (i * 16) as int,
                ) == gf128_mul_spec(
                    vh0_128(self.s, x0@, i as nat, 0),
                    self.s,
                ) ^ le16_u128(x0@, (i * 16) as int));
                assert(vh0_128(self.s, x0@, (i + 1) as nat, 0)
                    == gf128_mul_spec(
                        vh0_128(self.s, x0@, i as nat, 0),
                        self.s,
                    ) ^ le16_u128(x0@, (i * 16) as int));
                assert(h0 == vh0_128(self.s, x0@, (i + 1) as nat, 0));
                assert(vh1_128(self.t, x0@, (i + 1) as nat, 0)
                    == gf64_mul_spec(
                        gf64_mul_spec(vh1_128(self.t, x0@, i as nat, 0), self.t)
                            ^ le8_u64(x0@, (i * 16) as int),
                        self.t,
                    ) ^ le8_u64(x0@, ((i * 16) as int) + 8));
                assert(h1 == vh1_128(self.t, x0@, (i + 1) as nat, 0));
            }
            i += 1;
        }
        // the unpadded remainder (:104-106) -- the parent-side pad
        // bridging runs over machine scalar ghosts (the same
        // scalar-pad lemma family; no Seq-index or Int enters any
        // blast)
        if rem != 0 {
            let fh0x: usize = if rem < 8 { rem } else { 8 };
            let fh1x: usize = (rem - (if rem < 8 { rem } else { 8 }));
            let tail = &x0[nbi * 16..];
            proof {
                let fh0: usize = fh0x;
                let fh1: usize = fh1x;
                assert(tail@.len() == (rem as int));
                assert forall |k: int| 0 <= k < (rem as int) implies
                    #[trigger]
                    tail[k] == x0[((nbi * 16) as int) + k] by {
                }
            }
            // scalar rows: parent window bytes vs tail window bytes
            proof {
                let fl2: usize = rem;
                let h0s = (nbi * 16) as int;
                let e0: u8 = if 0 < fl2 { x0[h0s + 0] } else { 0u8 };
                assert(0 < fl2 ==> tail[0] == x0[h0s + 0]);
                let e1: u8 = if 1 < fl2 { x0[h0s + 1] } else { 0u8 };
                assert(1 < fl2 ==> tail[1] == x0[h0s + 1]);
                let e2: u8 = if 2 < fl2 { x0[h0s + 2] } else { 0u8 };
                assert(2 < fl2 ==> tail[2] == x0[h0s + 2]);
                let e3: u8 = if 3 < fl2 { x0[h0s + 3] } else { 0u8 };
                assert(3 < fl2 ==> tail[3] == x0[h0s + 3]);
                let e4: u8 = if 4 < fl2 { x0[h0s + 4] } else { 0u8 };
                assert(4 < fl2 ==> tail[4] == x0[h0s + 4]);
                let e5: u8 = if 5 < fl2 { x0[h0s + 5] } else { 0u8 };
                assert(5 < fl2 ==> tail[5] == x0[h0s + 5]);
                let e6: u8 = if 6 < fl2 { x0[h0s + 6] } else { 0u8 };
                assert(6 < fl2 ==> tail[6] == x0[h0s + 6]);
                let e7: u8 = if 7 < fl2 { x0[h0s + 7] } else { 0u8 };
                assert(7 < fl2 ==> tail[7] == x0[h0s + 7]);
                let e8: u8 = if 8 < fl2 { x0[h0s + 8] } else { 0u8 };
                assert(8 < fl2 ==> tail[8] == x0[h0s + 8]);
                let e9: u8 = if 9 < fl2 { x0[h0s + 9] } else { 0u8 };
                assert(9 < fl2 ==> tail[9] == x0[h0s + 9]);
                let e10: u8 = if 10 < fl2 { x0[h0s + 10] } else { 0u8 };
                assert(10 < fl2 ==> tail[10] == x0[h0s + 10]);
                let e11: u8 = if 11 < fl2 { x0[h0s + 11] } else { 0u8 };
                assert(11 < fl2 ==> tail[11] == x0[h0s + 11]);
                let e12: u8 = if 12 < fl2 { x0[h0s + 12] } else { 0u8 };
                assert(12 < fl2 ==> tail[12] == x0[h0s + 12]);
                let e13: u8 = if 13 < fl2 { x0[h0s + 13] } else { 0u8 };
                assert(13 < fl2 ==> tail[13] == x0[h0s + 13]);
                let e14: u8 = if 14 < fl2 { x0[h0s + 14] } else { 0u8 };
                assert(14 < fl2 ==> tail[14] == x0[h0s + 14]);
                let e15: u8 = if 15 < fl2 { x0[h0s + 15] } else { 0u8 };
                assert(15 < fl2 ==> tail[15] == x0[h0s + 15]);
                lemma_seq_flatpad16(x0@, h0s, fl2, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15);
                lemma_seq_flatpad16(tail@, 0, fl2, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15);
                assert(le16_pad_u128(tail@, 0, fl2 as int)
                    == le16_pad_u128(x0@, h0s, fl2 as int));
                // the two 8-byte GF64 sub-chunks: filled counts clamp
                if rem > 8 {
                    assert(le8_pad_u64(tail@, 8, fh1x as int)
                        == le8_pad_u64(x0@, h0s + 8, fh1x as int)) by {
                        lemma_seq_flatpad8(x0@, h0s + 8, fh1x, e8, e9, e10, e11, e12, e13, e14, e15);
                        lemma_seq_flatpad8(tail@, 8, fh1x, e8, e9, e10, e11, e12, e13, e14, e15);
                    }
                } else {
                    assert(fh1x == 0);
                    assert(le8_pad_u64(tail@, 8, 0) == 0u64) by {
                        assert(le8_pad_u64(tail@, 8, 0)
                            == 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64);
                        assert(0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 == 0u64) by (bit_vector);
                    }
                    assert(le8_pad_u64(x0@, h0s + 8, 0) == 0u64) by {
                        assert(le8_pad_u64(x0@, h0s + 8, 0)
                            == 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64);
                        assert(0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 | 0u64 == 0u64) by (bit_vector);
                    }
                }
                lemma_seq_flatpad8(x0@, h0s, fh0x, e0, e1, e2, e3, e4, e5, e6, e7);
                lemma_seq_flatpad8(tail@, 0, fh0x, e0, e1, e2, e3, e4, e5, e6, e7);
                assert(le8_pad_u64(tail@, 0, fh0x as int)
                    == le8_pad_u64(x0@, h0s, fh0x as int));
                assert(vh0_total_128(self.s, x0@, nb as nat, rem as nat, 0)
                    == gf128_mul_spec(
                        vh0_128(self.s, x0@, nb as nat, 0),
                        self.s,
                    ) ^ le16_pad_u128(x0@, h0s, rem as int));
                assert(vh1_total_128(self.t, x0@, nb as nat, rem as nat, 0)
                    == gf64_mul_spec(
                        gf64_mul_spec(vh1_128(self.t, x0@, nb as nat, 0), self.t)
                            ^ le8_pad_u64(x0@, h0s, fh0x as int),
                        self.t,
                    ) ^ le8_pad_u64(x0@, h0s + 8, fh1x as int));
            }
            self.process_unpadded_block(&mut h0, &mut h1, tail);
            proof {
                assert(h0 == vh0_total_128(self.s, x0@, nb as nat, rem as nat, 0));
                assert(h1 == vh1_total_128(self.t, x0@, nb as nat, rem as nat, 0));
            }
        } else {
            proof {
                assert(vh0_total_128(self.s, x0@, nb as nat, 0, 0)
                    == vh0_128(self.s, x0@, nb as nat, 0));
                assert(vh1_total_128(self.t, x0@, nb as nat, 0, 0)
                    == vh1_128(self.t, x0@, nb as nat, 0));
            }
        }
        let m0 = gf128_mul(self.r[0], h0);
        let g1 = gf128_mul_gf64(self.r[1], h1);
        let h2v = m0 ^ g1;
        let m2 = gf128_mul(self.r[2], h0);
        let g3 = gf128_mul_gf64(self.r[3], h1);
        let h3v = m2 ^ g3;
        proof {
            assert(h2v == gf128_mul_spec(
                self.r[0],
                vh0_total_128(self.s, x0@, nb as nat, rem as nat, 0),
            ) ^ gf128_mul_bits(
                self.r[1],
                (vh1_total_128(self.t, x0@, nb as nat, rem as nat, 0) as u128),
                64nat,
            ));
            assert(h3v == gf128_mul_spec(
                self.r[2],
                vh0_total_128(self.s, x0@, nb as nat, rem as nat, 0),
            ) ^ gf128_mul_bits(
                self.r[3],
                (vh1_total_128(self.t, x0@, nb as nat, rem as nat, 0) as u128),
                64nat,
            ));
        }
        let p2 = gf128_as_bytes(h2v);
        let p3 = gf128_as_bytes(h3v);
        let b0: u8 = p2[0];
        let xk0: u8 = x1[0];
        let o0: u8 = b0 ^ xk0;
        proof {
            assert((o0 as u128) == ((b0 as u128) ^ ((xk0) as u128))) by (bit_vector)
                requires
                    o0 == (b0 ^ xk0),
            ;
            assert(p2[0] == byte128(h2v, 0));
        }
        let b1: u8 = p2[1];
        let xk1: u8 = x1[1];
        let o1: u8 = b1 ^ xk1;
        proof {
            assert((o1 as u128) == ((b1 as u128) ^ ((xk1) as u128))) by (bit_vector)
                requires
                    o1 == (b1 ^ xk1),
            ;
            assert(p2[1] == byte128(h2v, 1));
        }
        let b2: u8 = p2[2];
        let xk2: u8 = x1[2];
        let o2: u8 = b2 ^ xk2;
        proof {
            assert((o2 as u128) == ((b2 as u128) ^ ((xk2) as u128))) by (bit_vector)
                requires
                    o2 == (b2 ^ xk2),
            ;
            assert(p2[2] == byte128(h2v, 2));
        }
        let b3: u8 = p2[3];
        let xk3: u8 = x1[3];
        let o3: u8 = b3 ^ xk3;
        proof {
            assert((o3 as u128) == ((b3 as u128) ^ ((xk3) as u128))) by (bit_vector)
                requires
                    o3 == (b3 ^ xk3),
            ;
            assert(p2[3] == byte128(h2v, 3));
        }
        let b4: u8 = p2[4];
        let xk4: u8 = x1[4];
        let o4: u8 = b4 ^ xk4;
        proof {
            assert((o4 as u128) == ((b4 as u128) ^ ((xk4) as u128))) by (bit_vector)
                requires
                    o4 == (b4 ^ xk4),
            ;
            assert(p2[4] == byte128(h2v, 4));
        }
        let b5: u8 = p2[5];
        let xk5: u8 = x1[5];
        let o5: u8 = b5 ^ xk5;
        proof {
            assert((o5 as u128) == ((b5 as u128) ^ ((xk5) as u128))) by (bit_vector)
                requires
                    o5 == (b5 ^ xk5),
            ;
            assert(p2[5] == byte128(h2v, 5));
        }
        let b6: u8 = p2[6];
        let xk6: u8 = x1[6];
        let o6: u8 = b6 ^ xk6;
        proof {
            assert((o6 as u128) == ((b6 as u128) ^ ((xk6) as u128))) by (bit_vector)
                requires
                    o6 == (b6 ^ xk6),
            ;
            assert(p2[6] == byte128(h2v, 6));
        }
        let b7: u8 = p2[7];
        let xk7: u8 = x1[7];
        let o7: u8 = b7 ^ xk7;
        proof {
            assert((o7 as u128) == ((b7 as u128) ^ ((xk7) as u128))) by (bit_vector)
                requires
                    o7 == (b7 ^ xk7),
            ;
            assert(p2[7] == byte128(h2v, 7));
        }
        let b8: u8 = p2[8];
        let xk8: u8 = x1[8];
        let o8: u8 = b8 ^ xk8;
        proof {
            assert((o8 as u128) == ((b8 as u128) ^ ((xk8) as u128))) by (bit_vector)
                requires
                    o8 == (b8 ^ xk8),
            ;
            assert(p2[8] == byte128(h2v, 8));
        }
        let b9: u8 = p2[9];
        let xk9: u8 = x1[9];
        let o9: u8 = b9 ^ xk9;
        proof {
            assert((o9 as u128) == ((b9 as u128) ^ ((xk9) as u128))) by (bit_vector)
                requires
                    o9 == (b9 ^ xk9),
            ;
            assert(p2[9] == byte128(h2v, 9));
        }
        let b10: u8 = p2[10];
        let xk10: u8 = x1[10];
        let o10: u8 = b10 ^ xk10;
        proof {
            assert((o10 as u128) == ((b10 as u128) ^ ((xk10) as u128))) by (bit_vector)
                requires
                    o10 == (b10 ^ xk10),
            ;
            assert(p2[10] == byte128(h2v, 10));
        }
        let b11: u8 = p2[11];
        let xk11: u8 = x1[11];
        let o11: u8 = b11 ^ xk11;
        proof {
            assert((o11 as u128) == ((b11 as u128) ^ ((xk11) as u128))) by (bit_vector)
                requires
                    o11 == (b11 ^ xk11),
            ;
            assert(p2[11] == byte128(h2v, 11));
        }
        let b12: u8 = p2[12];
        let xk12: u8 = x1[12];
        let o12: u8 = b12 ^ xk12;
        proof {
            assert((o12 as u128) == ((b12 as u128) ^ ((xk12) as u128))) by (bit_vector)
                requires
                    o12 == (b12 ^ xk12),
            ;
            assert(p2[12] == byte128(h2v, 12));
        }
        let b13: u8 = p2[13];
        let xk13: u8 = x1[13];
        let o13: u8 = b13 ^ xk13;
        proof {
            assert((o13 as u128) == ((b13 as u128) ^ ((xk13) as u128))) by (bit_vector)
                requires
                    o13 == (b13 ^ xk13),
            ;
            assert(p2[13] == byte128(h2v, 13));
        }
        let b14: u8 = p2[14];
        let xk14: u8 = x1[14];
        let o14: u8 = b14 ^ xk14;
        proof {
            assert((o14 as u128) == ((b14 as u128) ^ ((xk14) as u128))) by (bit_vector)
                requires
                    o14 == (b14 ^ xk14),
            ;
            assert(p2[14] == byte128(h2v, 14));
        }
        let b15: u8 = p2[15];
        let xk15: u8 = x1[15];
        let o15: u8 = b15 ^ xk15;
        proof {
            assert((o15 as u128) == ((b15 as u128) ^ ((xk15) as u128))) by (bit_vector)
                requires
                    o15 == (b15 ^ xk15),
            ;
            assert(p2[15] == byte128(h2v, 15));
        }
        let b16: u8 = p3[0];
        let xk16: u8 = x1[16];
        let o16: u8 = b16 ^ xk16;
        proof {
            assert((o16 as u128) == ((b16 as u128) ^ ((xk16) as u128))) by (bit_vector)
                requires
                    o16 == (b16 ^ xk16),
            ;
            assert(p3[0] == byte128(h3v, 0));
        }
        let b17: u8 = p3[1];
        let xk17: u8 = x1[17];
        let o17: u8 = b17 ^ xk17;
        proof {
            assert((o17 as u128) == ((b17 as u128) ^ ((xk17) as u128))) by (bit_vector)
                requires
                    o17 == (b17 ^ xk17),
            ;
            assert(p3[1] == byte128(h3v, 1));
        }
        [
            o0, o1, o2, o3, o4, o5, o6, o7,
            o8, o9, o10, o11, o12, o13, o14, o15,
            o16, o17,
        ]
    }

    /// Origin Rust (:54-59, process): the debug length contract
    /// re-erects as the requires (S-FA3-2); the split_at lower to
    /// the parent-slice spans; the nb/rem parse parameters ride as
    /// the same check-passing convention (requires-pinned).
    pub fn process(self: &Self, x: &[u8], nb: usize, rem: usize) -> (out: [u8; 18])
        requires
            x.len() > 18,
            nb == (x.len() - 18) / 16,
            rem == (x.len() - 18) % 16,
        ensures
            forall |j: int| 0 <= j < 18 ==> #[trigger] (out[j] as u128)
                == ((if j < 16 {
                    byte128(
                        gf128_mul_spec(
                            self.r[0],
                            vh0_total_128(self.s, x@.subrange(0, (x@.len() as int) - 18), nb as nat, rem as nat, 0),
                        ) ^ gf128_mul_bits(
                            self.r[1],
                            (vh1_total_128(self.t, x@.subrange(0, (x@.len() as int) - 18), nb as nat, rem as nat, 0)
                                as u128),
                            64nat,
                        ),
                        j,
                    )
                } else {
                    byte128(
                        gf128_mul_spec(
                            self.r[2],
                            vh0_total_128(self.s, x@.subrange(0, (x@.len() as int) - 18), nb as nat, rem as nat, 0),
                        ) ^ gf128_mul_bits(
                            self.r[3],
                            (vh1_total_128(self.t, x@.subrange(0, (x@.len() as int) - 18), nb as nat, rem as nat, 0)
                                as u128),
                            64nat,
                        ),
                        (j - 16),
                    )
                }) ^ (x@.subrange((x@.len() as int) - 18, x@.len() as int)[j] as u128)),
    {
        let n: usize = x.len() - 18;
        let x0s = &x[0..n];
        let x1s = &x[n..];
        proof {
            assert(x0s@ == x@.subrange(0, (n as int)));
            assert(x1s@ == x@.subrange((n as int), x@.len() as int));
            assert(x0s@.len() == (n as int));
            assert(x1s@.len() == (x@.len() as int) - (n as int));
        }
        self.process_split(x0s, x1s, nb, rem)
    }
}


// ===========================================================================
// ZKHasher at lambda 128 (upstream :142-222 at F = GF128;
// SDLength = Prod<Length, U3> + GF64::Length = 56 bytes).
// ===========================================================================

pub struct ZKHasher128 {
    /// h0: F accumulator (upstream :193)
    pub h0: u128,
    /// h1: F accumulator (updated with the GF64 multiplier t)
    pub h1: u128,
    /// s: F
    pub s: u128,
    /// t: GF64
    pub t: u64,
    /// r0 / r1: F (finalize)
    pub r0: u128,
    pub r1: u128,
}

impl ZKHasher128 {
    /// Origin Rust (:149-165, ZKHasherInit::new_zk_hasher at GF128):
    /// the 56-byte sd parses into r0 (block 0), r1 (block 1), s
    /// (block 2) and t (bytes 48..56); both accumulators start at
    /// F::ZERO. The F pair of r0/r1 rides the string diagram of
    /// upstream exactly (h0/h1/s/t then r0/r1).
    pub fn new_zk_hasher(sd: &[u8]) -> (h: Self)
        requires
            sd.len() == 3 * GF128_LENGTH_BYTES + 8,
        ensures
            h.h0 == GF128_ZERO,
            h.h1 == GF128_ZERO,
            h.s == le16_u128(sd@, 32),
            h.t == le8_u64(sd@, 48),
            h.r0 == le16_u128(sd@, 0),
            h.r1 == le16_u128(sd@, 16),
    {
        let s0 = &sd[0..16];
        let s1 = &sd[16..32];
        let s2 = &sd[32..48];
        let s3 = &sd[48..56];
        let r0v = gf128_from_bytes(s0);
        let r1v = gf128_from_bytes(s1);
        let sv = gf128_from_bytes(s2);
        let tv = gf64_from_bytes(s3);
        proof {
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r0v, j) == (s0[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r1v, j) == (s1[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(sv, j) == (s2[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte64(tv, j) == (s3[j] as u64) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                s0[j] == sd[j] by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                s1[j] == sd[16 + j] by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                s2[j] == sd[32 + j] by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                s3[j] == sd[48 + j] by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r0v, j) == (sd[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r1v, j) == (sd[16 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(sv, j) == (sd[32 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte64(tv, j) == (sd[48 + j] as u64) by {
            }
            lemma_plane16_le(sd@, 0, r0v);
            lemma_plane16_le(sd@, 16, r1v);
            lemma_plane16_le(sd@, 32, sv);
            lemma_plane8_le64(sd@, 48, tv);
        }
        ZKHasher128 {
            h0: GF128_ZERO,
            h1: GF128_ZERO,
            s: sv,
            t: tv,
            r0: r0v,
            r1: r1v,
        }
    }

    /// Origin Rust (:214-217, ZKHasherProcess::update):
    ///     fn update(&mut self, v: &F) {
    ///         self.h0 = (self.h0 * self.s) + v;
    ///         self.h1 = (self.h1 * self.t) + v; }
    /// h1 is an F element updated through Mul<GF64> (the orbit face);
    /// the field + lowers to the limb xor.
    pub fn update(self: &mut Self, v: u128)
        ensures
            final(self).h0 == gf128_mul_spec(old(self).h0, old(self).s) ^ v,
            final(self).h1 == gf128_mul_bits(old(self).h1, (old(self).t as u128), 64nat) ^ v,
            final(self).s == old(self).s,
            final(self).t == old(self).t,
            final(self).r0 == old(self).r0,
            final(self).r1 == old(self).r1,
    {
        let h0n = gf128_mul(self.h0, self.s);
        let h1n = gf128_mul_gf64(self.h1, self.t);
        self.h0 = h0n ^ v;
        self.h1 = h1n ^ v;
    }

    /// Origin Rust (:219-221, finalize):
    ///     fn finalize(self, x1: &F) -> F {
    ///         (self.r0 * self.h0) + (self.r1 * self.h1) + x1 }
    pub fn finalize(self: &Self, x1: u128) -> (res: u128)
        ensures
            res == gf128_mul_spec(self.r0, self.h0)
                ^ gf128_mul_spec(self.r1, self.h1) ^ x1,
    {
        let m0 = gf128_mul(self.r0, self.h0);
        let m1 = gf128_mul(self.r1, self.h1);
        m0 ^ m1 ^ x1
    }
}

// ===========================================================================
// ZKProofHasher at lambda 128 (upstream :224-305; the GF128-axis
// instantiation of the constraint-side proof hasher -- the GF192/256
// re-spellings ride the FA11 Fields twin axis deblock, record-only
// here).
// ===========================================================================

pub struct ZKProofHasher128 {
    /// a0/a1/a2_hasher (upstream :229-231)
    pub a0_hasher: ZKHasher128,
    pub a1_hasher: ZKHasher128,
    pub a2_hasher: ZKHasher128,
}

impl ZKProofHasher128 {
    /// Origin Rust (:238-248, new). Upstream takes the three hashers;
    /// the twin re-spells over the value triple.
    pub fn new(
        a0_hasher: ZKHasher128,
        a1_hasher: ZKHasher128,
        a2_hasher: ZKHasher128,
    ) -> (h: Self)
        ensures
            h.a0_hasher == a0_hasher,
            h.a1_hasher == a1_hasher,
            h.a2_hasher == a2_hasher,
    {
        ZKProofHasher128 { a0_hasher, a1_hasher, a2_hasher }
    }

    /// Origin Rust (:167-170, new_zk_proof_hasher): three fresh
    /// copies of the one zk hasher.
    pub fn new_zk_proof_hasher(sd: &[u8]) -> (h: Self)
        requires
            sd.len() == 3 * GF128_LENGTH_BYTES + 8,
        ensures
            h.a0_hasher.s == le16_u128(sd@, 32),
            h.a0_hasher.t == le8_u64(sd@, 48),
            h.a0_hasher.r0 == le16_u128(sd@, 0),
            h.a0_hasher.r1 == le16_u128(sd@, 16),
            h.a0_hasher.h0 == GF128_ZERO,
            h.a0_hasher.h1 == GF128_ZERO,
            h.a1_hasher.s == le16_u128(sd@, 32),
            h.a1_hasher.t == le8_u64(sd@, 48),
            h.a1_hasher.r0 == le16_u128(sd@, 0),
            h.a1_hasher.r1 == le16_u128(sd@, 16),
            h.a1_hasher.h0 == GF128_ZERO,
            h.a1_hasher.h1 == GF128_ZERO,
            h.a2_hasher.s == le16_u128(sd@, 32),
            h.a2_hasher.t == le8_u64(sd@, 48),
            h.a2_hasher.r0 == le16_u128(sd@, 0),
            h.a2_hasher.r1 == le16_u128(sd@, 16),
            h.a2_hasher.h0 == GF128_ZERO,
            h.a2_hasher.h1 == GF128_ZERO,
    {
        let h0 = ZKHasher128::new_zk_hasher(sd);
        let h1 = ZKHasher128::new_zk_hasher(sd);
        let h2 = ZKHasher128::new_zk_hasher(sd);
        ZKProofHasher128 { a0_hasher: h0, a1_hasher: h1, a2_hasher: h2 }
    }

    /// Origin Rust (:250-260, update over FieldCommitDegThree):
    ///     self.a0_hasher.update(&val.tag[0]);
    ///     self.a1_hasher.update(&val.tag[1]);
    ///     self.a2_hasher.update(&val.tag[2]);
    ///     debug_assert_eq!(val.key, F::ZERO);   // Should be a
    ///                                             commitment to 0
    /// The debug-assert contract re-erects as the requires (the
    /// S-FA3-2 / ByteCommitsRef convention).
    pub fn update(self: &mut Self, val: &FieldCommitDegThree)
        requires
            val.key == GF128_ZERO,
        ensures
            final(self).a0_hasher.h0
                == gf128_mul_spec(old(self).a0_hasher.h0, old(self).a0_hasher.s)
                    ^ val.tag[0],
            final(self).a0_hasher.h1
                == gf128_mul_bits(old(self).a0_hasher.h1,
                    (old(self).a0_hasher.t as u128), 64nat) ^ val.tag[0],
            final(self).a1_hasher.h0
                == gf128_mul_spec(old(self).a1_hasher.h0, old(self).a1_hasher.s)
                    ^ val.tag[1],
            final(self).a1_hasher.h1
                == gf128_mul_bits(old(self).a1_hasher.h1,
                    (old(self).a1_hasher.t as u128), 64nat) ^ val.tag[1],
            final(self).a2_hasher.h0
                == gf128_mul_spec(old(self).a2_hasher.h0, old(self).a2_hasher.s)
                    ^ val.tag[2],
            final(self).a2_hasher.h1
                == gf128_mul_bits(old(self).a2_hasher.h1,
                    (old(self).a2_hasher.t as u128), 64nat) ^ val.tag[2],
            final(self).a0_hasher.s == old(self).a0_hasher.s,
            final(self).a1_hasher.s == old(self).a1_hasher.s,
            final(self).a2_hasher.s == old(self).a2_hasher.s,
            final(self).a0_hasher.t == old(self).a0_hasher.t,
            final(self).a1_hasher.t == old(self).a1_hasher.t,
            final(self).a2_hasher.t == old(self).a2_hasher.t,
            final(self).a0_hasher.r0 == old(self).a0_hasher.r0,
            final(self).a1_hasher.r0 == old(self).a1_hasher.r0,
            final(self).a2_hasher.r0 == old(self).a2_hasher.r0,
            final(self).a0_hasher.r1 == old(self).a0_hasher.r1,
            final(self).a1_hasher.r1 == old(self).a1_hasher.r1,
            final(self).a2_hasher.r1 == old(self).a2_hasher.r1,
    {
        let v0 = val.tag[0];
        let v1 = val.tag[1];
        let v2 = val.tag[2];
        // bare-field per-plane runs (the delegated update face does
        // not chain through the &mut field projections; the algebra
        // is the same semantically)
        let p00 = self.a0_hasher.h0; let p01 = self.a0_hasher.h1;
        let s0 = self.a0_hasher.s; let tv0 = self.a0_hasher.t;
        let p10 = self.a1_hasher.h0; let p11 = self.a1_hasher.h1;
        let s1 = self.a1_hasher.s; let tv1 = self.a1_hasher.t;
        let p20 = self.a2_hasher.h0; let p21 = self.a2_hasher.h1;
        let s2 = self.a2_hasher.s; let tv2 = self.a2_hasher.t;
        let q00 = gf128_mul(p00, s0); let q01 = gf128_mul_gf64(p01, tv0);
        let q10 = gf128_mul(p10, s1); let q11 = gf128_mul_gf64(p11, tv1);
        let q20 = gf128_mul(p20, s2); let q21 = gf128_mul_gf64(p21, tv2);
        self.a0_hasher.h0 = q00 ^ v0; self.a0_hasher.h1 = q01 ^ v0;
        self.a1_hasher.h0 = q10 ^ v1; self.a1_hasher.h1 = q11 ^ v1;
        self.a2_hasher.h0 = q20 ^ v2; self.a2_hasher.h1 = q21 ^ v2;
    }

    /// Origin Rust (:262-283, lift_and_process): lift and hash the
    /// coefficients of <a^2> * <b> - <a> and <b^2> * <a> - <b>.
    ///     self.a1_hasher.update(&(a_sq.tag[0] * b.tag[0]));
    ///     self.a1_hasher.update(&(b_sq.tag[0] * a.tag[0]));
    ///     self.a2_hasher.update(&(a_sq.key * b.tag[0]
    ///         + a_sq.tag[0] * b.key - a.tag[0]));
    ///     self.a2_hasher.update(&(b_sq.key * a.tag[0]
    ///         + b_sq.tag[0] * a.key - b.tag[0]));
    ///     debug_assert_eq!(a_sq.key * b.key - a.key, F::ZERO);
    ///     debug_assert_eq!(b_sq.key * a.key - b.key, F::ZERO);
    /// The two debug-asserts re-erect as requires (field claims of
    /// the caller's square commitments; char-2 `-` lowers to the
    /// same xor and drops out of the value faces).
    pub fn lift_and_process(
        self: &mut Self,
        a: &FieldCommitDegOne,
        a_sq: &FieldCommitDegOne,
        b: &FieldCommitDegOne,
        b_sq: &FieldCommitDegOne,
    )
        requires
            gf128_mul_spec(a_sq.key, b.key) == a.key,
            gf128_mul_spec(b_sq.key, a.key) == b.key,
        ensures
            final(self).a0_hasher == old(self).a0_hasher,
            final(self).a1_hasher.h0
                == gf128_mul_spec(
                    gf128_mul_spec(old(self).a1_hasher.h0, old(self).a1_hasher.s)
                        ^ gf128_mul_spec(a_sq.tag[0], b.tag[0]),
                    old(self).a1_hasher.s,
                ) ^ gf128_mul_spec(b_sq.tag[0], a.tag[0]),
            final(self).a1_hasher.h1
                == gf128_mul_bits(
                    gf128_mul_bits(old(self).a1_hasher.h1,
                        (old(self).a1_hasher.t as u128), 64nat)
                        ^ gf128_mul_spec(a_sq.tag[0], b.tag[0]),
                    (old(self).a1_hasher.t as u128),
                    64nat,
                ) ^ gf128_mul_spec(b_sq.tag[0], a.tag[0]),
            final(self).a2_hasher.h0
                == gf128_mul_spec(
                    gf128_mul_spec(old(self).a2_hasher.h0, old(self).a2_hasher.s)
                        ^ (gf128_mul_spec(a_sq.key, b.tag[0])
                            ^ gf128_mul_spec(a_sq.tag[0], b.key) ^ a.tag[0]),
                    old(self).a2_hasher.s,
                ) ^ (gf128_mul_spec(b_sq.key, a.tag[0])
                    ^ gf128_mul_spec(b_sq.tag[0], a.key) ^ b.tag[0]),
            final(self).a2_hasher.h1
                == gf128_mul_bits(
                    gf128_mul_bits(old(self).a2_hasher.h1,
                        (old(self).a2_hasher.t as u128), 64nat)
                        ^ (gf128_mul_spec(a_sq.key, b.tag[0])
                            ^ gf128_mul_spec(a_sq.tag[0], b.key) ^ a.tag[0]),
                    (old(self).a2_hasher.t as u128),
                    64nat,
                ) ^ (gf128_mul_spec(b_sq.key, a.tag[0])
                    ^ gf128_mul_spec(b_sq.tag[0], a.key) ^ b.tag[0]),
            final(self).a1_hasher.s == old(self).a1_hasher.s,
            final(self).a2_hasher.s == old(self).a2_hasher.s,
            final(self).a1_hasher.t == old(self).a1_hasher.t,
            final(self).a2_hasher.t == old(self).a2_hasher.t,
            final(self).a1_hasher.r0 == old(self).a1_hasher.r0,
            final(self).a2_hasher.r0 == old(self).a2_hasher.r0,
            final(self).a1_hasher.r1 == old(self).a1_hasher.r1,
            final(self).a2_hasher.r1 == old(self).a2_hasher.r1,
    {
        // Degree 1
        let u1a = gf128_mul(a_sq.tag[0], b.tag[0]);
        let u1b = gf128_mul(b_sq.tag[0], a.tag[0]);
        // Degree 2
        let u2a = gf128_mul(a_sq.key, b.tag[0])
            ^ gf128_mul(a_sq.tag[0], b.key) ^ a.tag[0];
        let u2b = gf128_mul(b_sq.key, a.tag[0])
            ^ gf128_mul(b_sq.tag[0], a.key) ^ b.tag[0];
        proof {
            // stepwise enables: the update face composition spelled
            // once so the ensures chain closes by transitivity
            let s1 = old(self).a1_hasher.s;
            let s2 = old(self).a2_hasher.s;
            let h01 = old(self).a1_hasher.h0;
            let h02 = old(self).a2_hasher.h0;
            let t1 = old(self).a1_hasher.t;
            let t2 = old(self).a2_hasher.t;
            let h11 = old(self).a1_hasher.h1;
            let h12 = old(self).a2_hasher.h1;
            let U1a = gf128_mul_spec(a_sq.tag[0], b.tag[0]);
            let U1b = gf128_mul_spec(b_sq.tag[0], a.tag[0]);
            let U2a = gf128_mul_spec(a_sq.key, b.tag[0])
                ^ gf128_mul_spec(a_sq.tag[0], b.key) ^ a.tag[0];
            let U2b = gf128_mul_spec(b_sq.key, a.tag[0])
                ^ gf128_mul_spec(b_sq.tag[0], a.key) ^ b.tag[0];
            assert(u1a == U1a);
            assert(u2a == U2a);
            assert(u1b == U1b);
            assert(u2b == U2b);
        }
        let p10 = self.a1_hasher.h0; let p11 = self.a1_hasher.h1;
        let s1 = self.a1_hasher.s; let tv1 = self.a1_hasher.t;
        let p20 = self.a2_hasher.h0; let p21 = self.a2_hasher.h1;
        let s2 = self.a2_hasher.s; let tv2 = self.a2_hasher.t;
        let a10 = gf128_mul(p10, s1); let a11 = gf128_mul_gf64(p11, tv1);
        let mid10 = a10 ^ u1a; let mid11 = a11 ^ u1a;
        let b10 = gf128_mul(mid10, s1); let b11 = gf128_mul_gf64(mid11, tv1);
        self.a1_hasher.h0 = b10 ^ u1b; self.a1_hasher.h1 = b11 ^ u1b;
        let a20 = gf128_mul(p20, s2); let a21 = gf128_mul_gf64(p21, tv2);
        let mid20 = a20 ^ u2a; let mid21 = a21 ^ u2a;
        let b20 = gf128_mul(mid20, s2); let b21 = gf128_mul_gf64(mid21, tv2);
        self.a2_hasher.h0 = b20 ^ u2b; self.a2_hasher.h1 = b21 ^ u2b;
    }

}

/// The odd-round combination <a^2> * <b> + <a> at the spec level:
/// upstream odd_round_cstrnts' first argument (D1 x D2 via
/// mul_two_ref, then add_one absorbs si).
pub open spec fn odd_c1(
    si: FieldCommitDegOne,
    si_sq: FieldCommitDegOne,
    st0: FieldCommitDegTwo,
) -> FieldCommitDegThree {
    FieldCommitDegThree {
        key: gf128_mul_spec(si_sq.key, st0.key) ^ si.key,
        tag: [
            gf128_mul_spec(si_sq.tag[0], st0.tag[0]),
            gf128_mul_spec(si_sq.key, st0.tag[0])
                ^ gf128_mul_spec(si_sq.tag[0], st0.tag[1]),
            gf128_mul_spec(si_sq.key, st0.tag[1])
                ^ gf128_mul_spec(si_sq.tag[0], st0.key) ^ si.tag[0],
        ],
    }
}

/// The second combination <a> * <b^2> + <b>: D1 x D2 (si x st1_i)
/// then add_two absorbs st0_i.
pub open spec fn odd_c2(
    si: FieldCommitDegOne,
    st1: FieldCommitDegTwo,
    st0: FieldCommitDegTwo,
) -> FieldCommitDegThree {
    FieldCommitDegThree {
        key: gf128_mul_spec(si.key, st1.key) ^ st0.key,
        tag: [
            gf128_mul_spec(si.tag[0], st1.tag[0]),
            gf128_mul_spec(si.key, st1.tag[0])
                ^ gf128_mul_spec(si.tag[0], st1.tag[1]) ^ st0.tag[0],
            gf128_mul_spec(si.key, st1.tag[1])
                ^ gf128_mul_spec(si.tag[0], st1.key) ^ st0.tag[1],
        ],
    }
}

impl ZKProofHasher128 {
    /// Origin Rust (:285-296, odd_round_cstrnts):
    ///     self.update(&(si_sq * st0_i + si));
    ///     self.update(&(si * st1_i + st0_i));
    /// The updates' debug key contracts (commitments to 0) re-erect
    /// as the requires rows (the caller-side square-consistency
    /// claims; documented at the face).
    pub fn odd_round_cstrnts(
        self: &mut Self,
        si: &FieldCommitDegOne,
        si_sq: &FieldCommitDegOne,
        st0_i: &FieldCommitDegTwo,
        st1_i: &FieldCommitDegTwo,
    )
        requires
            gf128_mul_spec(si_sq.key, st0_i.key) == si.key,
            gf128_mul_spec(si.key, st1_i.key) == st0_i.key,
        ensures
            final(self).a0_hasher.h0
                == gf128_mul_spec(
                    gf128_mul_spec(old(self).a0_hasher.h0, old(self).a0_hasher.s)
                        ^ odd_c1(*si, *si_sq, *st0_i).tag[0],
                    old(self).a0_hasher.s,
                ) ^ odd_c2(*si, *st1_i, *st0_i).tag[0],
            final(self).a0_hasher.h1
                == gf128_mul_bits(
                    gf128_mul_bits(old(self).a0_hasher.h1,
                        (old(self).a0_hasher.t as u128), 64nat)
                        ^ odd_c1(*si, *si_sq, *st0_i).tag[0],
                    (old(self).a0_hasher.t as u128),
                    64nat,
                ) ^ odd_c2(*si, *st1_i, *st0_i).tag[0],
            final(self).a1_hasher.h0
                == gf128_mul_spec(
                    gf128_mul_spec(old(self).a1_hasher.h0, old(self).a1_hasher.s)
                        ^ odd_c1(*si, *si_sq, *st0_i).tag[1],
                    old(self).a1_hasher.s,
                ) ^ odd_c2(*si, *st1_i, *st0_i).tag[1],
            final(self).a1_hasher.h1
                == gf128_mul_bits(
                    gf128_mul_bits(old(self).a1_hasher.h1,
                        (old(self).a1_hasher.t as u128), 64nat)
                        ^ odd_c1(*si, *si_sq, *st0_i).tag[1],
                    (old(self).a1_hasher.t as u128),
                    64nat,
                ) ^ odd_c2(*si, *st1_i, *st0_i).tag[1],
            final(self).a2_hasher.h0
                == gf128_mul_spec(
                    gf128_mul_spec(old(self).a2_hasher.h0, old(self).a2_hasher.s)
                        ^ odd_c1(*si, *si_sq, *st0_i).tag[2],
                    old(self).a2_hasher.s,
                ) ^ odd_c2(*si, *st1_i, *st0_i).tag[2],
            final(self).a2_hasher.h1
                == gf128_mul_bits(
                    gf128_mul_bits(old(self).a2_hasher.h1,
                        (old(self).a2_hasher.t as u128), 64nat)
                        ^ odd_c1(*si, *si_sq, *st0_i).tag[2],
                    (old(self).a2_hasher.t as u128),
                    64nat,
                ) ^ odd_c2(*si, *st1_i, *st0_i).tag[2],
            final(self).a0_hasher.s == old(self).a0_hasher.s,
            final(self).a1_hasher.s == old(self).a1_hasher.s,
            final(self).a2_hasher.s == old(self).a2_hasher.s,
            final(self).a0_hasher.t == old(self).a0_hasher.t,
            final(self).a1_hasher.t == old(self).a1_hasher.t,
            final(self).a2_hasher.t == old(self).a2_hasher.t,
            final(self).a0_hasher.r0 == old(self).a0_hasher.r0,
            final(self).a1_hasher.r0 == old(self).a1_hasher.r0,
            final(self).a2_hasher.r0 == old(self).a2_hasher.r0,
            final(self).a0_hasher.r1 == old(self).a0_hasher.r1,
            final(self).a1_hasher.r1 == old(self).a1_hasher.r1,
            final(self).a2_hasher.r1 == old(self).a2_hasher.r1,
    {
        // self.update(&(si_sq * st0_i + si));
        let c1 = si_sq.mul_two_ref(st0_i);
        let comb1 = c1.add_one(si);
        proof {
            let k_sq = si_sq.key;
            let k_st0 = st0_i.key;
            let k_si = si.key;
            let m1v: u128 = gf128_mul_spec(k_sq, k_st0);
            assert(m1v == k_si);
            assert(m1v ^ k_si == GF128_ZERO) by (bit_vector)
                requires
                    m1v == k_si,
            ;
            assert(c1.key == gf128_mul_spec(k_sq, k_st0));
            assert(comb1.key == c1.key ^ k_si);
            assert(comb1.key == GF128_ZERO);
        }
        proof {
            // concrete instantiations of the spec-side combinations
            assert(odd_c1(*si, *si_sq, *st0_i).tag[0]
                == gf128_mul_spec(si_sq.tag[0], st0_i.tag[0]));
            assert(odd_c1(*si, *si_sq, *st0_i).tag[1]
                == gf128_mul_spec(si_sq.key, st0_i.tag[0])
                    ^ gf128_mul_spec(si_sq.tag[0], st0_i.tag[1]));
            assert(odd_c1(*si, *si_sq, *st0_i).tag[2]
                == gf128_mul_spec(si_sq.key, st0_i.tag[1])
                    ^ gf128_mul_spec(si_sq.tag[0], st0_i.key) ^ si.tag[0]);
        }
        let w1t0 = comb1.tag[0];
        let w1t1 = comb1.tag[1];
        let w1t2 = comb1.tag[2];
        let p00 = self.a0_hasher.h0; let p01 = self.a0_hasher.h1;
        let s0 = self.a0_hasher.s; let tv0 = self.a0_hasher.t;
        let p10 = self.a1_hasher.h0; let p11 = self.a1_hasher.h1;
        let s1 = self.a1_hasher.s; let tv1 = self.a1_hasher.t;
        let p20 = self.a2_hasher.h0; let p21 = self.a2_hasher.h1;
        let s2 = self.a2_hasher.s; let tv2 = self.a2_hasher.t;
        // (intermediate not needed here yet; the plane runs wait for
        // the second combination below)
        self.a0_hasher.h0 = p00; self.a0_hasher.h1 = p01;
        self.a1_hasher.h0 = p10; self.a1_hasher.h1 = p11;
        self.a2_hasher.h0 = p20; self.a2_hasher.h1 = p21;
        // self.update(&(si * st1_i + st0_i));
        let c2 = si.mul_two_ref(st1_i);
        let comb2 = c2.add_two(st0_i);
        proof {
            assert(odd_c2(*si, *st1_i, *st0_i).tag[0]
                == gf128_mul_spec(si.tag[0], st1_i.tag[0]));
            assert(odd_c2(*si, *st1_i, *st0_i).tag[1]
                == gf128_mul_spec(si.key, st1_i.tag[0])
                    ^ gf128_mul_spec(si.tag[0], st1_i.tag[1]) ^ st0_i.tag[0]);
            assert(odd_c2(*si, *st1_i, *st0_i).tag[2]
                == gf128_mul_spec(si.key, st1_i.tag[1])
                    ^ gf128_mul_spec(si.tag[0], st1_i.key) ^ st0_i.tag[1]);
        }
        let w2t0 = comb2.tag[0];
        let w2t1 = comb2.tag[1];
        let w2t2 = comb2.tag[2];
        // two bare-field rounds over all three hasher planes
        let r0a0 = gf128_mul(p00, s0); let r0a1 = gf128_mul_gf64(p01, tv0);
        let m00 = r0a0 ^ w1t0; let m01 = r0a1 ^ w1t0;
        let r0b0 = gf128_mul(m00, s0); let r0b1 = gf128_mul_gf64(m01, tv0);
        let r1a0 = gf128_mul(p10, s1); let r1a1 = gf128_mul_gf64(p11, tv1);
        let m10 = r1a0 ^ w1t1; let m11 = r1a1 ^ w1t1;
        let r1b0 = gf128_mul(m10, s1); let f11 = gf128_mul_gf64(m11, tv1);
        let r2a0 = gf128_mul(p20, s2); let r2a1 = gf128_mul_gf64(p21, tv2);
        let m20 = r2a0 ^ w1t2; let m21 = r2a1 ^ w1t2;
        let r2b0 = gf128_mul(m20, s2); let r2b1 = gf128_mul_gf64(m21, tv2);
        self.a0_hasher.h0 = r0b0 ^ w2t0; self.a0_hasher.h1 = r0b1 ^ w2t0;
        self.a1_hasher.h0 = r1b0 ^ w2t1; self.a1_hasher.h1 = f11 ^ w2t1;
        self.a2_hasher.h0 = r2b0 ^ w2t2; self.a2_hasher.h1 = r2b1 ^ w2t2;
        proof {
            assert(p00 == old(self).a0_hasher.h0);
            assert(p01 == old(self).a0_hasher.h1);
            assert(s0 == old(self).a0_hasher.s);
            assert(tv0 == old(self).a0_hasher.t);
            assert(p10 == old(self).a1_hasher.h0);
            assert(p11 == old(self).a1_hasher.h1);
            assert(s1 == old(self).a1_hasher.s);
            assert(tv1 == old(self).a1_hasher.t);
            assert(p20 == old(self).a2_hasher.h0);
            assert(p21 == old(self).a2_hasher.h1);
            assert(s2 == old(self).a2_hasher.s);
            assert(tv2 == old(self).a2_hasher.t);
            assert(c1.tag[1] == gf128_mul_spec(si_sq.key, st0_i.tag[0])
                ^ gf128_mul_spec(si_sq.tag[0], st0_i.tag[1]));
            // add_one leaves slot 1 unchanged (the absorbed degree-1
            // tag lands in slot 2 only -- upstream :400-413)
            assert(comb1.tag[1] == c1.tag[1]);
            assert(w1t0 == gf128_mul_spec(si_sq.tag[0], st0_i.tag[0]));
            assert(w1t1 == comb1.tag[1]);
            assert(w1t2 == gf128_mul_spec(si_sq.key, st0_i.tag[1])
                ^ gf128_mul_spec(si_sq.tag[0], st0_i.key) ^ si.tag[0]);
            assert(w2t0 == gf128_mul_spec(si.tag[0], st1_i.tag[0]));
            assert(w2t1 == gf128_mul_spec(si.key, st1_i.tag[0])
                ^ gf128_mul_spec(si.tag[0], st1_i.tag[1]) ^ st0_i.tag[0]);
            assert(w2t2 == gf128_mul_spec(si.key, st1_i.tag[1])
                ^ gf128_mul_spec(si.tag[0], st1_i.key) ^ st0_i.tag[1]);
            assert(odd_c1(*si, *si_sq, *st0_i).tag[0] == w1t0);
            assert(odd_c1(*si, *si_sq, *st0_i).tag[1] == w1t1);
            assert(odd_c1(*si, *si_sq, *st0_i).tag[2] == w1t2);
            assert(odd_c2(*si, *st1_i, *st0_i).tag[0] == w2t0);
            assert(odd_c2(*si, *st1_i, *st0_i).tag[1] == w2t1);
            assert(odd_c2(*si, *st1_i, *st0_i).tag[2] == w2t2);
        }
        proof {
            let k_si2 = si.key;
            let k_st1 = st1_i.key;
            let k_st = st0_i.key;
            let m2v: u128 = gf128_mul_spec(k_si2, k_st1);
            assert(m2v == k_st);
            assert(m2v ^ k_st == GF128_ZERO) by (bit_vector)
                requires
                    m2v == k_st,
            ;
            assert(c2.key == gf128_mul_spec(k_si2, k_st1));
            assert(comb2.key == c2.key ^ k_st);
            assert(comb2.key == GF128_ZERO);
        }
    }

    /// Origin Rust (:298-304, finalize): the three hashers finalize
    /// against u / u_plus_v / v.
    pub fn finalize(
        self: &Self,
        u: u128,
        u_plus_v: u128,
        v: u128,
    ) -> (res: (u128, u128, u128))
        ensures
            res.0 == gf128_mul_spec(self.a0_hasher.r0, self.a0_hasher.h0)
                ^ gf128_mul_spec(self.a0_hasher.r1, self.a0_hasher.h1) ^ u,
            res.1 == gf128_mul_spec(self.a1_hasher.r0, self.a1_hasher.h0)
                ^ gf128_mul_spec(self.a1_hasher.r1, self.a1_hasher.h1) ^ u_plus_v,
            res.2 == gf128_mul_spec(self.a2_hasher.r0, self.a2_hasher.h0)
                ^ gf128_mul_spec(self.a2_hasher.r1, self.a2_hasher.h1) ^ v,
    {
        let a0 = self.a0_hasher.finalize(u);
        let a1 = self.a1_hasher.finalize(u_plus_v);
        let a2 = self.a2_hasher.finalize(v);
        (a0, a1, a2)
    }
}


// ===========================================================================
// ZKVerifyHasher at lambda 128 (upstream :307-356).
// ===========================================================================

pub struct ZKVerifyHasher128 {
    /// b_hasher (upstream :311)
    pub b_hasher: ZKHasher128,
    /// delta: F
    pub delta: u128,
    /// delta_squared: F (upstream stores delta.square())
    pub delta_squared: u128,
}

impl ZKVerifyHasher128 {
    /// Origin Rust (:320-326, new):
    ///     Self { b_hasher, delta,
    ///            delta_squared: delta.square() }
    /// The Square face lowers to the FA3 gf128_square twin (verified
    /// == gf128_hmul for every input; the orbit body is the upstream
    /// generic Square at N == 1).
    pub fn new(b_hasher: ZKHasher128, delta: u128) -> (h: Self)
        ensures
            h.b_hasher == b_hasher,
            h.delta == delta,
            h.delta_squared == gf128_hmul(delta, delta),
    {
        let d2 = gf128_square(delta);
        ZKVerifyHasher128 {
            b_hasher,
            delta,
            delta_squared: d2,
        }
    }

    /// Origin Rust (:328-330, update; delegates to b_hasher).
    pub fn update(self: &mut Self, val: u128)
        ensures
            final(self).b_hasher.h0
                == gf128_mul_spec(old(self).b_hasher.h0, old(self).b_hasher.s) ^ val,
            final(self).b_hasher.h1
                == gf128_mul_bits(old(self).b_hasher.h1,
                    (old(self).b_hasher.t as u128), 64nat) ^ val,
            final(self).delta == old(self).delta,
            final(self).delta_squared == old(self).delta_squared,
    {
        // the b_hasher delegation re-spelled at the bare-field level
        // (the intermediate-state chaining of the delegated update
        // face does not survive the mut-ref field-projection path;
        // the value algebra is identical)
        let pre_h0 = self.b_hasher.h0;
        let pre_h1 = self.b_hasher.h1;
        let sv = self.b_hasher.s;
        let tv = self.b_hasher.t;
        let h0n = gf128_mul(pre_h0, sv);
        let h1n = gf128_mul_gf64(pre_h1, tv);
        self.b_hasher.h0 = h0n ^ val;
        self.b_hasher.h1 = h1n ^ val;
    }

    /// Origin Rust (:332-334, mul_and_update):
    ///     self.b_hasher.update(&(self.delta * a * b));
    pub fn mul_and_update(self: &mut Self, a: u128, b: u128)
        ensures
            final(self).b_hasher.h0
                == gf128_mul_spec(old(self).b_hasher.h0, old(self).b_hasher.s)
                    ^ gf128_mul_spec(gf128_mul_spec(old(self).delta, a), b),
            final(self).b_hasher.h1
                == gf128_mul_bits(old(self).b_hasher.h1,
                    (old(self).b_hasher.t as u128), 64nat)
                    ^ gf128_mul_spec(gf128_mul_spec(old(self).delta, a), b),
            final(self).delta == old(self).delta,
            final(self).delta_squared == old(self).delta_squared,
    {
        let m = gf128_mul(self.delta, a);
        let v = gf128_mul(m, b);
        let pre_h0 = self.b_hasher.h0;
        let pre_h1 = self.b_hasher.h1;
        let sv = self.b_hasher.s;
        let tv = self.b_hasher.t;
        let h0n = gf128_mul(pre_h0, sv);
        let h1n = gf128_mul_gf64(pre_h1, tv);
        self.b_hasher.h0 = h0n ^ v;
        self.b_hasher.h1 = h1n ^ v;
    }

    /// Origin Rust (:336-339, inv_norm_constraints):
    ///     let cnstr = *y * conjugates[1] * conjugates[4]
    ///         + self.delta_squared * conjugates[0];
    ///     self.b_hasher.update(&cnstr);
    pub fn inv_norm_constraints(self: &mut Self, conjugates: &[u128], y: u128)
        requires
            conjugates.len() >= 5,
        ensures
            final(self).b_hasher.h0
                == gf128_mul_spec(old(self).b_hasher.h0, old(self).b_hasher.s)
                    ^ gf128_mul_spec(gf128_mul_spec(y, conjugates[1]),
                        conjugates[4])
                    ^ gf128_mul_spec(old(self).delta_squared, conjugates[0]),
            final(self).b_hasher.h1
                == gf128_mul_bits(old(self).b_hasher.h1,
                    (old(self).b_hasher.t as u128), 64nat)
                    ^ gf128_mul_spec(gf128_mul_spec(y, conjugates[1]),
                        conjugates[4])
                    ^ gf128_mul_spec(old(self).delta_squared, conjugates[0]),
            final(self).delta == old(self).delta,
            final(self).delta_squared == old(self).delta_squared,
    {
        let m1 = gf128_mul(y, conjugates[1]);
        let m11 = gf128_mul(m1, conjugates[4]);
        let m2 = gf128_mul(self.delta_squared, conjugates[0]);
        let cnstr = m11 ^ m2;
        proof {
            assert(m1 == gf128_mul_spec(y, conjugates[1]));
            assert(m11 == gf128_mul_spec(gf128_mul_spec(y, conjugates[1]), conjugates[4]));
            assert(m2 == gf128_mul_spec(old(self).delta_squared, conjugates[0]));
            assert(cnstr == gf128_mul_spec(gf128_mul_spec(y, conjugates[1]), conjugates[4])
                ^ gf128_mul_spec(old(self).delta_squared, conjugates[0]));
        }
        let pre_h0 = self.b_hasher.h0;
        let pre_h1 = self.b_hasher.h1;
        let sv = self.b_hasher.s;
        let tv = self.b_hasher.t;
        let h0n = gf128_mul(pre_h0, sv);
        let h1n = gf128_mul_gf64(pre_h1, tv);
        proof {
            assert(pre_h0 == old(self).b_hasher.h0);
            assert(pre_h1 == old(self).b_hasher.h1);
            assert(sv == old(self).b_hasher.s);
            assert(tv == old(self).b_hasher.t);
            assert(h0n == gf128_mul_spec(old(self).b_hasher.h0,
                old(self).b_hasher.s));
            assert(h1n == gf128_mul_bits(old(self).b_hasher.h1,
                old(self).b_hasher.t as u128, 64nat));
            assert(self.delta_squared == old(self).delta_squared);
            assert(cnstr == gf128_mul_spec(gf128_mul_spec(y, conjugates[1]),
                conjugates[4])
                ^ gf128_mul_spec(old(self).delta_squared, conjugates[0]));
            xor_assoc3(h0n, m11, m2);
            assert((h0n ^ cnstr)
                == gf128_mul_spec(old(self).b_hasher.h0, old(self).b_hasher.s)
                    ^ gf128_mul_spec(gf128_mul_spec(y, conjugates[1]),
                        conjugates[4])
                    ^ gf128_mul_spec(old(self).delta_squared, conjugates[0]));
            xor_assoc3(h1n, m11, m2);
            assert((h1n ^ cnstr)
                == gf128_mul_bits(old(self).b_hasher.h1,
                    old(self).b_hasher.t as u128, 64nat)
                    ^ gf128_mul_spec(gf128_mul_spec(y, conjugates[1]),
                        conjugates[4])
                    ^ gf128_mul_spec(old(self).delta_squared, conjugates[0]));
        }
        self.b_hasher.h0 = h0n ^ cnstr;
        self.b_hasher.h1 = h1n ^ cnstr;
    }

    /// Origin Rust (:341-344, odd_round_cstrnts):
    ///     self.update(&(self.delta_squared * si + *si_sq * st0_i));
    ///     self.update(&(self.delta * st0_i + *si * st1_i));
    pub fn odd_round_cstrnts(
        self: &mut Self,
        si: u128,
        si_sq: u128,
        st0_i: u128,
        st1_i: u128,
    )
        ensures
            final(self).b_hasher.h0
                == gf128_mul_spec(
                    gf128_mul_spec(old(self).b_hasher.h0, old(self).b_hasher.s)
                        ^ (gf128_mul_spec(old(self).delta_squared, si)
                            ^ gf128_mul_spec(si_sq, st0_i)),
                    old(self).b_hasher.s,
                ) ^ (gf128_mul_spec(old(self).delta, st0_i)
                    ^ gf128_mul_spec(si, st1_i)),
            final(self).b_hasher.h1
                == gf128_mul_bits(
                    gf128_mul_bits(old(self).b_hasher.h1,
                        (old(self).b_hasher.t as u128), 64nat)
                        ^ (gf128_mul_spec(old(self).delta_squared, si)
                            ^ gf128_mul_spec(si_sq, st0_i)),
                    (old(self).b_hasher.t as u128),
                    64nat,
                ) ^ (gf128_mul_spec(old(self).delta, st0_i)
                    ^ gf128_mul_spec(si, st1_i)),
            final(self).delta == old(self).delta,
            final(self).delta_squared == old(self).delta_squared,
    {
        let m1 = gf128_mul(self.delta_squared, si);
        let m2 = gf128_mul(si_sq, st0_i);
        let m3 = gf128_mul(self.delta, st0_i);
        let m4 = gf128_mul(si, st1_i);
        let v1 = m1 ^ m2;
        let v2 = m3 ^ m4;
        let pre_h0 = self.b_hasher.h0;
        let pre_h1 = self.b_hasher.h1;
        let sv = self.b_hasher.s;
        let tv = self.b_hasher.t;
        let ha0 = gf128_mul(pre_h0, sv);
        let ha1 = gf128_mul_gf64(pre_h1, tv);
        let mid_h0 = ha0 ^ v1;
        let mid_h1 = ha1 ^ v1;
        let hb0 = gf128_mul(mid_h0, sv);
        let hb1 = gf128_mul_gf64(mid_h1, tv);
        self.b_hasher.h0 = hb0 ^ v2;
        self.b_hasher.h1 = hb1 ^ v2;
    }

    /// Origin Rust (:346-351, lift_and_process):
    ///     self.update(&(self.delta * (*a_sq * b
    ///         - self.delta * a)));
    ///     self.update(&(self.delta * (*a * b_sq
    ///         - self.delta * b)));
    /// The `-` lowers to the char-2 xor at the value plane.
    pub fn lift_and_process(self: &mut Self, a: u128, a_sq: u128, b: u128, b_sq: u128)
        ensures
            final(self).b_hasher.h0
                == gf128_mul_spec(
                    gf128_mul_spec(old(self).b_hasher.h0, old(self).b_hasher.s)
                        ^ gf128_mul_spec(old(self).delta,
                            (gf128_mul_spec(a_sq, b)
                                ^ gf128_mul_spec(old(self).delta, a))),
                    old(self).b_hasher.s,
                ) ^ gf128_mul_spec(old(self).delta,
                    (gf128_mul_spec(a, b_sq)
                        ^ gf128_mul_spec(old(self).delta, b))),
            final(self).b_hasher.h1
                == gf128_mul_bits(
                    gf128_mul_bits(old(self).b_hasher.h1,
                        (old(self).b_hasher.t as u128), 64nat)
                        ^ gf128_mul_spec(old(self).delta,
                            (gf128_mul_spec(a_sq, b)
                                ^ gf128_mul_spec(old(self).delta, a))),
                    (old(self).b_hasher.t as u128),
                    64nat,
                ) ^ gf128_mul_spec(old(self).delta,
                    (gf128_mul_spec(a, b_sq)
                        ^ gf128_mul_spec(old(self).delta, b))),
            final(self).delta == old(self).delta,
            final(self).delta_squared == old(self).delta_squared,
    {
        let i1 = gf128_mul(a_sq, b);
        let i2 = gf128_mul(self.delta, a);
        let j1 = gf128_mul(a, b_sq);
        let j2 = gf128_mul(self.delta, b);
        let v1 = gf128_mul(self.delta, i1 ^ i2);
        let v2 = gf128_mul(self.delta, j1 ^ j2);
        let pre_h0 = self.b_hasher.h0;
        let pre_h1 = self.b_hasher.h1;
        let sv = self.b_hasher.s;
        let tv = self.b_hasher.t;
        let ha0 = gf128_mul(pre_h0, sv);
        let ha1 = gf128_mul_gf64(pre_h1, tv);
        let mid_h0 = ha0 ^ v1;
        let mid_h1 = ha1 ^ v1;
        let hb0 = gf128_mul(mid_h0, sv);
        let hb1 = gf128_mul_gf64(mid_h1, tv);
        self.b_hasher.h0 = hb0 ^ v2;
        self.b_hasher.h1 = hb1 ^ v2;
    }

    /// Origin Rust (:353-355, finalize; delegates).
    pub fn finalize(self: &Self, v: u128) -> (res: u128)
        ensures
            res == gf128_mul_spec(self.b_hasher.r0, self.b_hasher.h0)
                ^ gf128_mul_spec(self.b_hasher.r1, self.b_hasher.h1) ^ v,
    {
        self.b_hasher.finalize(v)
    }
}

/// Origin Rust (:172-174, ZKHasherInit::new_zk_verify_hasher): a
/// fresh zk hasher plus the delta square carrier.
pub fn new_zk_verify_hasher_128(sd: &[u8], delta: u128) -> (h: ZKVerifyHasher128)
    requires
        sd.len() == 3 * GF128_LENGTH_BYTES + 8,
    ensures
        h.b_hasher.s == le16_u128(sd@, 32),
        h.b_hasher.t == le8_u64(sd@, 48),
        h.b_hasher.r0 == le16_u128(sd@, 0),
        h.b_hasher.r1 == le16_u128(sd@, 16),
        h.b_hasher.h0 == GF128_ZERO,
        h.b_hasher.h1 == GF128_ZERO,
        h.delta == delta,
        h.delta_squared == gf128_hmul(delta, delta),
{
    let bh = ZKHasher128::new_zk_hasher(sd);
    ZKVerifyHasher128::new(bh, delta)
}


// ===========================================================================
// LeafHasher at lambda 128 (upstream :377-402, LeafHasher128 at
// F = GF128; ExtensionField = GF384, Length 48 -- the typenum
// Prod<LambdaBytes, U3> algebra lowered to byte counts).
// ===========================================================================

/// Spec parse of the leaf-hash lanes at lambda 128: u parses into
/// the GF384 limb triple, x0 into the base field element, x1 into
/// the extension triple; h = u * x0 + x1 in the orbit model.
pub open spec fn leaf128_h(uhash: Seq<u8>, x: Seq<u8>) -> [u128; 3] {
    let u0 = le16_u128(uhash, 0);
    let u1 = le16_u128(uhash, 16);
    let u2 = le16_u128(uhash, 32);
    let x0 = le16_u128(x, 0);
    let p = gf384_mul_bits(u0, u1, u2, x0, 128nat);
    [p.0 ^ le16_u128(x, 16), p.1 ^ le16_u128(x, 32), p.2 ^ le16_u128(x, 48)]
}

/// Origin Rust (:388-401, LeafHasher128::hash):
///     let u = <GF384>::from(uhash);
///     let x0 = <GF128>::from(&x[..16]);
///     let x1 = <GF384>::from(&x[16..]);
///     let h = (u * x0) + x1;      // Mul<GF128> for GF384, then Add
///     h.as_bytes() }
/// Mul<BaseField> lowers to gf384_mul_gf128 (FA3 wave 3, exec ==
/// orbit model), Add to the limb xor (char 2).
pub fn leaf_hash_128(uhash: &[u8], x: &[u8]) -> (out: [u8; 48])
    requires
        uhash.len() == 3 * GF128_LENGTH_BYTES,
        x.len() == 4 * GF128_LENGTH_BYTES,
    ensures
        forall |j: int| 0 <= j < 48 ==> #[trigger] out[j]
            == byte384(leaf128_h(uhash@, x@), j),
{
    let uv = gf384_from_bytes(uhash);
    let sx0 = &x[0..16];
    let sx1 = &x[16..32];
    let sx2 = &x[32..48];
    let sx3 = &x[48..64];
    let x0v = gf128_from_bytes(sx0);
    let e0 = gf128_from_bytes(sx1);
    let e1 = gf128_from_bytes(sx2);
    let e2 = gf128_from_bytes(sx3);
    proof {
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[0], j) == (uhash[j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[1], j) == (uhash[16 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[2], j) == (uhash[32 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(x0v, j) == (sx0[j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sx0[j] == x[j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sx1[j] == x[16 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sx2[j] == x[32 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sx3[j] == x[48 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e0, j) == (x[16 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e1, j) == (x[32 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e2, j) == (x[48 + j] as u128) by {
        }
        lemma_plane16_le(uhash@, 0, uv[0]);
        lemma_plane16_le(uhash@, 16, uv[1]);
        lemma_plane16_le(uhash@, 32, uv[2]);
        lemma_plane16_le(x@, 0, x0v);
        lemma_plane16_le(x@, 16, e0);
        lemma_plane16_le(x@, 32, e1);
        lemma_plane16_le(x@, 48, e2);
    }
    let m = gf384_mul_gf128(uv[0], uv[1], uv[2], x0v);
    proof {
        let u0s = le16_u128(uhash@, 0);
        let u1s = le16_u128(uhash@, 16);
        let u2s = le16_u128(uhash@, 32);
        let x0s = le16_u128(x@, 0);
        assert(gf384_mul_bits(uv[0], uv[1], uv[2], x0v, 128nat)
            == gf384_mul_bits(u0s, u1s, u2s, x0s, 128nat));
    }
    let hv = [m.0 ^ e0, m.1 ^ e1, m.2 ^ e2];
    proof {
        assert(hv == leaf128_h(uhash@, x@));
    }
    gf384_as_bytes(hv)
}


// ===========================================================================
// LeafHasher at lambda 192 (upstream :404-429, LeafHasher192 at
// F = GF192; ExtensionField = GF576, Length 72).
// ===========================================================================

/// Spec parse of the leaf-hash lanes at lambda 192 (five le-limbs
/// plus the base pair, the GF576 product + limb xor in the orbit
/// model).
pub open spec fn leaf192_h(uhash: Seq<u8>, x: Seq<u8>) -> [u128; 5] {
    let u0 = le16_u128(uhash, 0);
    let u1 = le16_u128(uhash, 16);
    let u2 = le16_u128(uhash, 32);
    let u3 = le16_u128(uhash, 48);
    let u4 = le128_8(uhash, 64);
    let x00 = le16_u128(x, 0);
    let x01 = le128_8(x, 16);
    let e0 = le16_u128(x, 24);
    let e1 = le16_u128(x, 40);
    let e2 = le16_u128(x, 56);
    let e3 = le16_u128(x, 72);
    let e4 = le128_8(x, 88);
    let p = gf576_mul_bits(u0, u1, u2, u3, u4, (x00, x01), 192nat);
    [p.0 ^ e0, p.1 ^ e1, p.2 ^ e2, p.3 ^ e3, p.4 ^ e4]
}

/// The lane plane rows shared by leaf_hash_192 (helper proof fn:
/// per-lane plane facts to the le bridge forms; uv comes from
/// gf576_from_bytes, x0 from the GF192 wire face, e0..e3 from
/// gf128 lanes, e4 from the GF64 tail cast to the u128 plane).
proof fn lane_rows_192(
    uhash: Seq<u8>,
    x: Seq<u8>,
    uv: [u128; 5],
    x0: (u128, u128),
    e0: u128,
    e1: u128,
    e2: u128,
    e3: u128,
    e4: u128,
)
    requires
        uhash.len() == 72,
        x.len() == 96,
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[0], j) == (uhash[j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[1], j) == (uhash[16 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[2], j) == (uhash[32 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[3], j) == (uhash[48 + j] as u128),
        forall |j: int| 0 <= j < 8 ==> #[trigger] byte128(uv[4], j) == (uhash[64 + j] as u128),
        (uv[4] >> 64) == 0,
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(x0.0, j) == (x[j] as u128),
        forall |j: int| 0 <= j < 8 ==> #[trigger] byte128(x0.1, j) == (x[16 + j] as u128),
        (x0.1 >> 64) == 0,
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e0, j) == (x[24 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e1, j) == (x[40 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e2, j) == (x[56 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e3, j) == (x[72 + j] as u128),
        forall |j: int| 0 <= j < 8 ==> #[trigger] byte128(e4, j) == (x[88 + j] as u128),
        (e4 >> 64) == 0,
    ensures
        uv[0] == le16_u128(uhash, 0),
        uv[1] == le16_u128(uhash, 16),
        uv[2] == le16_u128(uhash, 32),
        uv[3] == le16_u128(uhash, 48),
        uv[4] == le128_8(uhash, 64),
        x0.0 == le16_u128(x, 0),
        x0.1 == le128_8(x, 16),
        e0 == le16_u128(x, 24),
        e1 == le16_u128(x, 40),
        e2 == le16_u128(x, 56),
        e3 == le16_u128(x, 72),
        e4 == le128_8(x, 88),
{
    lemma_plane16_le(uhash, 0, uv[0]);
    lemma_plane16_le(uhash, 16, uv[1]);
    lemma_plane16_le(uhash, 32, uv[2]);
    lemma_plane16_le(uhash, 48, uv[3]);
    lemma_plane8_le128(uhash, 64, uv[4]);
    lemma_plane16_le(x, 0, x0.0);
    lemma_plane8_le128(x, 16, x0.1);
    lemma_plane16_le(x, 24, e0);
    lemma_plane16_le(x, 40, e1);
    lemma_plane16_le(x, 56, e2);
    lemma_plane16_le(x, 72, e3);
    lemma_plane8_le128(x, 88, e4);
}

/// Origin Rust (:415-428, LeafHasher192::hash).
pub fn leaf_hash_192(uhash: &[u8], x: &[u8]) -> (out: [u8; 72])
    requires
        uhash.len() == 3 * GF192_LENGTH_BYTES,
        x.len() == 4 * GF192_LENGTH_BYTES,
    ensures
        forall |j: int| 0 <= j < 72 ==> #[trigger] out[j]
            == byte576(leaf192_h(uhash@, x@), j),
{
    let uv = gf576_from_bytes(uhash);
    let x0 = gf192_from_bytes(&x[0..24]);
    let sa0 = &x[24..40];
    let sa1 = &x[40..56];
    let sa2 = &x[56..72];
    let sa3 = &x[72..88];
    let sa4 = &x[88..96];
    let e0 = gf128_from_bytes(sa0);
    let e1 = gf128_from_bytes(sa1);
    let e2 = gf128_from_bytes(sa2);
    let e3 = gf128_from_bytes(sa3);
    let e4 = gf128_from_bytes8(sa4);
    proof {
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[0], j) == (uhash[j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[1], j) == (uhash[16 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[2], j) == (uhash[32 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[3], j) == (uhash[48 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 8 implies
            #[trigger]
            byte128(uv[4], j) == (uhash[64 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(x0.0, j) == (x[j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 8 implies
            #[trigger]
            byte128(x0.1, j) == (x[16 + j] as u128) by {
        }
        assert forall |j: int| 8 <= j < 16 implies
            #[trigger]
            byte128(x0.1, j) == 0 by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sa0[j] == x[24 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e0, j) == (x[24 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sa1[j] == x[40 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e1, j) == (x[40 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sa2[j] == x[56 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e2, j) == (x[56 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sa3[j] == x[72 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e3, j) == (x[72 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 8 implies
            #[trigger]
            sa4[j] == x[88 + j] by {
        }
        assert forall |j: int| 0 <= j < 8 implies
            #[trigger]
            byte128(e4, j) == (x[88 + j] as u128) by {
        }
        assert forall |j: int| 8 <= j < 16 implies
            #[trigger]
            byte128(e4, j) == 0 by {
        }
        // scalar high-half rows for the partial limbs (the plane8
        // bridge's clause shape): uv[4] comes scalar-native from the
        // gf576 ensures; x0.1 and e4 fold from their byte rows.
        lemma_hi8_zero(x0.1);
        lemma_hi8_zero(e4);
        lane_rows_192(uhash@, x@, uv, x0, e0, e1, e2, e3, e4);
    }
    let m = gf576_mul_gf192(uv[0], uv[1], uv[2], uv[3], uv[4], x0.0, x0.1);
    proof {
        assert(gf576_mul_bits(uv[0], uv[1], uv[2], uv[3], uv[4], (x0.0, x0.1), 192nat)
            == gf576_mul_bits(
                le16_u128(uhash@, 0), le16_u128(uhash@, 16), le16_u128(uhash@, 32),
                le16_u128(uhash@, 48), le128_8(uhash@, 64),
                (le16_u128(x@, 0), le128_8(x@, 16)), 192nat));
    }
    let hv = [m.0 ^ e0, m.1 ^ e1, m.2 ^ e2, m.3 ^ e3, m.4 ^ e4];
    proof {
        // elementwise tie (array-literal equality does not fold
        // whole here; the limb rows come from lane_rows_192's
        // ensures and the m==p row from the mul ensures chain)
        let u0 = le16_u128(uhash@, 0);
        let u1 = le16_u128(uhash@, 16);
        let u2 = le16_u128(uhash@, 32);
        let u3 = le16_u128(uhash@, 48);
        let u4l = le128_8(uhash@, 64);
        let x00 = le16_u128(x@, 0);
        let x01 = le128_8(x@, 16);
        let e0l = le16_u128(x@, 24);
        let e1l = le16_u128(x@, 40);
        let e2l = le16_u128(x@, 56);
        let e3l = le16_u128(x@, 72);
        let e4l = le128_8(x@, 88);
        let p = gf576_mul_bits(u0, u1, u2, u3, u4l, (x00, x01), 192nat);
        // the mask row: the gf576 mul ensures carries the partial
        // limb masked; fold it back with the scalar high-half fact
        // (a full u128-level blast; no byte lanes involved)
        let uv4 = uv[4];
        assert((uv4 & U128_LOWER_MASK) == uv4) by (bit_vector)
            requires (uv4 >> 64) == 0;
        assert(m == gf576_mul_bits(uv[0], uv[1], uv[2], uv[3], uv[4],
            (x0.0, x0.1), 192nat));
        assert(m.0 == p.0);
        assert(m.1 == p.1);
        assert(m.2 == p.2);
        assert(m.3 == p.3);
        assert(m.4 == p.4);
        assert(hv[0] == p.0 ^ e0l);
        assert(hv[1] == p.1 ^ e1l);
        assert(hv[2] == p.2 ^ e2l);
        assert(hv[3] == p.3 ^ e3l);
        assert(hv[4] == p.4 ^ e4l);
        assert(hv[0] == leaf192_h(uhash@, x@)[0]);
        assert(hv[1] == leaf192_h(uhash@, x@)[1]);
        assert(hv[2] == leaf192_h(uhash@, x@)[2]);
        assert(hv[3] == leaf192_h(uhash@, x@)[3]);
        assert(hv[4] == leaf192_h(uhash@, x@)[4]);
        assert(hv == leaf192_h(uhash@, x@));
    }
    gf576_as_bytes(hv)
}

// ===========================================================================
// LeafHasher at lambda 256 (upstream :431-456, LeafHasher256 at
// F = GF256; ExtensionField = GF768, Length 96).
// ===========================================================================

/// Spec parse of the leaf-hash lanes at lambda 256 (six le limbs on
/// each side, the GF768 product + limb xor in the orbit model).
pub open spec fn leaf256_h(uhash: Seq<u8>, x: Seq<u8>) -> [u128; 6] {
    let u0 = le16_u128(uhash, 0);
    let u1 = le16_u128(uhash, 16);
    let u2 = le16_u128(uhash, 32);
    let u3 = le16_u128(uhash, 48);
    let u4 = le16_u128(uhash, 64);
    let u5 = le16_u128(uhash, 80);
    let x00 = le16_u128(x, 0);
    let x01 = le16_u128(x, 16);
    let e0 = le16_u128(x, 32);
    let e1 = le16_u128(x, 48);
    let e2 = le16_u128(x, 64);
    let e3 = le16_u128(x, 80);
    let e4 = le16_u128(x, 96);
    let e5 = le16_u128(x, 112);
    let p = gf768_mul_bits(u0, u1, u2, u3, u4, u5, (x00, x01), 256nat);
    [p.0 ^ e0, p.1 ^ e1, p.2 ^ e2, p.3 ^ e3, p.4 ^ e4, p.5 ^ e5]
}

/// Lane plane rows shared by leaf_hash_256.
proof fn lane_rows_256(
    uhash: Seq<u8>,
    x: Seq<u8>,
    uv: [u128; 6],
    x0: (u128, u128),
    e0: u128,
    e1: u128,
    e2: u128,
    e3: u128,
    e4: u128,
    e5: u128,
)
    requires
        uhash.len() == 96,
        x.len() == 128,
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[0], j) == (uhash[j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[1], j) == (uhash[16 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[2], j) == (uhash[32 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[3], j) == (uhash[48 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[4], j) == (uhash[64 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(uv[5], j) == (uhash[80 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(x0.0, j) == (x[j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(x0.1, j) == (x[16 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e0, j) == (x[32 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e1, j) == (x[48 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e2, j) == (x[64 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e3, j) == (x[80 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e4, j) == (x[96 + j] as u128),
        forall |j: int| 0 <= j < 16 ==> #[trigger] byte128(e5, j) == (x[112 + j] as u128),
    ensures
        uv[0] == le16_u128(uhash, 0),
        uv[1] == le16_u128(uhash, 16),
        uv[2] == le16_u128(uhash, 32),
        uv[3] == le16_u128(uhash, 48),
        uv[4] == le16_u128(uhash, 64),
        uv[5] == le16_u128(uhash, 80),
        x0.0 == le16_u128(x, 0),
        x0.1 == le16_u128(x, 16),
        e0 == le16_u128(x, 32),
        e1 == le16_u128(x, 48),
        e2 == le16_u128(x, 64),
        e3 == le16_u128(x, 80),
        e4 == le16_u128(x, 96),
        e5 == le16_u128(x, 112),
{
    lemma_plane16_le(uhash, 0, uv[0]);
    lemma_plane16_le(uhash, 16, uv[1]);
    lemma_plane16_le(uhash, 32, uv[2]);
    lemma_plane16_le(uhash, 48, uv[3]);
    lemma_plane16_le(uhash, 64, uv[4]);
    lemma_plane16_le(uhash, 80, uv[5]);
    lemma_plane16_le(x, 0, x0.0);
    lemma_plane16_le(x, 16, x0.1);
    lemma_plane16_le(x, 32, e0);
    lemma_plane16_le(x, 48, e1);
    lemma_plane16_le(x, 64, e2);
    lemma_plane16_le(x, 80, e3);
    lemma_plane16_le(x, 96, e4);
    lemma_plane16_le(x, 112, e5);
}

/// Origin Rust (:446-455, LeafHasher256::hash).
pub fn leaf_hash_256(uhash: &[u8], x: &[u8]) -> (out: [u8; 96])
    requires
        uhash.len() == 3 * GF256_LENGTH_BYTES,
        x.len() == 4 * GF256_LENGTH_BYTES,
    ensures
        forall |j: int| 0 <= j < 96 ==> #[trigger] out[j]
            == byte768(leaf256_h(uhash@, x@), j),
{
    let uv = gf768_from_bytes(uhash);
    let x0 = gf256_from_bytes(&x[0..32]);
    let sb0 = &x[32..48];
    let sb1 = &x[48..64];
    let sb2 = &x[64..80];
    let sb3 = &x[80..96];
    let sb4 = &x[96..112];
    let sb5 = &x[112..128];
    let e0 = gf128_from_bytes(sb0);
    let e1 = gf128_from_bytes(sb1);
    let e2 = gf128_from_bytes(sb2);
    let e3 = gf128_from_bytes(sb3);
    let e4 = gf128_from_bytes(sb4);
    let e5 = gf128_from_bytes(sb5);
    proof {
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[0], j) == (uhash[j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[1], j) == (uhash[16 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[2], j) == (uhash[32 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[3], j) == (uhash[48 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[4], j) == (uhash[64 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(uv[5], j) == (uhash[80 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(x0.0, j) == (x[j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(x0.1, j) == (x[16 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sb0[j] == x[32 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e0, j) == (x[32 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sb1[j] == x[48 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e1, j) == (x[48 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sb2[j] == x[64 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e2, j) == (x[64 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sb3[j] == x[80 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e3, j) == (x[80 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sb4[j] == x[96 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e4, j) == (x[96 + j] as u128) by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            sb5[j] == x[112 + j] by {
        }
        assert forall |j: int| 0 <= j < 16 implies
            #[trigger]
            byte128(e5, j) == (x[112 + j] as u128) by {
        }
        lane_rows_256(uhash@, x@, uv, x0, e0, e1, e2, e3, e4, e5);
    }
    let m = gf768_mul_gf256(uv[0], uv[1], uv[2], uv[3], uv[4], uv[5], x0.0, x0.1);
    proof {
        assert(gf768_mul_bits(uv[0], uv[1], uv[2], uv[3], uv[4], uv[5], (x0.0, x0.1), 256nat)
            == gf768_mul_bits(
                le16_u128(uhash@, 0), le16_u128(uhash@, 16), le16_u128(uhash@, 32),
                le16_u128(uhash@, 48), le16_u128(uhash@, 64), le16_u128(uhash@, 80),
                (le16_u128(x@, 0), le16_u128(x@, 16)), 256nat));
    }
    let hv = [m.0 ^ e0, m.1 ^ e1, m.2 ^ e2, m.3 ^ e3, m.4 ^ e4, m.5 ^ e5];
    proof {
        assert(hv == leaf256_h(uhash@, x@));
    }
    gf768_as_bytes(hv)
}


// ===========================================================================
// ZKHasher at lambda 192 (upstream :142-222 at F = GF192;
// SDLength = Prod<Length, U3> + GF64::Length = 80 bytes). The h1
// plane rides the GF192 Mul<GF64> orbit face (this twin) and the
// h0 plane the gf192 composition spec (FA3).
// ===========================================================================

pub struct ZKHasher192 {
    pub h0: (u128, u128),
    pub h1: (u128, u128),
    pub s: (u128, u128),
    pub t: u64,
    pub r0: (u128, u128),
    pub r1: (u128, u128),
}

impl ZKHasher192 {
    /// Origin Rust (:149-165, new_zk_hasher at GF192): r0 (bytes
    /// 0..24), r1 (24..48), s (48..72), t (72..80); accumulators at
    /// F::ZERO.
    pub fn new_zk_hasher(sd: &[u8]) -> (h: Self)
        requires
            sd.len() == 3 * GF192_LENGTH_BYTES + 8,
        ensures
            h.h0 == GF192_ZERO,
            h.h1 == GF192_ZERO,
            h.s == (le16_u128(sd@, 48), le128_8(sd@, 64)),
            h.t == le8_u64(sd@, 72),
            h.r0 == (le16_u128(sd@, 0), le128_8(sd@, 16)),
            h.r1 == (le16_u128(sd@, 24), le128_8(sd@, 40)),
    {
        let r0 = gf192_from_bytes(&sd[0..24]);
        let r1 = gf192_from_bytes(&sd[24..48]);
        let sv = gf192_from_bytes(&sd[48..72]);
        let tv = gf64_from_bytes(&sd[72..80]);
        proof {
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r0.0, j) == (sd[j] as u128) by {
            }

            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte128(r0.1, j) == (sd[16 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r1.0, j) == (sd[24 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte128(r1.1, j) == (sd[40 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(sv.0, j) == (sd[48 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte128(sv.1, j) == (sd[64 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte64(tv, j) == (sd[72 + j] as u64) by {
            }
            lemma_hi8_zero(r0.1);
            lemma_hi8_zero(r1.1);
            lemma_hi8_zero(sv.1);
            lemma_plane16_le(sd@, 0, r0.0);
            lemma_plane8_le128(sd@, 16, r0.1);
            lemma_plane16_le(sd@, 24, r1.0);
            lemma_plane8_le128(sd@, 40, r1.1);
            lemma_plane16_le(sd@, 48, sv.0);
            lemma_plane8_le128(sd@, 64, sv.1);
            lemma_plane8_le64(sd@, 72, tv);
        }
        ZKHasher192 {
            h0: GF192_ZERO,
            h1: GF192_ZERO,
            s: sv,
            t: tv,
            r0: r0,
            r1: r1,
        }
    }

    /// Origin Rust (:214-217, update at GF192): field mul on h0 via
    /// gf192_mul (== the composition spec), the GF64 orbit face on
    /// h1 this twin provides.
    pub fn update(self: &mut Self, v: (u128, u128))
        ensures
            final(self).h0
                == xor2(
                    gf192_mul_spec(old(self).h0.0, old(self).h0.1,
                        old(self).s.0, old(self).s.1),
                    v,
                ),
            final(self).h1
                == xor2(
                    gf192_mg64_bits(old(self).h1.0, old(self).h1.1,
                        (old(self).t as u128), 64nat),
                    v,
                ),
            final(self).s == old(self).s,
            final(self).t == old(self).t,
            final(self).r0 == old(self).r0,
            final(self).r1 == old(self).r1,
    {
        let h0n = gf192_mul(self.h0.0, self.h0.1, self.s.0, self.s.1);
        let h1n = gf192_mul_gf64(self.h1.0, self.h1.1, self.t);
        self.h0 = (h0n.0 ^ v.0, h0n.1 ^ v.1);
        self.h1 = (h1n.0 ^ v.0, h1n.1 ^ v.1);
    }

    /// Origin Rust (:219-221, finalize at GF192).
    pub fn finalize(self: &Self, x1: (u128, u128)) -> (res: (u128, u128))
        ensures
            res == xor2(
                xor2(
                    gf192_mul_spec(self.r0.0, self.r0.1, self.h0.0, self.h0.1),
                    gf192_mul_spec(self.r1.0, self.r1.1, self.h1.0, self.h1.1),
                ),
                x1,
            ),
    {
        let m0 = gf192_mul(self.r0.0, self.r0.1, self.h0.0, self.h0.1);
        let m1 = gf192_mul(self.r1.0, self.r1.1, self.h1.0, self.h1.1);
        (m0.0 ^ m1.0 ^ x1.0, m0.1 ^ m1.1 ^ x1.1)
    }
}

// ===========================================================================
// ZKHasher at lambda 256 (upstream :142-222 at F = GF256;
// SDLength = 3*32+8 = 104 bytes).
// ===========================================================================

pub struct ZKHasher256 {
    pub h0: (u128, u128),
    pub h1: (u128, u128),
    pub s: (u128, u128),
    pub t: u64,
    pub r0: (u128, u128),
    pub r1: (u128, u128),
}

impl ZKHasher256 {
    /// Origin Rust (:149-165, new_zk_hasher at GF256): r0 (0..32),
    /// r1 (32..64), s (64..96), t (96..104).
    pub fn new_zk_hasher(sd: &[u8]) -> (h: Self)
        requires
            sd.len() == 3 * GF256_LENGTH_BYTES + 8,
        ensures
            h.h0 == GF256_ZERO,
            h.h1 == GF256_ZERO,
            h.s == (le16_u128(sd@, 64), le16_u128(sd@, 80)),
            h.t == le8_u64(sd@, 96),
            h.r0 == (le16_u128(sd@, 0), le16_u128(sd@, 16)),
            h.r1 == (le16_u128(sd@, 32), le16_u128(sd@, 48)),
    {
        let r0 = gf256_from_bytes(&sd[0..32]);
        let r1 = gf256_from_bytes(&sd[32..64]);
        let sv = gf256_from_bytes(&sd[64..96]);
        let tv = gf64_from_bytes(&sd[96..104]);
        proof {
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r0.0, j) == (sd[j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r0.1, j) == (sd[16 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r1.0, j) == (sd[32 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(r1.1, j) == (sd[48 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(sv.0, j) == (sd[64 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 16 implies
                #[trigger]
                byte128(sv.1, j) == (sd[80 + j] as u128) by {
            }
            assert forall |j: int| 0 <= j < 8 implies
                #[trigger]
                byte64(tv, j) == (sd[96 + j] as u64) by {
            }
            lemma_plane16_le(sd@, 0, r0.0);
            lemma_plane16_le(sd@, 16, r0.1);
            lemma_plane16_le(sd@, 32, r1.0);
            lemma_plane16_le(sd@, 48, r1.1);
            lemma_plane16_le(sd@, 64, sv.0);
            lemma_plane16_le(sd@, 80, sv.1);
            lemma_plane8_le64(sd@, 96, tv);
        }
        ZKHasher256 {
            h0: GF256_ZERO,
            h1: GF256_ZERO,
            s: sv,
            t: tv,
            r0: r0,
            r1: r1,
        }
    }

    /// Origin Rust (:214-217, update at GF256).
    pub fn update(self: &mut Self, v: (u128, u128))
        ensures
            final(self).h0
                == xor2(
                    gf256_mul_spec(old(self).h0.0, old(self).h0.1,
                        old(self).s.0, old(self).s.1),
                    v,
                ),
            final(self).h1
                == xor2(
                    gf256_mg64_bits(old(self).h1.0, old(self).h1.1,
                        (old(self).t as u128), 64nat),
                    v,
                ),
            final(self).s == old(self).s,
            final(self).t == old(self).t,
            final(self).r0 == old(self).r0,
            final(self).r1 == old(self).r1,
    {
        let h0n = gf256_mul(self.h0.0, self.h0.1, self.s.0, self.s.1);
        let h1n = gf256_mul_gf64(self.h1.0, self.h1.1, self.t);
        self.h0 = (h0n.0 ^ v.0, h0n.1 ^ v.1);
        self.h1 = (h1n.0 ^ v.0, h1n.1 ^ v.1);
    }

    /// Origin Rust (:219-221, finalize at GF256).
    pub fn finalize(self: &Self, x1: (u128, u128)) -> (res: (u128, u128))
        ensures
            res == xor2(
                xor2(
                    gf256_mul_spec(self.r0.0, self.r0.1, self.h0.0, self.h0.1),
                    gf256_mul_spec(self.r1.0, self.r1.1, self.h1.0, self.h1.1),
                ),
                x1,
            ),
    {
        let m0 = gf256_mul(self.r0.0, self.r0.1, self.h0.0, self.h0.1);
        let m1 = gf256_mul(self.r1.0, self.r1.1, self.h1.0, self.h1.1);
        (m0.0 ^ m1.0 ^ x1.0, m0.1 ^ m1.1 ^ x1.1)
    }
}

} // verus!
