//! faest 0.3.0 -- Verus transcription of src/fields/small_fields.rs,
//! batch FA2.
//!
//! Upstream: fields/small_fields.rs (372 lines, pin 9ccc68c0). The file
//! defines the SmallGF<T> wrapper over u8 (GF8) and u64 (GF64), the
//! ExtractBit helpers feeding the cmov conditions, the GaloisFieldHelper
//! trait with its constant-time mul_helper (small_fields.rs:63-76), the
//! Add/Sub/Neg/BitAnd faces (xor / identity semantics), GF8::square_bits
//! (:270), the Field impl for GF64 (:286), and From<&[u8]> for GF64
//! (:305). The inline test module (:314-372, gf64_test_mul) has its KAT
//! content re-erected in the FA2 harness (upstream identities + two of
//! the five hardcoded database tuples + one commutativity pair).
//!
//! Representation lowering (recorded per the inventory's trusted-face
//! decisions):
//!   - `SmallGF<T>` is #[repr(transparent)] over T with no runtime
//!     semantics of its own; the twin lowers it to plain u8/u64 with the
//!     wrapper documented at each face. From<T>/From<SmallGF<T>> for
//!     u8/u64, Default, PartialEq<T>, and BitAnd are identity/xor faces
//!     on that representation and transcribe as plain fns.
//!   - cmov Cmov::cmovnz(dst, src, cond) == `if cond != 0 { dst = src }`
//!     enters as a TRUSTED one-line select face (inventory section 4);
//!     the constant-time property itself stays a shape claim -- what IS
//!     machine-checked here is the select equivalence: the exec body
//!     keeps the upstream cmov-if-free branch shape (no early return,
//!     select-only structure), and verifies against the plain recursive
//!     multiplication model below.
//!   - cmov::Condition is a u8 alias; the helpers return u8 conditions
//!     exactly as upstream.
//!
//! Model note (probe-confirmed, out/kverus-run/FA2/probe1..6): the spec
//! below is machine-typed (u8/u64 spec-mode bit ops) and recursive over a
//! nat fuel w -- the u64 >> 1 measure has no termination axiom in this
//! build (probe2), so fuel carries the full-bit-domain witness (k=8/64:
//! every bit position of the multiplier is consumed). Folding rules
//! learned from the probes: concrete machine bit-op comparisons do not
//! fold in the default encoding (each one needs a bit_vector blast), BV
//! blast blocks must never carry spec-fn applications or Nat in their
//! requires, and the plain encoding proves nothing for over-width shifts
//! (the loop-exit invariant is therefore piecewise, probe6).

use vstd::prelude::*;

verus! {

// ===========================================================================
// GaloisFieldHelper constants (upstream small_fields.rs:190-200).
// Origin Rust:
//     impl GaloisFieldHelper<u64> for SmallGF<u64> {
//         const BITS: usize = u64::BITS as usize;
//         const MODULUS: u64 = 0b00011011u64;
//         const ZERO: u64 = 0u64; }
//     impl GaloisFieldHelper<u8> for SmallGF<u8> {
//         const BITS: usize = u8::BITS as usize;
//         const MODULUS: u8 = 0b00011011;
//         const ZERO: u8 = 0u8; }
// The modulus 0b11011 (x^4+x^3+x+1) is the low half of the reduction
// polynomials x^8 + x^4 + x^3 + x + 1 (GF(2^8)) and
// x^64 + x^4 + x^3 + x + 1 (GF(2^64)).
// ===========================================================================

/// `GaloisFieldHelper<u64>` constants, the GF(2^64) face (upstream
/// small_fields.rs:190-194). `BITS` is the full-bit-domain width of the
/// multiplication loop's witness.
pub const GF64_BITS: usize = 64;
/// Reduction-polynomial low half for GF(2^64) (upstream `MODULUS`).
pub const GF64_MODULUS: u64 = 0x1B;
/// Additive / multiplicative machine zero (upstream `ZERO`; also Field::ZERO
/// for GF64, small_fields.rs:287).
pub const GF64_ZERO: u64 = 0;

/// `GaloisFieldHelper<u8>` constants, the GF(2^8) face (upstream
/// small_fields.rs:196-200).
pub const GF8_BITS: usize = 8;
/// Reduction-polynomial low half for GF(2^8) (upstream `MODULUS`).
pub const GF8_MODULUS: u8 = 0x1B;
/// Machine zero (upstream `ZERO`).
pub const GF8_ZERO: u8 = 0;

// ===========================================================================
// Spec model: xtime ("multiply by x in the field") and the recursive
// orbit-consumed multiplication. This is the plain textbook definition of
// GF(2^k) multiplication (low-bit-first Horner over the multiplier's bits,
// reducing the orbit each step), NOT a copy of the exec body: the exec body
// below is the upstream cmov-register loop. Proving the latter equal to
// this model is the batch's main obligation.
// ===========================================================================

/// Value of x * v in GF(2^64) for v < 2^64: shift up, conditionally reduce
/// by the low half of x^64 + x^4 + x^3 + x + 1. (Machine-typed spec fn; the
/// default encoding reasons about it only through definitional unfolding
/// plus bit_vector-fed facts.)
pub open spec fn gf64_xtime(v: u64) -> u64 {
    (v << 1) ^ (if (v >> 63) & 1 == 1 { GF64_MODULUS } else { 0u64 })
}

/// Contribution stream of the multiplication: fold over the multiplier's
/// remaining bits (`r_tail`), each step taking `r_tail`'s low bit, adding
/// the current orbit element when set, and stepping the orbit by xtime.
/// `w` bounds how many bits are consumed (fuel); `w == GF64_BITS` covers
/// the whole u64 domain.
pub open spec fn gf64_mul_bits(orbit: u64, r_tail: u64, w: nat) -> u64
    decreases w,
{
    if w == 0 {
        0u64
    } else {
        (if r_tail & 1 == 1 { orbit } else { 0u64 })
            ^ gf64_mul_bits(gf64_xtime(orbit), r_tail >> 1, (w - 1) as nat)
    }
}

/// The multiplication of GF(2^64) used as the spec face of gf64_mul_helper:
/// full 64-bit fuel (the full-bit-domain witness, audit line: the upstream
/// loop is `for i in 1..Self::BITS` with BITS == 64).
pub open spec fn gf64_mul_spec(l: u64, r: u64) -> u64 {
    gf64_mul_bits(l, r, GF64_BITS as nat)
}

/// x * v in GF(2^8) (upstream's 0b00011011 reduction tail on u8).
pub open spec fn gf8_xtime(v: u8) -> u8 {
    (v << 1) ^ (if (v >> 7) & 1 == 1 { GF8_MODULUS } else { 0u8 })
}

/// GF(2^8) twin of gf64_mul_bits (fuel w, u8 domain).
pub open spec fn gf8_mul_bits(orbit: u8, r_tail: u8, w: nat) -> u8
    decreases w,
{
    if w == 0 {
        0u8
    } else {
        (if r_tail & 1 == 1 { orbit } else { 0u8 })
            ^ gf8_mul_bits(gf8_xtime(orbit), r_tail >> 1, (w - 1) as nat)
    }
}

/// The GF(2^8) multiplication spec face (full 8-bit fuel).
pub open spec fn gf8_mul_spec(l: u8, r: u8) -> u8 {
    gf8_mul_bits(l, r, GF8_BITS as nat)
}

// ===========================================================================
// BV micro-lemma bank. Rule from the probes: every lemma body proves its
// fact with a `by (bit_vector)` blast; parameters and requires of the
// blasts are plain machine values / literals ONLY (no spec-fn
// applications, no Nat -- probe2/4c hangs, the #FA1-6 family extended).
// Every lemma carries ensures: a bare assert inside a proof fn exports
// nothing to its callers (probe4d).
// ===========================================================================

proof fn bv_xor_comm64(a: u64, b: u64)
    ensures
        (a ^ b) == (b ^ a),
{
    assert(a ^ b == b ^ a) by (bit_vector);
}

proof fn bv_xor_ac64(a: u64, b: u64, c: u64)
    ensures
        ((a ^ b) ^ c) == (a ^ (b ^ c)),
        ((a ^ b) ^ c) == (b ^ (c ^ a)),
{
    assert((a ^ b) ^ c == a ^ (b ^ c)) by (bit_vector);
    assert((a ^ b) ^ c == b ^ (c ^ a)) by (bit_vector);
}

proof fn bv_xor_comm8(a: u8, b: u8)
    ensures
        (a ^ b) == (b ^ a),
{
    assert(a ^ b == b ^ a) by (bit_vector);
}

proof fn bv_xor_ac8(a: u8, b: u8, c: u8)
    ensures
        ((a ^ b) ^ c) == (a ^ (b ^ c)),
        ((a ^ b) ^ c) == (b ^ (c ^ a)),
{
    assert((a ^ b) ^ c == a ^ (b ^ c)) by (bit_vector);
    assert((a ^ b) ^ c == b ^ (c ^ a)) by (bit_vector);
}

/// The two concrete zero-bit facts the zero-tail induction needs at every
/// fuel level (default encoding does not fold even `0u64 & 1 == 0`).
proof fn bv_concrete_zero64()
    ensures
        (0u64 & 1) == 0u64,
        !(0u64 & 1 == 1),
        (0u64 >> 1) == 0u64,
{
    assert((0u64 & 1) == 0u64) by (bit_vector);
    assert(0u64 >> 1 == 0u64) by (bit_vector);
}

proof fn bv_concrete_zero8()
    ensures
        (0u8 & 1) == 0u8,
        !(0u8 & 1 == 1),
        (0u8 >> 1) == 0u8,
{
    assert((0u8 & 1) == 0u8) by (bit_vector);
    assert(0u8 >> 1 == 0u8) by (bit_vector);
}

// ===========================================================================
// Library lemmas over the model.
// ===========================================================================

/// Definitional one-level unfold of the GF(2^64) model at non-zero fuel.
/// (Plain definitional reasoning -- conditions stay symbolic here, so no
/// blast feeding is needed; probe4a.)
pub proof fn lemma_mul64_bits_unfold(o: u64, q: u64, w: nat)
    requires
        0 < w,
    ensures
        gf64_mul_bits(o, q, w)
            == (if q & 1 == 1 { o } else { 0u64 })
                ^ gf64_mul_bits(gf64_xtime(o), q >> 1, (w - 1) as nat),
{
}

/// Definitional one-level unfold of the GF(2^8) model at non-zero fuel.
pub proof fn lemma_mul8_bits_unfold(o: u8, q: u8, w: nat)
    requires
        0 < w,
    ensures
        gf8_mul_bits(o, q, w)
            == (if q & 1 == 1 { o } else { 0u8 })
                ^ gf8_mul_bits(gf8_xtime(o), q >> 1, (w - 1) as nat),
{
}

/// Zero-tail collapse for GF(2^64): a zero multiplier tail contributes
/// nothing, at any remaining fuel (probe4d shape).
pub proof fn lemma_mul64_zero_tail(o: u64, w: nat)
    ensures
        gf64_mul_bits(o, 0u64, w) == 0u64,
    decreases w,
{
    if w == 0 {
    } else {
        bv_concrete_zero64();
        assert(gf64_mul_bits(o, 0u64, w)
            == (if 0u64 & 1 == 1 { o } else { 0u64 })
                ^ gf64_mul_bits(gf64_xtime(o), 0u64 >> 1, (w - 1) as nat));
        assert((if 0u64 & 1 == 1 { o } else { 0u64 }) == 0u64);
        assert(0u64 >> 1 == 0u64);
        assert(gf64_mul_bits(o, 0u64, w)
            == 0u64 ^ gf64_mul_bits(gf64_xtime(o), 0u64, (w - 1) as nat));
        bv_xor_zero_tail64(gf64_mul_bits(gf64_xtime(o), 0u64, (w - 1) as nat));
        assert(gf64_mul_bits(o, 0u64, w)
            == gf64_mul_bits(gf64_xtime(o), 0u64, (w - 1) as nat));
        lemma_mul64_zero_tail(gf64_xtime(o), (w - 1) as nat);
    }
}

proof fn bv_xor_zero_tail64(t: u64)
    ensures
        (0u64 ^ t) == t,
{
    assert(0u64 ^ t == t) by (bit_vector);
}

/// Zero-tail collapse for GF(2^8).
pub proof fn lemma_mul8_zero_tail(o: u8, w: nat)
    ensures
        gf8_mul_bits(o, 0u8, w) == 0u8,
    decreases w,
{
    if w == 0 {
    } else {
        bv_concrete_zero8();
        assert(gf8_mul_bits(o, 0u8, w)
            == (if 0u8 & 1 == 1 { o } else { 0u8 })
                ^ gf8_mul_bits(gf8_xtime(o), 0u8 >> 1, (w - 1) as nat));
        assert((if 0u8 & 1 == 1 { o } else { 0u8 }) == 0u8);
        assert(0u8 >> 1 == 0u8);
        assert(gf8_mul_bits(o, 0u8, w)
            == 0u8 ^ gf8_mul_bits(gf8_xtime(o), 0u8, (w - 1) as nat));
        bv_xor_zero_tail8(gf8_mul_bits(gf8_xtime(o), 0u8, (w - 1) as nat));
        assert(gf8_mul_bits(o, 0u8, w)
            == gf8_mul_bits(gf8_xtime(o), 0u8, (w - 1) as nat));
        lemma_mul8_zero_tail(gf8_xtime(o), (w - 1) as nat);
    }
}

proof fn bv_xor_zero_tail8(t: u8)
    ensures
        (0u8 ^ t) == t,
{
    assert(0u8 ^ t == t) by (bit_vector);
}

/// Annihilation on the right (upstream test line: pol_anything * pol_0 ==
/// pol_0, small_fields.rs:330): the zero-tail collapse with full fuel.
pub proof fn lemma_mul64_zero_r(l: u64)
    ensures
        gf64_mul_spec(l, 0u64) == 0u64,
{
    lemma_mul64_zero_tail(l, GF64_BITS as nat);
}

pub proof fn lemma_mul8_zero_r(l: u8)
    ensures
        gf8_mul_spec(l, 0u8) == 0u8,
{
    lemma_mul8_zero_tail(l, GF8_BITS as nat);
}

/// Annihilation on the left (upstream test line: pol_0 * pol_anything
/// == pol_0, small_fields.rs:330): the zero orbit stays zero at every
/// fuel level (xtime of zero is zero), so every contribution is zero.
pub proof fn lemma_mul64_zero_l(r: u64)
    ensures
        gf64_mul_spec(0u64, r) == 0u64,
    decreases 64nat,
{
    lemma_mul64_zero_l_fuel(r, GF64_BITS as nat);
}

proof fn lemma_mul64_zero_l_fuel(r: u64, w: nat)
    ensures
        gf64_mul_bits(0u64, r, w) == 0u64,
    decreases w,
{
    if w == 0 {
    } else {
        // xtime(0) == 0 (concrete machine fold)
        assert(((0u64 << 1) ^ (if ((0u64 >> 63) & 1) == 1u64 { GF64_MODULUS } else { 0u64 })) == 0u64) by (bit_vector);
        lemma_mul64_bits_unfold(0u64, r, w);
        assert(gf64_mul_bits(0u64, (r) >> 1u64, (w - 1) as nat) == 0u64) by {
            lemma_mul64_zero_l_fuel(r >> 1u64, (w - 1) as nat);
        }
        // both select branches are 0, and 0 ^ 0 == 0
        assert((if r & 1 == 1u64 { 0u64 } else { 0u64 }) == 0u64);
        assert((0u64 ^ 0u64) == 0u64) by (bit_vector);
    }
}

/// GF(2^8) twin of the left-annihilation lemma.
pub proof fn lemma_mul8_zero_l(r: u8)
    ensures
        gf8_mul_spec(0u8, r) == 0u8,
{
    lemma_mul8_zero_l_fuel(r, GF8_BITS as nat);
}

proof fn lemma_mul8_zero_l_fuel(r: u8, w: nat)
    ensures
        gf8_mul_bits(0u8, r, w) == 0u8,
    decreases w,
{
    if w == 0 {
    } else {
        assert((((0u8 << 1) ^ (if ((0u8 >> 7) & 1) == 1u8 { GF8_MODULUS } else { 0u8 }))) == 0u8) by (bit_vector);
        lemma_mul8_bits_unfold(0u8, r, w);
        assert(gf8_mul_bits(0u8, (r) >> 1u8, (w - 1) as nat) == 0u8) by {
            lemma_mul8_zero_l_fuel(r >> 1u8, (w - 1) as nat);
        }
        assert((if r & 1 == 1u8 { 0u8 } else { 0u8 }) == 0u8);
        assert((0u8 ^ 0u8) == 0u8) by (bit_vector);
    }
}

/// Multiplicative identity on the right (upstream test line:
/// pol_anything * pol_1 == pol_anything, small_fields.rs:333): the only
/// set multiplier bit is bit 0, whose contribution is the unstepped
/// orbit, and the tail collapses.
pub proof fn lemma_mul64_one_r(l: u64)
    ensures
        gf64_mul_spec(l, 1u64) == l,
{
    assert((1u64 & 1) == 1u64) by (bit_vector);
    lemma_mul64_bits_unfold(l, 1u64, GF64_BITS as nat);
    assert((if (1u64 & 1) == 1u64 { l } else { 0u64 }) == l);
    assert(1u64 >> 1 == 0u64) by (bit_vector);
    lemma_mul64_zero_tail(gf64_xtime(l), (GF64_BITS - 1) as nat);
    assert(gf64_mul_bits(gf64_xtime(l), 1u64 >> 1, (GF64_BITS - 1) as nat)
        == gf64_mul_bits(gf64_xtime(l), 0u64, (GF64_BITS - 1) as nat));
    assert(gf64_mul_bits(l, 1u64, GF64_BITS as nat)
        == l ^ gf64_mul_bits(gf64_xtime(l), 0u64, (GF64_BITS - 1) as nat));
    assert((l ^ 0u64) == l) by (bit_vector);
    assert(gf64_mul_bits(l, 1u64, GF64_BITS as nat) == l);
    assert(gf64_mul_spec(l, 1u64) == gf64_mul_bits(l, 1u64, GF64_BITS as nat));
}

pub proof fn lemma_mul8_one_r(l: u8)
    ensures
        gf8_mul_spec(l, 1u8) == l,
{
    assert((1u8 & 1) == 1u8) by (bit_vector);
    lemma_mul8_bits_unfold(l, 1u8, GF8_BITS as nat);
    assert((if (1u8 & 1) == 1u8 { l } else { 0u8 }) == l);
    assert(1u8 >> 1 == 0u8) by (bit_vector);
    lemma_mul8_zero_tail(gf8_xtime(l), (GF8_BITS - 1) as nat);
    assert(gf8_mul_bits(gf8_xtime(l), 1u8 >> 1, (GF8_BITS - 1) as nat)
        == gf8_mul_bits(gf8_xtime(l), 0u8, (GF8_BITS - 1) as nat));
    assert(gf8_mul_bits(l, 1u8, GF8_BITS as nat)
        == l ^ gf8_mul_bits(gf8_xtime(l), 0u8, (GF8_BITS - 1) as nat));
    assert((l ^ 0u8) == l) by (bit_vector);
    assert(gf8_mul_bits(l, 1u8, GF8_BITS as nat) == l);
    assert(gf8_mul_spec(l, 1u8) == gf8_mul_bits(l, 1u8, GF8_BITS as nat));
}

// ===========================================================================
// ExtractBit (upstream small_fields.rs:10-42), u64 and u8 impls.
// Upstream signatures:
//     trait ExtractBit {
//         fn extract_bit(&self, bit: usize) -> Condition;
//         fn extract_lowest_bit(&self) -> Condition;
//         fn extract_highest_bit(&self) -> Condition; }
// (cmov::Condition is a u8 alias; the values are 0/1 conditions feeding
// cmovnz.) The helpers carry no upstream bounds on `bit`; the twin
// re-erects the machine shift's real domain as requires.
// ===========================================================================

/// Origin Rust (small_fields.rs:16-28, u64 impl):
///     fn extract_bit(&self, bit: usize) -> Condition {
///         ((self >> bit) & 0x1) as u8 }
/// Value face: the `bit`-th bit of x as a 0/1 u8 condition.
#[inline]
pub exec fn extract_bit_u64(x: u64, bit: usize) -> (c: u8)
    requires
        bit < GF64_BITS,
    ensures
        (c as u64) == ((x >> (bit as u64)) & 1),
        c <= 1u8,
{
    assert(((x >> (bit as u64)) & 1) == 0u64 || ((x >> (bit as u64)) & 1) == 1u64) by (bit_vector);
    (((x >> (bit as u64)) & 1) as u8) as u8
}

/// Origin Rust (small_fields.rs:21-23):
///     fn extract_lowest_bit(&self) -> Condition {
///         (self & 0x1) as u8 }
#[inline]
pub exec fn extract_lowest_bit_u64(x: u64) -> (c: u8)
    ensures
        (c as u64) == (x & 1),
        c <= 1u8,
{
    assert(((x & 1) == 0u64) || ((x & 1) == 1u64)) by (bit_vector);
    ((x & 1) as u8) as u8
}

/// Origin Rust (small_fields.rs:25-27):
///     fn extract_highest_bit(&self) -> Condition {
///         (self >> 63) as u8 }
/// The cast is value-exact because the shifted value is 0/1; the twin
/// spells that fact for the checked cast.
#[inline]
pub exec fn extract_highest_bit_u64(x: u64) -> (c: u8)
    ensures
        (c as u64) == ((x >> 63) & 1),
        c <= 1u8,
{
    assert(((x >> 63) & 1) == 0u64 || ((x >> 63) & 1) == 1u64) by (bit_vector);
    assert(((x >> 63) & 1) == (x >> 63)) by (bit_vector);
    #[verifier::truncate] let c: u8 = (x >> 63) as u8;
    assert((c as u64) == (x >> 63));
    c
}

/// Origin Rust (small_fields.rs:30-42, u8 impl):
///     fn extract_bit(&self, bit: usize) -> Condition { (self >> bit) & 0x1 }
#[inline]
pub exec fn extract_bit_u8(x: u8, bit: usize) -> (c: u8)
    requires
        bit < GF8_BITS,
    ensures
        c == ((x >> (bit as u8)) & 1),
        c <= 1u8,
{
    assert(((x >> (bit as u8)) & 1) == 0u8 || ((x >> (bit as u8)) & 1) == 1u8) by (bit_vector);
    ((x >> (bit as u8)) & 1) as u8
}

/// Origin Rust (small_fields.rs:34-36):
///     fn extract_lowest_bit(&self) -> Condition { self & 0x1 }
#[inline]
pub exec fn extract_lowest_bit_u8(x: u8) -> (c: u8)
    ensures
        c == (x & 1),
        c <= 1u8,
{
    assert(((x & 1) == 0u8) || ((x & 1) == 1u8)) by (bit_vector);
    (x & 1) as u8
}

/// Origin Rust (small_fields.rs:39-41):
///     fn extract_highest_bit(&self) -> Condition { self >> 7 }
#[inline]
pub exec fn extract_highest_bit_u8(x: u8) -> (c: u8)
    ensures
        c == (x >> 7),
        c <= 1u8,
{
    assert(((x >> 7) == 0u8) || ((x >> 7) == 1u8)) by (bit_vector);
    (x >> 7) as u8
}

// ===========================================================================
// mul_helper (upstream small_fields.rs:63-77) -- the constant-time heart.
// This file's twin keeps the upstream register-loop shape verbatim: the
// cmovnz calls lower to select expressions (trusted select face), the
// extract-bit helpers are called exactly where upstream calls them, and
// no early return or data-dependent branch exists in the body. The proof
// obligation discharged is that this loop computes the plain recursive
// multiplication model above.
// ===========================================================================

/// Origin Rust (small_fields.rs:63-77):
///     fn mul_helper(mut left: SmallGF<T>, right: SmallGF<T>) -> SmallGF<T> {
///         let mut result_value = Self::ZERO;
///         result_value.cmovnz(&left.0, right.0.extract_lowest_bit());
///         for i in 1..Self::BITS {
///             let mut mask = Self::ZERO;
///             mask.cmovnz(&Self::MODULUS, left.0.extract_highest_bit());
///             left.0 = (left.0 << 1) ^ mask;
///             let mut add = Self::ZERO;
///             add.cmovnz(&left.0, right.0.extract_bit(i));
///             result_value ^= add;
///         }
///         SmallGF(result_value) }
/// GF(2^64) face (SmallGF<u64>, SmallGF lowered to u64). Shape audit
/// (verified structurally here): no early return; every cmovnz is the
/// select face; the loop walks every bit 1..64 (full-bit-domain witness).
pub exec fn gf64_mul_helper(left0: u64, right: u64) -> (res: u64)
    ensures
        res == gf64_mul_spec(left0, right),
        res == gf64_mul_bits(left0, right, GF64_BITS as nat),
{
    let mut left: u64 = left0;
    let mut result_value: u64 = 0;
    let c0: u8 = extract_lowest_bit_u64(right);
    result_value = if (c0 as u64) != 0 { left } else { 0u64 };
    proof {
        assert((c0 as u64) == 1u64 <==> (right & 1) == 1u64) by (bit_vector)
            requires
                (c0 as u64) == (right & 1),
        ;
        let sel0: u64 = if right & 1 == 1 { left0 } else { 0u64 };
        assert(result_value == sel0);
        lemma_mul64_bits_unfold(left0, right, GF64_BITS as nat);
        let entry_tail: u64 = gf64_mul_bits(gf64_xtime(left0), right >> (1 as u64), (GF64_BITS - 1) as nat);
        assert(gf64_mul_bits(left0, right, GF64_BITS as nat) == sel0 ^ entry_tail);
        assert(entry_tail ^ result_value == gf64_mul_bits(left0, right, GF64_BITS as nat)) by {
            bv_xor_comm64(entry_tail, sel0);
            bv_xor_ac64(sel0, entry_tail, result_value);
        }
    }
    let mut i: usize = 1;
    while i < GF64_BITS
        invariant
            1 <= i <= GF64_BITS,
            i < GF64_BITS ==>
                gf64_mul_bits(gf64_xtime(left), right >> (i as u64), (GF64_BITS - i) as nat)
                    ^ result_value == gf64_mul_spec(left0, right),
            i == GF64_BITS ==> result_value == gf64_mul_spec(left0, right),
        decreases GF64_BITS - i,
    {
        let lold: u64 = left;
        let rold: u64 = result_value;
        let r_i: u64 = right >> (i as u64);
        proof {
            // tail shift compose (or the 63-case zero fold)
            if (i + 1) < GF64_BITS {
                let t = (right >> (i as u64)) >> 1u64;
                let t2 = right >> ((i + 1) as u64);
                assert(t == t2) by (bit_vector)
                    requires
                        (i + 1) < GF64_BITS,
                        t == (right >> (i as u64)) >> 1u64,
                        t2 == right >> ((i + 1) as u64),
                ;
            } else {
                // i == 63: r_i has at most 1 bit left
                let rv = (right >> (i as u64)) >> 1u64;
                assert(rv == 0u64) by (bit_vector)
                    requires
                        i == 63,
                        rv == (right >> (i as u64)) >> 1u64,
                ;
            }
        }
        let ch: u8 = extract_highest_bit_u64(lold);
        let mask: u64 = if (ch as u64) != 0 { GF64_MODULUS } else { 0u64 };
        left = (lold << 1) ^ mask;
        let ci: u8 = extract_bit_u64(right, i);
        let add: u64 = if (ci as u64) != 0 { left } else { 0u64 };
        result_value = rold ^ add;
        proof {
            let a1: u64 = gf64_xtime(lold);
            assert((ch as u64) == 1u64 <==> ((lold >> 63) & 1) == 1u64) by (bit_vector)
                requires
                    (ch as u64) == ((lold >> 63) & 1),
            ;
            assert(mask == (if ((lold >> 63) & 1) == 1u64 { GF64_MODULUS } else { 0u64 }));
            assert(left == a1) by {
                assert(gf64_xtime(lold)
                    == ((lold << 1) ^ (if ((lold >> 63) & 1) == 1u64 { GF64_MODULUS } else { 0u64 })));
            }
            assert((ci as u64) == 1u64 <==> (r_i & 1) == 1u64) by (bit_vector)
                requires
                    (ci as u64) == ((right >> (i as u64)) & 1),
                    r_i == right >> (i as u64),
            ;
            assert(add == (if (r_i & 1) == 1u64 { left } else { 0u64 }));
            assert(((GF64_BITS - i) - 1) == GF64_BITS - (i + 1));
            let w: nat = (GF64_BITS - i) as nat;
            lemma_mul64_bits_unfold(a1, r_i, w);
            let contrib: u64 = if (r_i & 1) == 1u64 { left } else { 0u64 };
            let tailA: u64 = gf64_mul_bits(gf64_xtime(a1), (r_i) >> 1u64, (w - 1) as nat);
            let tailB: u64 = gf64_mul_bits(gf64_xtime(left), (r_i) >> 1u64, (w - 1) as nat);
            assert(tailA == tailB);
            assert(gf64_mul_bits(a1, r_i, w) == contrib ^ tailA);
            let jn: usize = (i + 1) as usize;
            if (i + 1) < GF64_BITS {
                assert((r_i) >> 1u64 == right >> (jn as u64));
                // re-group for the piecewise (<) case
                assert(rold ^ contrib == result_value);
                assert((contrib ^ tailB) ^ rold == gf64_mul_spec(left0, right));
                assert((contrib ^ tailB) ^ rold == tailB ^ (rold ^ contrib)) by {
                    bv_xor_ac64(contrib, tailB, rold);
                    bv_xor_comm64(contrib, rold);
                }
                assert(tailB ^ result_value == gf64_mul_spec(left0, right));
            } else {
                // i == 63: fuel w == 1, the tail collapses and the exit
                // case of the piecewise invariant takes over
                assert(tailA == 0u64) by {
                    assert(gf64_mul_bits(gf64_xtime(a1), (r_i) >> 1u64, 0nat) == 0u64);
                }
                assert(gf64_mul_bits(a1, r_i, w) == contrib ^ 0u64);
                assert((contrib ^ 0u64) == contrib) by (bit_vector);
                assert(gf64_mul_bits(a1, r_i, w) == contrib);
                assert(rold ^ contrib == result_value);
                assert(result_value == gf64_mul_spec(left0, right)) by {
                    bv_xor_ac64(contrib, tailB, rold);
                    bv_xor_comm64(contrib, rold);
                    assert((contrib ^ tailB) ^ rold == tailB ^ (rold ^ contrib));
                    assert(tailB == 0u64);
                }
            }
        }
        i += 1;
    }
    result_value
}

/// GF(2^8) twin of gf64_mul_helper (upstream SmallGF<u8> instantiation,
/// same body at BITS == 8 with the u8 extract helpers).
pub exec fn gf8_mul_helper(left0: u8, right: u8) -> (res: u8)
    ensures
        res == gf8_mul_spec(left0, right),
        res == gf8_mul_bits(left0, right, GF8_BITS as nat),
{
    let mut left: u8 = left0;
    let mut result_value: u8 = 0;
    let c0: u8 = extract_lowest_bit_u8(right);
    result_value = if c0 != 0 { left } else { 0u8 };
    proof {
        let sel0: u8 = if right & 1 == 1 { left0 } else { 0u8 };
        assert(result_value == sel0) by {
            assert((right & 1) == 1u8 <==> c0 == 1u8) by (bit_vector)
                requires
                    c0 == (right & 1),
            ;
        }
        lemma_mul8_bits_unfold(left0, right, GF8_BITS as nat);
        let entry_tail: u8 = gf8_mul_bits(gf8_xtime(left0), right >> (1 as u8), (GF8_BITS - 1) as nat);
        assert(gf8_mul_bits(left0, right, GF8_BITS as nat) == sel0 ^ entry_tail);
        assert(entry_tail ^ result_value == gf8_mul_bits(left0, right, GF8_BITS as nat)) by {
            bv_xor_comm8(entry_tail, sel0);
            bv_xor_ac8(sel0, entry_tail, result_value);
        }
    }
    let mut i: usize = 1;
    while i < GF8_BITS
        invariant
            1 <= i <= GF8_BITS,
            i < GF8_BITS ==>
                gf8_mul_bits(gf8_xtime(left), right >> (i as u8), (GF8_BITS - i) as nat)
                    ^ result_value == gf8_mul_spec(left0, right),
            i == GF8_BITS ==> result_value == gf8_mul_spec(left0, right),
        decreases GF8_BITS - i,
    {
        let lold: u8 = left;
        let rold: u8 = result_value;
        let r_i: u8 = right >> (i as u8);
        proof {
            if (i + 1) < GF8_BITS {
                let t = (right >> (i as u8)) >> 1u8;
                let t2 = right >> ((i + 1) as u8);
                assert(t == t2) by (bit_vector)
                    requires
                        (i + 1) < GF8_BITS,
                        t == (right >> (i as u8)) >> 1u8,
                        t2 == right >> ((i + 1) as u8),
                ;
            } else {
                // i == 7: r_i has at most 1 bit left
                let rv = (right >> (i as u8)) >> 1u8;
                assert(rv == 0u8) by (bit_vector)
                    requires
                        i == 7,
                        rv == (right >> (i as u8)) >> 1u8,
                ;
            }
        }
        let ch: u8 = extract_highest_bit_u8(lold);
        let mask: u8 = if ch != 0 { GF8_MODULUS } else { 0u8 };
        left = (lold << 1) ^ mask;
        let ci: u8 = extract_bit_u8(right, i);
        let add: u8 = if ci != 0 { left } else { 0u8 };
        result_value = rold ^ add;
        proof {
            let a1: u8 = gf8_xtime(lold);
            assert(ch == 1u8 <==> ((lold >> 7) & 1) == 1u8) by (bit_vector)
                requires
                    ch == (lold >> 7),
            ;
            assert(mask == (if ((lold >> 7) & 1) == 1u8 { GF8_MODULUS } else { 0u8 }));
            assert(left == a1) by {
                assert(gf8_xtime(lold)
                    == ((lold << 1) ^ (if ((lold >> 7) & 1) == 1u8 { GF8_MODULUS } else { 0u8 })));
            }
            assert(ci == 1u8 <==> (r_i & 1) == 1u8) by (bit_vector)
                requires
                    ci == ((right >> (i as u8)) & 1),
                    r_i == right >> (i as u8),
            ;
            assert(add == (if (r_i & 1) == 1u8 { left } else { 0u8 }));
            assert(((GF8_BITS - i) - 1) == GF8_BITS - (i + 1));
            let w: nat = (GF8_BITS - i) as nat;
            lemma_mul8_bits_unfold(a1, r_i, w);
            let contrib: u8 = if (r_i & 1) == 1u8 { left } else { 0u8 };
            let tailA: u8 = gf8_mul_bits(gf8_xtime(a1), (r_i) >> 1u8, (w - 1) as nat);
            let tailB: u8 = gf8_mul_bits(gf8_xtime(left), (r_i) >> 1u8, (w - 1) as nat);
            assert(tailA == tailB);
            assert(gf8_mul_bits(a1, r_i, w) == contrib ^ tailA);
            let jn: usize = (i + 1) as usize;
            if (i + 1) < GF8_BITS {
                assert((r_i) >> 1u8 == right >> (jn as u8));
                assert(rold ^ contrib == result_value);
                assert((contrib ^ tailB) ^ rold == gf8_mul_spec(left0, right));
                assert((contrib ^ tailB) ^ rold == tailB ^ (rold ^ contrib)) by {
                    bv_xor_ac8(contrib, tailB, rold);
                    bv_xor_comm8(contrib, rold);
                }
                assert(tailB ^ result_value == gf8_mul_spec(left0, right));
            } else {
                // i == 7: fuel w == 1, tail fuel 0 collapses
                assert(tailA == 0u8) by {
                    assert(gf8_mul_bits(gf8_xtime(a1), (r_i) >> 1u8, 0nat) == 0u8);
                }
                assert(gf8_mul_bits(a1, r_i, w) == contrib ^ 0u8);
                assert((contrib ^ 0u8) == contrib) by (bit_vector);
                assert(gf8_mul_bits(a1, r_i, w) == contrib);
                assert(rold ^ contrib == result_value);
                assert(result_value == gf8_mul_spec(left0, right)) by {
                    bv_xor_ac8(contrib, tailB, rold);
                    bv_xor_comm8(contrib, rold);
                    assert((contrib ^ tailB) ^ rold == tailB ^ (rold ^ contrib));
                    assert(tailB == 0u8);
                }
            }
        }
        i += 1;
    }
    result_value
}

// ===========================================================================
// Operator faces (upstream small_fields.rs:104-264). SmallGF<T> lowers to
// the plain machine integer; the std::ops impls become named exec fns with
// the upstream trait recorded at each face. The xor-family carries a few
// algebra lemmas (verified with bit_vector) since add/sub/neg ARE the
// field's ring operations in characteristic 2.
// ===========================================================================

/// Origin Rust (small_fields.rs:133-155):
///     impl<T> Add for SmallGF<T> where T: BitXor<Output = T> {
///         type Output = Self;
///         #[allow(clippy::suspicious_arithmetic_impl)]
///         fn add(self, rhs: Self) -> Self::Output { Self(self.0 ^ rhs.0) } }
/// GF(2^64) addition = bitwise xor (characteristic 2).
#[inline]
pub exec fn gf64_add(a: u64, b: u64) -> (res: u64)
    ensures
        res == (a ^ b),
{
    a ^ b
}

/// Upstream AddAssign (small_fields.rs:146-155): self.0 ^= rhs.0.
#[inline]
pub exec fn gf64_add_assign(a: &mut u64, b: u64)
    ensures
        *final(a) == (*old(a) ^ b),
{
    *a = *a ^ b;
}

/// Upstream Sub (small_fields.rs:157-168) == Add: Self(self.0 ^ rhs.0).
#[inline]
pub exec fn gf64_sub(a: u64, b: u64) -> (res: u64)
    ensures
        res == (a ^ b),
{
    a ^ b
}

/// Upstream SubAssign (small_fields.rs:170-179): self.0 ^= rhs.0.
#[inline]
pub exec fn gf64_sub_assign(a: &mut u64, b: u64)
    ensures
        *final(a) == (*old(a) ^ b),
{
    *a = *a ^ b;
}

/// Upstream Neg (small_fields.rs:181-188): fn neg(self) -> Self { self } --
/// additive inverse is the element itself in characteristic 2.
#[inline]
pub exec fn gf64_neg(a: u64) -> (res: u64)
    ensures
        res == a,
{
    a
}

/// Upstream BitAnd (small_fields.rs:123-131): Self(self.0 & rhs.0) --
/// byte-mask face used by callers (not a field operation).
#[inline]
pub exec fn gf64_bitand(a: u64, b: u64) -> (res: u64)
    ensures
        res == (a & b),
{
    a & b
}

/// GF(2^8) addition (upstream Add over SmallGF<u8>, same body).
#[inline]
pub exec fn gf8_add(a: u8, b: u8) -> (res: u8)
    ensures
        res == (a ^ b),
{
    a ^ b
}

#[inline]
pub exec fn gf8_add_assign(a: &mut u8, b: u8)
    ensures
        *final(a) == (*old(a) ^ b),
{
    *a = *a ^ b;
}

#[inline]
pub exec fn gf8_sub(a: u8, b: u8) -> (res: u8)
    ensures
        res == (a ^ b),
{
    a ^ b
}

#[inline]
pub exec fn gf8_sub_assign(a: &mut u8, b: u8)
    ensures
        *final(a) == (*old(a) ^ b),
{
    *a = *a ^ b;
}

/// Upstream Neg for GF8: identity.
#[inline]
pub exec fn gf8_neg(a: u8) -> (res: u8)
    ensures
        res == a,
{
    a
}

#[inline]
pub exec fn gf8_bitand(a: u8, b: u8) -> (res: u8)
    ensures
        res == (a & b),
{
    a & b
}

/// Ring identities of the xor faces (bit_vector-verified, both widths):
/// commutativity, associativity, self-cancel, zero identity. These are the
/// algebraic facts the harness KATs and later batches (FA6 ZK hashers)
/// consume.
pub proof fn lemma_gf64_add_comm(a: u64, b: u64)
    ensures
        // applies to gf64_add via its res == (a ^ b) ensures
        (a ^ b) == (b ^ a),
{
    assert((a ^ b) == (b ^ a)) by (bit_vector);
}



pub proof fn lemma_gf64_add_self_cancel(a: u64)
    ensures
        (a ^ a) == 0u64,
{
    assert((a ^ a) == 0u64) by (bit_vector);
}

pub proof fn lemma_gf64_add_zero(a: u64)
    ensures
        (a ^ 0u64) == a,
{
    assert((a ^ 0u64) == a) by (bit_vector);
}

pub proof fn lemma_gf8_add_comm(a: u8, b: u8)
    ensures
        (a ^ b) == (b ^ a),
{
    assert((a ^ b) == (b ^ a)) by (bit_vector);
}

pub proof fn lemma_gf8_add_self_cancel(a: u8)
    ensures
        (a ^ a) == 0u8,
{
    assert((a ^ a) == 0u8) by (bit_vector);
}

// ===========================================================================
// Mul / MulAssign / Square (upstream small_fields.rs:202-264): thin
// wrappers over mul_helper.
// ===========================================================================

/// Origin Rust (small_fields.rs:202-222, Mul impl):
///     fn mul(self, rhs: Self) -> Self::Output { Self::mul_helper(self, rhs) }
/// (SmallGF<u64> face.)
#[inline]
pub exec fn gf64_mul(a: u64, b: u64) -> (res: u64)
    ensures
        res == gf64_mul_spec(a, b),
{
    gf64_mul_helper(a, b)
}

/// Origin Rust (small_fields.rs:224-242, MulAssign):
///     fn mul_assign(&mut self, rhs: Self) { *self = Self::mul_helper(*self, rhs) }
#[inline]
pub exec fn gf64_mul_assign(a: &mut u64, b: u64)
    ensures
        *final(a) == gf64_mul_spec(*old(a), b),
{
    *a = gf64_mul_helper(*a, b);
}

/// Origin Rust (small_fields.rs:244-264, Square):
///     fn square(self) -> Self::Output { Self::mul_helper(self, self) }
#[inline]
pub exec fn gf64_square(a: u64) -> (res: u64)
    ensures
        res == gf64_mul_spec(a, a),
{
    gf64_mul_helper(a, a)
}

/// Origin Rust (small_fields.rs:202-222, Mul for SmallGF<u8>).
#[inline]
pub exec fn gf8_mul(a: u8, b: u8) -> (res: u8)
    ensures
        res == gf8_mul_spec(a, b),
{
    gf8_mul_helper(a, b)
}

#[inline]
pub exec fn gf8_mul_assign(a: &mut u8, b: u8)
    ensures
        *final(a) == gf8_mul_spec(*old(a), b),
{
    *a = gf8_mul_helper(*a, b);
}

/// Origin Rust (small_fields.rs:244-264, Square for SmallGF<u8>).
#[inline]
pub exec fn gf8_square(a: u8) -> (res: u8)
    ensures
        res == gf8_mul_spec(a, a),
{
    gf8_mul_helper(a, a)
}

// ===========================================================================
// GF8::square_bits (upstream small_fields.rs:269-281): a hardcoded bit
// expression claimed to compute the GF(2^8) square. Verified property
// here: equality with the standard spread-then-reduce reference square
/// (Morton-spread the 8 bits into even positions, then fold the high
// byte back with the constant carry-less product by 0x1B twice). The
/// model-square link (square_bits == gf8_mul_spec(x, x)) remains a
/// deferred obligation (D-FA2-2): it needs the ring lemmas of FA3.
// ===========================================================================

/// The reference square as a spec fn: spread bits of x to positions
/// 0,2,..,14, then reduce below 2^8 by folding the high byte's
/// carry-less product with the modulus constant.
pub open spec fn gf8_ref_square_spread(x: u16) -> u16 {
    // Morton spread of the 8 bits (probe-verified formula)
    let x4 = (x | (x << 4)) & 0x0F0F;
    let x2 = (x4 | (x4 << 2)) & 0x3333;
    let s = (x2 | (x2 << 1)) & 0x5555;
    // fold 1: h = s >> 8 contributes clmul(h, 0x1B) = h ^ (h<<1) ^ (h<<3) ^ (h<<4)
    let h1 = s >> 8;
    let f1h = h1 ^ (h1 << 1) ^ (h1 << 3) ^ (h1 << 4);
    let s1 = (s & 0x00FF) ^ f1h;
    // fold 2: only 0..7 can remain above the low byte
    let h2 = s1 >> 8;
    let f2h = h2 ^ (h2 << 1) ^ (h2 << 3) ^ (h2 << 4);
    (s1 & 0x00FF) ^ f2h
}

/// Origin Rust (small_fields.rs:269-281):
///     pub fn square_bits(x: u8) -> u8 {
///         let mut res = (x ^ (x >> 4) ^ (x >> 6)) & 0x1;
///         res |= ((x >> 3) ^ (x >> 5) ^ (x >> 6)) & 0x2;
///         res |= ((x << 1) ^ (x >> 3)) & 0x4;
///         res |= ((x >> 1) ^ (x >> 2) ^ (x >> 3) ^ (x >> 4)) & 0x8;
///         res |= ((x << 2) ^ x ^ (x >> 3)) & 0x10;
///         res |= (x ^ (x >> 1)) & 0x20;
///         res |= ((x << 3) ^ (x << 1)) & 0x40;
///         res |= ((x << 1) ^ x) & 0x80;
///         res }
/// (u8 left shifts keep the machine wrap-drop semantics.)
#[inline]
pub exec fn gf8_square_bits(x: u8) -> (res: u8)
    ensures
        (res as u16) == gf8_ref_square_spread(x as u16),
{
    let mut res: u8 = (x ^ (x >> 4) ^ (x >> 6)) & 0x1;
    res = res | (((x >> 3) ^ (x >> 5) ^ (x >> 6)) & 0x2);
    res = res | (((x << 1) ^ (x >> 3)) & 0x4);
    res = res | (((x >> 1) ^ (x >> 2) ^ (x >> 3) ^ (x >> 4)) & 0x8);
    res = res | (((x << 2) ^ x ^ (x >> 3)) & 0x10);
    res = res | ((x ^ (x >> 1)) & 0x20);
    res = res | (((x << 3) ^ (x << 1)) & 0x40);
    res = res | (((x << 1) ^ x) & 0x80);
    proof {
        // both sides are pure machine bit expressions: one blast closes it
        assert((res as u16) == gf8_ref_square_spread(x as u16)) by (bit_vector)
            requires
                (res as u16)
                    == ((((((((((x ^ (x >> 4) ^ (x >> 6)) & 0x1u8)
                        | (((x >> 3) ^ (x >> 5) ^ (x >> 6)) & 0x2u8))
                        | (((x << 1) ^ (x >> 3)) & 0x4u8))
                        | (((x >> 1) ^ (x >> 2) ^ (x >> 3) ^ (x >> 4)) & 0x8u8))
                        | (((x << 2) ^ x ^ (x >> 3)) & 0x10u8))
                        | ((x ^ (x >> 1)) & 0x20u8))
                        | (((x << 3) ^ (x << 1)) & 0x40u8))
                        | (((x << 1) ^ x) & 0x80u8)) as u16),
        ;
    }
    res
}

// ===========================================================================
// Field face for GF64 (upstream small_fields.rs:286-312).
// ===========================================================================

/// Origin Rust (small_fields.rs:286-303):
///     impl Field for GF64 {
///         const ZERO: Self = Self(0);
///         const ONE: Self = Self(1);
///         type Length = U8;
///         fn as_bytes(&self) -> Array<u8, Self::Length> {
///             Array(self.0.to_le_bytes()) } }
/// hybrid-array Array<u8, U8> lowers to [u8; 8] (FA1 representation
/// convention); to_le_bytes lowers to the per-byte shift/mask face
/// (integer-encoding line precedent: vstd has no byte-order spec), one
/// concrete step per byte with a bit_vector fold each.
pub const GF64_ONE: u64 = 1;

/// Field::ZERO for GF64 (upstream small_fields.rs:287), value face.
pub const GF64_FIELD_ZERO: u64 = GF64_ZERO;

/// Field::as_bytes for GF64 (upstream small_fields.rs:292-294): the
/// little-endian byte representation, [u8; 8] lowered face.
pub exec fn gf64_as_bytes(v: u64) -> (out: [u8; 8])
    ensures
        forall |j: int| 0 <= j < 8
            ==> out[j] == (byte64(v, j)),
{
    #[verifier::truncate] let b0: u8 = ((v >> 0u64) & 0xFF) as u8;
    #[verifier::truncate] let b1: u8 = ((v >> 8u64) & 0xFF) as u8;
    #[verifier::truncate] let b2: u8 = ((v >> 16u64) & 0xFF) as u8;
    #[verifier::truncate] let b3: u8 = ((v >> 24u64) & 0xFF) as u8;
    #[verifier::truncate] let b4: u8 = ((v >> 32u64) & 0xFF) as u8;
    #[verifier::truncate] let b5: u8 = ((v >> 40u64) & 0xFF) as u8;
    #[verifier::truncate] let b6: u8 = ((v >> 48u64) & 0xFF) as u8;
    #[verifier::truncate] let b7: u8 = ((v >> 56u64) & 0xFF) as u8;
    proof {
        // each masked byte stays inside the u8 range (plain machine
        // blasts, no casts and no spec-fn payload)
        assert(((v >> 0u64) & 0xFF) <= 0xFFu64) by (bit_vector);
        assert(((v >> 8u64) & 0xFF) <= 0xFFu64) by (bit_vector);
        assert(((v >> 16u64) & 0xFF) <= 0xFFu64) by (bit_vector);
        assert(((v >> 24u64) & 0xFF) <= 0xFFu64) by (bit_vector);
        assert(((v >> 32u64) & 0xFF) <= 0xFFu64) by (bit_vector);
        assert(((v >> 40u64) & 0xFF) <= 0xFFu64) by (bit_vector);
        assert(((v >> 48u64) & 0xFF) <= 0xFFu64) by (bit_vector);
        assert(((v >> 56u64) & 0xFF) <= 0xFFu64) by (bit_vector);
        // truncated casts are value-exact; plain-stage chains
        assert((b0 as u64) == ((v >> 0u64) & 0xFF));
        assert((b1 as u64) == ((v >> 8u64) & 0xFF));
        assert((b2 as u64) == ((v >> 16u64) & 0xFF));
        assert((b3 as u64) == ((v >> 24u64) & 0xFF));
        assert((b4 as u64) == ((v >> 32u64) & 0xFF));
        assert((b5 as u64) == ((v >> 40u64) & 0xFF));
        assert((b6 as u64) == ((v >> 48u64) & 0xFF));
        assert((b7 as u64) == ((v >> 56u64) & 0xFF));
        // plain-stage byte64 unfolds at the concrete byte indexes
        assert(byte64(v, 0) == ((v >> 0u64) & 0xFF));
        assert(byte64(v, 1) == ((v >> 8u64) & 0xFF));
        assert(byte64(v, 2) == ((v >> 16u64) & 0xFF));
        assert(byte64(v, 3) == ((v >> 24u64) & 0xFF));
        assert(byte64(v, 4) == ((v >> 32u64) & 0xFF));
        assert(byte64(v, 5) == ((v >> 40u64) & 0xFF));
        assert(byte64(v, 6) == ((v >> 48u64) & 0xFF));
        assert(byte64(v, 7) == ((v >> 56u64) & 0xFF));
    }
    [b0 as u8, b1 as u8, b2 as u8, b3 as u8, b4 as u8, b5 as u8, b6 as u8, b7 as u8]
}

/// The little-endian byte j of a u64 value, machine view (spec helper for
/// the as_bytes/from_bytes faces).
pub open spec fn byte64(v: u64, j: int) -> u64 {
    (v >> ((8 * j) as u64)) & 0xFF
}

/// Origin Rust (small_fields.rs:305-312):
///     impl From<&[u8]> for GF64 {
///         fn from(value: &[u8]) -> Self {
///             debug_assert_eq!(value.len(), 8);
///             let mut array = [0u8; 8];
///             array.copy_from_slice(&value[..8]);
///             Self::from(u64::from_le_bytes(array)) } }
/// The debug_assert (absent in release builds) re-erects as the twin's
/// requires; from_le_bytes lowers to the OR-of-shifted-bytes face.
pub exec fn gf64_from_bytes(value: &[u8]) -> (res: u64)
    requires
        value.len() == 8,
    ensures
        forall |j: int| 0 <= j < 8 ==> #[trigger] byte64(res, j) == (value[j] as u64),
{
    let b0: u64 = value[0] as u64;
    let b1: u64 = value[1] as u64;
    let b2: u64 = value[2] as u64;
    let b3: u64 = value[3] as u64;
    let b4: u64 = value[4] as u64;
    let b5: u64 = value[5] as u64;
    let b6: u64 = value[6] as u64;
    let b7: u64 = value[7] as u64;
    let acc: u64 = (b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64))
        | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64));
    proof {
        // byte folds over the free byte symbols (bindings kept out of the
        // blasts: slices must not enter blast contexts, #FA1-6 family)
        assert(((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) >> 0u64) & 0xFF) == b0) by (bit_vector)
                    requires
                    b0 <= 0xFFu64,
                    b1 <= 0xFFu64,
                    b2 <= 0xFFu64,
                    b3 <= 0xFFu64,
                    b4 <= 0xFFu64,
                    b5 <= 0xFFu64,
                    b6 <= 0xFFu64,
                    b7 <= 0xFFu64,
                ;
        assert(((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) >> 8u64) & 0xFF) == b1) by (bit_vector)
                    requires
                    b0 <= 0xFFu64,
                    b1 <= 0xFFu64,
                    b2 <= 0xFFu64,
                    b3 <= 0xFFu64,
                    b4 <= 0xFFu64,
                    b5 <= 0xFFu64,
                    b6 <= 0xFFu64,
                    b7 <= 0xFFu64,
                ;
        assert(((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) >> 16u64) & 0xFF) == b2) by (bit_vector)
                    requires
                    b0 <= 0xFFu64,
                    b1 <= 0xFFu64,
                    b2 <= 0xFFu64,
                    b3 <= 0xFFu64,
                    b4 <= 0xFFu64,
                    b5 <= 0xFFu64,
                    b6 <= 0xFFu64,
                    b7 <= 0xFFu64,
                ;
        assert(((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) >> 24u64) & 0xFF) == b3) by (bit_vector)
                    requires
                    b0 <= 0xFFu64,
                    b1 <= 0xFFu64,
                    b2 <= 0xFFu64,
                    b3 <= 0xFFu64,
                    b4 <= 0xFFu64,
                    b5 <= 0xFFu64,
                    b6 <= 0xFFu64,
                    b7 <= 0xFFu64,
                ;
        assert(((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) >> 32u64) & 0xFF) == b4) by (bit_vector)
                    requires
                    b0 <= 0xFFu64,
                    b1 <= 0xFFu64,
                    b2 <= 0xFFu64,
                    b3 <= 0xFFu64,
                    b4 <= 0xFFu64,
                    b5 <= 0xFFu64,
                    b6 <= 0xFFu64,
                    b7 <= 0xFFu64,
                ;
        assert(((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) >> 40u64) & 0xFF) == b5) by (bit_vector)
                    requires
                    b0 <= 0xFFu64,
                    b1 <= 0xFFu64,
                    b2 <= 0xFFu64,
                    b3 <= 0xFFu64,
                    b4 <= 0xFFu64,
                    b5 <= 0xFFu64,
                    b6 <= 0xFFu64,
                    b7 <= 0xFFu64,
                ;
        assert(((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) >> 48u64) & 0xFF) == b6) by (bit_vector)
                    requires
                    b0 <= 0xFFu64,
                    b1 <= 0xFFu64,
                    b2 <= 0xFFu64,
                    b3 <= 0xFFu64,
                    b4 <= 0xFFu64,
                    b5 <= 0xFFu64,
                    b6 <= 0xFFu64,
                    b7 <= 0xFFu64,
                ;
        assert(((((b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64))) >> 56u64) & 0xFF) == b7) by (bit_vector)
                    requires
                    b0 <= 0xFFu64,
                    b1 <= 0xFFu64,
                    b2 <= 0xFFu64,
                    b3 <= 0xFFu64,
                    b4 <= 0xFFu64,
                    b5 <= 0xFFu64,
                    b6 <= 0xFFu64,
                    b7 <= 0xFFu64,
                ;
        // acc is exactly the OR combination of the bytes (plain-stage)
        let ored = (b0 | (b1 << 8u64) | (b2 << 16u64) | (b3 << 24u64)) | ((b4 << 32u64) | (b5 << 40u64) | (b6 << 48u64) | (b7 << 56u64));
        // acc is exactly the OR combination of the bytes
        assert(acc == ored);
        assert(byte64(acc, 0) == ((acc >> 0u64) & 0xFF));
        assert(byte64(acc, 1) == ((acc >> 8u64) & 0xFF));
        assert(byte64(acc, 2) == ((acc >> 16u64) & 0xFF));
        assert(byte64(acc, 3) == ((acc >> 24u64) & 0xFF));
        assert(byte64(acc, 4) == ((acc >> 32u64) & 0xFF));
        assert(byte64(acc, 5) == ((acc >> 40u64) & 0xFF));
        assert(byte64(acc, 6) == ((acc >> 48u64) & 0xFF));
        assert(byte64(acc, 7) == ((acc >> 56u64) & 0xFF));
    }
    acc
}

/// Byte-value equality of two u64s with all eight byte slots given as
/// machine values (pure-machine blast; no spec-fn payload).
pub proof fn lemma_u64_bytes_eq(a: u64, b: u64, e0: u64, e1: u64, e2: u64, e3: u64, e4: u64, e5: u64, e6: u64, e7: u64)
    requires
e0 <= 0xFF,
        e1 <= 0xFF,
        e2 <= 0xFF,
        e3 <= 0xFF,
        e4 <= 0xFF,
        e5 <= 0xFF,
        e6 <= 0xFF,
        e7 <= 0xFF,
        ((a >> 0u64) & 0xFF) == e0,
        ((a >> 8u64) & 0xFF) == e1,
        ((a >> 16u64) & 0xFF) == e2,
        ((a >> 24u64) & 0xFF) == e3,
        ((a >> 32u64) & 0xFF) == e4,
        ((a >> 40u64) & 0xFF) == e5,
        ((a >> 48u64) & 0xFF) == e6,
        ((a >> 56u64) & 0xFF) == e7,
        ((b >> 0u64) & 0xFF) == e0,
        ((b >> 8u64) & 0xFF) == e1,
        ((b >> 16u64) & 0xFF) == e2,
        ((b >> 24u64) & 0xFF) == e3,
        ((b >> 32u64) & 0xFF) == e4,
        ((b >> 40u64) & 0xFF) == e5,
        ((b >> 48u64) & 0xFF) == e6,
        ((b >> 56u64) & 0xFF) == e7,
    ensures
        a == b,
{
    assert(a == (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64) | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64))) by (bit_vector)
        requires
e0 <= 0xFF,
        e1 <= 0xFF,
        e2 <= 0xFF,
        e3 <= 0xFF,
        e4 <= 0xFF,
        e5 <= 0xFF,
        e6 <= 0xFF,
        e7 <= 0xFF,
        ((a >> 0u64) & 0xFF) == e0,
        ((a >> 8u64) & 0xFF) == e1,
        ((a >> 16u64) & 0xFF) == e2,
        ((a >> 24u64) & 0xFF) == e3,
        ((a >> 32u64) & 0xFF) == e4,
        ((a >> 40u64) & 0xFF) == e5,
        ((a >> 48u64) & 0xFF) == e6,
        ((a >> 56u64) & 0xFF) == e7,
    ;
    assert(b == (e0 | (e1 << 8u64) | (e2 << 16u64) | (e3 << 24u64) | (e4 << 32u64) | (e5 << 40u64) | (e6 << 48u64) | (e7 << 56u64))) by (bit_vector)
        requires
        e0 <= 0xFF,
        e1 <= 0xFF,
        e2 <= 0xFF,
        e3 <= 0xFF,
        e4 <= 0xFF,
        e5 <= 0xFF,
        e6 <= 0xFF,
        e7 <= 0xFF,
        ((b >> 0u64) & 0xFF) == e0,
        ((b >> 8u64) & 0xFF) == e1,
        ((b >> 16u64) & 0xFF) == e2,
        ((b >> 24u64) & 0xFF) == e3,
        ((b >> 32u64) & 0xFF) == e4,
        ((b >> 40u64) & 0xFF) == e5,
        ((b >> 48u64) & 0xFF) == e6,
        ((b >> 56u64) & 0xFF) == e7,
    ;
}

// No inversion exists in this file (Origin note): the upstream Field doc
// (fields/mod.rs:43-44) states "As such, no function to invert elements is
// provided", and small_fields.rs defines no inverse. The batch's inverse
// (inverse) item is therefore record-only: nothing to transcribe.

} // verus!
