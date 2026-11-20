//! faest 0.3.0 -- Verus transcription of src/utils.rs, batch FA1.
//!
//! Upstream: utils.rs (198 lines) of the pinned tree, plus the consumed
//! slice of parameter.rs (tau constants; see parameter.rs in this tree).
//! FA1 anchors (fixed by harness-inventory section 8):
//!   1. extract_k_bits_first_byte (utils.rs:25)
//!   2. chall_to_u16 (utils.rs:42)
//!   3. decode_all_chall_3 (utils.rs:79)
//! plus extract_k_bits_next_bytes (:36), the Reader trait face (:8-22),
//! the xor family (:93-112), get_bit (:114-122) and array_ref (:124-137).
//! The std/serde/shake test helpers (:139-198) are feature-gated upstream
//! (std + serde + shake) and stay out of this verified build profile.
//!
//! Machine bit-op note (probe-confirmed, this batch): u8/u16 shifts and
//! masks carry no reasoning in this build's default integer encoding
//! (probe1: even concrete `(1u16 << 3) == 8u16` fails plain). The value
//! faces ride the vstd bits.rs lemma bank (lemma_u16_shr_is_div,
//! lemma_u16_low_bits_mask_is_mod, lemma_u16_shl_is_mul, u8 twins) plus
//! `by (bit_vector)` blasts for the or-composition; the shift-amount
//! subexpressions are narrowed `as u16`/`as u8` in the twin's machine
//! bodies so the vstd lemma triggers match the lowered terms -- this is
//! value-identical to the upstream usize/untyped forms (Rust shift
//! semantics only look at the amount's value).

use vstd::prelude::*;
use vstd::seq::Seq;

use vstd::arithmetic::div_mod::{
    lemma_div_denominator, lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
};
use vstd::arithmetic::mul::{
    lemma_mul_is_associative, lemma_mul_is_commutative, lemma_mul_is_distributive_add,
    lemma_mul_inequality, lemma_mul_upper_bound,
};
use vstd::arithmetic::power2::{
    pow2, lemma2_to64, lemma_pow2_adds, lemma_pow2_pos, lemma_pow2_strictly_increases,
    lemma_pow2_subtracts, lemma_pow2_unfold,
};
// Machine bit-lemma bank (shift==div, shl==mul, mask==mod, per width).
use vstd::bits::low_bits_mask;
use vstd::bits::{
    lemma_low_bits_mask_values, lemma_u16_low_bits_mask_is_mod, lemma_u16_pow2_no_overflow,
    lemma_u16_shl_is_mul, lemma_u16_shr_is_div, lemma_u8_low_bits_mask_is_mod, lemma_u8_shr_is_div,
};

use super::parameter::{
    tau0_offset_spec, tau0_offset_unchecked, tau1_offset_spec, tau1_offset_unchecked, TAU128F_K,
    TAU128F_TAU0, TAU128F_TAU1,
};

verus! {


/// Int view of 2^e: pow2 returns nat, int-valued specs and proofs
/// divide through this wrapper (nat div/mod inference would otherwise
/// capture the surrounding expression types).
pub open spec fn pw(e: nat) -> int {
    (pow2(e) as int)
}


// ===========================================================================
// Reader interface (upstream utils.rs:8-22).
// Origin Rust:
//     /// Reader interface for PRGs and random oracles
//     pub(crate) trait Reader {
//         /// Read bytes from PRG/random oracle
//         fn read(&mut self, dst: &mut [u8]);
//         /// Read into array and consume the reader
//         fn read_into<Length: ArraySize>(mut self) -> Array<u8, Length>
//         where Self: Sized,
//         {
//             let mut dst = Array::default();
//             self.read(&mut dst);
//             dst
//         }
//     }
// The fill semantics of `read` are owned by the trusted PRG/oracle faces
// of the FA4/FA5 batches; this batch transcribes the interface only
// (Array<u8, Length> lowers to [u8; N] per the hybrid-array trusted
// representation decision).
// ===========================================================================

/// Reader interface for PRGs and random oracles (upstream utils.rs:8).
pub trait Reader {
    /// Read bytes from PRG/random oracle (upstream utils.rs:10).
    fn read(&mut self, dst: &mut [u8]);

    /// Read into array and consume the reader (upstream utils.rs:13).
    fn read_into<const N: usize>(mut self) -> [u8; N]
    where
        Self: Sized,
    {
        let mut dst: [u8; N] = [0u8; N];
        self.read(&mut dst);
        dst
    }
}

// ===========================================================================
// Value model (spec): LE bit numbering, matching get_bit (utils.rs:118)
// and the chall_to_u16 doc "chal[start_bit...start_bit+k]".
// The model is pure Euclidean arithmetic (value-level, per the
// bit-vec byte-bridge precedent: machine ops stay in the exec body,
// the spec model carries no machine bit ops), so it composes by int
// arithmetic without bit_vector help; the bridges to the machine
// bodies are the lemmas below.
// ===========================================================================

/// The bit of the byte sequence `ch` at (little-endian) position `b`,
/// as a 0/1 int; out-of-range positions read 0.
pub open spec fn bit_at(ch: Seq<u8>, b: int) -> int {
    if 0 <= b < 8 * ch.len() {
        (ch[b / 8] as int / pw((b % 8) as nat)) % 2
    } else {
        0
    }
}

/// The bit of the byte value `v` at position `p`, as a 0/1 int.
pub open spec fn span_bit(v: int, p: int) -> int {
    if 0 <= p {
        (v / pw(p as nat)) % 2
    } else {
        0
    }
}

/// The integer value of the `k` bits of `ch` counting from bit `s`
/// (low bit first), mirroring the chall_to_u16 doc line "Directly
/// convert `chal[start_bit...start_bit+k]` into a 16-bit integer"
/// (upstream utils.rs:41).
pub open spec fn chall_bits_value(ch: Seq<u8>, s: int, k: int) -> int
    decreases
        k,
{
    if k <= 0 {
        0
    } else {
        chall_bits_value(ch, s, k - 1) + bit_at(ch, s + k - 1) * pw((k - 1) as nat)
    }
}

/// The integer value of the `k` bits of a single byte value `v`
/// counting from bit `off` (low bit first).
pub open spec fn span_value(v: int, off: int, k: int) -> int
    decreases
        k,
{
    if k <= 0 {
        0
    } else {
        span_value(v, off, k - 1) + span_bit(v, off + k - 1) * pw((k - 1) as nat)
    }
}

// ===========================================================================
// Bridge lemmas: machine bit faces <-> value model.
// ===========================================================================

/// w % 2^m == (w % 2^(m-1)) + ((w / 2^(m-1)) % 2) * 2^(m-1): the
/// mod-split step the span induction peels with (probe-confirmed
/// int-side; vstd pow/div/mul lemma set).
proof fn lemma_mod_split_pow2(w: int, m: nat)
    requires
        1 <= m,
    ensures
        (w % pw(m)) == (w % pw((m - 1) as nat))
            + ((w / pw((m - 1) as nat)) % 2) * pw((m - 1) as nat),
{
    let p: int = pw((m - 1) as nat);
    lemma_pow2_pos((m - 1) as nat);
    lemma_pow2_adds((m - 1) as nat, 1nat);
    lemma2_to64();
    assert(pw(1nat) == 2);
    assert(((m - 1) + 1) as nat == m);
    assert(pw(m) == 2 * p);
    assert(w / p == 2 * ((w / p) / 2) + (w / p) % 2) by {
        lemma_fundamental_div_mod(w / p, 2);
    }
    assert(0 <= (w / p) % 2 < 2);
    assert(0 <= w % p < p);
    // w == (w/p/2)*(2p) + (w/p)%2 * p + w%p, remainder side in [0, 2p)
    lemma_fundamental_div_mod(w, p);
    lemma_fundamental_div_mod(w / p, 2);
    lemma_mul_is_distributive_add(p, 2 * ((w / p) / 2), (w / p) % 2);
    lemma_mul_is_associative(p, 2, (w / p) / 2);
    lemma_mul_is_commutative(2 * ((w / p) / 2), p);
    assert(w == p * (w / p) + (w % p));
    assert(w == (w / p / 2) * (2 * p) + ((w / p) % 2) * p + (w % p));
    assert(0 <= ((w / p) % 2) * p + (w % p) < 2 * p);
    assert(w % (2 * p) == ((w / p) % 2) * p + (w % p)) by {
        lemma_fundamental_div_mod_converse(w, 2 * p, w / p / 2, ((w / p) % 2) * p + (w % p));
    }
}

/// The closed form of the model: within one byte, the value of the k
/// bits from bit off equals (v / 2^off) % 2^k, and it sits below 2^k.
pub proof fn lemma_span_value(v: int, off: int, k: int)
    requires
        0 <= v < 256,
        0 <= off,
        1 <= k,
        off + k <= 8,
    ensures
        ((v / pw(off as nat)) % pw(k as nat)) == span_value(v, off, k),
        0 <= span_value(v, off, k) < pw(k as nat),
    decreases
        k,
{
    let w = v / pw(off as nat);
    lemma_pow2_pos(off as nat);
    if k == 1 {
        lemma2_to64();
        assert(pw(0nat) == 1);
        assert(pw(1nat) == 2);
        assert(span_value(v, off, 1) == span_value(v, off, 0) + span_bit(v, off) * pw(0nat));
        assert(span_value(v, off, 0) == 0);
        assert(span_bit(v, off) == (v / pw(off as nat)) % 2);
        assert(span_bit(v, off) == w % 2);
        assert(0 <= w % 2 < 2);
    } else {
        lemma_span_value(v, off, k - 1);
        lemma_mod_split_pow2(w, k as nat);
        // (v / 2^off) / 2^(k-1) == v / 2^(off + k - 1)
        assert((v / pw(off as nat)) / pw((k - 1) as nat) == v / pw((off + k - 1) as nat)) by {
            lemma_div_denominator(v, pw(off as nat), pw((k - 1) as nat));
            lemma_pow2_adds(off as nat, (k - 1) as nat);
        }
        // restate the span_value peel explicitly for z3
        assert(span_value(v, off, k)
            == span_value(v, off, k - 1) + span_bit(v, off + k - 1) * pw((k - 1) as nat));
        assert(span_bit(v, off + k - 1) == ((v / pw((off + k - 1) as nat)) % 2));
        assert(((v / pw((off + k - 1) as nat)) % 2) == ((w / pw((k - 1) as nat)) % 2));
        lemma_pow2_pos(k as nat);
        assert(0 <= w % pw(k as nat));
        assert((w % pw(k as nat)) < pw(k as nat));
    }
}

/// Within one byte, the sequence-level model over ch reduces to the
/// single-byte span model (ch[s/8] read from bit s%8).
pub proof fn lemma_bits_in_byte(ch: Seq<u8>, s: int, off: int, k: int)
    requires
        0 <= s,
        off == s % 8,
        0 <= k,
        off + k <= 8,
        s + k <= 8 * ch.len(),
    ensures
        chall_bits_value(ch, s, k) == span_value((ch[s / 8] as int), off, k),
    decreases
        k,
{
    if k <= 0 {
        assert(chall_bits_value(ch, s, 0) == 0);
        assert(span_value((ch[s / 8] as int), off, 0) == 0);
    } else {
        lemma_bits_in_byte(ch, s, off, k - 1);
        let b = s + k - 1;
        let bi = s / 8;
        // s == 8*bi + off, b == 8*bi + (off + k - 1), remainder in range
        assert(s == 8 * bi + off) by {
            lemma_fundamental_div_mod(s, 8);
        }
        assert(b == 8 * bi + (off + k - 1));
        assert(0 <= off + k - 1 < 8);
        assert(b / 8 == bi) by {
            lemma_fundamental_div_mod_converse(b, 8, bi, off + k - 1);
        }
        assert(b % 8 == off + k - 1) by {
            lemma_fundamental_div_mod_converse(b, 8, bi, off + k - 1);
        }
        assert(0 <= b < 8 * ch.len());
        assert(bit_at(ch, b) == (ch[b / 8] as int / pw((b % 8) as nat)) % 2);
        assert(span_bit((ch[bi] as int), off + k - 1) == (ch[b / 8] as int / pw((b % 8) as nat)) % 2);
    }
}

/// Span split: the value of [s, s+k) decomposes at s+m.
#[verifier::rlimit(6000)]
pub proof fn lemma_chall_bits_split(ch: Seq<u8>, s: int, k: int, m: int)
    requires
        0 <= s,
        0 <= m <= k,
    ensures
        chall_bits_value(ch, s, k)
            == chall_bits_value(ch, s, m)
                + chall_bits_value(ch, s + m, k - m) * pw(m as nat),
    decreases
        k - m,
{
    if k == m {
        assert(chall_bits_value(ch, s + m, 0) == 0) by {
            assert((k - m) == 0);
        }
    } else {
        assert(0 <= k - 1) by {
            assert(m <= k - 1);
        }
        lemma_chall_bits_split(ch, s, k - 1, m);
        assert(chall_bits_value(ch, s + m, k - m) == chall_bits_value(ch, s + m, k - m - 1) + bit_at(ch, s + k - 1) * pw((k - m - 1) as nat)) by {
            assert(s + m + (k - m - 1) == s + k - 1);
        }
        // distribute pw(m) over the high-part peel
        lemma_mul_is_distributive_add(pw(m as nat), chall_bits_value(ch, s + m, k - m - 1), bit_at(ch, s + k - 1) * pw((k - m - 1) as nat));
        lemma_pow2_adds((k - 1 - m) as nat, m as nat);
        assert(pw((k - m - 1) as nat) * pw(m as nat) == pw((k - 1) as nat)) by {
            lemma_pow2_adds((k - 1 - m) as nat, m as nat);
        }
        // associate the bit * pow product
        lemma_mul_is_associative(bit_at(ch, s + k - 1), pw((k - m - 1) as nat), pw(m as nat));
        // the outer peel on [s, s+k)
        assert(chall_bits_value(ch, s, k) == chall_bits_value(ch, s, k - 1) + bit_at(ch, s + k - 1) * pw((k - 1) as nat));
        // pin the composite with named pieces (context-stable restatement)
        let lo = chall_bits_value(ch, s, m);
        let hid = chall_bits_value(ch, s + m, k - m - 1);
        let b = bit_at(ch, s + k - 1);
        assert(chall_bits_value(ch, s + m, k - m) == hid + b * pw((k - m - 1) as nat));
        assert(chall_bits_value(ch, s + m, k - m) * pw(m as nat)
            == hid * pw(m as nat) + b * pw((k - 1) as nat)) by {
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                hid,
                b * pw((k - m - 1) as nat),
                pw(m as nat),
            );
            lemma_mul_is_associative(b, pw((k - m - 1) as nat), pw(m as nat));
            lemma_mul_is_commutative(pw((k - m - 1) as nat), pw(m as nat));
            assert(b * pw((k - m - 1) as nat) * pw(m as nat) == b * pw((k - 1) as nat)) by {
                lemma_mul_is_associative(b, pw((k - m - 1) as nat), pw(m as nat));
                lemma_pow2_adds((k - m - 1) as nat, m as nat);
                lemma_mul_is_commutative(pw((k - m - 1) as nat), pw(m as nat));
            }
        }
        assert(lo + chall_bits_value(ch, s + m, k - m) * pw(m as nat)
            == lo + hid * pw(m as nat) + b * pw((k - 1) as nat));
    }
}

/// (1u16 << k) machine faces: the shifted one is pow2(k), hence the
/// upstream mask form (1 << k) - 1 is low_bits_mask(k) (probe-confirmed
/// chain: pow2-no-overflow, shl==mul, pow2 pos).
proof fn lemma_mask_u16(k: usize)
    requires
        k < 16,
    ensures
        (1u16 << (k as u16)) as int == pw(k as nat),
        (((1u16 << (k as u16)) - 1u16)) as int == (low_bits_mask(k as nat) as int),
        0 < (1u16 << (k as u16)),
{
    lemma_u16_pow2_no_overflow(k as nat);
    lemma_u16_shl_is_mul(1u16, k as u16);
    lemma_pow2_pos(k as nat);
}

/// 0xFFFFu16 >> s == 2^(16-s) - 1: the machine form of the
/// shift-no-wrap bound.
proof fn lemma_max_shift_mask(s: usize)
    requires
        s < 16,
    ensures
        ((0xFFFFu16 >> (s as u16)) as int) == pw((16 - s) as nat) - 1,
{
    lemma_u16_shr_is_div(0xFFFFu16, s as u16);
    lemma_pow2_pos(s as nat);
    lemma_pow2_subtracts(s as nat, 16nat);
    let p: int = pw(s as nat);
    let q: int = pw((16 - s) as nat);
    assert(q * p == pw(16nat)) by {
        lemma_pow2_adds((16 - s) as nat, s as nat);
    }
    assert(pw(16nat) == 65536) by {
        lemma2_to64();
    }
    let m = 0xFFFFu16 as int;
    assert(m == q * p - 1);
    assert((q - 1) * p + (p - 1) == q * p - 1) by {
        vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(p, q, 1);
    }
    assert(m == (q - 1) * p + (p - 1));
    assert(0 <= p - 1 < p);
    assert(m / p == q - 1) by {
        lemma_fundamental_div_mod_converse(m, p, q - 1, p - 1);
    }
}

/// Or-composition, machine parts (two bit_vector blasts; probe2 Q3):
/// for res = a | (b << s) with a inside the low s bits and b not
/// wrapping, the s-shift recovers b and the shifted-one-minus mask
/// recovers a.
proof fn lemma_or_shift_parts(a: u16, b: u16, s: usize)
    requires
        s < 16,
        a < (1u16 << (s as u16)),
        b <= 0xFFFFu16 >> (s as u16),
    ensures
        ((a | (b << (s as u16))) >> (s as u16)) == b,
        (a | (b << (s as u16))) & (((1u16 << (s as u16)) - 1) as u16) == a,
{
    let res = a | (b << (s as u16));
    assert(res >> (s as u16) == b) by (bit_vector)
        requires
            s < 16,
            res == a | (b << (s as u16)),
            a < (1u16 << (s as u16)),
            b <= 0xFFFFu16 >> (s as u16),
    ;
    let m = (((1u16 << (s as u16)) - 1)) as u16;
    assert(res & m == a) by (bit_vector)
        requires
            s < 16,
            res == a | (b << (s as u16)),
            a < (1u16 << (s as u16)),
            b <= 0xFFFFu16 >> (s as u16),
            m == (((1u16 << (s as u16)) - 1)) as u16,
    ;
}

/// Or-composition, value face: a | (b << s) == a + b * 2^s when
/// a < 2^s and b * 2^s < 2^16 (the two-/three-byte chall_to_u16 paths).
proof fn lemma_or_shift_value(a: u16, b: u16, s: usize)
    requires
        s < 16,
        (a as int) < pw(s as nat),
        (b as int) * pw(s as nat) < 65536,
    ensures
        ((a | (b << (s as u16))) as int) == (a as int) + (b as int) * pw(s as nat),
{
    lemma_mask_u16(s);
    lemma_max_shift_mask(s);
    lemma_pow2_pos(s as nat);
    assert(a < (1u16 << (s as u16)));
    // b <= 0xFFFF >> s: otherwise b >= 2^(16-s) and b * 2^s >= 2^16,
    // contradicting the no-wrap bound
    assert(b as int <= ((0xFFFFu16 >> (s as u16)) as int)) by {
        let p: int = pw(s as nat);
        let q: int = pw((16 - s) as nat);
        lemma_pow2_adds((16 - s) as nat, s as nat);
        assert(q * p == 65536) by {
            lemma2_to64();
        }
        if b as int >= q {
            lemma_mul_inequality(q, b as int, p);
            assert(q * p <= (b as int) * p);
            assert(65536 <= (b as int) * p);
            assert(false);
        }
    }
    lemma_or_shift_parts(a, b, s);
    let res = a | (b << (s as u16));
    lemma_u16_shr_is_div(res, s as u16);
    let p: int = pw(s as nat);
    let m = (((1u16 << (s as u16)) - 1)) as u16;
    assert(res & m == a);
    assert(m == (low_bits_mask(s as nat)) as u16) by {
        lemma_mask_u16(s);
    }
    lemma_u16_low_bits_mask_is_mod(res, s as nat);
    let mmod: int = (res % (pw(s as nat) as u16)) as int;
    assert(mmod == (res as int) % p);
    let mres: int = res as int;
    // res / 2^s == b, res % 2^s == a, so res == a + b * 2^s
    assert((res >> (s as u16)) as int == mres / p);
    assert(mres / p == b as int);
    assert((res & (low_bits_mask(s as nat) as u16)) as int == mmod);
    assert(mres % p == a as int);
    assert(mres == p * (mres / p) + mres % p) by {
        lemma_fundamental_div_mod(mres, p);
        lemma_mul_is_commutative(p, mres / p);
    }
    assert(mres == (a as int) + (b as int) * p) by {
        lemma_mul_is_commutative(p, b as int);
    }
}

// ===========================================================================
// Anchors 1-2: bit-extraction helpers and chall_to_u16
// (upstream utils.rs:24-77).
// ===========================================================================

/// Origin Rust (utils.rs:24-33):
///     #[inline]
///     const fn extract_k_bits_first_byte(
///         chall: &[u8], first_byte: usize, bit_off: usize, k: usize,
///     ) -> u16 {
///         let mask = (1 << k) - 1;
///         (chall[first_byte] as u16 >> bit_off) & mask
///     }
/// The `const fn` qualifier is outside this tree's exec model (noted,
/// dropped); the absence of upstream bounds re-erects as requires --
/// indexes in range and the single-byte span this helper reads.
/// Value face: the low k bits of byte chall[first_byte] above bit_off.
#[inline]
pub exec fn extract_k_bits_first_byte(
    chall: &[u8],
    first_byte: usize,
    bit_off: usize,
    k: usize,
) -> (res: u16)
    requires
        first_byte < chall.len(),
        1 <= k,
        bit_off + k <= 8,
    ensures
        res as int == span_value((chall@[(first_byte as int)] as int), bit_off as int, k as int),
        0 <= res as int,
        (res as int) < pw(k as nat),
{
    proof {
        lemma_mask_u16(k);
    }
    let mask = (1u16 << (k as u16)) - 1u16;
    let v: u16 = chall[first_byte] as u16;
    proof {
        lemma_u16_shr_is_div(v, bit_off as u16);
        lemma_u16_low_bits_mask_is_mod(v >> (bit_off as u16), k as nat);
        lemma_span_value((chall@[(first_byte as int)] as int), bit_off as int, k as int);
        // assembly: ((v >> off) & mask) == span_value(byte, off, k)
        assert((v >> (bit_off as u16)) as int == (v as int) / pw(bit_off as nat));
        let mmod: int = ((v >> (bit_off as u16)) % (pw(k as nat) as u16)) as int;
        assert(mmod == ((v as int) / pw(bit_off as nat)) % pw(k as nat));
    }
    (v >> (bit_off as u16)) & mask
}

/// Origin Rust (utils.rs:35-39):
///     #[inline]
///     const fn extract_k_bits_next_bytes(
///         chall: &[u8], byte_idx: usize, k: usize) -> u16 {
///         let mask = (1 << k) - 1;
///         chall[byte_idx] as u16 & mask
///     }
/// Value face: the low k bits of byte chall[byte_idx].
#[inline]
pub exec fn extract_k_bits_next_bytes(chall: &[u8], byte_idx: usize, k: usize) -> (res: u16)
    requires
        byte_idx < chall.len(),
        1 <= k <= 8,
    ensures
        res as int == span_value((chall@[(byte_idx as int)] as int), 0int, k as int),
        0 <= res as int,
        (res as int) < pw(k as nat),
{
    proof {
        lemma_mask_u16(k);
    }
    let mask = (1u16 << (k as u16)) - 1u16;
    let v: u16 = chall[byte_idx] as u16;
    proof {
        lemma_mask_u16(k);
        assert(mask == (low_bits_mask(k as nat)) as u16);
        lemma_u16_low_bits_mask_is_mod(v, k as nat);
        lemma_span_value((chall@[(byte_idx as int)] as int), 0, k as int);
        assert((v as int) == (chall@[(byte_idx as int)] as int));
        let mmod: int = (v % (pw(k as nat) as u16)) as int;
        assert(mmod == (v as int) % pw(k as nat));
        assert(((v & mask) as int) == (v % (pw(k as nat) as u16)) as int);
        assert(pw(0nat) == 1) by {
            lemma2_to64();
        }
    }
    v & mask
}

/// Origin Rust (utils.rs:40-77): directly convert
/// `chal[start_bit...start_bit+k]` into a 16-bit integer.
///
/// Upstream lines carried verbatim as contract promises:
///   // As by current specification, we assume k<16
///   debug_assert!(k < 16);
///   debug_assert!(chall.len() >= k);
/// The debug_asserts erase in release; the twin re-erects the spec
/// promise as the `k <= 15` requires, and replaces the (weaker,
/// bit-vs-byte mismatched) `chall.len() >= k` with the true span
/// requirement `start_bit + k <= 8 * chall.len()`.
///
/// Upstream structure (the audited case split; body preserved):
///   byte/bit split, nbits_first_byte = 8 - bit_off;
///   k <= nbits_first_byte      -> first byte only
///   k <= 8 + nbits_first_byte  -> first two bytes
///   else                       -> three bytes
#[verifier::rlimit(6000)]
pub exec fn chall_to_u16(chall: &[u8], start_bit: usize, k: usize) -> (res: u16)
    requires
        1 <= k <= 15,
        start_bit + k <= 8 * chall.len(),
    ensures
        res as int == chall_bits_value(chall@, start_bit as int, k as int),
        0 <= res as int,
        (res as int) < pw(k as nat),
{
    // Starting byte and offset within byte (upstream 48-52)
    proof {
        lemma_fundamental_div_mod(start_bit as int, 8);
    }
    let byte_idx = start_bit / 8;
    let bit_off = start_bit % 8;
    let nbits_first_byte = 8 - bit_off;
    proof {
        assert(bit_off < 8);
        assert(byte_idx < chall.len());
    }

    if k <= nbits_first_byte {
        // Only consider first byte / Take k bits from first byte (54-57)
        proof {
            lemma_bits_in_byte(chall@, start_bit as int, bit_off as int, k as int);
        }
        let r1 = extract_k_bits_first_byte(chall, byte_idx, bit_off, k);
        assert((r1 as int) == chall_bits_value(chall@, start_bit as int, k as int));
        assert((r1 as int) < pw(k as nat));
        r1
    } else if k <= 8 + nbits_first_byte {
        // Only consider first two bytes (60-68): take all bits from the
        // first byte, then the remaining bits from the second byte.
        let a: u16 = extract_k_bits_first_byte(chall, byte_idx, bit_off, nbits_first_byte);
        let b: u16 = extract_k_bits_next_bytes(chall, byte_idx + 1, k - nbits_first_byte);
        proof {
            assert(byte_idx + 1 < chall.len());
            assert((a as int) < pw(nbits_first_byte as nat));
            assert((b as int) < pw((k - nbits_first_byte) as nat));
            assert((b as int) * pw(nbits_first_byte as nat) < 65536) by {
                lemma_pow2_pos(nbits_first_byte as nat);
                vstd::arithmetic::mul::lemma_mul_strict_inequality(
                    b as int,
                    pw((k - nbits_first_byte) as nat),
                    pw(nbits_first_byte as nat),
                );
                lemma_pow2_adds(nbits_first_byte as nat, (k - nbits_first_byte) as nat);
                lemma_pw_below_u16(k);
            }
            lemma_or_shift_value(a, b, nbits_first_byte);
            // model side: split at nbits_first_byte, align in byte twice
            lemma_chall_bits_split(chall@, start_bit as int, k as int, nbits_first_byte as int);
            lemma_bits_in_byte(
                chall@,
                start_bit as int,
                bit_off as int,
                nbits_first_byte as int,
            );
            assert((start_bit + nbits_first_byte) % 8 == 0) by {
                lemma_fundamental_div_mod(start_bit as int, 8);
            }
            assert(start_bit % 8 == bit_off as int);
            assert(start_bit + nbits_first_byte == 8 * byte_idx + 8);
            lemma_bits_in_byte(
                chall@,
                (start_bit + nbits_first_byte) as int,
                0,
                (k - nbits_first_byte) as int,
            );
            // link the pieces to the extract faces
            assert(chall_bits_value(chall@, start_bit as int, nbits_first_byte as int)
                == (a as int));
            assert(chall_bits_value(
                chall@,
                (start_bit + nbits_first_byte) as int,
                (k - nbits_first_byte) as int,
            ) == (b as int));
            // range: a + b*2^nb1 < 2^k
            assert((a as int) <= pw(nbits_first_byte as nat) - 1);
            assert((b as int) <= pw((k - nbits_first_byte) as nat) - 1);
            assert((b as int) * pw(nbits_first_byte as nat) <= pw(k as nat) - pw(nbits_first_byte as nat)) by {
                lemma_pow2_pos(nbits_first_byte as nat);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    (b as int),
                    (pw((k - nbits_first_byte) as nat) - 1),
                    pw(nbits_first_byte as nat),
                );
                vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(
                    pw(nbits_first_byte as nat),
                    pw((k - nbits_first_byte) as nat),
                    1,
                );
                lemma_pow2_adds(nbits_first_byte as nat, (k - nbits_first_byte) as nat);
            }
            assert((a as int) + (b as int) * pw(nbits_first_byte as nat) < pw(k as nat));
        }
        assert((a | (b << (nbits_first_byte as u16))) as int
            == chall_bits_value(chall@, start_bit as int, k as int));
        a | (b << (nbits_first_byte as u16))
    } else {
        // Take all bits from first byte (70-76);
        // Take all bits from second byte;
        // Take remaining bits from third byte.
        let a: u16 = extract_k_bits_first_byte(chall, byte_idx, bit_off, nbits_first_byte);
        let b: u16 = extract_k_bits_next_bytes(chall, byte_idx + 1, 8);
        let c: u16 = extract_k_bits_next_bytes(chall, byte_idx + 2, k - nbits_first_byte - 8);
        proof {
            assert(byte_idx + 2 < chall.len());
            assert(bit_off >= 2);
            assert(nbits_first_byte + 8 < 16);
            assert((a as int) < pw(nbits_first_byte as nat));
            assert((b as int) * pw(nbits_first_byte as nat) < 65536) by {
                lemma2_to64();
                assert(pw(8nat) == 256);
                assert((b as int) <= 255);
                if nbits_first_byte < 8 {
                    lemma_pow2_strictly_increases(nbits_first_byte as nat, 8nat);
                }
                assert(pw(nbits_first_byte as nat) <= 256);
                lemma_pow2_pos(nbits_first_byte as nat);
                vstd::arithmetic::mul::lemma_mul_upper_bound(
                    (b as int),
                    255,
                    pw(nbits_first_byte as nat),
                    256,
                );
            }
            lemma_or_shift_value(a, b, nbits_first_byte);
            assert(((a | (b << (nbits_first_byte as u16))) as int)
                < pw((nbits_first_byte + 8) as nat)) by {
                lemma2_to64();
                lemma_pow2_adds(nbits_first_byte as nat, 8nat);
                lemma_pow2_pos(nbits_first_byte as nat);
                assert(pw(8nat) == 256);
                assert((b as int) <= 255);
                assert((a as int) <= pw(nbits_first_byte as nat) - 1);
                // b*pw(s) + a <= (pw(8)-1)*pw(s) + pw(s) == pw(8)*pw(s)
                vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(
                    pw(nbits_first_byte as nat),
                    pw(8nat),
                    1,
                );
                assert((b as int) * pw(nbits_first_byte as nat)
                    + (a as int) < pw((nbits_first_byte + 8) as nat)) by {
                    vstd::arithmetic::mul::lemma_mul_inequality(
                        b as int,
                        255,
                        pw(nbits_first_byte as nat),
                    );
                    vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                        pw(nbits_first_byte as nat),
                        255,
                        1,
                    );
                }
            }
            assert((c as int) < pw((k - nbits_first_byte - 8) as nat));
            assert((c as int) * pw((nbits_first_byte + 8) as nat) < 65536) by {
                lemma_pow2_pos((nbits_first_byte + 8) as nat);
                vstd::arithmetic::mul::lemma_mul_strict_inequality(
                    c as int,
                    pw((k - nbits_first_byte - 8) as nat),
                    pw((nbits_first_byte + 8) as nat),
                );
                lemma_pow2_adds(
                    (nbits_first_byte + 8) as nat,
                    (k - nbits_first_byte - 8) as nat,
                );
                lemma_pw_below_u16(k);
            }
            lemma_or_shift_value(
                a | (b << (nbits_first_byte as u16)),
                c,
                (nbits_first_byte + 8) as usize,
            );
            // model side
            lemma_chall_bits_split(chall@, start_bit as int, k as int, nbits_first_byte as int);
            lemma_chall_bits_split(
                chall@,
                start_bit as int,
                k as int,
                (nbits_first_byte + 8) as int,
            );
            lemma_chall_bits_split(
                chall@,
                (start_bit + nbits_first_byte) as int,
                (k - nbits_first_byte) as int,
                8,
            );
            let s = start_bit as int;
            let nb1 = nbits_first_byte as int;
            let kf = k as int;
            assert(s % 8 == bit_off as int);
            assert(s + nb1 == 8 * (s / 8) + 8);
            assert((start_bit + nbits_first_byte) % 8 == 0) by {
                lemma_fundamental_div_mod(s, 8);
            }
            lemma_bits_in_byte(chall@, s, bit_off as int, nb1);
            lemma_bits_in_byte(chall@, s + nb1, 0, 8);
            lemma_bits_in_byte(chall@, s + nb1 + 8, 0, kf - nb1 - 8);
            // link the pieces to the extract faces
            assert(chall_bits_value(chall@, s, nb1) == (a as int));
            assert(chall_bits_value(chall@, s + nb1, 8) == (b as int));
            assert(chall_bits_value(chall@, s + nb1 + 8, kf - nb1 - 8) == (c as int));
            // distribute pw(nb1) over the middle+high split
            vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                pw(nb1 as nat),
                chall_bits_value(chall@, s + nb1, 8),
                chall_bits_value(chall@, s + nb1 + 8, kf - nb1 - 8) * pw(8nat),
            );
            assert(pw(nb1 as nat) * pw(8nat) == pw((nb1 + 8) as nat)) by {
                lemma_pow2_adds(nb1 as nat, 8nat);
            }
            vstd::arithmetic::mul::lemma_mul_is_associative(
                chall_bits_value(chall@, s + nb1 + 8, kf - nb1 - 8),
                pw(8nat),
                pw(nb1 as nat),
            );
            // range: a + b*2^nb1 + c*2^(nb1+8) < 2^k
            assert((a as int) <= pw(nb1 as nat) - 1);
            assert((b as int) <= pw(8nat) - 1);
            assert((b as int) * pw(nb1 as nat) <= pw((nb1 + 8) as nat) - pw(nb1 as nat)) by {
                lemma_pow2_pos(nb1 as nat);
                lemma_pow2_pos((nb1 + 8) as nat);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    (b as int),
                    (pw(8nat) - 1),
                    pw(nb1 as nat),
                );
                vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(
                    pw(nb1 as nat),
                    pw(8nat),
                    1,
                );
                lemma_pow2_adds(nb1 as nat, 8nat);
                assert(((pw(8nat) - 1) * pw(nb1 as nat)) == pw(8nat) * pw(nb1 as nat) - pw(nb1 as nat));
                assert(pw(8nat) * pw(nb1 as nat) == pw((nb1 + 8) as nat)) by {
                    lemma_pow2_adds(nb1 as nat, 8nat);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(pw(8nat), pw(nb1 as nat));
                }
            }
            assert((c as int) <= pw((kf - nb1 - 8) as nat) - 1);
            assert((c as int) * pw((nb1 + 8) as nat) <= pw(k as nat) - pw((nb1 + 8) as nat)) by {
                lemma_pow2_pos((nb1 + 8) as nat);
                vstd::arithmetic::mul::lemma_mul_inequality(
                    (c as int),
                    (pw((kf - nb1 - 8) as nat) - 1),
                    pw((nb1 + 8) as nat),
                );
                vstd::arithmetic::mul::lemma_mul_is_distributive_sub_other_way(
                    pw((nb1 + 8) as nat),
                    pw((kf - nb1 - 8) as nat),
                    1,
                );
                lemma_pow2_adds((nb1 + 8) as nat, (kf - nb1 - 8) as nat);
            }
            assert((a as int) + (b as int) * pw(nb1 as nat)
                + (c as int) * pw((nb1 + 8) as nat) < pw(k as nat));
        }
        let smid: usize = nbits_first_byte + 8;
        let mut res: u16 = a | (b << (nbits_first_byte as u16));
        res |= c << (smid as u16);
        assert((res as int) == (a as int) + (b as int) * pw(nbits_first_byte as nat)
            + (c as int) * pw(smid as nat));
        proof {
            assert(pw(smid as nat) == pw((nbits_first_byte + 8) as nat));
            // pin the model composite with named pieces (context-stable)
            let lo = chall_bits_value(chall@, start_bit as int, nbits_first_byte as int);
            let mid = chall_bits_value(chall@, (start_bit + nbits_first_byte) as int, 8);
            let hi = chall_bits_value(chall@, (start_bit + smid) as int, (k - smid) as int);
            assert(lo == (a as int));
            assert(mid == (b as int));
            assert(hi == (c as int));
            assert(chall_bits_value(chall@, start_bit as int, k as int)
                == lo + mid * pw(nbits_first_byte as nat) + hi * pw(smid as nat)) by {
                lemma_chall_bits_split(
                    chall@,
                    start_bit as int,
                    k as int,
                    nbits_first_byte as int,
                );
                lemma_chall_bits_split(
                    chall@,
                    (start_bit + nbits_first_byte) as int,
                    (k - nbits_first_byte) as int,
                    8,
                );
                assert(chall_bits_value(chall@, (start_bit + nbits_first_byte) as int, (k - nbits_first_byte) as int)
                    == mid + hi * pw(8nat));
                lemma_mul_is_distributive_add(pw(nbits_first_byte as nat), mid, hi * pw(8nat));
                lemma_mul_is_associative(hi, pw(8nat), pw(nbits_first_byte as nat));
                assert(pw(8nat) * pw(nbits_first_byte as nat) == pw(smid as nat)) by {
                    lemma_pow2_adds(nbits_first_byte as nat, 8nat);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(pw(8nat), pw(nbits_first_byte as nat));
                }
                // spell every intermediate sum for the harness compile unit
                let ps = pw(nbits_first_byte as nat);
                let p8 = pw(8nat);
                assert(chall_bits_value(chall@, start_bit as int, k as int)
                    == lo + chall_bits_value(chall@, (start_bit + nbits_first_byte) as int, (k - nbits_first_byte) as int) * ps);
                assert(chall_bits_value(chall@, (start_bit + nbits_first_byte) as int, (k - nbits_first_byte) as int)
                    == mid + hi * p8);
                assert((mid + hi * p8) * ps == ps * (mid + hi * p8)) by {
                    vstd::arithmetic::mul::lemma_mul_is_commutative((mid + hi * p8), ps);
                }
                assert(ps * (mid + hi * p8)
                    == ps * mid + ps * (hi * p8)) by {
                    lemma_mul_is_distributive_add(ps, mid, hi * p8);
                }
                assert((mid + hi * p8) * ps
                    == mid * ps + (hi * p8) * ps) by {
                    vstd::arithmetic::mul::lemma_mul_is_commutative(mid, ps);
                    vstd::arithmetic::mul::lemma_mul_is_commutative(hi * p8, ps);
                }
                assert((hi * p8) * ps == hi * (p8 * ps)) by {
                    lemma_mul_is_associative(hi, p8, ps);
                }
                assert(p8 * ps == ps * p8) by {
                    lemma_mul_is_commutative(p8, ps);
                }
                assert(ps * p8 == pw(smid as nat)) by {
                    lemma_pow2_adds(nbits_first_byte as nat, 8nat);
                }
                assert(hi * (p8 * ps)
                    == hi * (ps * p8)) by {
                    vstd::arithmetic::mul::lemma_mul_is_commutative(p8, ps);
                }
                assert(hi * (ps * p8) == hi * pw(smid as nat));
                assert(chall_bits_value(chall@, (start_bit + nbits_first_byte) as int, (k - nbits_first_byte) as int) * ps
                    == mid * ps + hi * pw(smid as nat));
                assert(lo + mid * ps + hi * pw(smid as nat)
                    == lo + mid * pw(nbits_first_byte as nat) + hi * pw(smid as nat));
            }
            assert((a as int) + (b as int) * pw(nbits_first_byte as nat)
                + (c as int) * pw(smid as nat)
                == chall_bits_value(chall@, start_bit as int, k as int));
        }
        res
    }
}


/// 2^k < 2^16 for k below 16 (the upper-tail bound the no-wrap chains
/// need; vstd only offers strictly-increases between two exponents).
pub proof fn lemma_pw_below_u16(k: usize)
    requires
        k < 16,
    ensures
        pw(k as nat) <= 32768,
{
    lemma2_to64();
    if k < 15 {
        lemma_pow2_strictly_increases(k as nat, 15nat);
    }
    // k == 15: pw(15nat) == 32768 concretely from lemma2_to64
    assert(pw(15nat) == 32768) by {
        lemma2_to64();
    }
}

// ===========================================================================
// Anchor 3: decode_all_chall_3 (upstream utils.rs:79-91).
// ===========================================================================

/// Origin Rust (utils.rs:79-91):
///     pub(crate) fn decode_all_chall_3<TAU: TauParameters>(
///         chall: &[u8]) -> Array<u16, TAU::Tau> {
///         let k = TAU::K::USIZE;
///         // Compute Delta_i[0...Tau1)
///         let first_half = (0..TAU::Tau1::USIZE)
///             .map(|i| chall_to_u16(chall, TAU::tau1_offset_unchecked(i), k));
///         // Compute Delta_i[Tau1..Tau)
///         let second_half = (TAU::Tau1::USIZE..TAU::Tau::USIZE)
///             .map(|i| chall_to_u16(chall, TAU::tau0_offset_unchecked(i), k - 1));
///         first_half.chain(second_half).collect()
///     }
/// Generic TAU instantiation lowers to the (k, tau1, tau0, N)
/// parameter set per the batch plan (concrete constants over trait
/// generics); Array<u16, TAU::Tau> lowers to [u16; N] (trusted
/// hybrid-array representation), the chained iterator to the two
/// sequential loops.
pub exec fn decode_all_chall_3<const N: usize>(
    chall: &[u8],
    k: usize,
    tau1: usize,
    tau0: usize,
) -> (chals: [u16; N])
    requires
        2 <= k <= 15,
        N == tau1 + tau0,
        tau1 * k + tau0 * (k - 1) <= 8 * chall.len(),
        tau1 * k + tau0 * (k - 1) <= usize::MAX,
    ensures
        forall |i: int| 0 <= i < tau1 ==> (chals[i] as int)
            == chall_bits_value(chall@, tau1_offset_spec(k as int, i), k as int),
        forall |i: int| 0 <= i < tau1 ==> (chals[i] as int) < pw(k as nat),
        forall |i: int| tau1 <= i < N ==> (chals[i] as int)
            == chall_bits_value(
                chall@,
                tau0_offset_spec(tau1 as int, k as int, i),
                (k - 1) as int,
            ),
        forall |i: int| tau1 <= i < N ==> (chals[i] as int) < pw((k - 1) as nat),
{
    let mut chals: [u16; N] = [0u16; N];
    // Compute Delta_i[0...Tau1) (upstream 84)
    let mut i: usize = 0;
    while i < tau1
        invariant
            i <= tau1,
            tau1 <= N,
            N == tau1 + tau0,
            2 <= k <= 15,
            tau1 * k + tau0 * (k - 1) <= 8 * chall.len(),
            tau1 * k + tau0 * (k - 1) <= usize::MAX,
            forall |j: int| 0 <= j < i ==> (chals[j] as int)
                == chall_bits_value(chall@, tau1_offset_spec(k as int, j), k as int),
            forall |j: int| 0 <= j < i ==> (chals[j] as int) < pw(k as nat),
        decreases tau1 - i,
    {
        proof {
            // per-iteration span bound for the call (T4-2: derived
            // facts must be restated inside the loop frame)
            assert((k as int) * ((i as int) + 1) == ((k as int) * (i as int)) + (k as int)) by {
                vstd::arithmetic::mul::lemma_mul_is_distributive_add(k as int, i as int, 1);
            }
            assert((k as int) * ((i as int) + 1) <= (tau1 as int) * (k as int)) by {
                vstd::arithmetic::mul::lemma_mul_is_commutative(k as int, (i as int) + 1);
                vstd::arithmetic::mul::lemma_mul_inequality((i as int) + 1, tau1 as int, k as int);
            }
            assert(0 <= (tau0 as int) * ((k as int) - 1));
            assert((k as int) * (i as int) + k
                <= (tau1 as int) * (k as int) + (tau0 as int) * ((k as int) - 1));
            assert(k * i <= usize::MAX);
            assert(i <= N);
        }
        chals[i] = chall_to_u16(chall, tau1_offset_unchecked(k, i), k);
        i += 1;
    }
    // Compute Delta_i[Tau1..Tau) (upstream 87-88)
    while i < N
        invariant
            tau1 <= i <= N,
            N == tau1 + tau0,
            2 <= k <= 15,
            tau1 * k + tau0 * (k - 1) <= 8 * chall.len(),
            tau1 * k + tau0 * (k - 1) <= usize::MAX,
            forall |j: int| 0 <= j < tau1 ==> (chals[j] as int)
                == chall_bits_value(chall@, tau1_offset_spec(k as int, j), k as int),
            forall |j: int| 0 <= j < tau1 ==> (chals[j] as int) < pw(k as nat),
            forall |j: int| tau1 <= j < i ==> (chals[j] as int)
                == chall_bits_value(
                    chall@,
                    tau0_offset_spec(tau1 as int, k as int, j),
                    (k - 1) as int,
                ),
            forall |j: int| tau1 <= j < i ==> (chals[j] as int) < pw((k - 1) as nat),
        decreases N - i,
    {
        proof {
            assert(((i as int) + 1) - (tau1 as int) <= (tau0 as int)) by {
                assert((i as int) + 1 <= N as int);
            }
            assert(((k as int) - 1) * (((i as int) + 1) - (tau1 as int))
                == (((k as int) - 1) * ((i as int) - (tau1 as int))) + ((k as int) - 1)) by {
                vstd::arithmetic::mul::lemma_mul_is_distributive_add(
                    ((k as int) - 1),
                    (i as int) - (tau1 as int),
                    1,
                );
            }
            assert(((k as int) - 1) * (((i as int) + 1) - (tau1 as int))
                <= ((k as int) - 1) * (tau0 as int)) by {
                vstd::arithmetic::mul::lemma_mul_is_commutative(
                    ((k as int) - 1),
                    ((i as int) + 1) - (tau1 as int),
                );
                vstd::arithmetic::mul::lemma_mul_inequality(
                    ((i as int) + 1) - (tau1 as int),
                    tau0 as int,
                    ((k as int) - 1),
                );
            }
            assert((tau1 as int) * (k as int) + ((k as int) - 1) * ((i as int) - (tau1 as int))
                + ((k as int) - 1)
                <= (tau1 as int) * (k as int) + (tau0 as int) * ((k as int) - 1));
            assert(0 <= (tau1 as int) * (k as int));
            assert((k - 1) * (i - tau1) <= usize::MAX - tau1 * k);
            assert(tau1 * k <= usize::MAX);
        }
        chals[i] = chall_to_u16(chall, tau0_offset_unchecked(tau1, k, i), k - 1);
        i += 1;
    }
    chals
}

/// FAEST128f binding: upstream fixes TAU = Tau128Fast for the
/// Faest128Fast rows (parameter.rs:1059-1063, type alias BAVC128Fast),
/// i.e. K=8, Tau1=8, Tau0=8, a 120-bit decode span inside the 128-bit
/// (16-byte) Fiat-Shamir challenge.
pub exec fn decode_all_chall_3_128f(chall: &[u8]) -> (chals: [u16; 16])
    requires
        chall.len() >= 15, // 120-bit span rounds up to 15 bytes
    ensures
        forall |i: int| 0 <= i < 8 ==> (chals[i] as int)
            == chall_bits_value(chall@, 8 * i, 8),
        forall |i: int| 0 <= i < 8 ==> (chals[i] as int) < pw(8),
        forall |i: int| 8 <= i < 16 ==> (chals[i] as int)
            == chall_bits_value(chall@, 64 + 7 * (i - 8), 7),
        forall |i: int| 8 <= i < 16 ==> (chals[i] as int) < pw(7),
{
    decode_all_chall_3::<16>(chall, TAU128F_K, TAU128F_TAU1, TAU128F_TAU0)
}

// ===========================================================================
// xor family (upstream utils.rs:93-112).
// ===========================================================================

/// Origin Rust (utils.rs:93-98):
///     /// Xors the input slices and retuns an iterator over the
///     resulting elements.
///     ///
///     /// The length of the resulting iterator is equal to the length
///     of the shortest input slice.
///     pub(crate) fn xor_arrays<'a>(lhs: &'a [u8], rhs: &'a [u8])
///         -> impl Iterator<Item = u8> + use<'a> {
///         zip(lhs, rhs).map(|(lhs, rhs)| lhs ^ rhs)
///     }
/// The iterator face lowers to a materialized Vec (elementwise xor over
/// the minimum length), the body shape downstream consumers use.
pub exec fn xor_arrays(lhs: &[u8], rhs: &[u8]) -> (o: Vec<u8>)
    ensures
        o@.len() == (if lhs@.len() < rhs@.len() { lhs@.len() } else { rhs@.len() }),
        forall |i: int| 0 <= i < o@.len() ==> o[i] == (lhs[i] ^ rhs[i]) as u8,
{
    let n: usize = if lhs.len() < rhs.len() { lhs.len() } else { rhs.len() };
    let mut o: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == (if lhs@.len() < rhs@.len() { lhs@.len() } else { rhs@.len() }),
            forall |j: int| 0 <= j < i ==> o[j] == (lhs[j] ^ rhs[j]) as u8,
            o.len() == i,
            n <= lhs@.len(),
            n <= rhs@.len(),
        decreases n - i,
    {
        o.push(lhs[i] ^ rhs[i]);
        i += 1;
    }
    o
}

/// Origin Rust (utils.rs:100-105):
///     /// Xors the input slices overwriting the first slice with the
///     resulting elements.
///     pub(crate) fn xor_arrays_inplace(lhs: &mut [u8], rhs: &[u8]) {
///         for (lhs, rhs) in zip(lhs.iter_mut(), rhs) {
///             *lhs ^= rhs;
///         }
///     }
/// The zip iterator stops at the shorter side, leaving the tail of lhs
/// untouched; the twin's ensures make both zones explicit (T4-1
/// old/final receiver spelling).
pub exec fn xor_arrays_inplace(lhs: &mut [u8], rhs: &[u8])
    ensures
        forall |i: int| 0 <= i < old(lhs)@.len() && i < rhs@.len() ==>
            final(lhs)[i] == (old(lhs)[i] ^ rhs[i]) as u8,
        forall |i: int| rhs@.len() <= i < old(lhs)@.len() ==> final(lhs)[i] == old(lhs)[i],
{
    let n: usize = if lhs.len() < rhs.len() { lhs.len() } else { rhs.len() };
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == (if old(lhs)@.len() < rhs@.len() { old(lhs)@.len() } else { rhs@.len() }),
            forall |j: int| 0 <= j < i ==> lhs[j] == (old(lhs)[j] ^ rhs[j]) as u8,
            forall |j: int| i <= j < lhs@.len() ==> lhs[j] == old(lhs)[j],
            lhs@.len() == old(lhs)@.len(),
            n <= lhs@.len(),
            n <= rhs@.len(),
        decreases n - i,
    {
        lhs[i] = lhs[i] ^ rhs[i];
        i += 1;
    }
}

/// Origin Rust (utils.rs:107-112):
///     /// Xors the input slices into the output slice
///     pub(crate) fn xor_arrays_into(
///         dst: &mut [u8], lhs: &[u8], rhs: &[u8]) {
///         for (dst, lhs, rhs) in izip!(dst.iter_mut(), lhs, rhs) {
///             *dst = lhs ^ rhs;
///         }
///     }
/// (itertools::izip lowers to the same minimum-length index loop).
pub exec fn xor_arrays_into(dst: &mut [u8], lhs: &[u8], rhs: &[u8])
    ensures
        forall |i: int| 0 <= i < old(dst)@.len() && i < lhs@.len() && i < rhs@.len() ==>
            final(dst)[i] == (lhs[i] ^ rhs[i]) as u8,
        forall |i: int| 0 <= i < old(dst)@.len()
            && (lhs@.len() <= i || rhs@.len() <= i) ==>
            final(dst)[i] == old(dst)[i],
{
    let n: usize = if dst.len() < lhs.len() { dst.len() } else { lhs.len() };
    let n2: usize = if n < rhs.len() { n } else { rhs.len() };
    let mut i: usize = 0;
    while i < n2
        invariant
            i <= n2,
            forall |j: int| 0 <= j < i ==> dst[j] == (lhs[j] ^ rhs[j]) as u8,
            forall |j: int| i <= j < dst@.len() ==> dst[j] == old(dst)[j],
            dst@.len() == old(dst)@.len(),
            n <= dst@.len(),
            n <= lhs@.len(),
            n2 <= n,
            n2 <= dst@.len(),
            n2 <= rhs@.len(),
        decreases n2 - i,
    {
        dst[i] = lhs[i] ^ rhs[i];
        i += 1;
    }
}

// ===========================================================================
// get_bit (upstream utils.rs:114-122).
// ===========================================================================

/// Origin Rust (utils.rs:114-122):
///     /// Returns the bit at the given index in the input byte array.
///     ///
///     /// Panics if the index is out of bounds.
///     #[inline]
///     pub(crate) const fn get_bit(input: &[u8], index: usize) -> u8 {
///         let byte_index = index / 8;
///         let bit_offset = index % 8;
///         (input[byte_index] >> bit_offset) & 1
///     }
/// The doc's panic promise for out-of-bounds indexes becomes the twin's
/// requires (panic-free contract face); `const fn` dropped as above.
#[inline]
pub exec fn get_bit(input: &[u8], index: usize) -> (r: u8)
    requires
        index < 8 * input.len(),
    ensures
        (r as int) == bit_at(input@, index as int),
        r <= 1u8,
{
    let byte_index = index / 8;
    let bit_offset = index % 8;
    proof {
        let x: u8 = (input@[(byte_index as int)] as u8);
        assert(((input@[(byte_index as int)] as u8)) == x);
        lemma_low_bits_mask_values();
        assert((low_bits_mask(1nat) as u8) == 1u8);
        lemma2_to64();
        assert(pow2(1nat) as u8 == 2u8);
        assert(pw(1nat) == 2);
        lemma_u8_shr_is_div(x, (bit_offset as u8));
        lemma_u8_low_bits_mask_is_mod((x >> (bit_offset as u8)), 1nat);
        assert(((x >> (bit_offset as u8)) & (low_bits_mask(1nat) as u8))
            == ((x >> (bit_offset as u8)) % (pow2(1nat) as u8)));
        assert(((x >> (bit_offset as u8)) & 1u8)
            == ((x >> (bit_offset as u8)) & (low_bits_mask(1nat) as u8)));
        assert(((x >> (bit_offset as u8)) & 1u8)
            == ((x >> (bit_offset as u8)) % (pow2(1nat) as u8)));
        assert(((x >> (bit_offset as u8)) & 1u8) as int == ((x as int) / pw(bit_offset as nat)) % 2);
        assert(bit_at(input@, index as int)
            == ((input@[(index / 8) as int] as int / pw((index % 8) as nat)) % 2));
        assert((((input@[(byte_index as int)] as u8) >> (bit_offset as u8)) & 1u8) as int
            == bit_at(input@, index as int));
    }
    (input[byte_index] >> (bit_offset as u8)) & 1u8
}

// ===========================================================================
// array_ref (upstream utils.rs:124-137), u8 face.
// ===========================================================================

/// Origin Rust (utils.rs:124-137):
///     /// Converts a slice into a shared `Array` reference.
///     ///
///     /// This is a small replacement for the deprecated
///     `Array::from_slice`.
///     /// It panics if the slice length does not exactly match the
///     array size,
///     /// so it should only be used when the length is an internal
///     invariant
///     #[inline]
///     pub(crate) fn array_ref<T, N>(slice: &[T]) -> &Array<T, N>
///     where N: ArraySize,
///     {
///         slice.try_into().expect("slice length must match Array size")
///     }
/// Twin lowering (u8 instantiation of the generic face): hybrid Array
/// is a trusted representation (inventory section 4), so the shared
/// reference lowers to the by-value fixed array with the same length
/// match and elementwise copy; the expect-panic on mismatch becomes
/// requires. T-generic faces ride with later batches' consumers.
#[inline]
pub exec fn array_ref<const N: usize>(slice: &[u8]) -> (a: [u8; N])
    requires
        slice.len() == N,
    ensures
        forall |i: int| 0 <= i < N ==> (a[i] as int) == (slice[i] as int),
{
    let mut a: [u8; N] = [0u8; N];
    let mut i: usize = 0;
    while i < N
        invariant
            i <= N,
            N == slice.len(),
            forall |j: int| 0 <= j < i ==> (a[j] as int) == (slice[j] as int),
        decreases N - i,
    {
        a[i] = slice[i];
        i += 1;
    }
    a
}

} // verus!
