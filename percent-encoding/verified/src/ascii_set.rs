//! `percent-encoding` crate mirror
//!
//! Upstream: https://github.com/servo/rust-url (pin 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a)
//! crate root at `code/percent_encoding/` (SUBDIR=percent_encoding; code/ tree untouched)
//! This file is the same-name mirror of `src/ascii_set.rs`.
//!
//! Mirror and relaxation ledger (KVerus relax criteria):
//! 1. `contains`/`add`/`remove` (upstream pub(crate)/pub const fn) keep the original in-place
//!    bit-operation implementation, but the obligation surface is closed with
//!    `requires byte < 0x80` per the struct doc "Represents a set of characters or bytes in the ASCII range"
//!    -- byte >= 0x80 is the upstream real panic face
//!    (mask[byte/32] index out of bounds; `add`/`remove` are publicly exposed with no `# Panics` doc);
//!    the OOB site is a known upstream issue (rust-url #1132), not filed separately here.
//! 2. The upstream `static_assert!` (macro + mem::transmute const trick, ascii_set.rs:116-132)
//!    is a compile-time assertion trick; the mirror turns its 5 assertions into spec facts of
//!    CONTROLS (lemma_controls).
//! 3. `impl ops::Add`/`impl ops::Not` (ascii_set.rs:86-100) are each a 1-line delegation
//!    (union/complement); verus does not verify std trait impls directly; the semantic
//!    obligations are fully verified at union/complement, and the delegated semantics is
//!    covered by property theorems (harness/ut_ascii_set.rs); the trait face itself is
//!    outside the verus support surface.
//! 4. Upstream `CONTROLS`/`NON_ALPHANUMERIC` are `pub const &'static AsciiSet`; the mirror
//!    uses a value-typed const / exec construction. The 30-call `add` chain of `NON_ALPHANUMERIC`
//!    is const-evaluated upstream; the mirror builds it step by step with the verified `add` exec,
//!    carrying the doc contract as ensures (see non_alphanumeric below).
//! 5. Verus engineering notes (unrelated to upstream semantics): writing
//!    `assert forall ... by { ...bit ops... }` directly inside an exec body makes the verus
//!    trigger-inference interpreter crash on the array view (interpreter.rs:856); this mirror
//!    puts all membership-face theorems in module-level proof fns (parameters are struct
//!    values / plain u32), and the exec side drives them with non-quantified asserts +
//!    `proof { lemma(...) }` calls.
//!    Bit-level facts use `assert(...) by (bit_vector) requires <bound>` -- the by clause
//!    does not inherit the outer requires, so the bound must be repeated inside the by
//!    clause.
//!
//! Consumption: this file has no fn main; KVerus drives it via harness files; the files
//! under harness/ reference this module's work via `#[path]` and must not copy its spec.

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

/* ============================================================
 * Bit model (Origin: modeling of the chunk/shift algorithm at ascii_set.rs:28-50)
 * ============================================================ */

/// Origin: ascii_set.rs:46-50, the bit-test semantics of `contains`:
/// `let chunk = self.mask[byte as usize / BITS_PER_CHUNK];
///  let mask = 1 << (byte as usize % BITS_PER_CHUNK]; (chunk & mask) != 0`
/// Spec form: for k in [0,128), read bit k%32 of mask[k/32].
pub open spec fn bit_at(mask: Seq<u32>, k: int) -> bool {
    (mask[k / 32] & (1u32 << (k % 32))) != 0u32
}

/// Origin: ascii_set.rs:52-54, the semantics of `should_percent_encode`:
/// `!byte.is_ascii() || self.contains(byte)`: non-ASCII is always encoded; ASCII consults the bitmap.
pub open spec fn should_encode(mask: Seq<u32>, k: int) -> bool {
    k >= 128 || bit_at(mask, k)
}

/// Functional spec of single-byte bit setting (the per-step handle of add)
pub open spec fn add_bit_spec(mask: Seq<u32>, b: int) -> Seq<u32> {
    mask.update(b / 32, mask[b / 32] | (1u32 << (b % 32)))
}

/// Functional spec of single-byte bit clearing (the remove dual)
pub open spec fn remove_bit_spec(mask: Seq<u32>, b: int) -> Seq<u32> {
    mask.update(b / 32, mask[b / 32] & !(1u32 << (b % 32)))
}

/* ============================================================
 * Struct (Origin: ascii_set.rs:27-30)
 * `pub struct AsciiSet { mask: [Chunk; ASCII_RANGE_LEN / BITS_PER_CHUNK] }`
 * (Chunk=u32, ASCII_RANGE_LEN=0x80, BITS_PER_CHUNK=32 -> [u32; 4])
 * Field elevated to pub: the reference-style harness needs field-wise construction (minimal visibility relaxation).
 * ============================================================ */

#[derive(PartialEq, Eq)]
pub struct AsciiSet {
    pub mask: [u32; 4],
}

/* ============================================================
 * impl AsciiSet (Origin: ascii_set.rs:38-84)
 * ============================================================ */

impl AsciiSet {
    /// Origin: ascii_set.rs:40-42 `pub const EMPTY: Self = Self { mask: [0; 4] }`
    pub open const EMPTY: AsciiSet = AsciiSet { mask: [0u32, 0u32, 0u32, 0u32] };

    /// Origin: ascii_set.rs:44-50
    /// `pub(crate) const fn contains(&self, byte: u8) -> bool {
    ///     let chunk = self.mask[byte as usize / BITS_PER_CHUNK];
    ///     let mask = 1 << (byte as usize % BITS_PER_CHUNK];
    ///     (chunk & mask) != 0 }`
    /// The contract face = the ASCII range of the struct doc (the panic face here is the
    /// pub(crate)-internal bit; the publicly exposed panic entries are add/remove, see ledger item 1).
    /// Upstream doc (ascii_set.rs:44-45):
    ///   Called with UTF-8 bytes rather than code points.
    ///   Not used for non-ASCII bytes.
    pub exec fn contains(&self, b: u8) -> (r: bool)
        requires
            (b as int) < 128,
        ensures
            r == bit_at(self.mask@, b as int),
    {
        /* Origin Rust: let chunk = self.mask[byte as usize / BITS_PER_CHUNK]; */
        let chunk = self.mask[(b as usize) / 32];
        /* Origin Rust: let mask = 1 << (byte as usize % BITS_PER_CHUNK]; */
        let msk = 1u32 << ((b as usize) % 32);
        (chunk & msk) != 0
    }

    /// Origin: ascii_set.rs:52-54
    /// `pub(crate) fn should_percent_encode(&self, byte: u8) -> bool {
    ///     !byte.is_ascii() || self.contains(byte) }`
    /// `is_ascii` is outside the verus support surface; it is rewritten as a constant
    /// comparison per its definition (byte < 0x80). Short-circuit semantics preserved:
    /// the non-ASCII branch does not touch contains (copying the upstream short-circuit);
    /// the function is in total panic-free (short-circuit protection), formalized with no precondition.
    pub exec fn should_percent_encode(&self, b: u8) -> (r: bool)
        ensures
            r == should_encode(self.mask@, b as int),
    {
        /* Origin Rust: !byte.is_ascii() || self.contains(byte) */
        if b >= 128 {
            true
        } else {
            self.contains(b)
        }
    }

    /// Origin: ascii_set.rs:56-60 `pub const fn add(&self, byte: u8) -> Self ...`
    /// Upstream has no byte < 0x80 precondition -- mask[byte/32] panics out of
    /// bounds for byte >= 0x80 (the known upstream OOB issue, ledger item 1);
    /// this mirror closes it with a requires per the struct-doc "ASCII range".
    pub exec fn add(&self, b: u8) -> (s: AsciiSet)
        requires
            (b as int) < 128,
        ensures
            forall|k: int| 0 <= k < 128 ==> bit_at(s.mask@, k)
                == (bit_at(self.mask@, k) || k == b as int),
            s.mask@ == add_bit_spec(self.mask@, b as int),
    {
        /* Origin Rust: let mut mask = self.mask; */
        let mut mask = self.mask;
        /* Origin Rust: mask[byte as usize / BITS_PER_CHUNK] |= 1 << (byte as usize % BITS_PER_CHUNK]; */
        let idx = (b as usize) / 32;
        let bitpos = (b as usize) % 32;
        mask[idx] = mask[idx] | (1u32 << bitpos);
        assert(idx == (b as int) / 32);
        assert(bitpos == (b as int) % 32);
        assert(mask@.len() == 4);
        proof {
            lemma_add_membership(self.mask@, mask@, b);
        }
        AsciiSet { mask }
    }

    /// Origin: ascii_set.rs:62-66 `pub const fn remove(&self, byte: u8) -> Self ...`
    /// Same as add: upstream panics out of bounds for byte >= 0x80; the mirror closes it with a requires.
    pub exec fn remove(&self, b: u8) -> (s: AsciiSet)
        requires
            (b as int) < 128,
        ensures
            forall|k: int| 0 <= k < 128 ==> bit_at(s.mask@, k)
                == (bit_at(self.mask@, k) && k != b as int),
            s.mask@ == remove_bit_spec(self.mask@, b as int),
    {
        /* Origin Rust: let mut mask = self.mask; */
        let mut mask = self.mask;
        /* Origin Rust: mask[byte as usize / BITS_PER_CHUNK] &= !(1 << (byte as usize % BITS_PER_CHUNK]); */
        let idx = (b as usize) / 32;
        let bitpos = (b as usize) % 32;
        mask[idx] = mask[idx] & (!(1u32 << bitpos));
        assert(idx == (b as int) / 32);
        assert(bitpos == (b as int) % 32);
        assert(mask@.len() == 4);
        proof {
            lemma_remove_membership(self.mask@, mask@, b);
        }
        AsciiSet { mask }
    }

    /// Origin: ascii_set.rs:68-77 `pub const fn union(&self, other: Self) -> Self`
    /// The literal four chunks are OR-ed chunk by chunk, copied verbatim.
    /// Upstream doc (ascii_set.rs:68-68):
    ///   Return the union of two sets.
    pub exec fn union(&self, other: AsciiSet) -> (s: AsciiSet)
        ensures
            forall|k: int| 0 <= k < 128 ==> bit_at(s.mask@, k)
                == (bit_at(self.mask@, k) || bit_at(other.mask@, k)),
            forall|j: int| 0 <= j < 4 ==> s.mask@.index(j)
                == (self.mask@.index(j) | other.mask@.index(j)),
    {
        /* Origin Rust: let mask = [ self.mask[0] | other.mask[0], ... ]; */
        let mask = [
            self.mask[0] | other.mask[0],
            self.mask[1] | other.mask[1],
            self.mask[2] | other.mask[2],
            self.mask[3] | other.mask[3],
        ];
        assert(mask@.len() == 4);
        proof {
            lemma_union_membership(self.mask@, other.mask@, mask@);
        }
        AsciiSet { mask }
    }

    /// Origin: ascii_set.rs:79-83 `pub const fn complement(&self) -> Self`
    /// Upstream doc (ascii_set.rs:79-79):
    ///   Return the negation of the set.
    pub exec fn complement(&self) -> (s: AsciiSet)
        ensures
            forall|k: int| 0 <= k < 128 ==> bit_at(s.mask@, k) == !bit_at(self.mask@, k),
            forall|j: int| 0 <= j < 4 ==> s.mask@.index(j)
                == (self.mask@.index(j) ^ 4294967295u32),
    {
        /* Origin Rust: let mask = [!self.mask[0], !self.mask[1], ...]; */
        let mask = [
            self.mask[0] ^ 4294967295u32,
            self.mask[1] ^ 4294967295u32,
            self.mask[2] ^ 4294967295u32,
            self.mask[3] ^ 4294967295u32,
        ];
        assert(mask@.len() == 4);
        proof {
            lemma_complement_membership(self.mask@, mask@);
        }
        AsciiSet { mask }
    }
}

/* ============================================================
 * Predefined sets (Origin: ascii_set.rs:102-170)
 * ============================================================ */

/// Origin: ascii_set.rs:107-114
/// `pub const CONTROLS: &AsciiSet = &AsciiSet { mask: [
///     !0_u32, 0, 0, 1 << (0x7F_u32 % 32) ] };`
/// (!0 == 4294967295; 1<<(0x7F%32) == 1<<31 == 2147483648;
///   upstream is `&'static`; the mirror takes a value-typed const, same semantics)
pub open const CONTROLS: AsciiSet = AsciiSet {
    mask: [4294967295u32, 0u32, 0u32, 2147483648u32],
};

/* ============================================================
 * NON_ALPHANUMERIC (Origin: ascii_set.rs:134-170)
 * ============================================================ */

/// Origin: ascii_set.rs:134-136, the spec form of the doc contract.
pub open spec fn is_alnum(k: int) -> bool {
    (0x30 <= k <= 0x39) || (0x41 <= k <= 0x5A) || (0x61 <= k <= 0x7A)
}

/// The source list of non-alphanumeric bits of NON_ALPHANUMERIC -- the 30 `.add(b'...')`
/// arguments of Origin: ascii_set.rs:137-170 (the full set of non-alphanumeric ASCII in 0x20..0x7E).
pub open spec fn added_by_non_alnum(k: int) -> bool {
    k == 0x20 || (0x21 <= k <= 0x2F) || k == 0x3A || (0x3B <= k <= 0x40)
        || (0x5B <= k <= 0x60) || (0x7B <= k <= 0x7E)
}

/// Origin: ascii_set.rs:137-170
/// `pub const NON_ALPHANUMERIC: &AsciiSet = &CONTROLS.add(b' ').add(b'!')
///   ....add(b'~');` (a 30-call const-evaluation chain, tail .add(b'~'))
/// The mirror builds it step by step with the verified `add` exec (chain order and arguments verbatim from upstream).
/// A 33-step taylor chain: the contract fact of each step is instantiated at the same k and
/// strung into a chain; the tail uses lemma_non_alnum_union to convert the CONTROLS union
/// list face into the doc contract.
/// Upstream doc (ascii_set.rs:134-136):
///   Everything that is not an ASCII letter or digit.
///   This is probably more eager than necessary in any context.
pub exec fn non_alphanumeric() -> (s: AsciiSet)
    ensures
        forall|k: int| 0 <= k < 128 ==> bit_at(s.mask@, k) == (!is_alnum(k)),
{
    /* Origin Rust: CONTROLS.add(b' ').add(b'!')....add(b'~')
     * (a 30-call chain, arguments above; upstream is const-evaluated) */
    let s0 = CONTROLS.add(0x20);
    let s1 = s0.add(0x21);
    let s2 = s1.add(0x22);
    let s3 = s2.add(0x23);
    let s4 = s3.add(0x24);
    let s5 = s4.add(0x25);
    let s6 = s5.add(0x26);
    let s7 = s6.add(0x27);
    let s8 = s7.add(0x28);
    let s9 = s8.add(0x29);
    let s10 = s9.add(0x2A);
    let s11 = s10.add(0x2B);
    let s12 = s11.add(0x2C);
    let s13 = s12.add(0x2D);
    let s14 = s13.add(0x2E);
    let s15 = s14.add(0x2F);
    let s16 = s15.add(0x3A);
    let s17 = s16.add(0x3B);
    let s18 = s17.add(0x3C);
    let s19 = s18.add(0x3D);
    let s20 = s19.add(0x3E);
    let s21 = s20.add(0x3F);
    let s22 = s21.add(0x40);
    let s23 = s22.add(0x5B);
    let s24 = s23.add(0x5C);
    let s25 = s24.add(0x5D);
    let s26 = s25.add(0x5E);
    let s27 = s26.add(0x5F);
    let s28 = s27.add(0x60);
    let s29 = s28.add(0x7B);
    let s30 = s29.add(0x7C);
    let s31 = s30.add(0x7D);
    let s32 = s31.add(0x7E);
    // Same-k chain: one assert per step (empty by-block, purely quantified; see ledger item 5
    // for the interpreter-crash avoidance), folding the CONTROLS membership face byte by byte
    // into the doc list.
    assert forall|k: int| 0 <= k < 128 implies bit_at(CONTROLS.mask@, k)
        == ((k <= 0x1F || k == 0x7F)) by { lemma_controls(); };
    assert forall|k: int| 0 <= k < 128 implies bit_at(s0.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s1.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s2.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s3.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s4.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s5.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s6.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s7.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s8.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s9.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s10.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s11.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s12.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s13.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s14.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s15.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s16.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s17.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s18.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s19.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s20.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s21.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s22.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s23.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s24.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s25.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C || k == 0x5D) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s26.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C || k == 0x5D || k == 0x5E) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s27.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C || k == 0x5D || k == 0x5E || k == 0x5F) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s28.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C || k == 0x5D || k == 0x5E || k == 0x5F || k == 0x60) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s29.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C || k == 0x5D || k == 0x5E || k == 0x5F || k == 0x60 || k == 0x7B) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s30.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C || k == 0x5D || k == 0x5E || k == 0x5F || k == 0x60 || k == 0x7B || k == 0x7C) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s31.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C || k == 0x5D || k == 0x5E || k == 0x5F || k == 0x60 || k == 0x7B || k == 0x7C || k == 0x7D) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s32.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || k == 0x20 || k == 0x21 || k == 0x22 || k == 0x23 || k == 0x24 || k == 0x25 || k == 0x26 || k == 0x27 || k == 0x28 || k == 0x29 || k == 0x2A || k == 0x2B || k == 0x2C || k == 0x2D || k == 0x2E || k == 0x2F || k == 0x3A || k == 0x3B || k == 0x3C || k == 0x3D || k == 0x3E || k == 0x3F || k == 0x40 || k == 0x5B || k == 0x5C || k == 0x5D || k == 0x5E || k == 0x5F || k == 0x60 || k == 0x7B || k == 0x7C || k == 0x7D || k == 0x7E) by {};
    assert forall|k: int| 0 <= k < 128 implies bit_at(s32.mask@, k)
        == ((k <= 0x1F || k == 0x7F) || added_by_non_alnum(k)) by {
        lemma_added_list_concrete();
    };
    proof {
        lemma_non_alnum_union(s32);
    }
    s32
}


// =========================================================================
// Proof lemmas -- the standalone proof fns live at the end of the file so
// the executable content reads directly; the inline proof {} blocks inside
// exec bodies stay in place.
// measured: all five verification panels identical before and after the move.
/// Membership face of EMPTY: an all-zero mask has no member in 0..=127 (the bypass
/// lemma for the const array_view interpretation pitfall -- exec/quantified asserts
/// referencing EMPTY.mask@ must go through this lemma to obtain the membership face).
pub proof fn lemma_empty_members(m: Seq<u32>)
    requires
        m == seq![0u32, 0u32, 0u32, 0u32],
    ensures
        forall|k: int| 0 <= k < 128 ==> !bit_at(m, k),
{
    assert forall|k: int| 0 <= k < 128 implies !bit_at(m, k) by {
        let c = m[k / 32];
        assert(c == 0u32);
        let p = (k % 32) as u32;
        assert(p < 32u32);
        assert(1u32 << (k % 32) == 1u32 << p);
        assert(c & (1u32 << p) == 0u32) by (bit_vector)
            requires
                p < 32u32,
                c == 0u32,
        ;
    }
}


/// After setting, the bit is set: `(old | 1<<p) & 1<<p != 0` (p < 32).
pub proof fn lemma_or_bit_set(old: u32, p: u32)
    requires
        p < 32u32,
    ensures
        ((old | (1u32 << p)) & (1u32 << p)) != 0u32,
{
    assert(((old | (1u32 << p)) & (1u32 << p)) != 0u32) by (bit_vector)
        requires
            p < 32u32,
    ;
}


/// Setting does not affect other bits: for p != q, `(old | 1<<p) & 1<<q == old & 1<<q`.
pub proof fn lemma_or_bit_clear(old: u32, p: u32, q: u32)
    requires
        p < 32u32,
        q < 32u32,
        p != q,
    ensures
        ((old | (1u32 << p)) & (1u32 << q)) == (old & (1u32 << q)),
{
    assert(((old | (1u32 << p)) & (1u32 << q)) == (old & (1u32 << q))) by (bit_vector)
        requires
            p < 32u32,
            q < 32u32,
            p != q,
    ;
}


/// After clearing, the bit is clear: `(old & !(1<<p)) & 1<<p == 0` (p < 32).
pub proof fn lemma_and_bit_clear(old: u32, p: u32)
    requires
        p < 32u32,
    ensures
        ((old & !(1u32 << p)) & (1u32 << p)) == 0u32,
{
    assert(((old & !(1u32 << p)) & (1u32 << p)) == 0u32) by (bit_vector)
        requires
            p < 32u32,
    ;
}


/// Clearing does not affect other bits: for p != q, `(old & !1<<p) & 1<<q == old & 1<<q`.
pub proof fn lemma_and_bit_clear_other(old: u32, p: u32, q: u32)
    requires
        p < 32u32,
        q < 32u32,
        p != q,
    ensures
        ((old & !(1u32 << p)) & (1u32 << q)) == (old & (1u32 << q)),
{
    assert(((old & !(1u32 << p)) & (1u32 << q)) == (old & (1u32 << q))) by (bit_vector)
        requires
            p < 32u32,
            q < 32u32,
            p != q,
    ;
}


/// OR left-distributes over AND (the membership-semantics core of union).
pub proof fn lemma_or_and_distrib(a: u32, b: u32, p: u32)
    ensures
        ((a | b) & p) == ((a & p) | (b & p)),
{
    assert(((a | b) & p) == ((a & p) | (b & p))) by (bit_vector);
}


/// NOT bit semantics (the membership-semantics core of complement):
/// `(x^all-ones) & p == p ^ (x&p)` (u32 NOT is a full-width inversion; the special-case bridge takes p = a single-point mask).
pub proof fn lemma_not_bit(x: u32, p: u32)
    ensures
        ((x ^ 4294967295u32) & p) == (p ^ (x & p)),
{
    assert(((x ^ 4294967295u32) & p) == (p ^ (x & p))) by (bit_vector);
}


/// All-ones bit state: x == 0xFFFFFFFF => any bit p (< 32) is set.
pub proof fn lemma_all_ones_bit(x: u32, p: u32)
    requires
        p < 32u32,
        x == 4294967295u32,
    ensures
        (x & (1u32 << p)) != 0u32,
{
    assert((x & (1u32 << p)) != 0u32) by (bit_vector)
        requires
            p < 32u32,
            x == 4294967295u32,
    ;
}


/// A single-point shift power is nonzero: 1 << p != 0 (p < 32).
pub proof fn lemma_bit_nonzero(p: u32)
    requires
        p < 32u32,
    ensures
        (1u32 << p) != 0u32,
{
    assert((1u32 << p) != 0u32) by (bit_vector)
        requires
            p < 32u32,
    ;
}


/// Single pointness: x & (1<<p) can only be 0 or 1<<p.
pub proof fn lemma_bit_either(x: u32, p: u32)
    requires
        p < 32u32,
    ensures
        (x & (1u32 << p)) == 0u32 || (x & (1u32 << p)) == (1u32 << p),
{
    assert((x & (1u32 << p)) == 0u32 || (x & (1u32 << p)) == (1u32 << p)) by (bit_vector)
        requires
            p < 32u32,
    ;
}


/// Inverted bit state (u32 level): ((x^all-ones) & bit) != 0 <=> (x & bit) == 0,
/// where bit = 1<<p (p < 32, a single-point bit).
pub proof fn lemma_not_bit_bool(x: u32, p: u32)
    requires
        p < 32u32,
    ensures
        ((x ^ 4294967295u32) & (1u32 << p)) != 0u32 <==> (x & (1u32 << p)) == 0u32,
{
    assert(((x ^ 4294967295u32) & (1u32 << p)) != 0u32 <==> (x & (1u32 << p)) == 0u32)
        by (bit_vector)
        requires
            p < 32u32,
    ;
}


/// Membership-face theorem of `add`: new sets only bit bi%32 in chunk bi/32.
pub proof fn lemma_add_membership(old: Seq<u32>, new: Seq<u32>, b: u8)
    requires
        (b as int) < 128,
        old.len() == 4,
        new.len() == 4,
        forall|j: int| 0 <= j < 4 ==> new[j] == (if j == (b as int) / 32 {
            old[(b as int) / 32] | (1u32 << ((b as int) % 32))
        } else {
            old[j]
        }),
    ensures
        forall|k: int| 0 <= k < 128 ==> bit_at(new, k)
            == (bit_at(old, k) || k == b as int),
{
    assert forall|k: int| 0 <= k < 128 implies bit_at(new, k)
        == (bit_at(old, k) || k == b as int) by {
        if (k / 32) == ((b as int) / 32) {
            if k == b as int {
                lemma_or_bit_set(old[(b as int) / 32], ((b as int) % 32) as u32);
            } else {
                lemma_or_bit_clear(
                    old[(b as int) / 32],
                    ((b as int) % 32) as u32,
                    (k % 32) as u32,
                );
            }
        }
    };
}


/// Membership-face theorem of `remove` (the dual).
pub proof fn lemma_remove_membership(old: Seq<u32>, new: Seq<u32>, b: u8)
    requires
        (b as int) < 128,
        old.len() == 4,
        new.len() == 4,
        forall|j: int| 0 <= j < 4 ==> new[j] == (if j == (b as int) / 32 {
            old[(b as int) / 32] & !(1u32 << ((b as int) % 32))
        } else {
            old[j]
        }),
    ensures
        forall|k: int| 0 <= k < 128 ==> bit_at(new, k)
            == (bit_at(old, k) && k != b as int),
{
    assert forall|k: int| 0 <= k < 128 implies bit_at(new, k)
        == (bit_at(old, k) && k != b as int) by {
        if (k / 32) == ((b as int) / 32) {
            if k == b as int {
                lemma_and_bit_clear(old[(b as int) / 32], ((b as int) % 32) as u32);
            } else {
                lemma_and_bit_clear_other(
                    old[(b as int) / 32],
                    ((b as int) % 32) as u32,
                    (k % 32) as u32,
                );
            }
        }
    };
}


/// Membership-face theorem of `union`: new chunk j = a chunk j OR b chunk j.
pub proof fn lemma_union_membership(a: Seq<u32>, b: Seq<u32>, new: Seq<u32>)
    requires
        a.len() == 4,
        b.len() == 4,
        new.len() == 4,
        forall|j: int| #![trigger new[j]] 0 <= j < 4 ==> new[j] == (a[j] | b[j]),
    ensures
        forall|k: int| 0 <= k < 128 ==> bit_at(new, k)
            == (bit_at(a, k) || bit_at(b, k)),
{
    assert forall|k: int| 0 <= k < 128 implies bit_at(new, k)
        == (bit_at(a, k) || bit_at(b, k)) by {
        let achunk: u32 = a[k / 32];
        let bchunk: u32 = b[k / 32];
        assert(new[k / 32] == (achunk | bchunk));
        let p = (k % 32) as u32;
        assert(p < 32u32);
        let bit = 1u32 << p;
        assert(1u32 << (k % 32) == bit);
        lemma_or_and_distrib(achunk, bchunk, bit);
        // Zero-OR resolution:
        assert(((achunk & bit) | (bchunk & bit)) == 0u32
            <==> ((achunk & bit) == 0u32 && (bchunk & bit) == 0u32)) by (bit_vector);
    };
}


/// Membership-face theorem of `complement`: new chunk j = a chunk j XOR all-ones.
pub proof fn lemma_complement_membership(a: Seq<u32>, new: Seq<u32>)
    requires
        a.len() == 4,
        new.len() == 4,
        forall|j: int| 0 <= j < 4 ==> new[j] == (a[j] ^ 4294967295u32),
    ensures
        forall|k: int| 0 <= k < 128 ==> bit_at(new, k) == !bit_at(a, k),
{
    assert forall|k: int| 0 <= k < 128 implies bit_at(new, k) == (!bit_at(a, k)) by {
        let p = (k % 32) as u32;
        assert(p < 32u32);
        let achunk: u32 = a[k / 32];
        assert(new[k / 32] == achunk ^ 4294967295u32);
        assert(1u32 << (k % 32) == 1u32 << p);
        lemma_bit_either(achunk, p);
        lemma_not_bit_bool(achunk, p);
        lemma_bit_nonzero(p);
    };
}


/// Origin: ascii_set.rs:102-106, the doc contract:
/// "The set of 0x00 to 0x1F (C0 controls), and 0x7F (DEL).
///  Note that this includes the newline and tab characters,
///  but not the space 0x20."
/// Also covers the 5 upstream static_assert! items (ascii_set.rs:126-132).
pub proof fn lemma_controls()
    ensures
        forall|k: int| 0 <= k < 128 ==> bit_at(CONTROLS.mask@, k) == (k <= 0x1F || k == 0x7F),
{
    assert forall|k: int| 0 <= k < 128 implies bit_at(CONTROLS.mask@, k)
        == (k <= 0x1F || k == 0x7F) by {
        if k <= 0x1F {
            assert((k / 32) == 0);
            lemma_all_ones_bit(4294967295u32, (k % 32) as u32);
        } else if k == 0x7F {
            assert((k / 32) == 3);
            assert((k % 32) == 31);
            // chunk 3 == 1<<31, exactly bit 31 set
            assert((2147483648u32 & (1u32 << 31)) != 0u32) by (bit_vector);
        } else {
            if (k / 32) == 3 {
                let kpos = (k % 32) as u32;
                assert(kpos <= 0x1Fu32);
                assert(1u32 << (k % 32) == 1u32 << kpos);
                assert(CONTROLS.mask@[3] == 2147483648u32);
                assert((2147483648u32 & (1u32 << kpos)) == 0u32) by (bit_vector)
                    requires
                        kpos < 31u32,
                ;
            } else {
                let kpos = (k % 32) as u32;
                assert(1u32 << (k % 32) == 1u32 << kpos);
                assert(CONTROLS.mask@[k / 32] == 0u32);
                assert((0u32 & (1u32 << kpos)) == 0u32) by (bit_vector);
            }
        }
    };
}


/// Doc-contract lemma: added_by_non_alnum is exactly the non-alphanumeric characters in [0x20,0x7E].
pub proof fn lemma_added_list_concrete()
    ensures
        forall|k: int| 0 <= k <= 0x7F ==> (added_by_non_alnum(k)
            == (0x20 <= k <= 0x7E && !is_alnum(k))),
{
}


/// CONTROLS union list face => doc-contract membership face (invoked at the exec tail).
pub proof fn lemma_non_alnum_union(cur: AsciiSet)
    requires
        forall|k: int| 0 <= k < 128 ==> bit_at(cur.mask@, k)
            == ((k <= 0x1F || k == 0x7F) || added_by_non_alnum(k)),
        cur.mask@.len() == 4,
    ensures
        forall|k: int| 0 <= k < 128 ==> bit_at(cur.mask@, k) == (!is_alnum(k)),
{
    assert forall|k: int| 0 <= k < 128 implies bit_at(cur.mask@, k) == (!is_alnum(k)) by {
        lemma_added_list_concrete();
    }
}


}
