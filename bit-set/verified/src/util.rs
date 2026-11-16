//! bit-set 0.11.1 utility family (set/src/util.rs) -- Verus translation.
//!
//! Shares the crate-root BitVec mount (../lib.rs; single source of
//! verified BitVec facts, B = u32). blocks_for_bits has its spec/exec
//! translation on the bit-vec side already; the mounted entry is reused
//! as the definition, nothing is re-copied.

use vstd::prelude::*;

verus! {

use super::bitvec_lib::{BitVec, blocks_for_bits_exec, inv};

/// Origin Rust: pub(crate) fn blocks_for_bits<B: BitBlock>(bits: usize) -> usize {
///     if bits % B::bits() == 0 {
///         bits / B::bits()
///     } else {
///         bits / B::bits() + 1
///     }
/// } (set/src/util.rs:8-22; B = u32 materialization, B::bits() == 32.
/// The body comment on the branch shape (the "17 bits" rationale) rides
/// the mounted bit-vec entry, whose translation is identical -- reused.)
/// Upstream doc (util.rs:7-7):
///   Computes how many blocks are needed to store that many bits
pub(crate) exec fn blocks_for_bits(bits: usize) -> (r: usize)
    ensures
        r == super::bitvec_lib::blocks_for_bits(bits),
{
    /* Origin Rust: the if/else blocks-for-bits body (set/src/util.rs:17-21);
       delegated to the mounted verified entry with the same body (the
       generic B axis materialized to u32). */
    blocks_for_bits_exec(bits)
}

/// Origin Rust: type MatchWords<'a, B: BitBlock> =
///     Chain<Enumerate<Blocks<'a, B>>, Skip<Take<Enumerate<Repeat<B>>>>>
///     (set/src/util.rs:4-5)
/// The Chain/Enumerate/Skip/Take/Repeat adapter types have no spec-level
/// materialization (iterator-adapter traits cannot be stated in Verus),
/// so match_words materializes as the index form of the padding role the
/// upstream comment documents: over the range 0..max(block counts), the
/// word of a padded stream at index i is the side's own block when i is
/// inside its block count, and zero beyond it.
///
/// the padded word at block index i: the own block inside the block
/// count, zero padding beyond it (one padded match_words stream).
pub open spec fn padded_word(bv: &BitVec, i: int) -> u32 {
    if 0 <= i < bv.storage@.len() { bv.storage@[i] } else { 0u32 }
}

/// the padded stream range: both padded words share the longer side's
/// block count, so the pair is stated for 0..max(a's, b's block counts).
pub(crate) closed spec fn match_words_bound(a: &BitVec, b: &BitVec) -> int {
    if a.storage@.len() < b.storage@.len() {
        (b.storage@.len() as int)
    } else {
        (a.storage@.len() as int)
    }
}

/// Origin Rust: pub(crate) fn match_words<'a, 'b, B: BitBlock>(
///         a: &BitVec<B>,
///         b: &BitVec<B>,
///     ) -> (MatchWords<'a, B>, MatchWords<'b, B>) {
///     let a_len = a.storage().len();
///     let b_len = b.storage().len();
///
///     // have to uselessly pretend to pad the longer one for type matching
///     if a_len < b_len {
///         (a.blocks().enumerate()
///              .chain(iter::repeat(B::zero()).enumerate().take(b_len).skip(a_len)),
///          b.blocks().enumerate()
///              .chain(iter::repeat(B::zero()).enumerate().take(0).skip(0)))
///     } else {
///         (a.blocks().enumerate()
///              .chain(iter::repeat(B::zero()).enumerate().take(0).skip(0)),
///          b.blocks().enumerate()
///              .chain(iter::repeat(B::zero()).enumerate().take(a_len).skip(b_len)))
///     }
/// } (set/src/util.rs:27-54)
/// Upstream comment (set/src/util.rs:24-26):
///   Take two BitVec's, and return iterators of their words, where the shorter one
///   has been padded with 0's
/// Index-form equivalent: the returned stream pair materialized as the
/// paired word at block index i, with out-of-range reads yielding the
/// zero padding (the enumerated adapter indices are the block indices).
pub(crate) exec fn match_words_at(a: &BitVec, b: &BitVec, i: usize) -> (p: (u32, u32))
    requires
        (i as int) < match_words_bound(a, b),
    ensures
        p.0 == padded_word(a, i as int),
        p.1 == padded_word(b, i as int),
{
    let a_len = a.storage().len();
    let b_len = b.storage().len();
    let wa: u32 = if i < a_len { a.storage()[i] } else { 0u32 };
    let wb: u32 = if i < b_len { b.storage()[i] } else { 0u32 };
    proof {
        if i < a_len {
            assert(padded_word(a, i as int) == a.storage@[i as int]);
        } else {
            assert(padded_word(a, i as int) == 0u32);
        }
        if i < b_len {
            assert(padded_word(b, i as int) == b.storage@[i as int]);
        } else {
            assert(padded_word(b, i as int) == 0u32);
        }
        assert(wa == padded_word(a, i as int));
        assert(wb == padded_word(b, i as int));
    }
    (wa, wb)
}

/// the padding role, unpacked: inside a side's block count the stream
/// word is the own block, beyond it the zero padding (the consumers'
/// usage contract of the index form).
pub(crate) proof fn lemma_padded_word_range(bv: &BitVec, i: usize)
    requires
        inv(bv),
    ensures
        (i as int) < bv.storage@.len() ==> padded_word(bv, i as int)
            == bv.storage@[i as int],
        (i as int) >= bv.storage@.len() ==> padded_word(bv, i as int) == 0u32,
{
    // the definition's two branches
}

} // verus!

// Verification driver (single-file driver form).
fn main() {}
