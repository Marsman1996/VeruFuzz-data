//! faest 0.3.0 -- Verus DRAFT + DEFERRED (D-FA10w-1) of the
//! src/witness.rs round-loop layer, batch FA10 wave2 (mounted by the
//! fa10w-driver panel; the wave-1 carry-over is closing here).
//!
//! This file holds the transcribed bodies of the three deep-loop
//! exec twins of upstream witness.rs (the save_non_lin_bits window
//! loop, the round_with_save round loop, and the aes_extendedwitness
//! top assembler) together with their spec faces (nl_written /
//! own_written sum family, circ_bytes / circ_rest / circ_done budget
//! family, the definitional unfold lemmas, the per-row fold ladders
//! -- nl AND circ -- and the row byte-budget identity
//! row_budget_ladder). The wave-1 continue-here kit's rules are
//! applied and extended as follows (every route probe- or
//! round-confirmed; see the wave-2 batch notes):
//! - probe2 d/e shape (offset-write writes): every write loop carries
//!   BOTH the @@-view total bound and the runtime running bound.
//! - the wave-1 draft's `(kc != 6 || j % 3 != 2) ==> idx + 4 <= len`
//!   pre-bound invariant is NOT maintainable (it would have to hold
//!   before the loop even when the window is empty); the write bound
//!   is instead DERIVED inside each write lane from the
//!   nl_written_split decomposition plus the nonneg lemmas, and the
//!   KNOWN-unprovable-at-entry clauses were dropped.
//! - `8 * (j + 2) <= kb.len()` inside round_with_save fails at the
//!   LAST round (j+2 overruns 8*R by one window exactly when the
//!   loop exits); the invariant is weakened to the guarded form
//!   `(j < rounds - 1) ==> 8 * (j + 2) <= kb.len()`.
//! - the len invariants behind the callee calls save_key_bits /
//!   save_non_lin_bits / round_with_save need the callees to ENSURE
//!   length preservation. save_non_lin_bits and round_with_save
//!   gained `final(witness).len() == old(witness).len()` ensures
//!   here; save_key_bits (wave-1's src/witness.rs, outside this
//!   wave's edit scope) does not carry the clause, so the top
//!   assembler fronts the wrapper save_key_bits_len (same
//!   lowered loop body, probe2 d/e shapes, length clause added).
//! - the frame invariants take an explicit `#![trigger old(witness)[k]]`
//!   (the auto-chosen trigger on the current view does not fire on
//!   the end-of-body obligation, which mentions only the post-call
//!   and entry views; the entry-view trigger chains both).
//! - requires nails the row-domain faces the top loop re-carries:
//!   kc <= 8, rounds < usize::MAX / 16, and is EM ==> InputSize ==
//!   LambdaBytes (the EM rows' public-input secret-key copy).

use vstd::prelude::*;
use super::parameter_tower::{
    OWF128EM_BETA, OWF128EM_IS_EM, OWF128EM_L_BYTES, OWF128EM_NK, OWF128EM_NST, OWF128EM_R,
    OWF128EM_SKE, OWF128_BETA, OWF128_IS_EM, OWF128_L_BYTES, OWF128_NK, OWF128_NST, OWF128_R,
    OWF128_SKE, OWF192EM_BETA, OWF192EM_IS_EM, OWF192EM_L_BYTES, OWF192EM_NK, OWF192EM_NST,
    OWF192EM_R, OWF192EM_SKE, OWF192_BETA, OWF192_IS_EM, OWF192_L_BYTES, OWF192_NK, OWF192_NST,
    OWF192_R, OWF192_SKE, OWF256EM_BETA, OWF256EM_IS_EM, OWF256EM_L_BYTES, OWF256EM_NK,
    OWF256EM_NST, OWF256EM_R, OWF256EM_SKE, OWF256_BETA, OWF256_IS_EM, OWF256_L_BYTES, OWF256_NK,
    OWF256_NST, OWF256_R, OWF256_SKE,
};
use super::rijndael_32::{
    bitslice, inv_bitslice, mix_columns_0, convert_from_batchblocks_word,
    rijndael_add_round_key, rijndael_shift_rows_1, rijndael_sub_bytes, State,
};
use super::small_fields::{gf8_mul, gf8_mul_spec, gf8_square};
use super::witness::{
    nl_start_off, nl_blocks, RowCfg, store_invnorm_state, ROW_OW128, ROW_OW128EM, ROW_OW192,
    ROW_OW192EM, ROW_OW256, ROW_OW256EM, OW128_KB_WORDS, OW192_KB_WORDS, OW192EM_KB_WORDS,
    OW256_KB_WORDS, OW256EM_KB_WORDS, copy4, kb_covers_rounds_identity,
    kb_covers_nonlin_identity,
};

verus! {


/// The written-byte budget identity: LBytes == LambdaBytes +
/// non_lin_written + Beta * (even*to_take*2 + odd*NSt*4) at every
/// row, where even = ceil((R-1)/2) j-slots of the store_invnorm_state
/// pass and odd = floor((R-1)/2) j-slots of the raw-word pass (the
/// save_non_lin_bits NK==6 rows write 8 of the 12 window blocks --
/// the j%3==2 blocks are skipped by upstream's branch shape).
/// Checked numbers -- OWF128: 16 + 40 + 1*(5*4*2 + 4*4*4) = 160;
/// OWF192: 24 + 32 + 2*(6*4*2 + 5*4*4) = 312; OWF256: 32 + 52 +
/// 2*(7*4*2 + 6*4*4) = 388; OWF128EM: 16 + 0 + 1*(5*4*2 + 4*4*4) =
/// 120; OWF192EM: 24 + 0 + 1*(6*6*2 + 5*6*4) = 216; OWF256EM: 32 +
/// 0 + 1*(7*8*2 + 6*8*4) = 336.
pub proof fn l_bytes_composition_identity() {
    nl_written_ladder_owf128();
    nl_written_ladder_owf192();
    nl_written_ladder_owf256();
    row_budget_ladder();
}

/// The round-pass byte count of one round_with_save call at a row:
/// the full round-tail sum of one beta sweep (alias of the
/// circ_rest face at zero; the closed even/odd form of upstream's
/// budget is asserted per row in row_budget_ladder).
pub open spec fn circ_bytes(row: RowCfg) -> int {
    circ_rest(row, 0)
}

/// The non-EM save_non_lin_bits written-byte count (the four
/// written lanes: NK!=6 -> all blocks write 4 bytes (inside[0]);
/// NK==6 -> j%3==0 writes inside[0], j%3==1 writes inside[2], j%3==2
/// writes nothing).
pub open spec fn nl_written(kc: int, ske: int) -> int {
    let start = nl_start_off(kc);
    let nlb = nl_blocks(kc, ske);
    sum_nl_written(kc, start, start + nlb)
}

pub open spec fn sum_nl_written(kc: int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi {
        0
    } else {
        own_written(kc, hi - 1) + sum_nl_written(kc, lo, hi - 1)
    }
}


// ---------------------------------------------------------------------------
// Definitional unfold lemmas (the FA2 lemma_mul8_bits_unfold form):
// the spec function symbols need an explicit call-site bridge per
// recursion level; the per-row fold ladders below climb these.
// ---------------------------------------------------------------------------

/// One-level peel of sum_nl_written at a non-empty window.
pub proof fn lemma_sum_nl_unfold(kc: int, lo: int, hi: int)
    requires
        lo < hi,
    ensures
        sum_nl_written(kc, lo, hi)
            == own_written(kc, hi - 1) + sum_nl_written(kc, lo, hi - 1),
{
}

/// Empty-window peel.
pub proof fn lemma_sum_nl_empty(kc: int, lo: int, hi: int)
    requires
        hi <= lo,
    ensures
        sum_nl_written(kc, lo, hi) == 0,
{
}

/// own_written at an anything-but-6 column count: constant 4.
pub proof fn lemma_own_written_kc_not6(kc: int, j: int)
    requires
        kc != 6,
    ensures
        own_written(kc, j) == 4,
{
}

/// own_written at kc==6, lane j%3==0.
pub proof fn lemma_own_written_6_r0(j: int)
    requires
        j % 3 == 0,
    ensures
        own_written(6, j) == 4,
{
}

/// own_written at kc==6, lane j%3==1.
pub proof fn lemma_own_written_6_r1(j: int)
    requires
        j % 3 == 1,
    ensures
        own_written(6, j) == 4,
{
}

/// own_written at kc==6, lane j%3==2: the silent lane.
pub proof fn lemma_own_written_6_r2(j: int)
    requires
        j % 3 == 2,
    ensures
        own_written(6, j) == 0,
{
}

/// Nonneg of the own_written family (all lanes return 4 or 0).
proof fn lemma_own_written_nonneg(kc: int, j: int)
    ensures
        0 <= own_written(kc, j),
{
    if kc != 6 {
        lemma_own_written_kc_not6(kc, j);
    } else if j % 3 == 0 {
        lemma_own_written_6_r0(j);
    } else if j % 3 == 1 {
        lemma_own_written_6_r1(j);
    } else {
        lemma_own_written_6_r2(j);
    }
}

/// Nonneg of the window sum, by induction on the window top.
pub proof fn lemma_sum_nl_nonneg(kc: int, lo: int, hi: int)
    ensures
        0 <= sum_nl_written(kc, lo, hi),
    decreases hi - lo,
{
    if lo < hi {
        lemma_sum_nl_nonneg(kc, lo, hi - 1);
        lemma_sum_nl_unfold(kc, lo, hi);
        lemma_own_written_nonneg(kc, hi - 1);
    }
}

/// Nonneg of nl_written (the entry bound of save_non_lin_bits).
pub proof fn lemma_nl_written_nonneg(kc: int, ske: int)
    ensures
        0 <= nl_written(kc, ske),
{
    assert(nl_written(kc, ske)
        == sum_nl_written(kc, nl_start_off(kc), nl_start_off(kc) + nl_blocks(kc, ske)));
    lemma_sum_nl_nonneg(kc, nl_start_off(kc), nl_start_off(kc) + nl_blocks(kc, ske));
}

// ---------------------------------------------------------------------------
// Per-row fold ladders: one assert per unroll level so each step needs
// only a single definitional peel (the recursion's default fuel does
// not unfold ten or more levels at once).
// ---------------------------------------------------------------------------

/// nl_written(4, 40) == 40 (ten all-writing window blocks at kc==4).
pub proof fn nl_written_ladder_owf128()
    ensures
        nl_written(4, 40) == 40,
{
    assert(nl_written(4, 40) == sum_nl_written(4, 1, 11));
    assert(nl_start_off(4) == 1);
    assert(nl_blocks(4, 40) == 10);
    assert(sum_nl_written(4, 1, 11) == sum_nl_written(4, 1, 10) + 4);
    assert(sum_nl_written(4, 1, 10) == sum_nl_written(4, 1, 9) + 4);
    assert(sum_nl_written(4, 1, 9) == sum_nl_written(4, 1, 8) + 4);
    assert(sum_nl_written(4, 1, 8) == sum_nl_written(4, 1, 7) + 4);
    assert(sum_nl_written(4, 1, 7) == sum_nl_written(4, 1, 6) + 4);
    assert(sum_nl_written(4, 1, 6) == sum_nl_written(4, 1, 5) + 4);
    assert(sum_nl_written(4, 1, 5) == sum_nl_written(4, 1, 4) + 4);
    assert(sum_nl_written(4, 1, 4) == sum_nl_written(4, 1, 3) + 4);
    assert(sum_nl_written(4, 1, 3) == sum_nl_written(4, 1, 2) + 4);
    assert(sum_nl_written(4, 1, 2) == sum_nl_written(4, 1, 1) + 4);
    assert(sum_nl_written(4, 1, 1) == 0);
    assert(sum_nl_written(4, 1, 11) == 40);
}

/// nl_written(6, 32) == 32 (twelve window blocks at kc==6, the j%3==2
/// lanes silent: j=2,5,8,11 write nothing, eight blocks write 4).
pub proof fn nl_written_ladder_owf192()
    ensures
        nl_written(6, 32) == 32,
{
    assert(nl_start_off(6) == 1);
    assert(nl_blocks(6, 32) == 12);
    assert(nl_written(6, 32) == sum_nl_written(6, 1, 13));
    lemma_own_written_6_r0(12);
    lemma_own_written_6_r2(11);
    lemma_own_written_6_r1(10);
    lemma_own_written_6_r0(9);
    lemma_own_written_6_r2(8);
    lemma_own_written_6_r1(7);
    lemma_own_written_6_r0(6);
    lemma_own_written_6_r2(5);
    lemma_own_written_6_r1(4);
    lemma_own_written_6_r0(3);
    lemma_own_written_6_r2(2);
    lemma_own_written_6_r1(1);
    // top-down peels with the per-lane own facts
    assert(sum_nl_written(6, 1, 13) == sum_nl_written(6, 1, 12) + own_written(6, 12));
    assert(sum_nl_written(6, 1, 12) == sum_nl_written(6, 1, 11) + own_written(6, 11));
    assert(sum_nl_written(6, 1, 11) == sum_nl_written(6, 1, 10) + own_written(6, 10));
    assert(sum_nl_written(6, 1, 10) == sum_nl_written(6, 1, 9) + own_written(6, 9));
    assert(sum_nl_written(6, 1, 9) == sum_nl_written(6, 1, 8) + own_written(6, 8));
    assert(sum_nl_written(6, 1, 8) == sum_nl_written(6, 1, 7) + own_written(6, 7));
    assert(sum_nl_written(6, 1, 7) == sum_nl_written(6, 1, 6) + own_written(6, 6));
    assert(sum_nl_written(6, 1, 6) == sum_nl_written(6, 1, 5) + own_written(6, 5));
    assert(sum_nl_written(6, 1, 5) == sum_nl_written(6, 1, 4) + own_written(6, 4));
    assert(sum_nl_written(6, 1, 4) == sum_nl_written(6, 1, 3) + own_written(6, 3));
    assert(sum_nl_written(6, 1, 3) == sum_nl_written(6, 1, 2) + own_written(6, 2));
    assert(sum_nl_written(6, 1, 2) == sum_nl_written(6, 1, 1) + own_written(6, 1));
    assert(sum_nl_written(6, 1, 1) == 0);
    assert(sum_nl_written(6, 1, 13) == 32);
}

/// nl_written(8, 52) == 52 (thirteen all-writing window blocks at
/// kc==8).
pub proof fn nl_written_ladder_owf256()
    ensures
        nl_written(8, 52) == 52,
{
    assert(nl_start_off(8) == 2);
    assert(nl_blocks(8, 52) == 13);
    assert(nl_written(8, 52) == sum_nl_written(8, 2, 15));
    assert(sum_nl_written(8, 2, 15) == sum_nl_written(8, 2, 14) + 4);
    assert(sum_nl_written(8, 2, 14) == sum_nl_written(8, 2, 13) + 4);
    assert(sum_nl_written(8, 2, 13) == sum_nl_written(8, 2, 12) + 4);
    assert(sum_nl_written(8, 2, 12) == sum_nl_written(8, 2, 11) + 4);
    assert(sum_nl_written(8, 2, 11) == sum_nl_written(8, 2, 10) + 4);
    assert(sum_nl_written(8, 2, 10) == sum_nl_written(8, 2, 9) + 4);
    assert(sum_nl_written(8, 2, 9) == sum_nl_written(8, 2, 8) + 4);
    assert(sum_nl_written(8, 2, 8) == sum_nl_written(8, 2, 7) + 4);
    assert(sum_nl_written(8, 2, 7) == sum_nl_written(8, 2, 6) + 4);
    assert(sum_nl_written(8, 2, 6) == sum_nl_written(8, 2, 5) + 4);
    assert(sum_nl_written(8, 2, 5) == sum_nl_written(8, 2, 4) + 4);
    assert(sum_nl_written(8, 2, 4) == sum_nl_written(8, 2, 3) + 4);
    assert(sum_nl_written(8, 2, 3) == sum_nl_written(8, 2, 2) + 4);
    assert(sum_nl_written(8, 2, 2) == 0);
    assert(sum_nl_written(8, 2, 15) == 52);
}

// ---------------------------------------------------------------------------
// Per-row circ fold ladders (the FA10w-1 pitfall class applied to the
// round budget): circ_bytes(row) -- circ_rest(row, 0) -- does not
// fold on demand either; each level needs one lemma_rest_unfold plus
// the concrete circ_bytes_at value. The written bytes per round j:
// even j writes 2 per to_take word pair (to_take = 4 non-EM, row.kc
// EM), odd j writes row.bc words of 4 bytes.
// ---------------------------------------------------------------------------

/// circ_bytes(ROW_OW128) == 104: rounds 10, to_take 4, bc 4 -- even
/// rounds j=0,2,4,6,8 write 8, odd rounds j=1,3,5,7 write 16 (the
/// wave-1 numbers 5*4*2 + 4*4*4).
pub proof fn circ_ladder_owf128()
    ensures
        circ_bytes(ROW_OW128) == 104,
{
    let row = ROW_OW128;
    assert(row.rounds == 10);
    assert(row.bc == 4);
    assert(row.kc == 4);
    assert(!row.is_em);
    assert(circ_bytes_at(row, 8) == 8);
    assert(circ_bytes_at(row, 7) == 16);
    assert(circ_bytes_at(row, 6) == 8);
    assert(circ_bytes_at(row, 5) == 16);
    assert(circ_bytes_at(row, 4) == 8);
    assert(circ_bytes_at(row, 3) == 16);
    assert(circ_bytes_at(row, 2) == 8);
    assert(circ_bytes_at(row, 1) == 16);
    assert(circ_bytes_at(row, 0) == 8);
    lemma_rest_zero(row, 9);
    lemma_rest_unfold(row, 8);
    assert(circ_rest(row, 8) == 8);
    lemma_rest_unfold(row, 7);
    assert(circ_rest(row, 7) == 24);
    lemma_rest_unfold(row, 6);
    assert(circ_rest(row, 6) == 32);
    lemma_rest_unfold(row, 5);
    assert(circ_rest(row, 5) == 48);
    lemma_rest_unfold(row, 4);
    assert(circ_rest(row, 4) == 56);
    lemma_rest_unfold(row, 3);
    assert(circ_rest(row, 3) == 72);
    lemma_rest_unfold(row, 2);
    assert(circ_rest(row, 2) == 80);
    lemma_rest_unfold(row, 1);
    assert(circ_rest(row, 1) == 96);
    lemma_rest_unfold(row, 0);
    assert(circ_rest(row, 0) == 104);
    assert(circ_bytes(row) == circ_rest(row, 0));
}

/// circ_bytes(ROW_OW192) == 128: rounds 12, to_take 4, bc 4 -- even
/// rounds j=0,2,..,10 write 8, odd rounds j=1,3,..,9 write 16.
pub proof fn circ_ladder_owf192()
    ensures
        circ_bytes(ROW_OW192) == 128,
{
    let row = ROW_OW192;
    assert(row.rounds == 12);
    assert(row.bc == 4);
    assert(row.kc == 6);
    assert(!row.is_em);
    assert(circ_bytes_at(row, 10) == 8);
    assert(circ_bytes_at(row, 9) == 16);
    assert(circ_bytes_at(row, 8) == 8);
    assert(circ_bytes_at(row, 7) == 16);
    assert(circ_bytes_at(row, 6) == 8);
    assert(circ_bytes_at(row, 5) == 16);
    assert(circ_bytes_at(row, 4) == 8);
    assert(circ_bytes_at(row, 3) == 16);
    assert(circ_bytes_at(row, 2) == 8);
    assert(circ_bytes_at(row, 1) == 16);
    assert(circ_bytes_at(row, 0) == 8);
    lemma_rest_zero(row, 11);
    lemma_rest_unfold(row, 10);
    assert(circ_rest(row, 10) == 8);
    lemma_rest_unfold(row, 9);
    assert(circ_rest(row, 9) == 24);
    lemma_rest_unfold(row, 8);
    assert(circ_rest(row, 8) == 32);
    lemma_rest_unfold(row, 7);
    assert(circ_rest(row, 7) == 48);
    lemma_rest_unfold(row, 6);
    assert(circ_rest(row, 6) == 56);
    lemma_rest_unfold(row, 5);
    assert(circ_rest(row, 5) == 72);
    lemma_rest_unfold(row, 4);
    assert(circ_rest(row, 4) == 80);
    lemma_rest_unfold(row, 3);
    assert(circ_rest(row, 3) == 96);
    lemma_rest_unfold(row, 2);
    assert(circ_rest(row, 2) == 104);
    lemma_rest_unfold(row, 1);
    assert(circ_rest(row, 1) == 120);
    lemma_rest_unfold(row, 0);
    assert(circ_rest(row, 0) == 128);
    assert(circ_bytes(row) == circ_rest(row, 0));
}

/// circ_bytes(ROW_OW256) == 152: rounds 14, to_take 4, bc 4 -- even
/// rounds j=0,2,..,12 write 8, odd rounds j=1,3,..,11 write 16.
pub proof fn circ_ladder_owf256()
    ensures
        circ_bytes(ROW_OW256) == 152,
{
    let row = ROW_OW256;
    assert(row.rounds == 14);
    assert(row.bc == 4);
    assert(row.kc == 8);
    assert(!row.is_em);
    assert(circ_bytes_at(row, 12) == 8);
    assert(circ_bytes_at(row, 11) == 16);
    assert(circ_bytes_at(row, 10) == 8);
    assert(circ_bytes_at(row, 9) == 16);
    assert(circ_bytes_at(row, 8) == 8);
    assert(circ_bytes_at(row, 7) == 16);
    assert(circ_bytes_at(row, 6) == 8);
    assert(circ_bytes_at(row, 5) == 16);
    assert(circ_bytes_at(row, 4) == 8);
    assert(circ_bytes_at(row, 3) == 16);
    assert(circ_bytes_at(row, 2) == 8);
    assert(circ_bytes_at(row, 1) == 16);
    assert(circ_bytes_at(row, 0) == 8);
    lemma_rest_zero(row, 13);
    lemma_rest_unfold(row, 12);
    assert(circ_rest(row, 12) == 8);
    lemma_rest_unfold(row, 11);
    assert(circ_rest(row, 11) == 24);
    lemma_rest_unfold(row, 10);
    assert(circ_rest(row, 10) == 32);
    lemma_rest_unfold(row, 9);
    assert(circ_rest(row, 9) == 48);
    lemma_rest_unfold(row, 8);
    assert(circ_rest(row, 8) == 56);
    lemma_rest_unfold(row, 7);
    assert(circ_rest(row, 7) == 72);
    lemma_rest_unfold(row, 6);
    assert(circ_rest(row, 6) == 80);
    lemma_rest_unfold(row, 5);
    assert(circ_rest(row, 5) == 96);
    lemma_rest_unfold(row, 4);
    assert(circ_rest(row, 4) == 104);
    lemma_rest_unfold(row, 3);
    assert(circ_rest(row, 3) == 120);
    lemma_rest_unfold(row, 2);
    assert(circ_rest(row, 2) == 128);
    lemma_rest_unfold(row, 1);
    assert(circ_rest(row, 1) == 144);
    lemma_rest_unfold(row, 0);
    assert(circ_rest(row, 0) == 152);
    assert(circ_bytes(row) == circ_rest(row, 0));
}

/// circ_bytes(ROW_OW128EM) == 104: rounds 10, to_take 4 (kc 4), bc 4
/// -- even rounds write 8, odd rounds 16.
pub proof fn circ_ladder_owf128em()
    ensures
        circ_bytes(ROW_OW128EM) == 104,
{
    let row = ROW_OW128EM;
    assert(row.rounds == 10);
    assert(row.bc == 4);
    assert(row.kc == 4);
    assert(row.is_em);
    assert(circ_bytes_at(row, 8) == 8);
    assert(circ_bytes_at(row, 7) == 16);
    assert(circ_bytes_at(row, 6) == 8);
    assert(circ_bytes_at(row, 5) == 16);
    assert(circ_bytes_at(row, 4) == 8);
    assert(circ_bytes_at(row, 3) == 16);
    assert(circ_bytes_at(row, 2) == 8);
    assert(circ_bytes_at(row, 1) == 16);
    assert(circ_bytes_at(row, 0) == 8);
    lemma_rest_zero(row, 9);
    lemma_rest_unfold(row, 8);
    assert(circ_rest(row, 8) == 8);
    lemma_rest_unfold(row, 7);
    assert(circ_rest(row, 7) == 24);
    lemma_rest_unfold(row, 6);
    assert(circ_rest(row, 6) == 32);
    lemma_rest_unfold(row, 5);
    assert(circ_rest(row, 5) == 48);
    lemma_rest_unfold(row, 4);
    assert(circ_rest(row, 4) == 56);
    lemma_rest_unfold(row, 3);
    assert(circ_rest(row, 3) == 72);
    lemma_rest_unfold(row, 2);
    assert(circ_rest(row, 2) == 80);
    lemma_rest_unfold(row, 1);
    assert(circ_rest(row, 1) == 96);
    lemma_rest_unfold(row, 0);
    assert(circ_rest(row, 0) == 104);
    assert(circ_bytes(row) == circ_rest(row, 0));
}

/// circ_bytes(ROW_OW192EM) == 192: rounds 12, to_take 6 (kc 6), bc 6
/// -- even rounds write 12, odd rounds 24.
pub proof fn circ_ladder_owf192em()
    ensures
        circ_bytes(ROW_OW192EM) == 192,
{
    let row = ROW_OW192EM;
    assert(row.rounds == 12);
    assert(row.bc == 6);
    assert(row.kc == 6);
    assert(row.is_em);
    assert(circ_bytes_at(row, 10) == 12);
    assert(circ_bytes_at(row, 9) == 24);
    assert(circ_bytes_at(row, 8) == 12);
    assert(circ_bytes_at(row, 7) == 24);
    assert(circ_bytes_at(row, 6) == 12);
    assert(circ_bytes_at(row, 5) == 24);
    assert(circ_bytes_at(row, 4) == 12);
    assert(circ_bytes_at(row, 3) == 24);
    assert(circ_bytes_at(row, 2) == 12);
    assert(circ_bytes_at(row, 1) == 24);
    assert(circ_bytes_at(row, 0) == 12);
    lemma_rest_zero(row, 11);
    lemma_rest_unfold(row, 10);
    assert(circ_rest(row, 10) == 12);
    lemma_rest_unfold(row, 9);
    assert(circ_rest(row, 9) == 36);
    lemma_rest_unfold(row, 8);
    assert(circ_rest(row, 8) == 48);
    lemma_rest_unfold(row, 7);
    assert(circ_rest(row, 7) == 72);
    lemma_rest_unfold(row, 6);
    assert(circ_rest(row, 6) == 84);
    lemma_rest_unfold(row, 5);
    assert(circ_rest(row, 5) == 108);
    lemma_rest_unfold(row, 4);
    assert(circ_rest(row, 4) == 120);
    lemma_rest_unfold(row, 3);
    assert(circ_rest(row, 3) == 144);
    lemma_rest_unfold(row, 2);
    assert(circ_rest(row, 2) == 156);
    lemma_rest_unfold(row, 1);
    assert(circ_rest(row, 1) == 180);
    lemma_rest_unfold(row, 0);
    assert(circ_rest(row, 0) == 192);
    assert(circ_bytes(row) == circ_rest(row, 0));
}

/// circ_bytes(ROW_OW256EM) == 304: rounds 14, to_take 8 (kc 8), bc 8
/// -- even rounds write 16, odd rounds 32.
pub proof fn circ_ladder_owf256em()
    ensures
        circ_bytes(ROW_OW256EM) == 304,
{
    let row = ROW_OW256EM;
    assert(row.rounds == 14);
    assert(row.bc == 8);
    assert(row.kc == 8);
    assert(row.is_em);
    assert(circ_bytes_at(row, 12) == 16);
    assert(circ_bytes_at(row, 11) == 32);
    assert(circ_bytes_at(row, 10) == 16);
    assert(circ_bytes_at(row, 9) == 32);
    assert(circ_bytes_at(row, 8) == 16);
    assert(circ_bytes_at(row, 7) == 32);
    assert(circ_bytes_at(row, 6) == 16);
    assert(circ_bytes_at(row, 5) == 32);
    assert(circ_bytes_at(row, 4) == 16);
    assert(circ_bytes_at(row, 3) == 32);
    assert(circ_bytes_at(row, 2) == 16);
    assert(circ_bytes_at(row, 1) == 32);
    assert(circ_bytes_at(row, 0) == 16);
    lemma_rest_zero(row, 13);
    lemma_rest_unfold(row, 12);
    assert(circ_rest(row, 12) == 16);
    lemma_rest_unfold(row, 11);
    assert(circ_rest(row, 11) == 48);
    lemma_rest_unfold(row, 10);
    assert(circ_rest(row, 10) == 64);
    lemma_rest_unfold(row, 9);
    assert(circ_rest(row, 9) == 96);
    lemma_rest_unfold(row, 8);
    assert(circ_rest(row, 8) == 112);
    lemma_rest_unfold(row, 7);
    assert(circ_rest(row, 7) == 144);
    lemma_rest_unfold(row, 6);
    assert(circ_rest(row, 6) == 160);
    lemma_rest_unfold(row, 5);
    assert(circ_rest(row, 5) == 192);
    lemma_rest_unfold(row, 4);
    assert(circ_rest(row, 4) == 208);
    lemma_rest_unfold(row, 3);
    assert(circ_rest(row, 3) == 240);
    lemma_rest_unfold(row, 2);
    assert(circ_rest(row, 2) == 256);
    lemma_rest_unfold(row, 1);
    assert(circ_rest(row, 1) == 288);
    lemma_rest_unfold(row, 0);
    assert(circ_rest(row, 0) == 304);
    assert(circ_bytes(row) == circ_rest(row, 0));
}

/// The EM rows write no non-lin part; the row budget reduces to
/// lambda_bytes + beta*circ_bytes. Numbers: OWF128EM 16+104=120,
/// OWF192EM 24+192=216, OWF256EM 32+304=336.
pub proof fn row_budget_ladder()
    ensures
        witness_budget(ROW_OW128) == ROW_OW128.l_bytes,
        witness_budget(ROW_OW192) == ROW_OW192.l_bytes,
        witness_budget(ROW_OW256) == ROW_OW256.l_bytes,
        witness_budget(ROW_OW128EM) == ROW_OW128EM.l_bytes,
        witness_budget(ROW_OW192EM) == ROW_OW192EM.l_bytes,
        witness_budget(ROW_OW256EM) == ROW_OW256EM.l_bytes,
{
    //
    // OWF128: 16 + 40 + 1*(5*4*2 + 4*4*4) = 16+40+104
    assert(ROW_OW128.lambda_bytes == 16);
    assert(ROW_OW128.kc == 4);
    assert(ROW_OW128.ske == 40);
    assert(ROW_OW128.beta == 1);
    assert(ROW_OW128.rounds == 10);
    circ_ladder_owf128();
    assert(circ_bytes(ROW_OW128) == 5 * 4 * 2 + 4 * 4 * 4);
    //
    // OWF192: 24 + 32 + 2*(6*4*2 + 5*4*4) = 24+32+256
    assert(ROW_OW192.lambda_bytes == 24);
    assert(ROW_OW192.kc == 6);
    assert(ROW_OW192.ske == 32);
    assert(ROW_OW192.beta == 2);
    assert(ROW_OW192.rounds == 12);
    circ_ladder_owf192();
    assert(circ_bytes(ROW_OW192) == 6 * 4 * 2 + 5 * 4 * 4);
    assert(circ_bytes(ROW_OW192) == 128);
    //
    // OWF256: 32 + 52 + 2*(7*4*2 + 6*4*4) = 32+52+304
    assert(ROW_OW256.lambda_bytes == 32);
    assert(ROW_OW256.kc == 8);
    assert(ROW_OW256.ske == 52);
    assert(ROW_OW256.beta == 2);
    assert(ROW_OW256.rounds == 14);
    circ_ladder_owf256();
    assert(circ_bytes(ROW_OW256) == 7 * 4 * 2 + 6 * 4 * 4);
    assert(circ_bytes(ROW_OW256) == 152);
    //
    // EM rows: no non-lin part; circ bytes as above per row shape.
    assert(ROW_OW128EM.lambda_bytes == 16);
    assert(ROW_OW128EM.kc == 4);
    assert(ROW_OW128EM.rounds == 10);
    assert(ROW_OW128EM.is_em);
    circ_ladder_owf128em();
    assert(circ_bytes(ROW_OW128EM) == 5 * 4 * 2 + 4 * 4 * 4);
    assert(ROW_OW192EM.lambda_bytes == 24);
    assert(ROW_OW192EM.kc == 6);
    assert(ROW_OW192EM.rounds == 12);
    assert(ROW_OW192EM.is_em);
    circ_ladder_owf192em();
    assert(circ_bytes(ROW_OW192EM) == 6 * 6 * 2 + 5 * 6 * 4);
    assert(circ_bytes(ROW_OW192EM) == 192);
    assert(ROW_OW256EM.lambda_bytes == 32);
    assert(ROW_OW256EM.kc == 8);
    assert(ROW_OW256EM.rounds == 14);
    assert(ROW_OW256EM.is_em);
    circ_ladder_owf256em();
    assert(circ_bytes(ROW_OW256EM) == 7 * 8 * 2 + 6 * 8 * 4);
    assert(circ_bytes(ROW_OW256EM) == 304);
    // non-EM rows chain their ladders
    nl_written_ladder_owf128();
    nl_written_ladder_owf192();
    nl_written_ladder_owf256();
    assert(witness_budget(ROW_OW128) == 16 + 40 + 1 * 104);
    assert(witness_budget(ROW_OW192) == 24 + 32 + 2 * 128);
    assert(witness_budget(ROW_OW256) == 32 + 52 + 2 * 152);
    assert(witness_budget(ROW_OW128EM) == 16 + 1 * 104);
    assert(witness_budget(ROW_OW192EM) == 24 + 1 * 192);
    assert(witness_budget(ROW_OW256EM) == 32 + 1 * 304);
}

/// Full-witness budget at a row: the identity above as a spec face.
pub open spec fn witness_budget(row: RowCfg) -> int {
    row.lambda_bytes
        + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
        + row.beta * circ_bytes(row)
}

/// The per-j written byte count of the loop body (4 on the kc!=6 or
/// j%3==0 / j%3==1 branches, 0 on the silent j%3==2 branch -- the
/// upstream else-if chain falls through there and writes nothing).
pub open spec fn own_written(kc: int, j: int) -> int {
    if kc != 6 {
        4
    } else if j % 3 == 0 {
        4
    } else if j % 3 == 1 {
        4
    } else {
        0
    }
}

/// Mid-window split of the byte budget: everything written before j,
/// the j-th own bytes, and the tail. (Definitional induction over the
/// top-peel of sum_nl_written.)
pub proof fn nl_written_split(kc: int, ske: int, j: int)
    requires
        nl_start_off(kc) <= j < nl_start_off(kc) + nl_blocks(kc, ske),
    ensures
        nl_written(kc, ske)
            == sum_nl_written(kc, nl_start_off(kc), j) + (own_written(kc, j)
                + sum_nl_written(kc, j + 1, nl_start_off(kc) + nl_blocks(kc, ske))),
{
    let lo = nl_start_off(kc);
    let hi = lo + nl_blocks(kc, ske);
    nl_sum_split(kc, lo, j, hi);
}

proof fn nl_sum_split(kc: int, lo: int, m: int, hi: int)
    requires
        lo <= m < hi,
    ensures
        sum_nl_written(kc, lo, hi)
            == sum_nl_written(kc, lo, m) + (own_written(kc, m) + sum_nl_written(kc, m + 1, hi)),
    decreases hi - m,
{
    if m + 1 == hi {
        assert(sum_nl_written(kc, m, m + 1)
            == own_written(kc, m) + sum_nl_written(kc, m, m));
        assert(sum_nl_written(kc, m, m) == 0);
        assert(sum_nl_written(kc, m + 1, hi) == 0);
        assert(sum_nl_written(kc, lo, hi)
            == own_written(kc, hi - 1) + sum_nl_written(kc, lo, hi - 1));
    } else {
        assert(m + 1 < hi);
        assert(m <= hi - 2);
        assert(lo <= m <= hi - 1);
        nl_sum_split(kc, lo, m, hi - 1);
        assert(sum_nl_written(kc, lo, hi)
            == own_written(kc, hi - 1) + sum_nl_written(kc, lo, hi - 1));
        assert(sum_nl_written(kc, lo, hi - 1)
            == sum_nl_written(kc, lo, m) + (own_written(kc, m)
                + sum_nl_written(kc, m + 1, hi - 1)));
        assert(sum_nl_written(kc, m + 1, hi)
            == own_written(kc, hi - 1) + sum_nl_written(kc, m + 1, hi - 1));
    }
}


/// Exec twin of the non-linear-bits save. (Upstream from_iter builds
/// all three words but only inside[0]/inside[2] are consumed; the
/// twin reads the two consumed words.) The upstream `*index`
/// accumulation lowers to the local idx, returned as new_index.
/// The write bound is derived inside each write lane from the
/// nl_written_split decomposition plus the tail's nonneg -- the
/// wave-1 draft's pre-bound invariant was not maintainable.
pub fn save_non_lin_bits(
    row_nl: RowCfg,
    witness: &mut [u8],
    kb: &[u32],
    index: usize,
    kb_words: usize,
) -> (new_index: usize)
    requires
        !row_nl.is_em,
        row_nl.kc % 4 == 0 || row_nl.kc == 6,
        kb.len() == kb_words,
        8 * (nl_start_off(row_nl.kc as int) + nl_blocks(row_nl.kc as int, row_nl.ske as int))
            <= kb_words,
        index + nl_written(row_nl.kc as int, row_nl.ske as int) <= witness.len(),
        (2 + row_nl.kc / 8 + row_nl.ske) < usize::MAX,
    ensures
        new_index == index + nl_written(row_nl.kc as int, row_nl.ske as int),
        final(witness).len() == old(witness).len(),
        forall |k: int| #![trigger old(witness)[k]] k < index || new_index <= k < final(witness).len()
            ==> final(witness)[k] == old(witness)[k],
{
    let start_off: usize = 1 + (row_nl.kc / 8);

    let non_lin_blocks: usize = if row_nl.kc % 4 == 0 {
        row_nl.ske / 4
    } else {
        row_nl.ske * 3 / 8
    };

    // wiring of the exec bound faces to the spec faces
    assert(start_off as int == nl_start_off(row_nl.kc as int));
    assert(non_lin_blocks as int == nl_blocks(row_nl.kc as int, row_nl.ske as int));
    assert(nl_written(row_nl.kc as int, row_nl.ske as int)
        == sum_nl_written(
            row_nl.kc as int,
            start_off as int,
            start_off as int + non_lin_blocks as int,
        ));
    assert(8 * (start_off + non_lin_blocks) <= kb.len());
    if row_nl.kc == 6 {
        assert(row_nl.kc % 4 != 0);
    }
    proof {
        lemma_nl_written_nonneg(row_nl.kc as int, row_nl.ske as int);
        lemma_sum_nl_nonneg(row_nl.kc as int, start_off as int, start_off as int);
    }

    let entry_len: usize = witness.len();
    let mut j: usize = start_off;
    let mut idx: usize = index;
    while j < start_off + non_lin_blocks
        invariant
            start_off <= j <= start_off + non_lin_blocks,
            start_off as int == nl_start_off(row_nl.kc as int),
            non_lin_blocks as int == nl_blocks(row_nl.kc as int, row_nl.ske as int),
            8 * (start_off + non_lin_blocks) <= kb.len(),
            kb.len() == kb_words,
            witness.len() == old(witness)@.len(),
            witness.len() == entry_len,
            idx as int
                == index as int
                    + sum_nl_written(row_nl.kc as int, start_off as int, j as int),
            index + nl_written(row_nl.kc as int, row_nl.ske as int) <= witness.len(),
            idx <= witness.len(),
            forall |k: int| #![trigger old(witness)[k]] k < index || idx <= k < witness.len()
                ==> witness[k] == old(witness)[k],
        decreases start_off + non_lin_blocks - j,
    {
        proof {
            nl_written_split(row_nl.kc as int, row_nl.ske as int, j as int);
            lemma_sum_nl_unfold(row_nl.kc as int, start_off as int, (j + 1) as int);
            lemma_sum_nl_nonneg(row_nl.kc as int, start_off as int, j as int);
            lemma_sum_nl_nonneg(
                row_nl.kc as int,
                (j + 1) as int,
                start_off as int + non_lin_blocks as int,
            );
        }
        let bb = inv_bitslice(&kb[8 * j..8 * (j + 1)]);
        let i0 = convert_from_batchblocks_word(&bb, 0);
        let i2 = convert_from_batchblocks_word(&bb, 2);

        if row_nl.kc != 6 || j % 3 == 0 {
            proof {
                if row_nl.kc != 6 {
                    lemma_own_written_kc_not6(row_nl.kc as int, j as int);
                } else {
                    lemma_own_written_6_r0(j as int);
                }
                // idx + own + tail == index + nl_written <= len
                assert(idx as int
                    + own_written(row_nl.kc as int, j as int)
                    + sum_nl_written(
                        row_nl.kc as int,
                        (j + 1) as int,
                        start_off as int + non_lin_blocks as int,
                    )
                    == index as int + nl_written(row_nl.kc as int, row_nl.ske as int));
            }
            assert(idx + 4 <= witness.len());
            let idx_pre = idx;
            copy4(witness, idx, &i0);
            assert(witness.len() == entry_len);
            idx += 4;
        } else if j % 3 == 1 {
            proof {
                lemma_own_written_6_r1(j as int);
                assert(idx as int
                    + own_written(row_nl.kc as int, j as int)
                    + sum_nl_written(
                        row_nl.kc as int,
                        (j + 1) as int,
                        start_off as int + non_lin_blocks as int,
                    )
                    == index as int + nl_written(row_nl.kc as int, row_nl.ske as int));
            }
            assert(idx + 4 <= witness.len());
            let idx_pre = idx;
            copy4(witness, idx, &i2);
            assert(witness.len() == entry_len);
            idx += 4;
        } else {
            proof {
                lemma_own_written_6_r2(j as int);
            }
        }
        j += 1;
    }
    assert(j == start_off + non_lin_blocks);
    assert(idx as int == index as int
        + sum_nl_written(row_nl.kc as int, start_off as int, j as int));
    assert(sum_nl_written(row_nl.kc as int, start_off as int,
        start_off as int + non_lin_blocks as int)
        == nl_written(row_nl.kc as int, row_nl.ske as int));
    idx
}

/// Bytes written by round j of round_with_save (4 bytes per even
/// round word pair * to_take, odd rounds write NSt raw words).
pub open spec fn circ_bytes_at(row: RowCfg, j: int) -> int {
    let to_take = if !row.is_em { 4 } else { row.kc };
    if j % 2 == 0 {
        to_take * 2
    } else {
        row.bc * 4
    }
}

/// Bytes still to be written by rounds j..R-1 (the loop-tail budget).
pub open spec fn circ_rest(row: RowCfg, j: int) -> int
    decreases row.rounds - 1 - j,
{
    if j >= row.rounds - 1 {
        0
    } else {
        circ_bytes_at(row, j) + circ_rest(row, j + 1)
    }
}

/// Bytes already written by rounds 0..j of round_with_save.
pub open spec fn circ_done(row: RowCfg, j: int) -> int
    decreases j,
{
    if j <= 0 {
        0
    } else {
        circ_done(row, j - 1) + circ_bytes_at(row, j - 1)
    }
}

/// Definitional peel of circ_rest at a live round.
pub proof fn lemma_rest_unfold(row: RowCfg, j: int)
    requires
        0 <= j < row.rounds - 1,
    ensures
        circ_rest(row, j) == circ_bytes_at(row, j) + circ_rest(row, j + 1),
{
}

/// The tail is zero at the last round.
pub proof fn lemma_rest_zero(row: RowCfg, j: int)
    requires
        j >= row.rounds - 1,
    ensures
        circ_rest(row, j) == 0,
{
}

/// Definitional peel of circ_done at a live round.
pub proof fn lemma_done_unfold(row: RowCfg, j: int)
    requires
        0 < j <= row.rounds - 1,
    ensures
        circ_done(row, j) == circ_done(row, j - 1) + circ_bytes_at(row, j - 1),
{
}

/// done + tail == the full budget (induction over the round index).
pub proof fn lemma_rest_split(row: RowCfg, j: int)
    requires
        0 <= j <= row.rounds - 1,
    ensures
        circ_rest(row, 0) == circ_done(row, j) + circ_rest(row, j),
    decreases j,
{
    if j > 0 {
        lemma_rest_split(row, j - 1);
        lemma_rest_unfold(row, j - 1);
        lemma_done_unfold(row, j);
    }
}

/// Nonneg of the round-tail budget, by induction on the round index.
pub proof fn lemma_circ_rest_nonneg(row: RowCfg, j: int)
    requires
        0 <= j <= row.rounds - 1,
    ensures
        0 <= circ_rest(row, j),
    decreases row.rounds - 1 - j,
{
    if j >= row.rounds - 1 {
        lemma_rest_zero(row, j);
    } else {
        assert(j + 1 <= row.rounds - 1);
        lemma_circ_rest_nonneg(row, j + 1);
        lemma_rest_unfold(row, j);
        if j % 2 == 0 {
            if !row.is_em {
                assert(circ_bytes_at(row, j) == 8);
            } else {
                assert(circ_bytes_at(row, j) == row.kc * 2);
                assert(row.kc as int >= 0);
            }
        } else {
            assert(circ_bytes_at(row, j) == row.bc * 4);
            assert(row.bc as int >= 0);
        }
    }
}

/// Nonneg of the full round-pass budget (the entry bound face of
/// round_with_save / the top assembler).
pub proof fn lemma_circ_bytes_nonneg(row: RowCfg)
    requires
        1 <= row.rounds,
    ensures
        0 <= circ_bytes(row),
{
    assert(circ_bytes(row) == circ_rest(row, 0));
    lemma_circ_rest_nonneg(row, 0);
}

/// Ring step of the beta-count budget: (b+1)*c == b*c + c (this
/// build's default arithmetic does not distribute symbolic
/// products in situ; the nonlinear_arith proof discharges the
/// distribution once, and the loops consume it linearly).
proof fn lemma_beta_mul_step(b: int, c: int)
    requires
        0 <= c,
    ensures
        (b + 1) * c == b * c + c,
{
    assert((b + 1) * c == b * c + c) by (nonlinear_arith)
        requires
            0 <= c,
    ;
}

/// Order step of the beta-count budget: b <= beta and c >= 0 give
/// b*c <= beta*c.
proof fn lemma_beta_mul_mono(b: int, beta: int, c: int)
    requires
        0 <= c,
        b <= beta,
    ensures
        b * c <= beta * c,
{
    assert(b * c <= beta * c) by (nonlinear_arith)
        requires
            0 <= c,
            b <= beta,
    ;
}


/// Exec twin of one beta-round: state init, the round loop with the
/// even-round invnorm captures and odd-round raw word saves.
pub fn round_with_save(
    row_r: RowCfg,
    input1: &[u8], // in
    kb: &[u32],    // k_bar
    witness: &mut [u8],
    index: usize,
) -> (new_index: usize)
    requires
        row_r.bc == 4 || row_r.bc == 6 || row_r.bc == 8,
        row_r.kc <= 8,
        input1.len() == 16 || (row_r.is_em && (input1.len() == 24 || input1.len() == 32)),
        kb.len() >= 8 * row_r.rounds,
        row_r.rounds < usize::MAX / 16,
        row_r.bc <= 8,
        index + circ_bytes(row_r) <= witness.len(),
        4 <= row_r.rounds,
    ensures
        new_index as int == index as int + circ_bytes(row_r),
        final(witness).len() == old(witness).len(),
        forall |k: int| #![trigger old(witness)[k]] k < index || new_index <= k < final(witness).len()
            ==> final(witness)[k] == old(witness)[k],
{
    let mut state: State = [0u32; 8];

    // Input1 is always empty except for FAEST-EM-192 and FAEST-EM-256
    // (upstream split_at(16); lowered to the two workspace copies.)
    assert(input1.len() == 16 || input1.len() == 24 || input1.len() == 32);
    assert(8 * row_r.rounds <= kb.len());
    let mut i0: [u8; 16] = [0u8; 16];
    let mut t: usize = 0;
    while t < 16
        invariant
            t <= 16,
            forall |k: int| 0 <= k < t ==> i0[k as int] == input1[k as int],
            input1.len() >= 16,
        decreases 16 - t,
    {
        i0[t] = input1[t];
        t += 1;
    }
    let n1t: usize = input1.len() - 16;
    assert(n1t == 0 || n1t == 8 || n1t == 16);
    let mut i1t: [u8; 16] = [0u8; 16];
    let mut t: usize = 0;
    while t < n1t
        invariant
            t <= n1t,
            n1t <= 16,
            n1t + 16 == input1.len(),
            forall |k: int| 0 <= k < t ==> i1t[k as int] == input1[16 + k as int],
        decreases n1t - t,
    {
        i1t[t] = input1[16 + t];
        t += 1;
    }
    bitslice(&mut state, &i0, &i1t[..n1t]);

    rijndael_add_round_key(&mut state, &kb[..8]);

    proof {
        lemma_circ_bytes_nonneg(row_r);
        lemma_rest_split(row_r, 0);
    }
    let start_len: usize = witness.len();
    let mut j: usize = 0;
    let mut idx: usize = index;
    while j < row_r.rounds - 1
        invariant
            j <= row_r.rounds - 1,
            row_r.bc == 4 || row_r.bc == 6 || row_r.bc == 8,
            row_r.kc <= 8,
            witness.len() == old(witness)@.len(),
            witness.len() == start_len,
            kb.len() >= 8 * row_r.rounds,
            (j < row_r.rounds - 1) ==> 8 * (j + 2) <= kb.len(),
            index <= idx,
            idx <= witness.len(),
            idx as int == index as int + circ_done(row_r, j as int),
            idx as int + circ_rest(row_r, j as int) <= witness.len() as int,
            circ_bytes(row_r) == circ_done(row_r, j as int) + circ_rest(row_r, j as int),
            forall |k: int| #![trigger old(witness)[k]] k < index || idx <= k < witness.len()
                ==> witness[k] == old(witness)[k],
        decreases row_r.rounds - 1 - j,
    {
        let even_round = (j % 2) == 0;

        proof {
            lemma_rest_unfold(row_r, j as int);
            lemma_done_unfold(row_r, (j + 1) as int);
            lemma_circ_rest_nonneg(row_r, (j + 1) as int);
        }
        assert(index as int + circ_bytes(row_r)
            == idx as int + circ_bytes_at(row_r, j as int) + circ_rest(row_r, (j + 1) as int));

        // Step 19
        if even_round {
            let to_take: usize = if !row_r.is_em { 4 } else { row_r.kc };
            assert(to_take <= 8);
            if !row_r.is_em {
                assert(circ_bytes_at(row_r, j as int) == 8);
            } else {
                assert(circ_bytes_at(row_r, j as int) == row_r.kc as int * 2);
            }
            assert(idx + 2 * to_take <= witness.len());
            let bb = inv_bitslice(&state);
            let idx0: usize = idx;
            let mut wi: usize = 0;
            while wi < to_take
                invariant
                    wi <= to_take,
                    to_take <= 8,
                    witness.len() == old(witness)@.len(),
                    witness.len() == start_len,
                    index <= idx,
                    idx <= witness.len(),
                    idx0 as int == index as int + circ_done(row_r, j as int),
                    index <= idx0,
                    idx == idx0 + 2 * wi,
                    2 * (to_take - wi) + idx <= witness.len(),
                    forall |k: int| #![trigger old(witness)[k]] k < index || idx <= k < witness.len()
                        ==> witness[k] == old(witness)[k],
                decreases to_take - wi,
            {
                let w = convert_from_batchblocks_word(&bb, wi);
                assert(idx + 2 <= witness.len());
                let lo_v = store_invnorm_state(w[0], w[1]);
                witness[idx] = lo_v;
                idx += 1;
                assert(idx <= witness.len());
                let hi_v = store_invnorm_state(w[2], w[3]);
                witness[idx] = hi_v;
                idx += 1;
                wi += 1;
            }
            assert(idx as int
                == index as int + circ_done(row_r, j as int) + 2 * to_take as int);
            assert(idx as int == index as int + circ_done(row_r, (j + 1) as int));
        }

        // Step 23
        rijndael_sub_bytes(&mut state);

        // Step 24
        rijndael_shift_rows_1(&mut state, row_r.bc);

        // Step 25
        if !even_round {
            // Step 26
            assert(circ_bytes_at(row_r, j as int) == row_r.bc as int * 4);
            assert(idx + row_r.bc * 4 <= witness.len());
            let bb = inv_bitslice(&state);
            let mut wi: usize = 0;
            while wi < row_r.bc
                invariant
                    wi <= row_r.bc,
                    row_r.bc <= 8,
                    witness.len() == old(witness)@.len(),
                    witness.len() == start_len,
                    index <= idx,
                    idx <= witness.len(),
                    idx as int
                        == index as int + circ_done(row_r, j as int) + 4 * wi as int,
                    4 * (row_r.bc - wi) + idx <= witness.len(),
                    forall |k: int| #![trigger old(witness)[k]] k < index || idx <= k < witness.len()
                        ==> witness[k] == old(witness)[k],
                decreases row_r.bc - wi,
            {
                let w = convert_from_batchblocks_word(&bb, wi);
                assert(idx + 4 <= witness.len());
                copy4(witness, idx, &w);
                assert(witness.len() == old(witness)@.len());
                idx += 4;
                wi += 1;
            }
            assert(idx as int
                == index as int + circ_done(row_r, j as int) + row_r.bc as int * 4);
            assert(idx as int == index as int + circ_done(row_r, (j + 1) as int));
        }

        // Step 27
        mix_columns_0(&mut state);

        // Step 28
        rijndael_add_round_key(&mut state, &kb[8 * (j + 1)..8 * (j + 2)]);
        j += 1;
    }
    proof {
        lemma_rest_split(row_r, (row_r.rounds - 1) as int);
        lemma_rest_zero(row_r, (row_r.rounds - 1) as int);
    }
    assert(idx as int == index as int + circ_bytes(row_r));
    idx
}

/// Data contract of the kb input: the kb lengths and consumption
/// windows of the six rows (the FA10-pre oracle's measured lengths;
/// the pinned consts above carry the values).
pub open spec fn kb_contract_holds(row: RowCfg, kb_len: int) -> bool {
    &&& kb_len == row.kb_words
    &&& 8 * row.rounds <= row.kb_words
    &&& (row.is_em
        || 8 * (nl_start_off(row.kc as int) + nl_blocks(row.kc as int, row.ske as int))
            <= row.kb_words)
}

/// Wave-2 wrapper for upstream save_key_bits (witness.rs:59-65, the
/// witness[..LambdaBytes].copy_from_slice(key) + index step): the
/// wave-1 twin in src/witness.rs is green but its ensures list does
/// not carry a final-length clause, and the top assembler's
/// length invariants need the callee to keep witness.len(). Same
/// lowered loop body (the probe2 d/e offset-write shapes), length
/// clause added. The upstream call line in aes_extendedwitness
/// fronts this wrapper either way.
pub fn save_key_bits_len(
    witness: &mut [u8],
    key: &[u8],
    index: usize,
    lambda_bytes: usize,
) -> (new_index: usize)
    requires
        key.len() == lambda_bytes,
        index + lambda_bytes <= witness.len(),
    ensures
        new_index == index + lambda_bytes,
        final(witness).len() == old(witness).len(),
        forall |k: int| 0 <= k < key.len() ==> final(witness)[index + k] == key[k],
        forall |k: int| #![trigger old(witness)[k]] k < index || index + key.len() <= k < final(witness).len()
            ==> final(witness)[k] == old(witness)[k],
{
    let mut i: usize = 0;
    while i < key.len()
        invariant
            i <= key.len(),
            witness@.len() == old(witness)@.len(),
            index + key.len() <= witness@.len(),
            index + i <= witness.len(),
            forall |k: int| 0 <= k < i ==> witness[index + k] == key[k],
            forall |k: int| #![trigger old(witness)[k]] k < index || index + key.len() <= k < witness.len()
                ==> witness[k] == old(witness)[k],
        decreases key.len() - i,
    {
        witness[index + i] = key[i];
        i += 1;
    }
    index + lambda_bytes
}

/// Exec twin of the witness extension core, taking the (upstream-
/// produced) fixsliced key-schedule words as the kb parameter. The
/// returned index is upstream's final `index` == LBytes (the Array-
/// length type guarantee of upstream's Box<Array<u8, LBytes>>).
pub fn aes_extendedwitness_from_kb(
    row: RowCfg,
    owf_secret: &[u8],
    owf_input: &[u8],
    kb: &[u32],
    witness: &mut [u8],
) -> (index: usize)
    requires
        owf_secret.len() == row.lambda_bytes,
        owf_input.len() == row.input_size,
        row.input_size == 16 || (row.is_em && (row.input_size == 24 || row.input_size == 32)),
        row.is_em ==> row.input_size == row.lambda_bytes,
        row.bc == 4 || row.bc == 6 || row.bc == 8,
        row.kc <= 8,
        kb_contract_holds(row, kb.len() as int),
        row.kc % 4 == 0 || row.kc == 6,
        witness.len() == row.l_bytes,
        witness_budget(row) == row.l_bytes,
        4 <= row.rounds,
        row.rounds < usize::MAX / 16,
        (2 + row.kc / 8 + row.ske) < usize::MAX,
    ensures
        index == row.l_bytes,
        forall |k: int| #![trigger owf_secret[k]] #![trigger owf_input[k]] 0 <= k < row.lambda_bytes
            ==> final(witness)[k] == (if !row.is_em { owf_secret[k] } else { owf_input[k] }),
{
    // Step 0 (upstream to_owned; lowered to the 32-byte workspace)
    let mut input: [u8; 32] = [0u8; 32];
    let inp_len: usize = owf_input.len();
    let mut t: usize = 0;
    while t < inp_len
        invariant
            t <= inp_len,
            inp_len == owf_input.len(),
            inp_len <= 32,
            forall |k: int| 0 <= k < t ==> input[k as int] == owf_input[k as int],
        decreases inp_len - t,
    {
        input[t] = owf_input[t];
        t += 1;
    }

    // Step 3 (upstream Box::default(); here the caller-provided slice
    // of exactly LBytes bytes under requires).

    // Step 6 -- the upstream kb production line
    // (rijndael_key_schedule::<NSt, NK, R>(owf_secret, SKe)) is NOT
    // verified exec here (D-FA10-1); kb arrives as the data contract.

    let mut index: usize = 0;
    proof {
        lemma_nl_written_nonneg(row.kc as int, row.ske as int);
        lemma_circ_bytes_nonneg(row);
        assert(witness_budget(row)
            == row.lambda_bytes as int
                + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
                + row.beta as int * circ_bytes(row));
        assert(row.lambda_bytes as int
            + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
            + row.beta as int * circ_bytes(row)
            == witness.len() as int);
        assert(row.lambda_bytes as int
            + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
            + row.beta as int * circ_bytes(row)
            == row.l_bytes as int);
    }
    assert(row.lambda_bytes <= witness.len());
    assert(0 + row.lambda_bytes <= witness.len());

    // Step 7
    if !row.is_em {
        index = save_key_bits_len(witness, owf_secret, 0, row.lambda_bytes);
        assert(witness.len() == old(witness)@.len());
        assert(forall |k: int| 0 <= k < row.lambda_bytes
            ==> witness[k as int] == owf_secret[k as int]);
        // Step 8
        assert(row.lambda_bytes as int
            + nl_written(row.kc as int, row.ske as int) <= witness.len() as int);
        index = save_non_lin_bits(row, witness, kb, index, row.kb_words);
    } else {
        // In EM mode, AES key is part of public input while pt is secret
        assert(owf_input.len() == row.lambda_bytes);
        index = save_key_bits_len(witness, owf_input, 0, row.lambda_bytes);
        assert(witness.len() == old(witness)@.len());
        assert(forall |k: int| 0 <= k < row.lambda_bytes
            ==> witness[k as int] == owf_input[k as int]);
    }
    assert(index as int == row.lambda_bytes as int
        + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) }));

    // Step 14
    assert(row.lambda_bytes as int
        + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
        + row.beta as int * circ_bytes(row)
        <= witness.len() as int);
    let mut b: usize = 0;
    while b < row.beta
        invariant
            b <= row.beta,
            row.bc == 4 || row.bc == 6 || row.bc == 8,
            row.kc <= 8,
            4 <= row.rounds,
            row.rounds < usize::MAX / 16,
            row.input_size == 16
                || (row.is_em && (row.input_size == 24 || row.input_size == 32)),
            row.input_size <= 32,
            0 <= circ_bytes(row),
            0 <= nl_written(row.kc as int, row.ske as int),
            witness.len() == old(witness)@.len(),
            witness.len() == row.l_bytes,
            kb.len() >= 8 * row.rounds,
            row.lambda_bytes <= index,
            index as int
                == row.lambda_bytes as int
                    + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
                    + b as int * circ_bytes(row),
            forall |k: int| #![trigger owf_secret[k as int]] #![trigger owf_input[k as int]]
                0 <= k < row.lambda_bytes
                ==> witness[k as int]
                    == (if !row.is_em { owf_secret[k as int] } else { owf_input[k as int] }),
            row.lambda_bytes as int
                + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
                + row.beta as int * circ_bytes(row)
                <= witness.len() as int,
        decreases row.beta - b,
    {
        assert(row.input_size == 16 || (row.is_em && (row.input_size == 24 || row.input_size == 32)));
        assert(row.input_size <= 32);
        assert(row.bc == 4 || row.bc == 6 || row.bc == 8);
        assert(row.kc <= 8);
        assert(4 <= row.rounds);
        assert(row.rounds < usize::MAX / 16);
        assert(kb.len() >= 8 * row.rounds);
        proof {
            lemma_beta_mul_step(b as int, circ_bytes(row));
            lemma_beta_mul_mono((b + 1) as int, row.beta as int, circ_bytes(row));
        }
        assert(index as int + circ_bytes(row)
            == row.lambda_bytes as int
                + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
                + (b + 1) as int * circ_bytes(row));
        assert(index + circ_bytes(row) <= witness.len());
        let inp1: &[u8] = &input[..row.input_size];
        assert(inp1.len() == row.input_size);
        index = round_with_save(row, inp1, kb, witness, index);
        input[0] ^= 1;
        b += 1;
    }
    assert(index as int
        == row.lambda_bytes as int
            + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
            + row.beta as int * circ_bytes(row));
    assert(row.l_bytes as int
        == row.lambda_bytes as int
            + (if row.is_em { 0 } else { nl_written(row.kc as int, row.ske as int) })
            + row.beta as int * circ_bytes(row));
    assert(index == row.l_bytes);
    index
}


} // verus!
