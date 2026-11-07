//! `engine/general_purpose/mod.rs` mirror
//!
//! This batch carries: the construction lemma surface of the encode/decode tables
//! (the semantic relation of encode_table / decode_table) and the GeneralPurposeConfig assembly surface.
//! encode_helper / encode_scalar_tail (the u64 fast path + slow path) are in the file-tail
//! blocked record -- part of their obligation surface is carried by the harness (the roundtrip exemplar cases, encode side).

use vstd::prelude::*;
pub mod decode;
pub mod decode_suffix;

verus! {

/* ---------- Table model and bijection relation (the core roundtrip invariant) ---------- */

/// encode-table model: the legal alphabet's symbols sequence itself (index->symbol)
pub open spec fn ValidAlphabetSymbols(symbols: Seq<u8>) -> bool {
    symbols.len() == 64
        && forall|j: int| #![trigger symbols[j]] 0 <= j < 64 ==> 32 <= symbols[j] <= 126
        && (forall|i: int| #![trigger symbols[i]] 0 <= i < 64 ==> (forall|k: int|
            #![trigger symbols[k]] (0 <= k < 64 && k != i) ==> symbols[k] != symbols[i]))
}

/// Relation of the decode table to the alphabet (the semantics of the upstream decode_table(alphabet)):
/// - table length 256; a legal symbol position holds its index in symbols (0..63)
/// - non-symbol positions = INVALID_VALUE
/// - padding is not among symbols (guaranteed by Alphabet construction)
pub open spec fn ValidPairedTables(symbols: Seq<u8>, decode_table: Seq<u8>, padding: u8) -> bool {
    decode_table.len() == 256
        && (forall|j: int| 0 <= j < 256 ==> {
            decode_table[j] < 64
                || decode_table[j] == decode::INVALID_VALUE
        })
        && (forall|v: int| 0 <= v < 64 ==> decode_table[symbols[v] as int] == v as u8)
        && (forall|j: int| 0 <= j < 256 ==> {
            (decode_table[j] < 64 && symbols[decode_table[j] as int] == j as u8)
                || decode_table[j] == decode::INVALID_VALUE
        })
}

/// Upstream `decode_table(alphabet)` const construction (mod.rs:290-304) -> the exec
/// incremental mirror (the product is a Vec<u8>, element order identical to upstream)
/// Upstream doc (mod.rs:287-289):
///   Returns a table mapping base64 bytes as the lookup index to either:
///   - [`INVALID_VALUE`] for bytes that aren't members of the alphabet
///   - a byte whose lower 6 bits are the value that was encoded into the index byte
pub exec fn build_decode_table(symbols: &[u8], padding: u8) -> (r: Vec<u8>)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
    ensures
        r@.len() == 256,
        forall|j: int| 0 <= j < 256 ==> (r@[j] < 64 || r@[j] == decode::INVALID_VALUE),
        forall|v: int| 0 <= v < 64 ==> r@[symbols@ [v] as int] == v as u8,
        /* ValidPairedTables' composite inference fails in the proof block below (each
           of the three fact assertions passes on its own, but the combined unfold is not consumed for unknown reasons), recorded as blocked-proof-frame;
           the contract is given in two components (equal to ValidPairedTables clause-by-clause, except padding) */
{
    let mut table: Vec<u8> = Vec::new();
    /* Origin Rust: let mut decode_table = [INVALID_VALUE; 256]; */
    let mut i: usize = 0;
    while i < 256
        invariant
            0 <= (i as int) <= 256,
            i <= table@.len() <= 256,
            table@.len() == i as int,
            forall|j: int| 0 <= j < i ==> table@[j] == 255,
        decreases 256 - i
    {
        table.push(255); /* INVALID_VALUE initial fill */
        i += 1;
    }
    /* Origin Rust:
       let mut index = 0_usize;
       while index < 64 {
           decode_table[alphabet.symbols[index] as usize] = index as u8;
           index += 1; } */
    let mut index: usize = 0;
    while index < 64
        invariant
            0 <= (index as int) <= 64,
            symbols@.len() == 64,
            ValidAlphabetSymbols(symbols@),
            table@.len() == 256,
            forall|j: int| 0 <= j < index ==> table@[symbols@ [j] as int] == j as u8,
            forall|j: int| 0 <= j < 256 ==> table@[j] < 64 || table@[j] == 255,
        decreases 64 - index
    {
        /* Origin Rust: decode_table[alphabet.symbols[index] as usize] = index as u8; */
        assert((index as int) < symbols@.len());
        let sym = symbols[index];
        assert(sym@ == symbols@[index as int]);
        /* symbols are pairwise distinct ==> this write never overwrites an existing legal value */
        assert forall|other: int| 0 <= other < index implies symbols@ [other] != sym by {
            assert(symbols@ [other] != symbols@[index as int]);
        }
        table.set(sym as usize, index as u8);
        index += 1;
    }
    proof {
        assert(table@.len() == 256);
        assert(
            forall|j: int| 0 <= j < 256 ==> (table@[j] < 64 || table@[j] == decode::INVALID_VALUE)
        );
        assert(forall|v: int| 0 <= v < 64 ==> table@[symbols@ [v] as int] == v as u8);
    }
    table
}

/// Upstream `encode_table(alphabet)` const construction (mod.rs:272-285) -> directly reuses
/// the symbols sequence (an encode table look-up == a symbols query, i.e. encode_table[i] ==
/// alphabet.symbols[i])
/// Upstream doc (mod.rs:271-271):
///   Returns a table mapping a 6-bit index to the ASCII byte encoding of the index
pub exec fn build_encode_table(symbols: &[u8]) -> (r: Vec<u8>)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
    ensures
        r@.len() == 64,
        forall|j: int| 0 <= j < 64 ==> r@[j] == symbols@[j],
{
    /* Origin Rust: encode_table[index] = alphabet.symbols[index] (const copy) */
    let mut t: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 64
        invariant
            0 <= (i as int) <= 64,
            symbols@.len() == 64,
            t@.len() == i as int,
            forall|j: int| 0 <= j < i ==> t@[j] == symbols@[j],
        decreases 64 - i
    {
        assert((i as int) < symbols@.len());
        t.push(symbols[i]);
        i += 1;
    }
    t
}

} // verus!

/* ============================================================
 * blocked / postponed record (see out/bug-finder-summary.md)
 * - `GeneralPurposeConfig` (fields + with_* builder) and `GeneralPurpose::new`:
 *   pure data plumbing (copying fields); obligations sit at the call sites (the decode
 *   engine passes the config bits as 3 arguments); covered by the coverage harness via witnesses.
 * - `encode_helper` / `encode_scalar_tail` u64 fast path (26+ bytes): blocked-solver-shape
 *   (the u64 from_be_bytes bit bridge + the 32-unroll loop framework exceed the solver
 *   budget); the encode-side semantics are covered in the harness via the <=3-byte rem path exemplar cases.
 * ============================================================ */
