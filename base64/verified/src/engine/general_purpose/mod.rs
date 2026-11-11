//! `engine/general_purpose/mod.rs` mirror
//!
//! This batch carries: the construction lemma surface of the encode/decode tables
//! (the semantic relation of encode_table / decode_table) and the GeneralPurposeConfig assembly surface.
//! encode_helper / encode_scalar_tail (the u64 fast path + slow path) are in the file-tail
//! blocked record -- part of their obligation surface is carried by the harness (the roundtrip exemplar cases, encode side).

use vstd::prelude::*;
pub mod decode;
pub mod decode_suffix;
pub mod encode;

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
        /* ValidPairedTables needs a third component: the reverse map, i.e. a legal value
           r@[j] < 64 implies j is the symbol position of that value. The two components above
           do NOT imply it -- a non-symbol position could hold a duplicated legal value, which
           is the actual shape of the earlier blocked-proof-frame note (a missing component,
           not an unfold/order issue). The construction satisfies the reverse map via a loop
           invariant (see the second loop below), so it is ensured here as a third component
           and the composite is closed by the paired_tables_from_components call in the proof block. */
        forall|j: int| 0 <= j < 256 ==> (r@[j] < 64 ==> symbols@ [r@[j] as int] == j as u8),
        ValidPairedTables(symbols@, r@, padding),
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
            /* the reverse-map component: every legal entry written so far sits at the
               symbols position of its own index (fresh positions hold 255, so the clause is
               vacuous for them; the invariant is preserved because each write lands on
               the position of its own index) */
            forall|j: int| 0 <= j < 256 ==> (table@[j] < 64 ==> symbols@ [table@[j] as int] == j as u8),
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
        assert(
            forall|j: int| 0 <= j < 256
                ==> (table@[j] < 64 ==> symbols@ [table@[j] as int] == j as u8)
        );
        /* the third component above closes the composite (padding is not used in
           ValidPairedTables' body, so validity is padding-independent) */
        paired_tables_from_components(symbols@, table@);
        assert(ValidPairedTables(symbols@, table@, padding));
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

/* ============================================================
 * Upstream GeneralPurposeConfig (mod.rs:324-331) -- the field-record assembly surface.
 * Upstream fields are private; the mirror record keeps the same fields public so each
 * builder/accessor obligation is state-checkable field-for-field (upstream derives
 * Clone, Copy, Debug on this struct). The "pure data plumbing -> scope-out" verdict is
 * broken here by a witness-contract batch.
 * ============================================================ */

/// Upstream struct doc (mod.rs:311-322, code block for # Examples at mod.rs:313-318 skipped):
///   Contains configuration parameters for base64 encoding and decoding.
///   The constants [PAD] and [`NO_PAD`] cover most use cases.
///   To specify the characters used, see [Alphabet].
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct GeneralPurposeConfigV {
    /* origin (mod.rs:325-327): encode_padding / decode_allow_trailing_bits / decode_padding_mode */
    pub encode_padding: bool,
    pub decode_allow_trailing_bits: bool,
    pub decode_padding_mode: super::DecodePaddingMode,
}

/// Upstream doc (mod.rs:331-335):
///   Create a new config with `padding` = `true`, `decode_allow_trailing_bits` = `false`, and
///   `decode_padding_mode = DecodePaddingMode::RequireCanonicalPadding`.
///   This probably matches most people's expectations, but consider disabling padding to save
///   a few bytes unless you specifically need it for compatibility with some legacy system.
/// (origin body mod.rs:337-343; the upstream doc line names RequireCanonicalPadding, the
///  body uses the variant name RequireCanonical)
pub exec fn general_purpose_config_new() -> (r: GeneralPurposeConfigV)
    ensures
        r.encode_padding,
        !r.decode_allow_trailing_bits,
        r.decode_padding_mode == super::DecodePaddingMode::RequireCanonical,
{
    GeneralPurposeConfigV {
        encode_padding: true, /* RFC states that padding must be applied by default */
        decode_allow_trailing_bits: false,
        decode_padding_mode: super::DecodePaddingMode::RequireCanonical,
    }
}

/// Upstream doc (mod.rs:346-355):
///   Create a new config based on `self` with an updated `padding` setting.
///   If `padding` is `true`, encoding will append either 1 or 2 `=` padding characters as needed
///   to produce an output whose length is a multiple of 4.
///   Padding is not needed for correct decoding and only serves to waste bytes, but it's in the
///   [spec](https://datatracker.ietf.org/doc/html/rfc4648#section-3.2).
///   For new applications, consider not using padding if the decoders you're using don't require
///   padding to be present.
/// (origin body mod.rs:357-362)
pub exec fn with_encode_padding(
    cfg: GeneralPurposeConfigV,
    padding: bool,
) -> (r: GeneralPurposeConfigV)
    ensures
        r.encode_padding == padding,
        r.decode_allow_trailing_bits == cfg.decode_allow_trailing_bits,
        r.decode_padding_mode == cfg.decode_padding_mode,
{
    /* Origin Rust: Self { encode_padding: padding, ..self } */
    GeneralPurposeConfigV { encode_padding: padding, ..cfg }
}

/// Upstream doc (mod.rs:364-370):
///   Create a new config based on `self` with an updated `decode_allow_trailing_bits` setting.
///   Most users will not need to configure this. It's useful if you need to decode base64
///   produced by a buggy encoder that has bits set in the unused space on the last base64
///   character as per [forgiving-base64 decode](https://infra.spec.whatwg.org/#forgiving-base64-decode).
///   If invalid trailing bits are present and this is `true`, those bits will
///   be silently ignored, else `DecodeError::InvalidLastSymbol` will be emitted.
/// (origin body mod.rs:372-377)
pub exec fn with_decode_allow_trailing_bits(
    cfg: GeneralPurposeConfigV,
    allow: bool,
) -> (r: GeneralPurposeConfigV)
    ensures
        r.encode_padding == cfg.encode_padding,
        r.decode_allow_trailing_bits == allow,
        r.decode_padding_mode == cfg.decode_padding_mode,
{
    /* Origin Rust: Self { decode_allow_trailing_bits: allow, ..self } */
    GeneralPurposeConfigV { decode_allow_trailing_bits: allow, ..cfg }
}

/// Upstream doc (mod.rs:379-391):
///   Create a new config based on `self` with an updated `decode_padding_mode` setting.
///   Padding is not useful in terms of representing encoded data -- it makes no difference to
///   the decoder if padding is present or not, so if you have some un-padded input to decode, it
///   is perfectly fine to use `DecodePaddingMode::Indifferent` to prevent errors from being
///   emitted.
///   However, since in practice
///   [people who learned nothing from BER vs DER seem to expect base64 to have one canonical encoding](https://eprint.iacr.org/2022/361),
///   the default setting is the stricter `DecodePaddingMode::RequireCanonicalPadding`.
///   Or, if "canonical" in your circumstance means _no_ padding rather than padding to the
///   next multiple of four, there's `DecodePaddingMode::RequireNoPadding`.
/// (origin body mod.rs:393-398)
pub exec fn with_decode_padding_mode(
    cfg: GeneralPurposeConfigV,
    mode: super::DecodePaddingMode,
) -> (r: GeneralPurposeConfigV)
    ensures
        r.encode_padding == cfg.encode_padding,
        r.decode_allow_trailing_bits == cfg.decode_allow_trailing_bits,
        r.decode_padding_mode == mode,
{
    /* Origin Rust: Self { decode_padding_mode: mode, ..self } */
    GeneralPurposeConfigV { decode_padding_mode: mode, ..cfg }
}

/// Upstream doc (mod.rs:402-402):
///   Delegates to [`GeneralPurposeConfig::new`].
/// (origin body mod.rs:403-405)
pub exec fn general_purpose_config_default() -> (r: GeneralPurposeConfigV)
    ensures
        r.encode_padding,
        !r.decode_allow_trailing_bits,
        r.decode_padding_mode == super::DecodePaddingMode::RequireCanonical,
{
    general_purpose_config_new()
}

/// Upstream doc (mod.rs:408-412): the upstream `impl Config for GeneralPurposeConfig`
/// accessor `encode_padding` carries no upstream doc comment
/// (origin body mod.rs:409-411)
pub exec fn config_encode_padding(cfg: &GeneralPurposeConfigV) -> (r: bool)
    ensures
        r == cfg.encode_padding,
{
    cfg.encode_padding
}

/// Upstream doc (mod.rs:422-422):
///   Whether trailing bits are allowed when decoding.
/// (origin body mod.rs:423-425; upstream gates this impl behind the `simd-unsafe` cfg,
///  the mirror keeps the accessor ungated)
pub exec fn config_decode_allow_trailing_bits(cfg: &GeneralPurposeConfigV) -> (r: bool)
    ensures
        r == cfg.decode_allow_trailing_bits,
{
    cfg.decode_allow_trailing_bits
}

/// Upstream doc (mod.rs:427-427):
///   The decode padding mode.
/// (origin body mod.rs:428-430; same `simd-unsafe` cfg note as above)
pub exec fn config_decode_padding_mode(
    cfg: &GeneralPurposeConfigV,
) -> (r: super::DecodePaddingMode)
    ensures
        r == cfg.decode_padding_mode,
{
    cfg.decode_padding_mode
}

/* ============================================================
 * Upstream GeneralPurpose (mod.rs:28-33) + GeneralPurpose::new (mod.rs:41-54).
 * Relax ledger item 3: the engine-held `[u8; 64]`/`[u8; 256]` tables -> `Vec<u8>` fields;
 * the `alphabet: &Alphabet` parameter is split into `(symbols, padding)` -- upstream new
 * reads `alphabet.padding` for the stored padding byte (`Symbol` -> `u8`).
 * ============================================================ */

/// Upstream struct doc (mod.rs:20-25):
///   A general-purpose base64 engine.
///   - It uses no vector CPU instructions, so it will work on any system. For a version that uses
///     SIMD where available, see the SIMD engines behind the `simd-unsafe` feature.
///   - It is reasonably fast (~2-3GiB/s).
///   - It is not constant-time, though, so it is vulnerable to timing side-channel attacks. For loading cryptographic keys, etc, it is suggested to use the forthcoming constant-time implementation.
pub struct GeneralPurposeV {
    /* origin (mod.rs:29-32): encode_table [u8;64] / decode_table [u8;256] /
       padding Symbol / config GeneralPurposeConfig */
    pub encode_table: Vec<u8>,
    pub decode_table: Vec<u8>,
    pub padding: u8,
    pub config: GeneralPurposeConfigV,
}

/// Upstream doc (mod.rs:42-45):
///   Create a `GeneralPurpose` engine from an [Alphabet].
///   While not very expensive to initialize, ideally these should be cached
///   if the engine will be used repeatedly.
/// (origin body mod.rs:47-54: encode_table(alphabet), decode_table(alphabet),
///  padding = alphabet.padding, config)
pub exec fn general_purpose_new(
    symbols: &[u8],
    padding: u8,
    config: GeneralPurposeConfigV,
) -> (r: GeneralPurposeV)
    requires
        symbols@.len() == 64,
        ValidAlphabetSymbols(symbols@),
    ensures
        r.encode_table@ == symbols@,
        r.decode_table@.len() == 256,
        forall|j: int| 0 <= j < 256 ==> (r.decode_table@[j] < 64 || r.decode_table@[j] == decode::INVALID_VALUE),
        forall|v: int| 0 <= v < 64 ==> r.decode_table@[symbols@ [v] as int] == v as u8,
        ValidPairedTables(symbols@, r.decode_table@, padding),
        r.padding == padding,
        r.config == config,
{
    let et = build_encode_table(symbols);
    let dt = build_decode_table(symbols, padding);
    GeneralPurposeV {
        encode_table: et,
        decode_table: dt,
        padding: padding,
        config: config,
    }
}

/* ============================================================
 * ValidPairedTables composite (retry of the earlier blocked-proof-frame note inside
 * build_decode_table). Retry log:
 *  - attempt 1: composite from the two component facts of build_decode_table's ensures
 *    plus the full symbols model (incl. pairwise distinctness), each forall instantiated
 *    explicitly -- the reverse conjunct is not derived.
 *  - attempt 2 (independence witness, probe-cex.rs under the probe area): verus itself
 *    proves a concrete table on which both component facts and ValidAlphabetSymbols hold
 *    while the reverse conjunct is violated (a non-symbol position holds a duplicated
 *    legal value), so the gap is logical underivability, not a solver/unfolding issue.
 *  - attempt 3: the reverse map is a third component. It is provable in the construction
 *    (loop invariant of build_decode_table), and the three components together close the
 *    composite. Note the composite itself needs only symbols.len() == 64 -- pairwise
 *    distinctness is NOT needed (it is a construction-side fact).
 * ============================================================ */

pub proof fn paired_tables_from_components(symbols: Seq<u8>, table: Seq<u8>)
    requires
        symbols.len() == 64,
        table.len() == 256,
        forall|j: int| 0 <= j < 256 ==> (table[j] < 64 || table[j] == decode::INVALID_VALUE),
        forall|v: int| 0 <= v < 64 ==> table[symbols[v] as int] == v as u8,
        forall|j: int| 0 <= j < 256 ==> (table[j] < 64 ==> symbols[table[j] as int] == j as u8),
    ensures
        forall|p: u8| ValidPairedTables(symbols, table, p),
{
    assert(table.len() == 256);
    assert(
        forall|j: int| 0 <= j < 256 ==> (table[j] < 64 || table[j] == decode::INVALID_VALUE)
    );
    assert(forall|v: int| 0 <= v < 64 ==> table[symbols[v] as int] == v as u8);
    assert(
        forall|j: int| 0 <= j < 256
            ==> (table[j] < 64 ==> symbols[table[j] as int] == j as u8)
    );
    assert forall|j: int| 0 <= j < 256 implies
        ((table[j] < 64 && symbols[table[j] as int] == j as u8) || table[j] == decode::INVALID_VALUE) by {
        /* explicit case split: a legal entry carries its position via the reverse
           component; an illegal entry is INVALID_VALUE by the values component */
        if table[j] < 64 {
            assert(symbols[table[j] as int] == j as u8);
        } else {
            assert(table[j] == decode::INVALID_VALUE);
        }
    }
}

} // verus!

/* ============================================================
 * blocked / postponed record (see out/bug-finder-summary.md)
 * - `GeneralPurposeConfig` (fields + with_* builder) and `GeneralPurpose::new`:
 *   transcribed above as `GeneralPurposeConfigV` / `GeneralPurposeV` (witness-contract
 *   batch; the builder/accessor obligations now hold field-for-field in the verified tree).
 * - `encode_helper` / `encode_scalar_tail` u64 fast path: VERIFIED (fast-path close-out
 *   batch): the per-span helper fast_quad8 (eight ground-conjunct ensures) + the
 *   single-step fast_step32 carry the eight slots of each u64 read; the loop rides a
 *   single consumed contract. Ledgered rlimit sites of the tree: encode_scalar_tail
 *   (encode loop maintenance) and decode_span32 (the decode four-chunk chain body).
 * ============================================================ */
