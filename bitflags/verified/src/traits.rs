//! bitflags 2.13.2 x Verus -- monomorphized mirror of `code/src/traits.rs`
//! (the upstream code/ tree is untouched)
//!
//! Upstream site: https://github.com/bitflags/bitflags
//!   the `src/traits.rs` of pin 8384f6f6e1fd1ab3f448ccf17d400a9e1d6a5280
//!   (the `Flag` struct traits.rs:14-63, `Flags` trait default bodies
//!   traits.rs:132-371, the `Bits` marker trait traits.rs:376-392).
//!
//! ## Why monomorphization (carried-verification note)
//! The user-visible API of bitflags is generated entirely by the declarative
//! macro `bitflags!`: internal types (internal.rs
//! `__impl_public_bitflags!` -> public.rs:32-285 expansion bodies) carry
//! inherent methods, while
//! generic code goes through the `Flags` trait default bodies
//! (traits.rs:132-371). The upstream UTs (the src/tests UT files)
//! double-check both example by example (e.g. `T::x(..)` and `Flags::x(..)`
//! agree on the same value),
//! i.e. they implicitly expect "macro-expanded body == trait default body"
//! equivalence. A Verus proof of trait default bodies
//! per generic signature B: Flags needs trait-level spec machinery, so per
//! skill ruling this transcription carries them
//! **as monomorphized instances**: the bits type is u32 (mirroring the
//! upstream `example_generated.rs` instance
//! `Flags: u32 { A=1, B=2, C=4, ABC=7 }`); the two implementations (macro-expanded body
//! vs trait default body)
//! are transcribed independently; their equivalence is closed by the theorems
//! of verified/harness/coverage_props.rs.
//!
//! ## Mirror and relaxation ledger (KVerus relax conventions)
//! 1. `Flag<B> { name: &'static str, value: B }` (traits.rs:15-18) is not
//!    carried into the Verus `&'static str` literal layer: `name` is modeled
//!    as `name_id: u64` with id `0` standing for the empty string
//!    (<-> unnamed flag; cf. the unnamed branch `(Flag::new("", ..))` of
//!    `__bitflags_flag!` in internal.rs/public.rs); `value: B` is mirrored
//!    at the bits layer as `value_bits: u32`. String ** equality **
//!    comparison is a std trust boundary (upstream `flag.name() == name`),
//!    not a verification target.
//! 2. `Self::FLAGS: &'static [Flag<Self>]` (traits.rs:134) is a
//!    macro-expanded const table, transcribed as a fixed 4-entry table:
//!    spec twins `flag_*_spec(i)` + exec accessors
//!    `flag_name_id_at(i)`/`flag_bits_at(i)` (ensures bound entry by entry to
//!    the spec twins).
//! 3. The `Bits`/`Primitive`/`PublicFlags` marker traits (traits.rs:376-458)
//!    carry no verifiable obligations and are not transcribed; EMPTY/ALL in
//!    `impl_bits!` (traits.rs:398-448) are `0`/`u32::MAX` for u32 and are
//!    given as constants in the spec layer.
//! 4. The `iter().fold` loops of `Flags::all`/`all_named` (traits.rs:144-165)
//!    are transcribed as index loops + closed-form specs (the table has 4
//!    entries; the macro-expansion side is const-folded anyway);
//!    the `for + early return` of `Flags::from_name` (traits.rs:212-225) is
//!    unrolled on the fixed 4-entry table into a 4-step if-chain
//!    (first-match order preserved).
//! 5. The ** state machines proper ** of the str/iterator/fmt members
//!    (`iter`/`iter_names`/`iter_defined_names`/`iter_equal_names`)
//!    are mirrored separately in `verified/src/iter.rs`; the
//!    `parser::{ParseHex, WriteHex}` members live at the str layer -- see the
//!    B1 entry in the out/ summary ledger.
//! Consumption: this file is pulled in by `verified/src/lib.rs`; the harness
//! side mounts the whole src zone via `#[path = "../src/lib.rs"] mod ..;` and
//! never duplicates this file's specs.

use vstd::prelude::*;

verus! {

// Upstream `Bits::EMPTY` (traits.rs:389; u32 instance = 0)
pub open spec fn bits_empty() -> u32 {
    0u32
}

// Upstream `Bits::ALL` (traits.rs:390; u32 instance = u32::MAX)
pub open spec fn bits_all() -> u32 {
    0xffff_ffffu32
}

/* ============================================================
 * spec model (L2: the "Definitions" chapter of spec.md + the traits.rs
 * default bodies; authority = upstream spec.md, the crate's own
 * quasi-formal semantic document, plus the implementation code bodies)
 * ============================================================ */

/// `Self::all().bits()` of the monomorphized instance `TestFlags`
/// (A|B|C|ABC; the macro const-folded value)
pub open spec fn tflags_all_bits() -> u32 {
    0b0000_0111u32
}

/// spec.md sec. Known bit / sec. Unknown bit -- `Flags::known_bits` (traits.rs:167-170)
/// `self.bits() & Self::all().bits()`
pub open spec fn known_bits_of(all: u32, v: u32) -> u32 {
    v & all
}

/// `Flags::unknown_bits` (traits.rs:172-175): `self.bits() & !Self::all().bits()`
pub open spec fn unknown_bits_of(all: u32, v: u32) -> u32 {
    v & !all
}

/// spec.md sec. Contains -- `Flags::contains` (traits.rs:277-282)
/// `self.bits() & other.bits() == other.bits()`
pub open spec fn contains_sem(a: u32, b: u32) -> bool {
    a & b == b
}

/// spec.md sec. Intersects -- `Flags::intersects` (traits.rs:269-274)
pub open spec fn intersects_sem(a: u32, b: u32) -> bool {
    a & b != 0u32
}

/// spec.md sec. Empty -- `Flags::is_empty` (traits.rs:257-259)
pub open spec fn is_empty_sem(v: u32) -> bool {
    v == 0u32
}

/// spec.md sec. All -- `Flags::is_all` (traits.rs:262-266)
/// `Self::all().bits() | self.bits() == self.bits()` (the contains direction)
pub open spec fn is_all_sem_of(all: u32, v: u32) -> bool {
    contains_sem(v, all)
}

/// spec.md sec. Union -- `Flags::union` (traits.rs:347-349)
pub open spec fn union_sem(a: u32, b: u32) -> u32 {
    a | b
}

/// spec.md sec. Intersection -- `Flags::intersection` (traits.rs:341-343)
pub open spec fn intersection_sem(a: u32, b: u32) -> u32 {
    a & b
}

/// spec.md sec. Difference -- `Flags::difference` (traits.rs:356-358)
/// `self.bits() & !other.bits()` (explicitly does ** NOT ** truncate)
pub open spec fn difference_sem(a: u32, b: u32) -> u32 {
    a & !b
}

/// spec.md sec. Symmetric difference -- `Flags::symmetric_difference` (traits.rs:362-364)
pub open spec fn symmetric_difference_sem(a: u32, b: u32) -> u32 {
    a ^ b
}

/// spec.md sec. Complement -- `Flags::complement` (traits.rs:368-370)
/// `Self::from_bits_truncate(!self.bits())`: ** the only op that explicitly truncates **
pub open spec fn complement_sem_of(all: u32, v: u32) -> u32 {
    !v & all
}

/// spec.md sec. Truncate -- `Flags::from_bits_truncate` (traits.rs:201-203)
pub open spec fn truncate_sem_of(all: u32, v: u32) -> u32 {
    v & all
}

/* ============================================================
 * Flag model (the bits-layer mirror of traits.rs:14-63; relaxation 1)
 * ============================================================ */

/// Upstream `Flag::new(name, value)` (traits.rs:26-28, `pub const fn`;
/// carried by a Verus exec fn; value-construction semantics unchanged)
pub struct Flag {
/// models the upstream `name: &'static str`; id `0` <-> empty string <-> unnamed
    pub name_id: u64,
/// models the upstream `value: B` (via `value().bits()`, i.e. this very field)
    pub value_bits: u32,
}

impl Flag {
    /// traits.rs:26-28 `pub const fn new`
/// Upstream doc (traits.rs:21-25):
///   Define a flag.
///   If `name` is non-empty then the flag is named, otherwise it's unnamed.
    pub exec fn new(name_id: u64, value_bits: u32) -> (r: Flag)
        ensures
            r.name_id == name_id,
            r.value_bits == value_bits,
    {
        Flag { name_id, value_bits }
    }

/// traits.rs:35-37 `name` (returning the string is modeled as returning its id)
/// Upstream doc (traits.rs:30-34):
///   Get the name of this flag.
///   If the flag is unnamed then the returned string will be empty.
    pub exec fn name(&self) -> (r: u64)
        ensures r == self.name_id
    {
        self.name_id
    }

/// traits.rs:42-44 `value` (bits-layer mirror: returns the bits of the flag value)
/// Upstream doc (traits.rs:39-41):
///   Get the flags value of this flag.
    pub exec fn value_bits_fn(&self) -> (r: u32)
        ensures r == self.value_bits
    {
        self.value_bits
    }

/// traits.rs:51-53 `is_named`: upstream `!self.name.is_empty()`
/// model: id != 0 <-> non-empty name <-> named
/// Upstream doc (traits.rs:46-50):
///   Whether the flag is named.
///   If [`Flag::name`] returns a non-empty string then this method will return `true`.
    pub exec fn is_named(&self) -> (r: bool)
        ensures r == (self.name_id != 0u64)
    {
        self.name_id != 0u64
    }

/// traits.rs:60-62 `is_unnamed`: upstream `self.name.is_empty()`
/// Upstream doc (traits.rs:55-59):
///   Whether the flag is unnamed.
///   If [`Flag::name`] returns a non-empty string then this method will return `false`.
    pub exec fn is_unnamed(&self) -> (r: bool)
        ensures r == (self.name_id == 0u64)
    {
        self.name_id == 0u64
    }
}

/* ============================================================
 * FLAGS table of the monomorphized instance (macro-expanded const table; relaxation 2)
 *   TestFlags: u32 { const A = 1; const B = 2; const C = 4;
 *                     const ABC = A|B|C }      // example_generated.rs:8-65
 * ============================================================ */

/// Table length (FLAGS holds 4 entries: A, B, C, ABC)
pub const NUM_FLAGS: usize = 4;

/// spec twin: name id of the i-th flag ("A"->1, "B"->2, "C"->3, "ABC"->4;
/// consistent with the macro expansion entries `Flag::new("A", TestFlags::A)` etc.)
pub open spec fn flag_name_id_spec(i: int) -> u64 {
    if i == 0 {
        1u64
    } else if i == 1 {
        2u64
    } else if i == 2 {
        3u64
    } else {
        4u64
    }
}

/// spec twin: bits value of the i-th flag (A=0b001, B=0b010, C=0b100, ABC=0b111)
pub open spec fn flag_bits_spec(i: int) -> u32 {
    if i == 0 {
        0b0000_0001u32
    } else if i == 1 {
        0b0000_0010u32
    } else if i == 2 {
        0b0000_0100u32
    } else {
        0b0000_0111u32
    }
}

/// spec twin: whether the i-th flag is named (all 4 TestFlags entries are named)
pub open spec fn flag_named_spec(i: int) -> bool {
    0 <= i < 4
}

/// exec accessor: name id of the i-th entry (an if-chain == a const-table index)
pub exec fn flag_name_id_at(i: usize) -> (r: u64)
    requires i < NUM_FLAGS
    ensures
        r == flag_name_id_spec(i as int),
        r == (if i == 0 { 1u64 } else if i == 1 { 2u64 } else if i == 2 { 3u64 } else { 4u64 }),
{
    if i == 0 {
        1u64
    } else if i == 1 {
        2u64
    } else if i == 2 {
        3u64
    } else {
        4u64
    }
}

/// exec accessor: bits value of the i-th entry
pub exec fn flag_bits_at(i: usize) -> (r: u32)
    requires i < NUM_FLAGS
    ensures
        r == flag_bits_spec(i as int),
        // UF-free view (for the bit_vector tactic context)
        r == (if i == 0 { 0b0000_0001u32 } else if i == 1 { 0b0000_0010u32 } else if i == 2 { 0b0000_0100u32 } else { 0b0000_0111u32 }),
{
    if i == 0 {
        0b0000_0001u32
    } else if i == 1 {
        0b0000_0010u32
    } else if i == 2 {
        0b0000_0100u32
    } else {
        0b0000_0111u32
    }
}

/// exec accessor: whether the i-th entry is named
pub exec fn flag_named_at(i: usize) -> (r: bool)
    requires i < NUM_FLAGS
    ensures r == flag_named_spec(i as int)
{
    true
}

/* ---------- fold spec of all()/all_named() (relaxation 4 closed form) ---------- */

/// prefix fold of the index loop `for flag in Self::FLAGS`: the | of the bits
/// of the first i entries (traits.rs:146-152 `truncated |= flag.value().bits()`)
pub open spec fn all_fold_spec(i: int) -> u32 {
    if i <= 0 {
        0u32
    } else if i == 1 {
        0b0000_0001u32
    } else if i == 2 {
        0b0000_0011u32
    } else if i == 3 {
        0b0000_0111u32
    } else {
        0b0000_0111u32
    }
}

/// prefix fold of all_named (traits.rs:159-164: fold after filtering !name().is_empty())
/// all 4 TestFlags entries are named => all_named == all
pub open spec fn all_named_fold_spec(i: int) -> u32 {
    all_fold_spec(i)
}

/// lookup spec of from_name: the bits of the first flag in the table whose
/// `name id matches and which is named`
/// (the first-match return of traits.rs:218-224; no match => None)
pub open spec fn from_name_lookup(name: u64) -> Option<u32> {
    if name == 0u64 {
        Option::None
    } else if flag_name_id_spec(0) == name {
        Option::Some(flag_bits_spec(0))
    } else if flag_name_id_spec(1) == name {
        Option::Some(flag_bits_spec(1))
    } else if flag_name_id_spec(2) == name {
        Option::Some(flag_bits_spec(2))
    } else if flag_name_id_spec(3) == name {
        Option::Some(flag_bits_spec(3))
    } else {
        Option::None
    }
}


/* ============================================================
 * `Flags` trait default bodies -> monomorphized exec fns (bits layer;
 * entry-by-entry correspondence with traits.rs)
 * ============================================================ */

/// traits.rs:140-142 `fn empty()` (`from_bits_retain(Bits::EMPTY)`)
/// Upstream doc (traits.rs:139-139):
///   Get a flags value with all bits unset.
pub exec fn flags_empty() -> (r: u32)
    ensures
        r == bits_empty(),
        r == 0u32,
{
    0u32
}

/// traits.rs:144-153 `fn all()` -- index-loop mirror of
/// `truncated = truncated | flag.value().bits()` over `for flag in Self::FLAGS.iter()`
/// Upstream doc (traits.rs:144-144):
///   Get a flags value with all known bits set.
pub exec fn flags_all() -> (r: u32)
    ensures r == tflags_all_bits()
{
    let mut truncated: u32 = 0u32;
    let mut i: usize = 0;
    while i < NUM_FLAGS
        invariant
            i <= NUM_FLAGS,
            truncated == all_fold_spec(i as int),
        decreases NUM_FLAGS - i
    {
        let b: u32 = flag_bits_at(i);
        proof {
            if i == 0 {
                assert(truncated == 0u32);
                assert(b == 0b0000_0001u32);
                assert(0u32 | 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
                assert(truncated | b == 0b0000_0001u32);
                assert(all_fold_spec(1) == 0b0000_0001u32);
                assert(truncated | b == all_fold_spec(1));
            } else if i == 1 {
                assert(truncated == 0b0000_0001u32);
                assert(b == 0b0000_0010u32);
                assert(0b0000_0001u32 | 0b0000_0010u32 == 0b0000_0011u32) by (bit_vector);
                assert(truncated | b == 0b0000_0011u32);
                assert(all_fold_spec(2) == 0b0000_0011u32);
                assert(truncated | b == all_fold_spec(2));
            } else if i == 2 {
                assert(truncated == 0b0000_0011u32);
                assert(b == 0b0000_0100u32);
                assert(0b0000_0011u32 | 0b0000_0100u32 == 0b0000_0111u32) by (bit_vector);
                assert(truncated | b == 0b0000_0111u32);
                assert(all_fold_spec(3) == 0b0000_0111u32);
                assert(truncated | b == all_fold_spec(3));
            } else {
                assert(truncated == 0b0000_0111u32);
                assert(b == 0b0000_0111u32);
                assert(0b0000_0111u32 | 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
                assert(truncated | b == 0b0000_0111u32);
                assert(all_fold_spec(4) == 0b0000_0111u32);
                assert(truncated | b == all_fold_spec(4));
            }
        }
        truncated = truncated | b;
        i += 1;
    }
    proof {
        lemma_tflags_all_bits();
    }
    truncated
}

/// traits.rs:158-165 `fn all_named()` (fold after filtering named flags;
/// index loop + named-check mirror)
/// Upstream doc (traits.rs:155-157):
///   Get a flags value with all bits from named flags set.
///   This method is equivalent to [`Flags::all`] unless [`Flags::FLAGS`] contains unnamed flags.
pub exec fn flags_all_named() -> (r: u32)
    ensures r == all_named_fold_spec(NUM_FLAGS as int)
{
    let mut truncated: u32 = 0u32;
    let mut i: usize = 0;
    while i < NUM_FLAGS
        invariant
            i <= NUM_FLAGS,
            truncated == all_fold_spec(i as int),
        decreases NUM_FLAGS - i
    {
        let bits: u32 = flag_bits_at(i);
        let named: bool = flag_named_at(i);
        proof {
            if i == 0 {
                assert(truncated == 0u32);
                assert(bits == 0b0000_0001u32);
                assert(named == flag_named_spec(0)); assert(flag_named_spec(0) == true);
                if named {
                    assert(0u32 | 0b0000_0001u32 == 0b0000_0001u32) by (bit_vector);
                    assert(truncated | bits == 0b0000_0001u32);
                    assert(all_fold_spec(1) == 0b0000_0001u32);
                    assert(truncated | bits == all_fold_spec(1));
                }
            } else if i == 1 {
                assert(truncated == 0b0000_0001u32);
                assert(bits == 0b0000_0010u32);
                assert(named == flag_named_spec(1)); assert(flag_named_spec(1) == true);
                if named {
                    assert(0b0000_0001u32 | 0b0000_0010u32 == 0b0000_0011u32) by (bit_vector);
                    assert(truncated | bits == 0b0000_0011u32);
                    assert(all_fold_spec(2) == 0b0000_0011u32);
                    assert(truncated | bits == all_fold_spec(2));
                }
            } else if i == 2 {
                assert(truncated == 0b0000_0011u32);
                assert(bits == 0b0000_0100u32);
                assert(named == flag_named_spec(2)); assert(flag_named_spec(2) == true);
                if named {
                    assert(0b0000_0011u32 | 0b0000_0100u32 == 0b0000_0111u32) by (bit_vector);
                    assert(truncated | bits == 0b0000_0111u32);
                    assert(all_fold_spec(3) == 0b0000_0111u32);
                    assert(truncated | bits == all_fold_spec(3));
                }
            } else {
                assert(truncated == 0b0000_0111u32);
                assert(bits == 0b0000_0111u32);
                assert(named == flag_named_spec(3)); assert(flag_named_spec(3) == true);
                if named {
                    assert(0b0000_0111u32 | 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
                    assert(truncated | bits == 0b0000_0111u32);
                    assert(all_fold_spec(4) == 0b0000_0111u32);
                    assert(truncated | bits == all_fold_spec(4));
                }
            }
        }
        if named {
            truncated = truncated | bits;
        }
        i += 1;
    }
    proof {
        lemma_tflags_all_bits();
    }
    truncated
}

/// traits.rs:167-170 `fn known_bits(&self)` -- the mask param = Self::all().bits()
/// Upstream doc (traits.rs:167-167):
///   Get the known bits from a flags value.
pub exec fn flags_known_bits(all: u32, v: u32) -> (r: u32)
    ensures r == known_bits_of(all, v)
{
    v & all
}

/// traits.rs:172-175 `fn unknown_bits(&self)`
/// Upstream doc (traits.rs:172-172):
///   Get the unknown bits from a flags value.
pub exec fn flags_unknown_bits(all: u32, v: u32) -> (r: u32)
    ensures r == unknown_bits_of(all, v)
{
    v & !all
}

/// traits.rs:177-180 `fn contains_unknown_bits(&self)`
/// Upstream doc (traits.rs:177-177):
///   This method will return `true` if any unknown bits are set.
pub exec fn flags_contains_unknown_bits(all: u32, v: u32) -> (r: bool)
    ensures r == (unknown_bits_of(all, v) != 0u32)
{
    flags_unknown_bits(all, v) != 0u32
}

/// traits.rs:190-198 `fn from_bits(bits)`
/// Upstream doc (traits.rs:187-189):
///   Convert from a bits value.
///   This method will return `None` if any unknown bits are set.
pub exec fn flags_from_bits(all: u32, bits: u32) -> (r: Option<u32>)
    ensures
        r.is_some() == (bits == truncate_sem_of(all, bits)),
        r.is_some() ==> r.unwrap() == bits,
{
    let truncated = flags_from_bits_truncate(all, bits);
    if truncated == bits {
        Option::Some(bits)
    } else {
        Option::None
    }
}

/// traits.rs:201-203 `fn from_bits_truncate(bits)`
/// Upstream doc (traits.rs:200-200):
///   Convert from a bits value, unsetting any unknown bits.
pub exec fn flags_from_bits_truncate(all: u32, bits: u32) -> (r: u32)
    ensures r == truncate_sem_of(all, bits)
{
    flags_from_bits_retain(bits & all)
}

/// traits.rs:206 `fn from_bits_retain(bits)` (identity at the bits layer)
/// Upstream doc (traits.rs:205-205):
///   Convert from a bits value exactly.
pub exec fn flags_from_bits_retain(bits: u32) -> (r: u32)
    ensures r == bits
{
    bits
}

/// traits.rs:212-225 `fn from_name(name)` -- the for + first-match return is unrolled
/// on the fixed table into a 4-step if-chain (relaxation 4; the empty name
/// => None branch is the explicit check of upstream lines 213-215)
/// Upstream doc (traits.rs:208-211):
///   Get a flags value with the bits of a flag with the given name set.
///   This method will return `None` if `name` is empty or doesn't
///   correspond to any named flag.
pub exec fn flags_from_name(name: u64) -> (r: Option<u32>)
    ensures r == from_name_lookup(name)
{
    // Don't parse empty names as empty flags
    if name == 0u64 {
        return Option::None;
    }
    if flag_name_id_at(0) == name {
        return Option::Some(flag_bits_at(0));
    }
    if flag_name_id_at(1) == name {
        return Option::Some(flag_bits_at(1));
    }
    if flag_name_id_at(2) == name {
        return Option::Some(flag_bits_at(2));
    }
    if flag_name_id_at(3) == name {
        return Option::Some(flag_bits_at(3));
    }
    Option::None
}

/// traits.rs:257-259 `fn is_empty(&self)`
/// Upstream doc (traits.rs:256-256):
///   Whether all bits in this flags value are unset.
pub exec fn flags_is_empty(v: u32) -> (r: bool)
    ensures r == is_empty_sem(v)
{
    v == 0u32
}

/// traits.rs:262-266 `fn is_all(&self)`
/// (NOTE comment, verbatim: check against `Self::all` not `Bits::ALL`)
/// Upstream doc (traits.rs:261-261):
///   Whether all known bits in this flags value are set.
pub exec fn flags_is_all(all: u32, v: u32) -> (r: bool)
    ensures r == is_all_sem_of(all, v)
{
    proof {
        // (all | v == v) == (v & all == all): the is_all body vs the contains semantics
        assert((all | v == v) == (v & all == all)) by (bit_vector);
    }
    all | v == v
}

/// traits.rs:269-274 `fn intersects(&self, other)`
/// Upstream doc (traits.rs:268-268):
///   Whether any set bits in `other` are also set in `self`.
pub exec fn flags_intersects(a: u32, b: u32) -> (r: bool)
    ensures r == intersects_sem(a, b)
{
    a & b != 0u32
}

/// traits.rs:277-282 `fn contains(&self, other)`
/// Upstream doc (traits.rs:276-276):
///   Whether all set bits in `other` are also set in `self`.
pub exec fn flags_contains(a: u32, b: u32) -> (r: bool)
    ensures r == contains_sem(a, b)
{
    a & b == b
}

/// traits.rs:285-290 `fn truncate(&mut self)`
/// Upstream doc (traits.rs:284-284):
///   Remove any unknown bits from the flags.
pub exec fn flags_truncate(all: u32, v: &mut u32)
    requires true
    ensures *final(v) == truncate_sem_of(all, *old(v))
{
    *v = flags_from_bits_truncate(all, *v);
}

/// traits.rs:293-298 `fn insert(&mut self, other)`
/// (default body: `*self = from_bits_retain(self.bits()).union(other)`)
/// Upstream doc (traits.rs:292-292):
///   The bitwise or (`|`) of the bits in `self` and `other`.
pub exec fn flags_insert(a: &mut u32, b: u32)
    ensures *final(a) == union_sem(*old(a), b)
{
    *a = flags_union(*a, b);
}

/// traits.rs:304-309 `fn remove(&mut self, other)`
/// Upstream doc (traits.rs:300-303):
///   The intersection of `self` with the complement of `other` (`&!`).
///   This method is not equivalent to `self & !other` when `other` has unknown bits set.
///   `remove` won't truncate `other`, but the `!` operator will.
pub exec fn flags_remove(a: &mut u32, b: u32)
    ensures *final(a) == difference_sem(*old(a), b)
{
    *a = flags_difference(*a, b);
}

/// traits.rs:312-317 `fn toggle(&mut self, other)`
/// Upstream doc (traits.rs:311-311):
///   The bitwise exclusive-or (`^`) of the bits in `self` and `other`.
pub exec fn flags_toggle(a: &mut u32, b: u32)
    ensures *final(a) == symmetric_difference_sem(*old(a), b)
{
    *a = flags_symmetric_difference(*a, b);
}

/// traits.rs:320-329 `fn set(&mut self, other, value)`
/// Upstream doc (traits.rs:319-319):
///   Call [`Flags::insert`] when `value` is `true` or [`Flags::remove`] when `value` is `false`.
pub exec fn flags_set(a: &mut u32, b: u32, value: bool)
    ensures
        if value {
            *final(a) == union_sem(*old(a), b)
        } else {
            *final(a) == difference_sem(*old(a), b)
        },
{
    if value {
        flags_insert(a, b);
    } else {
        flags_remove(a, b);
    }
}

/// traits.rs:332-337 `fn clear(&mut self)` (`*self = Self::empty()`)
/// Upstream doc (traits.rs:331-331):
///   Unsets all bits in the flags.
pub exec fn flags_clear(a: &mut u32)
    ensures *final(a) == 0u32
{
    *a = flags_empty();
}

/// traits.rs:341-343 `fn intersection(self, other)`
/// Upstream doc (traits.rs:339-339):
///   The bitwise and (`&`) of the bits in `self` and `other`.
pub exec fn flags_intersection(a: u32, b: u32) -> (r: u32)
    ensures r == intersection_sem(a, b)
{
    flags_from_bits_retain(a & b)
}

/// traits.rs:347-349 `fn union(self, other)`
/// Upstream doc (traits.rs:345-345):
///   The bitwise or (`|`) of the bits in `self` and `other`.
pub exec fn flags_union(a: u32, b: u32) -> (r: u32)
    ensures r == union_sem(a, b)
{
    flags_from_bits_retain(a | b)
}

/// traits.rs:356-358 `fn difference(self, other)`
/// Upstream doc (traits.rs:351-354):
///   The intersection of `self` with the complement of `other` (`&!`).
///   This method is not equivalent to `self & !other` when `other` has unknown bits set.
///   `difference` won't truncate `other`, but the `!` operator will.
pub exec fn flags_difference(a: u32, b: u32) -> (r: u32)
    ensures r == difference_sem(a, b)
{
    flags_from_bits_retain(a & !b)
}

/// traits.rs:362-364 `fn symmetric_difference(self, other)`
/// Upstream doc (traits.rs:360-360):
///   The bitwise exclusive-or (`^`) of the bits in `self` and `other`.
pub exec fn flags_symmetric_difference(a: u32, b: u32) -> (r: u32)
    ensures r == symmetric_difference_sem(a, b)
{
    flags_from_bits_retain(a ^ b)
}

/// traits.rs:368-370 `fn complement(self)`
/// Upstream doc (traits.rs:366-366):
///   The bitwise negation (`!`) of the bits in `self`, truncating the result.
pub exec fn flags_complement(all: u32, v: u32) -> (r: u32)
    ensures r == complement_sem_of(all, v)
{
    flags_from_bits_truncate(all, !v)
}

// ---------------------------------------------------------------------------
// Proof lemmas (shared proof helpers; placed at the end of the file before the
// close of verus! so the spec and exec implementations read directly)
// ---------------------------------------------------------------------------
/// shared proof: instance mask value (machine grounds of the macro const folding)
pub proof fn lemma_tflags_all_bits()
    ensures tflags_all_bits() == 0b0000_0111u32
{
    assert(0b0000_0001u32 | 0b0000_0010u32 == 0b0000_0011u32) by (bit_vector);
    assert(0b0000_0011u32 | 0b0000_0100u32 == 0b0000_0111u32) by (bit_vector);
    assert(0b0000_0111u32 | 0b0000_0111u32 == 0b0000_0111u32) by (bit_vector);
}
} // verus!
