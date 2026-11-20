//! tpm-core 0.1.4 virtual-handle space bit arithmetic (src/handle.rs)
//! -- Verus translation.
//!
//! Upstream face: the slot-count constant, the handle-type mask
//! predicates, and the vhandle<->slot address pair
//! (src/handle.rs:1-26). The verifiable properties re-erected here:
//! vhandle_of and slot_of are mutual inverses on the whole
//! 0..2^24 index range (the twin closes it down to the arithmetic
//! edge, not just 0..SLOTS, since the same two-word decomposition
//! does both), every virtual handle is transient-range (top byte
//! 0x80), and the physical-handle validity predicate excludes the
//! two reserved values.
//!
//! TOOLCHAIN NOTE (probe-confirmed, pitfall #T5-1 of this batch):
//! this verus build treats ALL machine bit-ops (u32 `&`, on both
//! variables and constants -- even `0x80FF_FFFF & 0xFF00_0000 ==
//! 0x8000_0000` fails) as uninterpreted, extending the known u8
//! black hole (#T4-6) to every machine width. Every mask predicate
//! below is therefore lowered to the / %-spelling with the same
//! value face; an Origin note marks each lowering site.

use vstd::prelude::*;

verus! {

/// Origin Rust: /// Number of slots in the context table and session table.
/// pub const SLOTS: usize = 3; (handle.rs:1-2)
pub const SLOTS: usize = 3;

// ------------------------------------------------------------------
// Handle-type constants (handle.rs:3-9)
// ------------------------------------------------------------------

/// Origin Rust: const HANDLE_TYPE_MASK: u32 = 0xFF00_0000; (handle.rs:4)
pub(crate) const HANDLE_TYPE_MASK: u32 = 0xFF00_0000;
/// Origin Rust: const HT_HMAC_SESSION: u32 = 0x0200_0000; (handle.rs:5)
pub(crate) const HT_HMAC_SESSION: u32 = 0x0200_0000;
/// Origin Rust: const HT_POLICY_SESSION: u32 = 0x0300_0000; (handle.rs:6)
pub(crate) const HT_POLICY_SESSION: u32 = 0x0300_0000;
/// Origin Rust: const HT_TRANSIENT: u32 = 0x8000_0000; (handle.rs:7)
pub(crate) const HT_TRANSIENT: u32 = 0x8000_0000;
/// Pub-visibility twin of the sentinel constant: public spec faces
/// (rewrite.rs's predicates) may not cite pub(crate) constants, so
/// the value twin is published alongside the upstream pub(crate)
/// one below.
pub const CTX_SAVED_SENTINEL_VALUE: u32 = 0xFFFF_FFFF;
/// Origin Rust: /// Sentinel value in the context table meaning "saved but not loaded yet".
/// pub(crate) const CTX_SAVED_SENTINEL: u32 = 0xFFFF_FFFF; (handle.rs:8-9)
pub(crate) const CTX_SAVED_SENTINEL: u32 = CTX_SAVED_SENTINEL_VALUE;

// ------------------------------------------------------------------
// Spec twins of the handle-type arithmetic
// ------------------------------------------------------------------

/// Top byte of a handle word: bits 24..31 (the spec-level image of
/// `h & 0xFF00_0000`, lowered per the toolchain note above).
pub open spec fn handle_top_byte(h: u32) -> int {
    (h as int) / 16777216
}

/// Low 24 bits of a handle word (`h & 0x00FF_FFFF`, lowered).
pub open spec fn handle_low24(h: u32) -> int {
    (h as int) % 16777216
}

// ------------------------------------------------------------------
// vhandle <-> slot address pair (handle.rs:10-16)
// ------------------------------------------------------------------

/// Spec twin of the virtual-handle address: 0x80FF_FFFF - i. The
/// 24 low bits carry the index complemented; the top byte marks the
/// transient range.
pub open spec fn spec_vhandle_of(i: int) -> int {
    2164260863 - i
}

/// Spec twin of the slot address: 0x00FF_FFFF - (low 24 bits of v),
/// lowered from `0xFF_FFFF - (v & 0xFF_FFFF)`.
pub open spec fn spec_slot_of(v: int) -> int {
    16777215 - (v % 16777216)
}

/// Origin Rust: pub(crate) fn vhandle_of_exec(i: usize) -> u32 {
///     0x80FF_FFFFu32 - (i as u32)
/// } (handle.rs:10-12; upstream performs no bounds check on `i`: the
/// subtraction panics in debug when (i as u32) > 0x80FF_FFFF after
/// the usize-to-u32 truncation. The twin carries the missing bound
/// as a requires -- suspect row S-T5-1; every in-tree caller passes
/// a table slot index i < SLOTS)
pub(crate) exec fn vhandle_of_exec(i: usize) -> (v: u32)
    requires
        (i as int) <= 16777215,
    ensures
        (v as int) == spec_vhandle_of(i as int),
        handle_top_byte(v) == 128,
        spec_slot_of(v as int) == (i as int),
{
    let v = 0x80FF_FFFFu32 - (i as u32);
    // 0x80FF_FFFF == 16777216 * 129 - 1: the top byte is always
    // 0x80 here and the low bits keep the complemented index. These
    // two asserts are the whole bridge.
    assert(v as int == 16777216 * 129 - 1 - (i as int));
    assert((v as int) / 16777216 == 128);
    assert((v as int) % 16777216 == 16777215 - (i as int));
    v
}

/// Origin Rust: /// Reverse-map a slot index. Returns `usize`; callers check bounds with `< SLOTS`.
/// pub(crate) fn slot_of_exec(v: u32) -> usize {
///     (0xFF_FFFFu32 - (v & 0xFF_FFFFu32)) as usize
/// } (handle.rs:13-16; the `& 0xFF_FFFF` is lowered to
/// `% 16777216` -- same value on all u32, see the toolchain note)
pub(crate) exec fn slot_of_exec(v: u32) -> (r: usize)
    ensures
        (r as int) == spec_slot_of(v as int),
{
    (0x00FF_FFFFu32 - (v % 16777216u32)) as usize
}

// ------------------------------------------------------------------
// Handle-type predicates (handle.rs:17-26)
// ------------------------------------------------------------------

/// Spec twin of the transient test: top byte == 0x80.
pub open spec fn spec_is_transient(h: u32) -> bool {
    handle_top_byte(h) == 0x80
}

/// Spec twin of the session test: HMAC or policy family.
pub open spec fn spec_is_session(h: u32) -> bool {
    handle_top_byte(h) == 0x02 || handle_top_byte(h) == 0x03
}

/// Int-valued twins of the three predicates (wire-decoded handle
/// words are ints everywhere upstream of this twin; the same top-
/// byte arithmetic, no casts anywhere).
pub open spec fn spec_is_transient_val(h: int) -> bool {
    h / 16777216 == 128
}

/// Int-valued session test: HMAC or policy family.
pub open spec fn spec_is_session_val(h: int) -> bool {
    h / 16777216 == 2 || h / 16777216 == 3
}

/// Int-valued physical-handle validity test.
pub open spec fn spec_valid_phandle_val(h: int) -> bool {
    h != 0 && h != 4294967295
}

/// Spec twin of the physical-handle validity test: neither of the
/// two reserved values.
pub open spec fn spec_valid_phandle(h: u32) -> bool {
    h != 0 && h != CTX_SAVED_SENTINEL_VALUE
}

/// Origin Rust: pub fn is_transient_exec(h: u32) -> bool {
///     (h & HANDLE_TYPE_MASK) == HT_TRANSIENT
/// } (handle.rs:17-19; & lowered to the top-byte quotient per #T5-1)
pub exec fn is_transient_exec(h: u32) -> (r: bool)
    ensures
        r == spec_is_transient(h),
{
    h / 16777216u32 == HT_TRANSIENT / 16777216u32
}

/// Origin Rust: pub fn is_session_exec(h: u32) -> bool {
///     let t = h & HANDLE_TYPE_MASK;
///     t == HT_HMAC_SESSION || t == HT_POLICY_SESSION
/// } (handle.rs:20-23; same lowering)
pub exec fn is_session_exec(h: u32) -> (r: bool)
    ensures
        r == spec_is_session(h),
{
    let t = h / 16777216u32;
    t == HT_HMAC_SESSION / 16777216u32 || t == HT_POLICY_SESSION / 16777216u32
}

/// Origin Rust: pub fn valid_phandle_exec(h: u32) -> bool {
///     h != 0 && h != CTX_SAVED_SENTINEL
/// } (handle.rs:24-26; pure value comparisons, no lowering needed)
pub exec fn valid_phandle_exec(h: u32) -> (r: bool)
    ensures
        r == spec_valid_phandle(h),
{
    h != 0 && h != CTX_SAVED_SENTINEL
}

// ------------------------------------------------------------------
// Roundtrip lemmas (file tail per the proof zone banner).
// ------------------------------------------------------------------

/// The vhandle/slot pair are exact inverses on the full index range
/// 0..=16777215 (the twin extends the inventory's 0..SLOTS claim to
/// the arithmetic edge). The exec twins each carry this as their own
/// ensures; this lemma states the spec-level composition and the
/// word bounds for downstream proof use.
pub(crate) proof fn lemma_vhandle_slot_inverses(i: int)
    requires
        0 <= i <= 16777215,
    ensures
        spec_slot_of(spec_vhandle_of(i)) == i,
        spec_vhandle_of(i) / 16777216 == 128,
        spec_vhandle_of(i) >= 2147483648,
        spec_vhandle_of(i) <= 2164260863,
        spec_vhandle_of(i) % 16777216 == 16777215 - i,
{
    let v = spec_vhandle_of(i);
    assert(v == 16777216 * 129 - 1 - i);
    assert(v / 16777216 == 128);
    assert(v % 16777216 == 16777215 - i);
}

/// Slot images never leave the index range: 16777215 - (v % 2^24)
/// stays within 0..=16777215, so the `>= SLOTS` checks downstream
/// are pure range comparisons with no overflow surprises.
pub(crate) proof fn lemma_slot_of_bounds(v: u32)
    ensures
        0 <= spec_slot_of(v as int),
        spec_slot_of(v as int) <= 16777215,
{
    let low = (v as int) % 16777216;
    assert(0 <= low < 16777216);
}

} // verus!
