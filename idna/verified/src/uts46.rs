// Verified transcription of idna 1.1.0 src/uts46.rs: leaf/skeleton helpers plus
// the idna_adapter injection perimeter, the bidi/joining scan tiers, and the
// in-place validity tiers check_label/after_punycode_decode.
//
// Upstream pin: 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a (servo/rust-url, SUBDIR=idna).
// Basis: database/idna/code/idna/src/uts46.rs (1721 lines) as a standalone file
// (no #[path] includes, no external crate deps), ending with fn main() {}.
// Visibility note: the private leaf helpers below are opened to `pub` where the
// assertion-theorem harness (../harness/uts46_leaf.rs and
// ../harness/idnatest_v2_samples.rs) consumes them via #[path];
// upstream keeps these helpers private (crate-internal consumers only). A few
// consts and one bit_vector binding lemma are opened to `pub` the same way
// (UPPER_CASE_MASK/GLYPHLESS_MASK/LDH_MASK/mask_const_lemmas; the PUNYCODE_ENCODE
// gate const likewise).
// Scope: mask/deny-list constants and mask builders, punycode prefix detection,
// inclusive-range helpers, label predicates, punycode classification,
// AsciiDenyList construction, DNS length verification, hyphen marking, the
// ASCII fast-path scan tier of process_inner, the adapter-contract injection
// perimeter (P1-P6), the per-position scan tiers of is_bidi and
// has_appropriately_joining_char, the two in-place validity tiers
// check_label (ContextJ working-state channels: a marked joiner participates
// in later neighbor scans with its U+FFFD identity) and after_punycode_decode
// (the normalize_validate push phase and the first-difference zip marking),
// the WHATWG UTF-8 lossy-decoder transcription of the map_normalize entry
// feed (utf8_lossy_chars and its step model), the punycode emission tier
// write_punycode_label against the Vec<char> sink representation, and the
// CheckBidi post-pass marking tier (bidi_marking_pass/bidi_mark_label with
// the positional predicates b_marked/b_final_at and the numeral-state
// coding of the RtlNumeralState machine).
// Zone rule: each verified transcription keeps live proof obligations at its
// panic/bounds/overflow points; relaxation is used only where noted inline
// (bitwise reasoning routes through bit_vector-mode lemma calls, each of which
// is machine-checked, not assumed).
//
// Locked ledger of the blocked pipeline surface (one line each with reason):
// * Uts46::to_ascii/to_ascii_from_cow/to_unicode/to_user_interface and the
//   lib-level domain_to_* entries: depend on the Cow/str/String layer
//   (from_utf8_unchecked, String allocation) plus the closed pipeline core.
// * process_innermost / process (uts46.rs:1093-1494, 773-1045): the
//   process-level label loop and the sink state machines. Closed now:
//   check_label (ContextJ working-state semantics), after_punycode_decode
//   (the P6 push/zip marking, plus the batch-F aggregate content
//   channels), utf8_lossy_chars (the WHATWG lossy-decoder transcription
//   of the map_normalize entry feed), write_punycode_label (the punycode
//   emission tier), bidi_marking_pass (the CheckBidi post-pass over the
//   assembled buffer, batch E), and the batch-F innermost tier closes:
//   the Vec-window bridge family (pim_win_extract/pim_win_storeback/
//   pim_check_hyphens_dom/pim_check_label_dom; the build leaves the
//   caller content of a `&mut v[s..t]` Range borrow unconstrained while
//   Vec::as_mut_slice carries the full two-way bridge, so in-place tier
//   consumption routes clone-out/copy-back), the ASCII deny push family
//   (pim_first_fffd_pos/pim_ascii_deny_push with a scan/push split: the
//   while join keeps only invariants, so fire discriminators never ride
//   break edges), the pre-existing-punycode label branch
//   (pim_label_ascii_punycode consuming decode_bytes_internal +
//   after_punycode_decode + the check_label window wrapper, exact
//   per-arm content split on the decode model), and the mapping window
//   (pim_map_window + pim_map_event: the mapped-char walker with the
//   per-sub-label tag census, and the full uts46.rs:1262-1360 xn--
//   rediscovery whose marking pass carries the pass-reality equation --
//   U+FFFD itself is non-ASCII, so the pass is a no-op iff the window
//   was pristine ASCII, which also carries the decode precondition).
//   Closed in batch G: the outer label loop of process_innermost itself
//   (the label motor over (pos, last_done) with the value-equal
//   pre-consumed separator accounting; the upstream dots+1 label
//   counter is re-encoded without a usize counter, whose increment
//   this build cannot discharge against usize::MAX), the passthrough-
//   prefix ASCII channel and the tag-payload ASCII channel of the
//   innermost contract, and the process_inner fast-path wrapper (the
//   scan defer composition; the tail is the domain_name suffix from
//   the defer index, a requires of the innermost call per the upstream
//   geometry).
//   Still open (the takeover continuation): the process sink-write walk
//   (uts46.rs:832-1040, the mixed-case/pass-through/decide/punycode
//   emission arms with the passthrough_up_to_extended register, the
//   flush bookkeeping, and the ascii_sink mirror pass) with the
//   DecideUnicode threading at the output_as_unicode seam; then the
//   Cow/str facade of the lib-level domain_to_* entries. The io
//   overhead of 6 exec shims P1-P6 is the complete assumed perimeter;
//   nothing else is assumed (the strengthened callee contracts are
//   same-tree, internally machine-verified additions).
// * From<core::fmt::Error> / From<crate::punycode::PunycodeEncodeError> impls
//   (uts46.rs:435-447): tied to blocked external ends; enum semantics need no
//   From impls in this face.
// Build notes for the takeover (reproduced, probe-tested): while joins
// keep only invariants (every break/return carries its own ensure
// bridges); every ghost-let/slice-view/param-derived constant (even
// dn_off + tail.len() == domain_name.len()) is havoced at loop heads and
// must be re-bound by an invariant conjunct; assert-forall takes implies
// with a chained-comparison antecedent; usize increment overflow checks
// need int-space feed asserts; aggregate callee channels must be prefix
// form (old@.subrange(0,s).add(f(window))).
//
// Upstream doc (uts46.rs:9-22), module header condensed:
// "This module provides the lower-level API for UTS 46. [`Uts46::process`] is
// the core that the other convenience methods build on. UTS 46 flags map to
// this API as follows: CheckHyphens -> Hyphens; CheckBidi and CheckJoiners are
// always true; UseSTD3ASCIIRules -> AsciiDenyList::STD3/EMPTY, with the
// WHATWG post-check corresponding to AsciiDenyList::URL;
// Transitional_Processing is deprecated and always false; VerifyDnsLength ->
// DnsLength; IgnoreInvalidPunycode is always false."

use vstd::prelude::*;
use vstd::seq::Seq;

// The pipeline tiers below consume the punycode internal-caller cores and
// their models (decode_bytes_internal/decode_char_internal/
// encode_into_chars_internal/encode_full_model/is_valid_code_point and the
// std::char::from_u32 assume_specification registered in that file). The
// single-file consumption is the established #[path] pattern (the harness
// panels consume this file the same way), so the punycode mirror stays the
// single source of truth for those assets.
#[path = "punycode.rs"]
mod punycode_v;

verus! {

// ---------------------------------------------------------------- Spec models

/// Bitwise membership predicate: bit b of bits is set (b must be in 0..128).
pub open spec fn bit_is_set(bits: u128, b: u8) -> bool {
    b < 128 && ((bits >> b) & 1) == 1
}

/// Plain bool-range model of the upper-case ASCII mask (chars 'A'..='Z').
pub open spec fn upper_case_pred(b: u8) -> bool {
    b >= b'A' && b <= b'Z'
}

/// Plain bool-range model of the glyphless ASCII mask (bytes <= ' ' or 0x7F).
pub open spec fn glyphless_pred(b: u8) -> bool {
    b <= b' ' || b == 0x7F
}

/// Plain bool-range model of the STD3 ASCII deny list (the complement of
/// letters, digits, hyphen, and dot).
pub open spec fn ldh_pred(b: u8) -> bool {
    !((b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-' || b == b'.')
}

/// Spec model of the 13 WHATWG-forbidden ASCII bytes of the URL deny list
/// (the bytes of the upstream string "%#/:<>?@[\\]^|").
pub open spec fn url_deny_pred(k: u8) -> bool {
    k == b'%' || k == b'#' || k == b'/' || k == b':' || k == b'<'
        || k == b'>' || k == b'?' || k == b'@' || k == b'[' || k == b'\\'
        || k == b']' || k == b'^' || k == b'|'
}

/// Membership model used by AsciiDenyList::new: is byte k among the first
/// `upto` bytes of deny_list.
pub open spec fn bytes_contain_upto(deny_list: &[u8], upto: int, k: u8) -> bool
    decreases upto
{
    if upto <= 0 {
        false
    } else {
        deny_list[upto - 1] == k || bytes_contain_upto(deny_list, upto - 1, k)
    }
}

// ---------------------------------------------------------------- Constants (uts46.rs:33-106)

/// Upstream doc (uts46.rs:33-34):
/// ICU4C-compatible constraint.
/// https://unicode-org.atlassian.net/browse/ICU-13727
const PUNYCODE_DECODE_MAX_INPUT_LENGTH: usize = 2000;

/// Upstream doc (uts46.rs:37-43):
/// ICU4C-compatible constraint. (Note: ICU4C measures
/// UTF-16 and we measure UTF-32. This means that we
/// allow longer non-BMP inputs. For this implementation,
/// the denial-of-service scaling does not depend on BMP vs.
/// non-BMP: only the scalar values matter.)
///
/// https://unicode-org.atlassian.net/browse/ICU-13727
// Visibility note: opened to `pub` so the pub spec models of check_label
// can name the gate constant; upstream keeps it private.
pub const PUNYCODE_ENCODE_MAX_INPUT_LENGTH: usize = 1000;

/// Upstream doc (uts46.rs:46-47):
/// For keeping track of what kind of numerals have been
/// seen in an RTL label.
#[derive(Debug, PartialEq, Eq)]
enum RtlNumeralState {
    Undecided,
    European,
    Arabic,
}

/// Upstream doc (uts46.rs:55):
/// Computes the mask for upper-case ASCII.
///
/// Verus note: the upstream item is `const fn`; this build cannot call a
/// verified function from a const initializer, so the builder is transcribed
/// as a verified exec fn (below). The runtime recomputation is semantically
/// identical; see the const UPPER_CASE_MASK discussion below.
/* Origin Rust: const fn upper_case_mask() -> u128 {
 *     let mut accu = 0u128;
 *     let mut b = 0u8;
 *     while b < 128 {
 *         if (b >= b'A') && (b <= b'Z') {
 *             accu |= 1u128 << b;
 *         }
 *         b += 1;
 *     }
 *     accu
 * }
 */
fn upper_case_mask() -> (r: u128)
    ensures
        forall |b: u8| b < 128 ==> bit_is_set(r, b) == upper_case_pred(b),
{
    proof { zero_bits_lemma(); }
    let mut accu: u128 = 0;
    let mut b: u8 = 0;
    while b < 128
        invariant
            b <= 128,
            forall |k: u8| k < b ==> bit_is_set(accu, k) == upper_case_pred(k),
            forall |k: u8| b <= k < 128 ==> !bit_is_set(accu, k),
        decreases 128 - b as int
    {
        if (b >= b'A') && (b <= b'Z') {
            /* Verus treats machine-bitwise ops as uninterpreted in the default
             * prover mode; loop-body maintenance facts are closed by a
             * bit_vector-mode lemma (machine-checked) on the named new value.
             * Origin Rust: accu |= 1u128 << b;
             */
            let nb = accu | (1u128 << b);
            proof { set_bit_lemma(accu, nb, b); }
            accu = nb;
        }
        b = b + 1;
    }
    accu
}

/// Upstream doc (uts46.rs:68):
/// Bit set for upper-case ASCII.
///
/// Verus note: the upstream initializers of UPPER_CASE_MASK/GLYPHLESS_MASK/
/// LDH_MASK/DOT_MASK call const fns, which verus cannot verify inside const
/// initializers. Each mask const is transcribed with its pre-computed literal
/// value; the binding between the literal and the spec model is machine-checked
/// by a bit_vector-mode lemma (mask_const_lemmas below), so no unverified
/// arithmetic remains in the file. Upstream const-eval would produce exactly
/// these literals (verified per-bit by those lemmas).
/* Origin Rust: const UPPER_CASE_MASK: u128 = upper_case_mask();
 */
// Visibility note: opened to `pub` (with the binding lemma) so the
// assertion harness can exercise the mask consts; upstream keeps them
// private.
pub const UPPER_CASE_MASK: u128 = 0x7fffffe0000000000000000;

/// Upstream doc (uts46.rs:71):
/// Computes the mask for glyphless ASCII.
/* Origin Rust: const fn glyphless_mask() -> u128 {
 *     let mut accu = 0u128;
 *     let mut b = 0u8;
 *     while b < 128 {
 *         if (b <= b' ') || (b == 0x7F) {
 *             accu |= 1u128 << b;
 *         }
 *         b += 1;
 *     }
 *     accu
 * }
 */
fn glyphless_mask() -> (r: u128)
    ensures
        forall |b: u8| b < 128 ==> bit_is_set(r, b) == glyphless_pred(b),
{
    proof { zero_bits_lemma(); }
    let mut accu: u128 = 0;
    let mut b: u8 = 0;
    while b < 128
        invariant
            b <= 128,
            forall |k: u8| k < b ==> bit_is_set(accu, k) == glyphless_pred(k),
            forall |k: u8| b <= k < 128 ==> !bit_is_set(accu, k),
        decreases 128 - b as int
    {
        if (b <= b' ') || (b == 0x7F) {
            /* Origin Rust: accu |= 1u128 << b;
             */
            let nb = accu | (1u128 << b);
            proof { set_bit_lemma(accu, nb, b); }
            accu = nb;
        }
        b = b + 1;
    }
    accu
}

/// Upstream doc (uts46.rs:84):
/// Bit set for glyphless ASCII.
/* Origin Rust: const GLYPHLESS_MASK: u128 = glyphless_mask();
 */
pub const GLYPHLESS_MASK: u128 = 0x800000000000000000000001ffffffff;

/// Upstream doc (uts46.rs:87):
/// The mask for the ASCII dot.
const DOT_MASK: u128 = 1u128 << b'.' as u128;

/// Upstream doc (uts46.rs:90):
/// Computes the ASCII deny list for STD3 ASCII rules.
/* Origin Rust: const fn ldh_mask() -> u128 {
 *     let mut accu = 0u128;
 *     let mut b = 0u8;
 *     while b < 128 {
 *         if !((b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-' || b == b'.') {
 *             accu |= 1u128 << b;
 *         }
 *         b += 1;
 *     }
 *     accu
 * }
 */
fn ldh_mask() -> (r: u128)
    ensures
        forall |b: u8| b < 128 ==> bit_is_set(r, b) == ldh_pred(b),
{
    proof { zero_bits_lemma(); }
    let mut accu: u128 = 0;
    let mut b: u8 = 0;
    while b < 128
        invariant
            b <= 128,
            forall |k: u8| k < b ==> bit_is_set(accu, k) == ldh_pred(k),
            forall |k: u8| b <= k < 128 ==> !bit_is_set(accu, k),
        decreases 128 - b as int
    {
        if !((b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-' || b == b'.') {
            /* Origin Rust: accu |= 1u128 << b;
             */
            let nb = accu | (1u128 << b);
            proof { set_bit_lemma(accu, nb, b); }
            accu = nb;
        }
        b = b + 1;
    }
    accu
}

/* Origin Rust: const LDH_MASK: u128 = ldh_mask();
 */
// Visibility note: opened to `pub` (with its binding lemma below) so the
// assertion harness can exercise the STD3 deny-bits at the exec level;
// upstream keeps the const private.
pub const LDH_MASK: u128 = 0xf8000001fffffffffc009fffffffffff;

const PUNYCODE_PREFIX: u32 =
    ((b'-' as u32) << 24) | ((b'-' as u32) << 16) | ((b'N' as u32) << 8) | b'X' as u32;

const PUNYCODE_PREFIX_MASK: u32 = (0xFF << 24) | (0xFF << 16) | (0xDF << 8) | 0xDF;

// ---------------------------------------------------------------- Punycode prefix detection (uts46.rs:117-130)

/// Byte-form spec model of has_punycode_prefix: (u & PUNYCODE_PREFIX_MASK)
/// == PUNYCODE_PREFIX means slice[0..2] == "xn" case-insensitively (the 0xDF
/// masks fold 'x'/'X' and 'n'/'N') and slice[2..4] == "--" exactly.
pub open spec fn spec_has_punycode_prefix(slice: &[u8]) -> bool {
    slice.len() >= 4
        && (((slice[0] as u32) & 0xDF) == b'X' as u32)
        && (((slice[1] as u32) & 0xDF) == b'N' as u32)
        && slice[2] == b'-'
        && slice[3] == b'-'
}

#[inline(always)]
pub fn has_punycode_prefix(slice: &[u8]) -> (r: bool)
    ensures
        r == spec_has_punycode_prefix(slice),
{
    if slice.len() < 4 {
        return false;
    }
    /* u32::from is not specced by vstd; the widening cast is semantics-equal.
     * Origin Rust: let a = slice[0];
     *             let b = slice[1];
     *             let c = slice[2];
     *             let d = slice[3];
     *             let u = (u32::from(d) << 24) | (u32::from(c) << 16) | (u32::from(b) << 8) | u32::from(a);
     */
    let a = slice[0];
    let b = slice[1];
    let c = slice[2];
    let d = slice[3];
    let u = ((d as u32) << 24) | ((c as u32) << 16) | ((b as u32) << 8) | (a as u32);
    // Bitwise reasoning is closed by the bit_vector mode on ground constants.
    // The upstream comment: "Sadly, the optimizer doesn't figure out that more
    // idiomatic code should compile to masking on 32-bit value."
    assert(((u & PUNYCODE_PREFIX_MASK) == PUNYCODE_PREFIX) == (
        (((a as u32) & 0xDF) == (b'X' as u32))
        && (((b as u32) & 0xDF) == (b'N' as u32))
        && (c == b'-')
        && (d == b'-')
    )) by (bit_vector)
        requires
            u == (((d as u32) << 24) | ((c as u32) << 16) | ((b as u32) << 8) | (a as u32));
    (u & PUNYCODE_PREFIX_MASK) == PUNYCODE_PREFIX
}

// ---------------------------------------------------------------- Inclusive range helpers (uts46.rs:132-140)

/* u8::wrapping_sub is not specced by vstd; it is transcribed as the Euclidean
 * remainder of the integer difference, which is exactly the u8 wrapping
 * semantics, with start <= end assumed as upstream call sites do.
 * Origin Rust: fn in_inclusive_range8(u: u8, start: u8, end: u8) -> bool {
 *                 u.wrapping_sub(start) <= (end - start)
 *             }
 */
#[inline(always)]
fn in_inclusive_range8(u: u8, start: u8, end: u8) -> (r: bool)
    requires
        start <= end,
    ensures
        r == (u >= start && u <= end),
{
    /* u8::wrapping_sub is not specced by vstd and int-casts are spec-only;
     * the wrapping difference is computed in-range on u32 with the same
     * value as u.wrapping_sub(start).
     * Origin Rust: (u.wrapping_sub(start) <= (end - start))
     */
    let diff: u32 = if u >= start {
        (u - start) as u32
    } else {
        (u as u32) + 256 - (start as u32)
    };
    diff <= (end as u32) - (start as u32)
}

/* Origin Rust: fn in_inclusive_range_char(c: char, start: char, end: char) -> bool {
 *                 u32::from(c).wrapping_sub(u32::from(start)) <= (u32::from(end) - u32::from(start))
 *             }
 */
#[inline(always)]
fn in_inclusive_range_char(c: char, start: char, end: char) -> (r: bool)
    requires
        start <= end,
    ensures
        r == (c >= start && c <= end),
{
    /* Origin Rust: (u32::from(c).wrapping_sub(u32::from(start)) <= (u32::from(end) - u32::from(start)))
     */
    let cu = c as u32;
    let su = start as u32;
    let eu = end as u32;
    let diff: u64 = if cu >= su {
        (cu - su) as u64
    } else {
        (cu as u64) + 4294967296 - (su as u64)
    };
    diff <= (eu - su) as u64
}

// ---------------------------------------------------------------- Passthrough label (uts46.rs:142-183)

/// Spec model of is_passthrough_ascii_label: not a "xn--"-prefixed label with
/// the 3rd/4th hyphen pair, first byte in a..=z, all bytes [a-z0-9-] past the
/// first, and no trailing hyphen; the empty label passes through outright.
pub open spec fn spec_is_passthrough_ascii_label(label: &[u8]) -> bool {
    (label.len() < 4 || !(label[2] == b'-' && label[3] == b'-'))
    && (label.len() == 0
        || ((label[0] >= b'a' && label[0] <= b'z')
            && (forall |i: int| 1 <= i < label.len() ==>
                ((label[i] >= b'a' && label[i] <= b'z')
                    || (label[i] >= b'0' && label[i] <= b'9')
                    || label[i] == b'-'))
            && label[label.len() - 1] != b'-'))
}

#[inline(always)]
pub fn is_passthrough_ascii_label(label: &[u8]) -> (r: bool)
    ensures
        r == spec_is_passthrough_ascii_label(label),
{
    // XXX if we aren't performing _CheckHyphens_, this could
    // check for "xn--" and pass through YouTube CDN node names.
    if label.len() >= 4 && label[2] == b'-' && label[3] == b'-' {
        return false;
    }
    /* slice::split_first is not specced by vstd; the (first, tail) split is
     * transcribed as index accesses over [0] and [1, len).
     * Origin Rust: if let Some((&first, tail)) = label.split_first() {
     */
    if label.len() == 0 {
        // empty
        return true;
    }
    // We need to check the first and last character
    // more strictly in case this turns out to be a
    // label in a bidi domain name. This has the side
    // effect that this function only accepts labels
    // that also conform to the STD3 rules.
    //
    // XXX: If we are in the fail-fast mode (i.e. we don't need
    // to be able to overwrite anything with U+FFFD), we could
    // merely record that we've seen a digit here and error out
    // if we later discover that the domain name is a bidi
    // domain name.
    if !in_inclusive_range8(label[0], b'a', b'z') {
        return false;
    }
    let mut i: usize = 1;
    while i < label.len()
        invariant
            1 <= i <= label.len(),
            forall |j: int| 1 <= j < i ==>
                ((label[j] >= b'a' && label[j] <= b'z')
                    || (label[j] >= b'0' && label[j] <= b'9')
                    || label[j] == b'-'),
        decreases label.len() - i
    {
        /* Origin Rust: for &b in tail {
         *                 // If we used LDH_MASK, we'd have to check
         *                 // the bytes for the ASCII range anyhow.
         */
        let b = label[i];
        if in_inclusive_range8(b, b'a', b'z') {
            i = i + 1;
            continue;
        }
        if in_inclusive_range8(b, b'0', b'9') {
            i = i + 1;
            continue;
        }
        if b == b'-' {
            i = i + 1;
            continue;
        }
        return false;
    }
    /* Origin Rust: label.last() != Some(&b'-')
     */
    label[label.len() - 1] != b'-'
}

// ---------------------------------------------------------------- ASCII fast-path split (uts46.rs:185-202)

#[inline(always)]
fn split_ascii_fast_path_prefix(label: &[u8]) -> (ret: (&[u8], &[u8]))
    ensures
        ret.0.len() + ret.1.len() == label.len(),
        forall |i: int| 0 <= i < ret.0.len() ==> ret.0[i] == label[i] && label[i] < 0x80,
        forall |i: int| 0 <= i < ret.1.len() ==> ret.1[i] == label[ret.0.len() + i],
        // either all ASCII, or the tail starts either at a first non-ASCII
        // byte (head.len()==0) or one byte before the first non-ASCII byte
        // (one ASCII char is left in the tail for combining characters).
        (ret.0.len() == label.len()
            || (ret.0.len() == 0 && label.len() >= 1 && label[0] >= 0x80)
            || (ret.0.len() + 2 <= label.len()
                && label[ret.0.len() as int] < 0x80
                && label[ret.0.len() as int + 1] >= 0x80)),
{
    /* slice::iter().position is not specced by vstd; transcribed as an index
     * search loop computing the same position.
     * Origin Rust: if let Some(pos) = label.iter().position(|b| !b.is_ascii()) {
     *                 if pos == 0 {
     *                     // First is non-ASCII
     *                     (&[], label)
     *                 } else {
     *                     // Leave one ASCII character in the suffix
     *                     // in case it's a letter that a combining
     *                     // character combines with.
     *                     let (head, tail) = label.split_at(pos - 1);
     *                     (head, tail)
     *                 }
     *             } else {
     *                 // All ASCII
     *                 (label, &[])
     *             }
     */
    let mut pos: usize = 0;
    while pos < label.len()
        invariant
            pos <= label.len(),
            forall |j: int| 0 <= j < pos ==> label[j] < 0x80,
        decreases label.len() - pos
    {
        if label[pos] >= 0x80 {
            if pos == 0 {
                // First is non-ASCII
                let head = &label[0..0];
                let tail = &label[0..label.len()];
                return (head, tail);
            } else {
                // Leave one ASCII character in the suffix
                // in case it's a letter that a combining
                // character combines with.
                proof {
                    assert(pos >= 1);
                    assert(label[(pos - 1) as int] < 0x80);
                    assert(label[pos as int] >= 0x80);
                    assert(pos + 1 <= label.len());
                }
                let head = &label[0..pos - 1];
                let tail = &label[pos - 1..label.len()];
                return (head, tail);
            }
        }
        pos = pos + 1;
    }
    // All ASCII
    let head = &label[0..pos];
    let tail = &label[pos..pos];
    (head, tail)
}

// ---------------------------------------------------------------- Deny-list application (uts46.rs:204-228)

// Input known to be lower-case, but may contain non-ASCII.
//
/// Verus note: `checked_shl` is not specced by vstd; its None channel covers
/// exactly code points >= 128 (the u128 shift width), so the fall-through is
/// transcribed as an explicit code-point bound check.
/* Origin Rust: fn apply_ascii_deny_list_to_lower_cased_unicode(c: char, deny_list: u128) -> char {
 *                 if let Some(shifted) = 1u128.checked_shl(u32::from(c)) {
 *                     if (deny_list & shifted) == 0 {
 *                         c
 *                     } else {
 *                         '\u{FFFD}'
 *                     }
 *                 } else {
 *                     c
 *                 }
 *             }
 */
#[inline(always)]
pub fn apply_ascii_deny_list_to_lower_cased_unicode(c: char, deny_list: u128) -> (r: char)
    ensures
        r == c || r == '\u{FFFD}',
        (r == c) == (((c as u32) >= 0x80) || !bit_is_set(deny_list, (c as u32) as u8)),
        // Denied ASCII code points map to U+FFFD.
        ((c as u32) < 0x80) && bit_is_set(deny_list, (c as u32) as u8) ==> r == '\u{FFFD}',
{
    if (c as u32) < 0x80 {
        let cb = (c as u32) as u8;
        if (deny_list & (1u128 << cb)) != 0 {
            assert(((deny_list & (1u128 << cb)) != 0) == bit_is_set(deny_list, cb)) by (bit_vector);
            '\u{FFFD}'
        } else {
            assert(((deny_list & (1u128 << cb)) != 0) == bit_is_set(deny_list, cb)) by (bit_vector);
            c
        }
    } else {
        c
    }
}

// Input known to be ASCII, but may contain upper case ASCII.
//
// Verus note: the "Input known to be ASCII" comment is transcribed as the
// requires below (the 1u128 << b shift of the upstream body panics, per Rust
// shift semantics, for b >= 128, so the domain is the ASCII range).
#[inline(always)]
pub fn apply_ascii_deny_list_to_potentially_upper_case_ascii(b: u8, deny_list: u128) -> (r: char)
    requires
        b < 0x80,
    ensures
        (r as u32 == b as u32) == !bit_is_set(deny_list, b),
        bit_is_set(deny_list, b) && b >= b'A' && b <= b'Z'
            ==> r as u32 == (b as u32) + 0x20,
        bit_is_set(deny_list, b) && !(b >= b'A' && b <= b'Z') ==> r == '\u{FFFD}',
{
    assert(((deny_list & (1u128 << b)) != 0) == bit_is_set(deny_list, b)) by (bit_vector);
    if (deny_list & (1u128 << b)) == 0 {
        return b as char;
    }
    if in_inclusive_range8(b, b'A', b'Z') {
        return (b + 0x20) as char;
    }
    '\u{FFFD}'
}

// ---------------------------------------------------------------- is_ascii (uts46.rs:230-238)

#[inline(always)]
pub fn is_ascii(label: &[char]) -> (r: bool)
    ensures
        r == (forall |i: int| 0 <= i < label.len() ==> (label[i] as u32) < 0x80),
{
    /* Origin Rust: for c in label.iter() {
     *                 if !c.is_ascii() {
     *                     return false;
     *                 }
     *             }
     *             true
     */
    let mut i: usize = 0;
    while i < label.len()
        invariant
            i <= label.len(),
            forall |j: int| 0 <= j < i ==> (label[j] as u32) < 0x80,
        decreases label.len() - i
    {
        if (label[i] as u32) >= 0x80 {
            return false;
        }
        i = i + 1;
    }
    true
}

// ---------------------------------------------------------------- Punycode classification (uts46.rs:240-267)

#[derive(PartialEq, Eq, Copy, Clone)]
pub enum PunycodeClassification {
    Ascii,
    Unicode,
    Error,
}

/// Spec model: label chars from index i onward, does a U+FFFD occur.
pub open spec fn has_fffd_from(label: &[char], i: int) -> bool
    decreases label.len() - i
{
    i < label.len() && (label[i] == '\u{FFFD}' || has_fffd_from(label, i + 1))
}

/// Definitional one-step unfold of has_fffd_from.
proof fn ffd_step_lemma(label: &[char], i: int)
    ensures
        has_fffd_from(label, i) == (i < label.len() && (label[i] == '\u{FFFD}' || has_fffd_from(label, i + 1))),
{
}

/// If no char of [a, j) is U+FFFD, then has_fffd_from at a equals the one at j.
proof fn ffd_prefix_none(label: &[char], a: int, j: int)
    requires
        a <= j,
        forall |p: int| a <= p < j ==> label[p] != '\u{FFFD}',
    ensures
        has_fffd_from(label, a) == has_fffd_from(label, j),
    decreases j - a
{
    if a < j {
        ffd_prefix_none(label, a + 1, j);
        ffd_step_lemma(label, a);
    }
}

#[inline(always)]
pub fn classify_for_punycode(label: &[char]) -> (r: PunycodeClassification)
    ensures
        (r == PunycodeClassification::Ascii)
            == (forall |i: int| 0 <= i < label.len() ==> (label[i] as u32) < 0x80),
        (r == PunycodeClassification::Error) == has_fffd_from(label, 0),
        (r == PunycodeClassification::Unicode)
            == (!(forall |i: int| 0 <= i < label.len() ==> (label[i] as u32) < 0x80)
                && !has_fffd_from(label, 0)),
{
    /* The upstream two-loop iterator structure (outer scan to the first
     * non-ASCII, inner FFFD scan of the remainder) collapses to a single
     * index scan here: a U+FFFD char is never ASCII, so checking every
     * char for U+FFFD and remembering whether any non-ASCII was seen
     * computes the same three-way classification. Early returns match.
     * Origin Rust: let mut iter = label.iter().copied();
     *             loop {
     *                 if let Some(c) = iter.next() {
     *                     if c.is_ascii() {
     *                         continue;
     *                     }
     *                     if c == '\u{FFFD}' {
     *                         return PunycodeClassification::Error;
     *                     }
     *                     for c in iter {
     *                         if c == '\u{FFFD}' {
     *                             return PunycodeClassification::Error;
     *                         }
     *                     }
     *                     return PunycodeClassification::Unicode;
     *                 }
     *                 return PunycodeClassification::Ascii;
     *             }
     */
    let mut i: usize = 0;
    let mut all_ascii_so_far: bool = true;
    while i < label.len()
        invariant
            i <= label.len(),
            forall |j: int| 0 <= j < i ==> label[j] != '\u{FFFD}',
            forall |j: int| 0 <= j < i ==> (label[j] as u32) < 0x80 || !all_ascii_so_far,
            (forall |j: int| 0 <= j < i ==> (label[j] as u32) < 0x80) == all_ascii_so_far,
        decreases label.len() - i
    {
        let c = label[i];
        if c == '\u{FFFD}' {
            proof {
                ffd_prefix_none(label, 0, i as int);
                assert(label[i as int] == '\u{FFFD}');
                assert(has_fffd_from(label, i as int));
                assert(has_fffd_from(label, 0));
            }
            return PunycodeClassification::Error;
        }
        if (c as u32) >= 0x80 {
            all_ascii_so_far = false;
        }
        i = i + 1;
    }
    proof {
        ffd_prefix_none(label, 0, label.len() as int);
        assert(!has_fffd_from(label, 0));
    }
    if all_ascii_so_far {
        PunycodeClassification::Ascii
    } else {
        PunycodeClassification::Unicode
    }
}

// ---------------------------------------------------------------- AsciiDenyList (uts46.rs:269-352)

/// Upstream doc (uts46.rs:269):
/// The ASCII deny list to be applied.
#[derive(PartialEq, Eq, Copy, Clone)]
#[repr(transparent)]
pub struct AsciiDenyList {
    bits: u128,
}

/// Spec accessor for the (upstream-private) bits field; the field stays
/// private like upstream, and external spec consumers go through this view
/// (kept closed so the private field does not leak into external unfolding).
pub closed spec fn deny_list_bits(dl: &AsciiDenyList) -> u128 {
    dl.bits
}

impl AsciiDenyList {
    /// Upstream doc (uts46.rs:277-293):
    /// Computes (preferably at compile time) an ASCII deny list.
    ///
    /// Setting `deny_glyphless` to `true` denies U+0020 SPACE and below
    /// as well as U+007F DELETE for convenience without having to list
    /// these characters in the `deny_list` string.
    ///
    /// `deny_list` is the list of ASCII characters to deny. This
    /// list must not contain any of:
    /// * Letters
    /// * Digits
    /// * Hyphen
    /// * Dot (period / full-stop)
    /// * Non-ASCII
    ///
    /// # Panics
    ///
    /// If the deny list contains characters listed as prohibited above.
    //
    // Verus note: upstream is a const fn whose ASCII-prohibited-byte asserts
    // panic; here the documented panic domain is transcribed as `requires`
    // (contract transcription, not weakening: the deny-list byte domain in
    // the # Panics section is exactly this precondition), and `&str` is
    // restructured to `&[u8]` (the str layer is external; upstream consumes
    // only the bytes).

    /* The upstream `&str` parameter is restructured to `&[u8]`: the str layer
     * (UTF-8 well-formedness) is external to this face and upstream only
     * consumes the bytes (deny_list.as_bytes() at uts46.rs:300).
     * Origin Rust: pub const fn new(deny_glyphless: bool, deny_list: &str) -> Self {
     *                 let mut bits = UPPER_CASE_MASK;
     *                 if deny_glyphless {
     *                     bits |= GLYPHLESS_MASK;
     *                 }
     *                 let mut i = 0;
     *                 let bytes = deny_list.as_bytes();
     *                 while i < bytes.len() {
     *                     let b = bytes[i];
     *                     assert!(b < 0x80, "ASCII deny list must be ASCII.");
     *                     // assert_ne not yet available in const context.
     *                     assert!(b != b'.', "ASCII deny list must not contain the dot.");
     *                     assert!(b != b'-', "ASCII deny list must not contain the hyphen.");
     *                     assert!(
     *                         !((b >= b'0') && (b <= b'9')),
     *                         "ASCII deny list must not contain digits."
     *                     );
     *                     assert!(
     *                         !((b >= b'a') && (b <= b'z')),
     *                         "ASCII deny list must not contain letters."
     *                     );
     *                     assert!(
     *                         !((b >= b'A') && (b <= b'Z')),
     *                         "ASCII deny list must not contain letters."
     *                     );
     *                     bits |= 1u128 << b;
     *                     i += 1;
     *                 }
     *                 Self { bits }
     *             }
     */
    pub fn new(deny_glyphless: bool, deny_list: &[u8]) -> (r: AsciiDenyList)
        requires
            forall |i: int|
                0 <= i < deny_list.len() ==>
                (deny_list[i] < 0x80
                    && deny_list[i] != b'.'
                    && deny_list[i] != b'-'
                    && !((deny_list[i] >= b'0') && (deny_list[i] <= b'9'))
                    && !((deny_list[i] >= b'a') && (deny_list[i] <= b'z'))
                    && !((deny_list[i] >= b'A') && (deny_list[i] <= b'Z'))),
        ensures
            forall |k: u8| #![trigger bit_is_set(deny_list_bits(&r), k)] k < 128
                ==> bit_is_set(deny_list_bits(&r), k) == (
                upper_case_pred(k)
                || (deny_glyphless && glyphless_pred(k))
                || bytes_contain_upto(deny_list, deny_list.len() as int, k)
            ),
    {
        proof { zero_bits_lemma(); }
        // The upstream const-evaluated mask values are recomputed at runtime
        // by the verified mask builders (same per-bit values; see
        // mask_const_lemmas for the machine-checked const linkage).
        let um = upper_case_mask();
        let mut bits: u128 = um;
        if deny_glyphless {
            /* Origin Rust: bits |= GLYPHLESS_MASK;
             */
            let gm = glyphless_mask();
            let z = bits | gm;
            proof { or_bits_lemma(um, gm, z); }
            bits = z;
        }
        let mut i: usize = 0;
        while i < deny_list.len()
            invariant
                0 <= i <= deny_list.len(),
                forall |j: int| 0 <= j < deny_list.len() ==> deny_list[j] < 0x80,
                forall |k: u8| #![trigger bit_is_set(bits, k)] k < 128 ==> bit_is_set(bits, k) == (
                    upper_case_pred(k)
                    || (deny_glyphless && glyphless_pred(k))
                    || bytes_contain_upto(deny_list, i as int, k)
                ),
            decreases deny_list.len() - i
        {
            let b = deny_list[i];
            /* Origin Rust: bits |= 1u128 << b;
             */
            let pattern = 1u128 << b;
            let nb = bits | pattern;
            proof { set_bit_lemma(bits, nb, b); }
            bits = nb;
            i = i + 1;
        }
        let res = Self { bits };
        proof {
            assert(res.bits == bits);
            assert(forall |k: u8| #![trigger bit_is_set(deny_list_bits(&res), k)] k < 128
                ==> bit_is_set(deny_list_bits(&res), k) == (
                upper_case_pred(k)
                || (deny_glyphless && glyphless_pred(k))
                || bytes_contain_upto(deny_list, deny_list.len() as int, k)
            ));
        }
        res
    }

    /// Upstream doc (uts46.rs:325-334):
    /// No ASCII deny list. This corresponds to _UseSTD3ASCIIRules=false_.
    ///
    /// Equivalent to `AsciiDenyList::new(false, "")`.
    ///
    /// Note: Not denying the space and control characters can result in
    /// strange behavior. Without a deny list provided to the UTS 46
    /// operation, the caller is expected perform filtering afterwards,
    /// but it's more efficient to use `AsciiDenyList` than post-processing,
    /// because the internals of this crate can optimize away checks in
    /// certain cases.
    //
    // Verus note: upstream is `pub const EMPTY: Self = Self::new(false, "")`;
    // a const initializer cannot call this verified new (see mask note), so
    // the constant is transcribed as a verified exec constructor with the
    // same postcondition (the computation is the recompute route).
    /* Origin Rust: pub const EMPTY: Self = Self::new(false, "");
     */
    pub fn empty() -> (r: AsciiDenyList)
        ensures
            forall |k: u8| k < 128 ==> bit_is_set(deny_list_bits(&r), k) == upper_case_pred(k),
    {
        Self::new(false, b"")
    }

    /// Upstream doc (uts46.rs:337-341):
    /// The STD3 deny list. This corresponds to _UseSTD3ASCIIRules=true_.
    ///
    /// Note that this deny list rejects the underscore, which occurs in
    /// pseudo-hosts used by various TXT record-based protocols, and also
    /// characters that may occurs in non-DNS naming, such as NetBIOS.
    //
    // Verus note: same const-init limitation as EMPTY.
    /* Origin Rust: pub const STD3: Self = Self { bits: ldh_mask() };
     */
    pub fn std3() -> (r: AsciiDenyList)
        ensures
            forall |k: u8| k < 128 ==> bit_is_set(deny_list_bits(&r), k) == ldh_pred(k),
    {
        Self { bits: ldh_mask() }
    }

    /// Upstream doc (uts46.rs:344-350):
    /// [Forbidden domain code point](https://url.spec.whatwg.org/#forbidden-domain-code-point) from the WHATWG URL Standard.
    ///
    /// Equivalent to `AsciiDenyList::new(true, "%#/:<>?@[\\]^|")`.
    ///
    /// Note that this deny list rejects IPv6 addresses, so (as in URL
    /// parsing) you need to check for IPv6 addresses first and not
    /// put them through UTS 46 processing.
    //
    // Verus note: same const-init limitation as EMPTY. Additionally, this
    // build's spec encoding treats byte-string slice literals opaquely (their
    // element facts do not discharge), so the deny-list string is spelled as
    // its 13 constituent bytes in a ground array, whose element facts do.
    /* Origin Rust: pub const URL: Self = Self::new(true, "%#/:<>?@[\\]^|");
     */
    pub fn url() -> (r: AsciiDenyList)
        ensures
            forall |k: u8| k < 128 ==> bit_is_set(deny_list_bits(&r), k) == (
                upper_case_pred(k)
                || glyphless_pred(k)
                || url_deny_pred(k)
            ),
    {
        let dl: [u8; 13] = [b'%', b'#', b'/', b':', b'<', b'>', b'?', b'@', b'[', b'\\', b']', b'^', b'|'];
        let dls: &[u8] = &dl;
        proof {
            assert(dls.len() == 13);
            assert(dls[0] == b'%');
            assert(dls[1] == b'#');
            assert(dls[2] == b'/');
            assert(dls[3] == b':');
            assert(dls[4] == b'<');
            assert(dls[5] == b'>');
            assert(dls[6] == b'?');
            assert(dls[7] == b'@');
            assert(dls[8] == b'[');
            assert(dls[9] == b'\\');
            assert(dls[10] == b']');
            assert(dls[11] == b'^');
            assert(dls[12] == b'|');
            // Incremental unfolding of bytes_contain_upto over the 13 bytes;
            // each step assert mentions the recursive subterm so that the
            // defining axiom of the recursive spec fn (multi-triggered in this
            // build) fires.
            assert(forall |k: u8| bytes_contain_upto(dls, 0, k) == false);
            assert(forall |k: u8| bytes_contain_upto(dls, 1, k) == (dls[0] == k || bytes_contain_upto(dls, 0, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 2, k) == (dls[1] == k || bytes_contain_upto(dls, 1, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 3, k) == (dls[2] == k || bytes_contain_upto(dls, 2, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 4, k) == (dls[3] == k || bytes_contain_upto(dls, 3, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 5, k) == (dls[4] == k || bytes_contain_upto(dls, 4, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 6, k) == (dls[5] == k || bytes_contain_upto(dls, 5, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 7, k) == (dls[6] == k || bytes_contain_upto(dls, 6, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 8, k) == (dls[7] == k || bytes_contain_upto(dls, 7, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 9, k) == (dls[8] == k || bytes_contain_upto(dls, 8, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 10, k) == (dls[9] == k || bytes_contain_upto(dls, 9, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 11, k) == (dls[10] == k || bytes_contain_upto(dls, 10, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 12, k) == (dls[11] == k || bytes_contain_upto(dls, 11, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 13, k) == (dls[12] == k || bytes_contain_upto(dls, 12, k)));
            assert(forall |k: u8| bytes_contain_upto(dls, 13, k) == (
                dls[0] == k || dls[1] == k || dls[2] == k || dls[3] == k || dls[4] == k
                || dls[5] == k || dls[6] == k || dls[7] == k || dls[8] == k || dls[9] == k
                || dls[10] == k || dls[11] == k || dls[12] == k
            ));
            assert(forall |k: u8| bytes_contain_upto(dls, 13, k) == url_deny_pred(k));
        }
        Self::new(true, dls)
    }
}

// ---------------------------------------------------------------- Policy enums (uts46.rs:354-454)

/// Upstream doc (uts46.rs:354):
/// The _CheckHyphens_ mode.
#[derive(PartialEq, Eq, Copy, Clone)]
#[non_exhaustive] // non_exhaustive in case a middle mode that prohibits only first and last position needs to be added
pub enum Hyphens {
    /// Upstream doc (uts46.rs:358-361):
    /// _CheckHyphens=false_: Do not place positional restrictions on hyphens.
    ///
    /// This mode is used by the WHATWG URL Standard for normal User Agent processing
    /// (i.e. not conformance checking).
    Allow,

    /// Upstream doc (uts46.rs:364-367):
    /// Prohibit hyphens in the first and last position in the label but allow in
    /// the third and fourth position.
    ///
    /// Note that this mode rejects real-world names, including some GitHub user pages.
    CheckFirstLast,

    /// Upstream doc (uts46.rs:370-374):
    /// _CheckHyphens=true_: Prohibit hyphens in the first, third, fourth,
    /// and last position in the label.
    ///
    /// Note that this mode rejects real-world names, including YouTube CDN nodes
    /// and some GitHub user pages.
    Check,
}

/// Upstream doc (uts46.rs:378):
/// The UTS 46 _VerifyDNSLength_ flag.
#[derive(PartialEq, Eq, Copy, Clone)]
#[non_exhaustive]
pub enum DnsLength {
    /// Upstream doc (uts46.rs:382):
    /// _VerifyDNSLength=false_. (Possibly relevant for allowing non-DNS naming systems.)
    Ignore,
    /// Upstream doc (uts46.rs:384-385):
    /// _VerifyDNSLength=true_ with the exception that the trailing root label dot is
    /// allowed.
    VerifyAllowRootDot,
    /// Upstream doc (uts46.rs:387):
    /// _VerifyDNSLength=true_. (The trailing root label dot is not allowed.)
    Verify,
}

/// Upstream doc (uts46.rs:391):
/// Policy for customizing behavior in case of an error.
#[derive(PartialEq, Eq, Copy, Clone)]
#[non_exhaustive]
pub enum ErrorPolicy {
    /// Upstream doc (uts46.rs:395):
    /// Return as early as possible without producing output in case of error.
    FailFast,
    /// Upstream doc (uts46.rs:397-399):
    /// In case of error, mark errors with the REPLACEMENT CHARACTER. (The output
    /// containing REPLACEMENT CHARACTERs may be show to the user to illustrate
    /// what was wrong but must not be used for naming in a network protocol.)
    MarkErrors,
}

/// Upstream doc (uts46.rs:403):
/// The success outcome of [`Uts46::process`]
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum ProcessingSuccess {
    /// Upstream doc (uts46.rs:405-411):
    /// There were no errors. The caller must consider the input to be the output.
    ///
    /// This asserts that the input can be safely passed to [`core::str::from_utf8_unchecked`].
    ///
    /// (Distinct from `WroteToSink` in order to allow `Cow` behavior to be implemented on top of
    /// [`Uts46::process`].)
    Passthrough,

    /// Upstream doc (uts46.rs:414-417):
    /// There were no errors. The caller must consider what was written to the sink to be the output.
    ///
    /// (Distinct from `Passthrough` in order to allow `Cow` behavior to be implemented on top of
    /// [`Uts46::process`].)
    WroteToSink,
}

/// Upstream doc (uts46.rs:421):
/// The failure outcome of [`Uts46::process`]
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum ProcessingError {
    /// Upstream doc (uts46.rs:424-427):
    /// There was a validity error according to the chosen options.
    ///
    /// In case of `Operation::ToAscii`, there is no output. Otherwise, output was written to the
    /// sink and the output contains at least one U+FFFD REPLACEMENT CHARACTER to denote an error.
    ValidityError,

    /// Upstream doc (uts46.rs:430-431):
    /// The sink emitted [`core::fmt::Error`]. The partial output written to the sink must not
    /// be used.
    SinkError,
}

// Upstream note: the From<core::fmt::Error> and
// From<crate::punycode::PunycodeEncodeError> impls (uts46.rs:435-447) are
// not transcribed here; see the file-header ledger.

#[derive(Debug, Clone, Copy)]
enum AlreadyAsciiLabel<'a> {
    MixedCaseAscii(&'a [u8]),
    MixedCasePunycode(&'a [u8]),
    Other,
}

/// The Other-sentinel discriminator (the quantifier trigger carrier:
/// the verus `is` operator only takes an unqualified variant name, so
/// the sentinel test travels as this named predicate).
spec fn tile_other_cell(l: AlreadyAsciiLabel) -> bool {
    match l {
        AlreadyAsciiLabel::Other => true,
        AlreadyAsciiLabel::MixedCaseAscii(_) => false,
        AlreadyAsciiLabel::MixedCasePunycode(_) => false,
    }
}

/// Spec view: the payload of a mixed-case tag is pure ASCII (the sink
/// pass of Uts46::process re-emits those raw bytes directly through the
/// byte-as-char sink, so the payload domain is carried through the tag).
/// File-private like the datatype it matches (consumed only by the
/// pipeline faces of this file).
spec fn tag_payload_ascii(tag: AlreadyAsciiLabel) -> bool {
    match tag {
        AlreadyAsciiLabel::MixedCaseAscii(m) =>
            (forall |q: int| 0 <= q < m.len() as int ==> m[q] < 0x80),
        AlreadyAsciiLabel::MixedCasePunycode(m) =>
            (forall |q: int| 0 <= q < m.len() as int ==> m[q] < 0x80),
        AlreadyAsciiLabel::Other => true,
    }
}

/// Sink-walk tiling: the raw input offset where the label of tag cell j
/// starts, accumulated from a0 (the passthrough boundary the walk
/// inherits) forward over the cells before j -- each MixedCase cell
/// consumes its payload plus the one separator dot that follows it in
/// the pre-flush arithmetic (upstream 826, 844, 858, 899, 913: the
/// unflushed passthrough_up_to_extended register). An Other cell at or
/// before j poisons the fold to -1: the walk flushes its prefix at the
/// first Other-tagged label and freezes the register, so a MixedCase
/// cell after an Other never re-enters the arithmetic and carries no
/// alignment obligation of its own. Cells past the end of the tag
/// sequence fold to -1 as well (defensive; the walk only evaluates
/// cells it reads). File-private like the datatype it matches.
spec fn align_cell_a(
    tags: Seq<AlreadyAsciiLabel>,
    j: int,
    a0: int,
) -> (r: int)
    decreases j
{
    if j <= 0 {
        a0
    } else if j - 1 >= tags.len() as int {
        -1
    } else {
        let prev = align_cell_a(tags, j - 1, a0);
        match tags.index(j - 1) {
            AlreadyAsciiLabel::Other => -1,
            AlreadyAsciiLabel::MixedCaseAscii(m) =>
                if prev < 0 { -1 } else { prev + m@.len() as int + 1 },
            AlreadyAsciiLabel::MixedCasePunycode(m) =>
                if prev < 0 { -1 } else { prev + m@.len() as int + 1 },
        }
    }
}

/// The per-payload walk-side alignment: the tag payload Equals the
/// domain_name range [a, a + payload), the range fits the input, and
/// the separator dot (or the input end) sits right past the range --
/// exactly the facts the walk's unflushed arithmetic needs at its
/// payload-advance and separator-consume sites (upstream 826-830,
/// 856-861, 911-917). Vacuous along three dead lanes: the poisoned
/// fold (-1, cells behind an Other), and the cells at or past input
/// exhaustion holding empty payloads (the trailing empty-label cells
/// of a dot-terminated input, which the walk leaves behind on its
/// early passthrough return). File-private like the datatype family it
/// supports.
spec fn aligned_payload(dn: Seq<u8>, m: Seq<u8>, a: int) -> bool
{
    a < 0
    || (a >= dn.len() as int && m.len() == 0)
    || (
        0 <= a
        && a + m.len() <= dn.len() as int
        && (forall |q: int| 0 <= q < m.len() as int
            ==> dn[a + q] == m[q])
        && (a + m.len() == dn.len() as int
            || dn[a + m.len()] == b'.')
    )
}

/// The walk-side tiling obligation of tag cell j against the boundary
/// a0: a MixedCase cell holds a payload that tiles the aligned raw
/// input window; Other cells carry no obligation (the flush lane), and
/// out-of-range indexes carry none either.
spec fn align_cell_ok(
    dn: Seq<u8>,
    tags: Seq<AlreadyAsciiLabel>,
    j: int,
    a0: int,
) -> bool
{
    if 0 <= j < tags.len() as int {
        let a = align_cell_a(tags, j, a0);
        match tags.index(j) {
            AlreadyAsciiLabel::Other => true,
            AlreadyAsciiLabel::MixedCaseAscii(m) =>
                aligned_payload(dn, m@, a),
            AlreadyAsciiLabel::MixedCasePunycode(m) =>
                aligned_payload(dn, m@, a),
        }
    } else {
        true
    }
}

/// Front-stability of the fold: appending cells at the end leaves the
/// fold at every front index unchanged (the fold at j only reads
/// cells below j).
proof fn lemma_align_cell_a_append_front(
    tags: Seq<AlreadyAsciiLabel>,
    extra: Seq<AlreadyAsciiLabel>,
    j: int,
    a0: int,
)
    requires
        0 <= j <= tags.len() as int,
    ensures
        align_cell_a(tags.add(extra), j, a0)
            == align_cell_a(tags, j, a0),
    decreases j
{
    if j > 0 && j - 1 < tags.len() as int {
        assert((tags.add(extra)).index(j - 1) == tags.index(j - 1)) by {
            vstd::seq::lemma_seq_add_index1(tags, extra, j - 1);
        }
        assert(tags.add(extra).len() as int
            == tags.len() as int + extra.len() as int) by {
            vstd::seq::lemma_seq_add_len(tags, extra);
        }
        lemma_align_cell_a_append_front(tags, extra, j - 1, a0);
    }
}

/// One-step fold-at-the-tip over a single pushed cell.
proof fn lemma_align_cell_a_push_tip(
    tags: Seq<AlreadyAsciiLabel>,
    cell: AlreadyAsciiLabel,
    a0: int,
)
    ensures
        align_cell_a(tags.push(cell), tags.len() as int + 1, a0)
            == (if align_cell_a(tags, tags.len() as int, a0) < 0 {
                    -1
                } else {
                    match cell {
                        AlreadyAsciiLabel::Other => -1,
                        AlreadyAsciiLabel::MixedCaseAscii(m) =>
                            align_cell_a(tags, tags.len() as int, a0)
                                + m@.len() as int + 1,
                        AlreadyAsciiLabel::MixedCasePunycode(m) =>
                            align_cell_a(tags, tags.len() as int, a0)
                                + m@.len() as int + 1,
                    }
                }),
{
    // definitional at the pushed tip; the recursive fold over the
    // pushed sequence at index tags.len() reads only the front cells,
    // so it equals the fold over the original sequence there
    lemma_align_cell_a_push_front(tags, cell, tags.len() as int, a0);
    reveal_with_fuel(align_cell_a, 1);
}

/// Front-stability of the fold over a single pushed cell.
proof fn lemma_align_cell_a_push_front(
    tags: Seq<AlreadyAsciiLabel>,
    cell: AlreadyAsciiLabel,
    j: int,
    a0: int,
)
    requires
        0 <= j <= tags.len() as int,
    ensures
        align_cell_a(tags.push(cell), j, a0)
            == align_cell_a(tags, j, a0),
    decreases j
{
    if j > 0 && j - 1 < tags.len() as int {
        assert((tags.push(cell)).index(j - 1) == tags.index(j - 1)) by {
            vstd::seq::lemma_seq_push_index_different(tags, cell, j - 1);
        }
        lemma_align_cell_a_push_front(tags, cell, j - 1, a0);
    }
}

// ---------------------------------------------------------------- E-TILE
// wave-3 site helpers: the per-call-site proof obligations of the
// sink-walk tiling channel, factored as standalone lemmas. The batch H
// attempt stated these obligations inline (by-blocks at the four push
// sites); the z3 obligation chains behind the inline asserts failed
// without decomposable inner reasons (run5/run6 error maps, 8 assertion
// failures at the push sites plus 2 subrange-index precondition
// failures and the loop-wide rlimit), while the same algebra inside
// the standalone fold lemmas discharged trivially -- so every part of a
// site's duty that can be a lemma parameter is a lemma parameter now,
// and the call sites keep only the position glue and the rope
// equalities.

/// The per-label raw-input geometry: a label slice [pos, le) of the
/// tail (the tail being the dn_off-anchored suffix of domain_name, the
/// label-scan evidence supplying the separator dot right past a
/// non-terminal label) has its payload value-equal to the raw input
/// range [dn_off + pos, dn_off + le) with the separator-or-input-end
/// sitting right past it. This is the whole dn-side content of the
/// new-cell tiling obligation at any push site: the cell's window
/// start, while the chain is alive, is exactly dn_off + pos.
proof fn lemma_raw_label_tiled(
    dn: Seq<u8>,
    tail: Seq<u8>,
    dn_off: int,
    pos: int,
    le: int,
    label: &[u8],
)
    requires
        0 <= dn_off,
        0 <= pos <= le <= tail.len() as int,
        dn_off + tail.len() as int == dn.len() as int,
        tail == dn.subrange(dn_off, dn.len() as int),
        label@ == tail.subrange(pos, le),
        (le < tail.len() as int) ==> tail.index(le) == b'.',
    ensures
        aligned_payload(dn, label@, dn_off + pos),
{
    let lo: int = dn_off + pos;
    let hi: int = dn_off + le;
    assert(label.len() as int == le - pos);
    assert(hi == lo + label.len() as int);
    assert(lo >= 0);
    assert(hi <= dn.len() as int);
    // the value equality of the payload range: dn[dn_off + i] ==
    // tail[i] for the tail window, then tail[pos + q] == label[q]
    assert forall |q: int|
        #![trigger label@.index(q)]
        0 <= q < label@.len() as int
        implies dn[lo + q] == label@.index(q) by {
        if 0 <= q && q < label@.len() as int {
            assert(lo + q >= 0);
            assert(pos + q < le);
            assert(dn_off <= lo + q);
            assert(lo + q < dn.len() as int);
            assert(pos + q < dn.len() as int - dn_off);
            assert(dn[lo + q]
                == (dn.subrange(dn_off, dn.len() as int)).index(pos + q)) by {
                vstd::seq::lemma_seq_subrange_index(
                    dn, dn_off, dn.len() as int, pos + q);
            }
            assert((dn.subrange(dn_off, dn.len() as int)).index(pos + q)
                == tail.index(pos + q));
            assert(q < le - pos);
            assert(tail.index(pos + q)
                == (tail.subrange(pos, le)).index(q)) by {
                vstd::seq::lemma_seq_subrange_index(
                    tail, pos, le as int, q);
            }
            assert((tail.subrange(pos, le)).index(q)
                == label@.index(q));
        }
    }
    // the separator-or-end limb
    if le < tail.len() as int {
        assert(hi < dn.len() as int);
        assert(dn[hi] == (dn.subrange(dn_off, dn.len() as int)).index(le)) by {
            vstd::seq::lemma_seq_subrange_index(
                dn, dn_off, dn.len() as int, le);
        }
        assert((dn.subrange(dn_off, dn.len() as int)).index(le)
            == tail.index(le));
        assert(dn[hi] == b'.');
    }
}

/// The generic push envelope: the per-cell obligations of the pushed
/// rope follow from (a) the per-cell obligations of the pre-push rope
/// (the fold at every front index and the index read are stable
/// through the push) and (b) the new cell's payload alignment at the
/// pre-push fold tip (the -1 tip is the poisoned-fold vacuous lane of
/// aligned_payload). The tip ledger is carried through the same lemma
/// so the call sites never re-derive the fold: an Other cell always
/// poisons the tip to -1, a dead tip stays -1, and a live tip under a
/// MixedCase cell advances by the payload plus the separator limb.
proof fn lemma_tile_push_cell(
    dn: Seq<u8>,
    tags: Seq<AlreadyAsciiLabel>,
    cell: AlreadyAsciiLabel,
    a0: int,
)
    requires
        forall |j: int| 0 <= j < tags.len() as int
            ==> align_cell_ok(dn, tags, j, a0),
        match cell {
            AlreadyAsciiLabel::Other => true,
            AlreadyAsciiLabel::MixedCaseAscii(m) =>
                aligned_payload(dn, m@,
                    align_cell_a(tags, tags.len() as int, a0)),
            AlreadyAsciiLabel::MixedCasePunycode(m) =>
                aligned_payload(dn, m@,
                    align_cell_a(tags, tags.len() as int, a0)),
        },
    ensures
        forall |j: int| 0 <= j < tags.len() as int + 1
            ==> align_cell_ok(dn, tags.push(cell), j, a0),
        match cell {
            AlreadyAsciiLabel::Other =>
                align_cell_a(tags.push(cell),
                    tags.len() as int + 1, a0) == -1,
            AlreadyAsciiLabel::MixedCaseAscii(m) =>
                (align_cell_a(tags, tags.len() as int, a0) < 0
                    ==> align_cell_a(tags.push(cell),
                        tags.len() as int + 1, a0) == -1)
                && (0 <= align_cell_a(tags, tags.len() as int, a0)
                    ==> align_cell_a(tags.push(cell),
                        tags.len() as int + 1, a0)
                        == align_cell_a(tags, tags.len() as int, a0)
                            + m@.len() as int + 1),
            AlreadyAsciiLabel::MixedCasePunycode(m) =>
                (align_cell_a(tags, tags.len() as int, a0) < 0
                    ==> align_cell_a(tags.push(cell),
                        tags.len() as int + 1, a0) == -1)
                && (0 <= align_cell_a(tags, tags.len() as int, a0)
                    ==> align_cell_a(tags.push(cell),
                        tags.len() as int + 1, a0)
                        == align_cell_a(tags, tags.len() as int, a0)
                            + m@.len() as int + 1),
        },
{
    assert((tags.push(cell)).len() as int
        == tags.len() as int + 1) by {
        vstd::seq::lemma_seq_push_len(tags, cell);
    }
    assert forall |j: int|
        #![trigger align_cell_ok(dn, tags.push(cell), j, a0)]
        0 <= j < tags.len() as int + 1
        implies align_cell_ok(dn, tags.push(cell), j, a0) by {
        if j < tags.len() as int {
            // a front cell: the index read and the window-start fold
            // are both stable through the push
            vstd::seq::lemma_seq_push_index_different(tags, cell, j);
            lemma_align_cell_a_push_front(tags, cell, j, a0);
            assert((tags.push(cell)).index(j) == tags.index(j));
            assert(align_cell_a(tags.push(cell), j, a0)
                == align_cell_a(tags, j, a0));
            assert(align_cell_ok(dn, tags.push(cell), j, a0)
                == align_cell_ok(dn, tags, j, a0));
        } else {
            // the new cell at the tip index: the fold there is the
            // pre-push tip (front-stability at index tags.len()), and
            // the distributed payload-alignment requires supplies the
            // MixedCase obligation at exactly that position
            assert(j == tags.len() as int);
            vstd::seq::lemma_seq_push_index_same(tags, cell, j);
            lemma_align_cell_a_push_front(tags, cell,
                tags.len() as int, a0);
            assert((tags.push(cell)).index(j) == cell);
            assert(align_cell_a(tags.push(cell), j, a0)
                == align_cell_a(tags, tags.len() as int, a0));
        }
    }
    // the tip ledger: one definitional step of the fold at the pushed
    // tip
    lemma_align_cell_a_push_tip(tags, cell, a0);
    lemma_align_cell_a_push_front(tags, cell,
        tags.len() as int, a0);
}

/// The Other-block append envelope (the mapping window's tag extend):
/// the front cells keep their obligations through the add (append-front
/// fold stability), every added cell is the Other sentinel whose
/// per-cell obligation is vacuous by the align_cell_ok spec (the Other
/// arm never reads the fold), and a nonempty Other block pins the
/// post-add fold tip to -1 in one definitional step of the fold (the
/// recursion at the full-tip index reads the last cell, which is
/// Other).
proof fn lemma_tile_append_others(
    dn: Seq<u8>,
    tags: Seq<AlreadyAsciiLabel>,
    blk: Seq<AlreadyAsciiLabel>,
    a0: int,
)
    requires
        forall |j: int| 0 <= j < tags.len() as int
            ==> align_cell_ok(dn, tags, j, a0),
        forall |k: int| 0 <= k < blk.len() as int
            ==> #[trigger] tile_other_cell(blk.index(k)),
    ensures
        forall |j: int|
            0 <= j < tags.len() as int + blk.len() as int
            ==> align_cell_ok(dn, tags.add(blk), j, a0),
        0 < blk.len() as int
            ==> align_cell_a(tags.add(blk),
                tags.len() as int + blk.len() as int, a0) == -1,
{
    assert((tags.add(blk)).len() as int
        == tags.len() as int + blk.len() as int) by {
        vstd::seq::lemma_seq_add_len(tags, blk);
    }
    assert forall |j: int|
        #![trigger align_cell_ok(dn, tags.add(blk), j, a0)]
        0 <= j < tags.len() as int + blk.len() as int
        implies align_cell_ok(dn, tags.add(blk), j, a0) by {
        if j < tags.len() as int {
            // a front cell: the index read and the window-start fold
            // are both stable through the add
            vstd::seq::lemma_seq_add_index1(tags, blk, j);
            lemma_align_cell_a_append_front(tags, blk, j, a0);
            assert((tags.add(blk)).index(j) == tags.index(j));
            assert(align_cell_a(tags.add(blk), j, a0)
                == align_cell_a(tags, j, a0));
            assert(align_cell_ok(dn, tags.add(blk), j, a0)
                == align_cell_ok(dn, tags, j, a0));
        } else {
            // an appended Other cell: the composed rope reads
            // blk.index(j - tags.len()) at this index, which the
            // requires holds as the Other sentinel -- the
            // align_cell_ok Other arm is true without any fold read
            vstd::seq::lemma_seq_add_index2(tags, blk, j);
            assert((tags.add(blk)).index(j)
                == blk.index(j - tags.len() as int));
            assert(tile_other_cell(blk.index(j - tags.len() as int)));
        }
    }
    if 0 < blk.len() as int {
        // the definitional fold step at the full-tip index reads the
        // last cell of the composed rope, which is an Other sentinel
        let full: int = tags.len() as int + blk.len() as int;
        let rope = tags.add(blk);
        assert(rope.index(full - 1)
            == blk.index(blk.len() as int - 1)) by {
            vstd::seq::lemma_seq_add_index2(tags, blk, full - 1);
        }
        assert(tile_other_cell(blk.index(blk.len() as int - 1)));
        assert(0 <= full - 1 && full - 1 < rope.len() as int);
        reveal_with_fuel(align_cell_a, 1);
        assert(align_cell_a(rope, full, a0) == -1);
    }
}

// ---------------------------------------------------------------- idna_adapter external contract abstraction (uts46.rs:29 "use idna_adapter::*", 488-1683)

// Injection perimeter of this file. Upstream structures its Unicode data
// face as the external crate idna_adapter (Adapter with the mapping and
// the Bidi_Class/Joining_Type/General_Category/Canonical_Combining_Class
// lookups). This build models each consumed face as exactly one bodyless
// `uninterp` spec function (no defining axioms exist for uninterp
// functions, so the binding below is the complete set of assumed facts)
// plus one external_body exec shim whose ensures is the injected contract.
// The per-face injected properties are P1-P6 (binding = totality and
// determinism/"pure function" of the data face read-out; nothing else is
// assumed about the table contents in this face):
//   P1 adapter_bidi_class (Bidi_Class lookup, Adapter::bidi_class)
//   P2 adapter_joining_type (Joining_Type lookup, Adapter::joining_type)
//   P3 adapter_is_mark (General_Category in {Mn,Mc,Me}, Adapter::is_mark)
//   P4 adapter_is_virama (Canonical_Combining_Class==Virama, Adapter::is_virama)
//   P5 adapter_map_normalize (UTS 46 Map + NFC, Adapter::map_normalize)
//   P6 adapter_normalize_validate (UTS 46 map/normalize with Ignored treated
//      as disallowed, Adapter::normalize_validate)
// Upstream truth of P1-P4: table lookups (icu_properties CodePointMapData
// in the icu4x adapter build; idna_mapping/unicode-bidi tables in the
// ls-2020 adapter build of the upstream CI lock) are total deterministic
// functions of the character. Upstream truth of P5/P6: the UTS 46 mapping
// pipeline mapped-character/wildcard semantics ("ignored characters are
// ignored; mapped are mapped; disallowed are replaced with U+FFFD; ...
// the result is normalized to NFC") is a deterministic algorithm, so the
// produced sequence is a total deterministic function of the input
// sequence. Properties known to hold upstream but deliberately NOT
// injected (no verified obligation consumes them): the U+FFFD replacement
// semantics for disallowed characters, the lower-casing of mapped ASCII,
// NFC representativeness, absence of U+200F from mapping output, and any
// correlation between the faces.

/// Model of the Bidi_Class values as distinguished by the consumers of
/// this file (the masks and class predicates below). L, R, AL, EN, AN,
/// and NSM appear atomically in the consumed masks; the five classes
/// European_Separator, Common_Separator, European_Terminator,
/// Other_Neutral, and Boundary_Neutral appear only as one indivisible
/// group in the middle masks (MidNeutral); every other UAX #9 class
/// (B, S, WS, LRE, LRO, RLE, RLO, PDF, LRI, RLI, FSI, PDI) appears in no
/// consumed mask (Other). The grouping is lossless: no consumed read
// ever distinguishes members within MidNeutral or within Other.
#[derive(PartialEq, Eq, Copy, Clone)]
pub enum BcModel {
    L,
    R,
    AL,
    EN,
    AN,
    NSM,
    MidNeutral,
    Other,
}

/// Model of the Joining_Type values (all six distinct values retained;
/// the masks below consume L, D, R, and T; U and C appear in no mask).
#[derive(PartialEq, Eq, Copy, Clone)]
pub enum JtModel {
    NonJoining,
    JoinCausing,
    DualJoining,
    LeftJoining,
    RightJoining,
    Transparent,
}

// The consumed BidiClassMask constants, as membership predicates over
// BcModel. Each row is the exact class set of the upstream mask
// (idna_adapter builds them from the icu4x BidiClass enumeration):
//   RTL_MASK = R|AL|AN; FIRST_BC_MASK = L|R|AL; LAST_LTR_MASK = L|EN;
//   LAST_RTL_MASK = R|AL|EN|AN;
//   MIDDLE_LTR_MASK = L|EN|ES|CS|ET|ON|BN|NSM;
//   MIDDLE_RTL_MASK = R|AL|AN|EN|ES|CS|ET|ON|BN|NSM.

pub open spec fn bc_in_rtl_mask(bc: BcModel) -> bool {
    bc == BcModel::R || bc == BcModel::AL || bc == BcModel::AN
}

pub open spec fn bc_in_first_mask(bc: BcModel) -> bool {
    bc == BcModel::L || bc == BcModel::R || bc == BcModel::AL
}

pub open spec fn bc_in_last_ltr(bc: BcModel) -> bool {
    bc == BcModel::L || bc == BcModel::EN
}

pub open spec fn bc_in_last_rtl(bc: BcModel) -> bool {
    bc == BcModel::R || bc == BcModel::AL || bc == BcModel::EN || bc == BcModel::AN
}

pub open spec fn bc_in_middle_ltr(bc: BcModel) -> bool {
    bc == BcModel::L || bc == BcModel::EN || bc == BcModel::NSM || bc == BcModel::MidNeutral
}

pub open spec fn bc_in_middle_rtl(bc: BcModel) -> bool {
    bc == BcModel::R || bc == BcModel::AL || bc == BcModel::AN
        || bc == BcModel::EN || bc == BcModel::NSM || bc == BcModel::MidNeutral
}

/// Upstream doc (idna_adapter BidiClass::is_ltr): true iff this value is
/// Left_To_Right.
pub open spec fn bc_is_ltr(bc: BcModel) -> bool {
    bc == BcModel::L
}

/// Upstream doc (idna_adapter BidiClass::is_nonspacing_mark): true iff
/// this value is Nonspacing_Mark.
pub open spec fn bc_is_nsm(bc: BcModel) -> bool {
    bc == BcModel::NSM
}

/// Upstream doc (idna_adapter BidiClass::is_european_number): true iff
/// this value is European_Number.
pub open spec fn bc_is_en(bc: BcModel) -> bool {
    bc == BcModel::EN
}

/// Upstream doc (idna_adapter BidiClass::is_arabic_number): true iff
/// this value is Arabic_Number.
pub open spec fn bc_is_an(bc: BcModel) -> bool {
    bc == BcModel::AN
}

// The consumed JoiningTypeMask constants:
//   LEFT_OR_DUAL_JOINING_MASK = L|D; RIGHT_OR_DUAL_JOINING_MASK = R|D;
// plus BidiClass-independent JoiningType::is_transparent (T).

pub open spec fn jt_in_left_or_dual(jt: JtModel) -> bool {
    jt == JtModel::LeftJoining || jt == JtModel::DualJoining
}

pub open spec fn jt_in_right_or_dual(jt: JtModel) -> bool {
    jt == JtModel::RightJoining || jt == JtModel::DualJoining
}

pub open spec fn jt_is_transparent(jt: JtModel) -> bool {
    jt == JtModel::Transparent
}

// P1: the Bidi_Class read-out is a total deterministic function of the
// character (upstream: idna_adapter::Adapter::bidi_class table lookup).
pub uninterp spec fn adapter_bidi_class_of(c: char) -> (r: BcModel);

// P2: the Joining_Type read-out (Adapter::joining_type lookup).
pub uninterp spec fn adapter_joining_type_of(c: char) -> (r: JtModel);

// P3: the General_Category is-Mark read-out (Adapter::is_mark; GC in
// {Nonspacing_Mark, Spacing_Mark, Enclosing_Mark}).
pub uninterp spec fn adapter_is_mark_of(c: char) -> (r: bool);

// P4: the Canonical_Combining_Class is-Virama read-out (Adapter::is_virama).
pub uninterp spec fn adapter_is_virama_of(c: char) -> (r: bool);

// P5: Adapter::map_normalize - the UTS 46 "Map" + NFC pipeline as one
// total deterministic function of the whole input character sequence
// (NFC composes across characters, so the per-sequence granularity is
// the finest faithful one).
pub uninterp spec fn adapter_map_norm_of(s: Seq<char>) -> (r: Seq<char>);

// P6: Adapter::normalize_validate - the UTS 46 mapping/normalization with
// Ignored characters treated as disallowed, likewise one total
// deterministic function of the input sequence.
pub uninterp spec fn adapter_norm_valid_of(s: Seq<char>) -> (r: Seq<char>);

/// P1 exec shim; the ensures is the entire injected contract.
#[verifier::external_body]
pub fn adapter_bidi_class(c: char) -> (r: BcModel)
    ensures
        r == adapter_bidi_class_of(c),
{
    BcModel::L
}

/// P2 exec shim.
#[verifier::external_body]
pub fn adapter_joining_type(c: char) -> (r: JtModel)
    ensures
        r == adapter_joining_type_of(c),
{
    JtModel::NonJoining
}

/// P3 exec shim.
#[verifier::external_body]
pub fn adapter_is_mark(c: char) -> (r: bool)
    ensures
        r == adapter_is_mark_of(c),
{
    false
}

/// P4 exec shim.
#[verifier::external_body]
pub fn adapter_is_virama(c: char) -> (r: bool)
    ensures
        r == adapter_is_virama_of(c),
{
    false
}

/// Arrangement note: upstream feeds the two mapping stages lazily fused
/// iterators (Adapter::map_normalize(non_ascii.chars()) at uts46.rs:1252
/// and Adapter::normalize_validate(label.iter().copied()) at uts46.rs:1506);
/// the transcription decomposes the fusion into a decode step (the WHATWG
/// lossy decoder transcribed below, no injection) followed by this whole-
/// sequence mapping call; the produced sequence is identical (strict
/// in-order composition of the same two stages).

/// P5 exec shim.
#[verifier::external_body]
pub fn adapter_map_normalize(input: &[char]) -> (r: Vec<char>)
    ensures
        r@ == adapter_map_norm_of(input@),
{
    Vec::new()
}

/// P6 exec shim.
#[verifier::external_body]
pub fn adapter_normalize_validate(input: &[char]) -> (r: Vec<char>)
    ensures
        r@ == adapter_norm_valid_of(input@),
{
    Vec::new()
}

/// Transcription of the `output_as_unicode: FnMut(&[char], &[char], bool)
/// -> bool` parameter of Uts46::process (uts46.rs:665, 779): a decision
/// trait with a spec-level view. The upstream |_, _, _| false closure is
/// the ToASCII policy; |_, _, _| true is the ToUnicode policy; both are
/// provided as impls by the assertion harness; the per-call contract is
/// the upstream doc: only non-erroneous labels that contain at least one
/// non-ASCII character are passed to the decision, and the second and
/// third arguments stay constant across one call to process (carried by
/// the caller-side ghosts of the pipeline transcription).
pub trait DecideUnicode {
    spec fn decision(label: Seq<char>, tld: Seq<char>, is_bidi: bool) -> bool;

    fn decide(label: &[char], tld: &[char], is_bidi: bool) -> (r: bool)
        ensures
            r == Self::decision(label@, tld@, is_bidi);
}

// ---------------------------------------------------------------- verify_dns_length (uts46.rs:456-486)

/// Spec model: scanning with the current label starting at `ls` and the next
/// byte at `cur` within the first `lim` bytes, every label is nonempty and at
/// most 63 bytes long.
pub open spec fn dns_scan_ok(bytes: &[u8], lim: int, ls: int, cur: int) -> bool
    decreases lim - cur
{
    if cur >= lim {
        1 <= cur - ls && cur - ls <= 63
    } else if bytes[cur] == b'.' {
        (1 <= cur - ls && cur - ls <= 63) && dns_scan_ok(bytes, lim, cur + 1, cur + 1)
    } else {
        dns_scan_ok(bytes, lim, ls, cur + 1)
    }
}

/// Definitional bridge for the spec model: on the trailing-dot path the spec
/// reduces to the total-length bound and the scan property.
proof fn dns_spec_scan_only(bytes: &[u8], allow_trailing_dot: bool, lim: int)
    requires
        bytes.len() >= 1 && bytes[bytes.len() as int - 1] == b'.',
        allow_trailing_dot,
        lim == bytes.len() as int - 1,
    ensures
        spec_verify_dns_length(bytes, allow_trailing_dot) == (
            (lim <= 253) && dns_scan_ok(bytes, lim, 0, 0)
        ),
{
}

/// Definitional bridge for the spec model: with no trailing dot the spec
/// reduces to the total-length bound and the scan property.
proof fn dns_spec_scan_only_no_dot(bytes: &[u8], allow_trailing_dot: bool, lim: int)
    requires
        !(bytes.len() >= 1 && bytes[bytes.len() as int - 1] == b'.'),
        lim == bytes.len() as int,
    ensures
        spec_verify_dns_length(bytes, allow_trailing_dot) == (
            (lim <= 253) && dns_scan_ok(bytes, lim, 0, 0)
        ),
{
}

/// Spec model of verify_dns_length: trailing root label dot allowed only when
/// `allow_trailing_dot` is set (and then excluded from length accounting);
/// total length at most 253; per-label nonempty and at most 63 bytes.
pub open spec fn spec_verify_dns_length(bytes: &[u8], allow_trailing_dot: bool) -> bool {
    let n = bytes.len() as int;
    let lim = if n >= 1 && bytes[n - 1] == b'.' {
        n - 1
    } else {
        n
    };
    (bytes.len() >= 1 && bytes[bytes.len() - 1] == b'.' ==> allow_trailing_dot)
        && lim <= 253
        && dns_scan_ok(bytes, lim, 0, 0)
}

/// Upstream doc (uts46.rs:456-462):
/// Performs the _VerifyDNSLength_ check on the output of the _ToASCII_ operation.
///
/// If the second argument is `false`, the trailing root label dot is allowed.
///
/// # Panics
///
/// Panics in debug mode if the argument isn't ASCII.
//
// Verus note on the # Panics transcription: upstream debug_asserts ASCII and
// release builds compute lengths over bytes regardless; the ASCII domain is
// transcribed as `requires` (which matches release semantics for non-ASCII:
// plain byte-length arithmetic).
/* The upstream `domain_name: &str` parameter is restructured to `bytes:
 * &[u8]`: upstream immediately takes as_bytes() (uts46.rs:464) and the str
 * layer is external to this face.
 * Origin Rust: pub fn verify_dns_length(domain_name: &str, allow_trailing_dot: bool) -> bool {
 *                 let bytes = domain_name.as_bytes();
 *                 debug_assert!(bytes.is_ascii());
 *                 let domain_name_without_trailing_dot = if let Some(without) = bytes.strip_suffix(b".") {
 *                     if !allow_trailing_dot {
 *                         return false;
 *                     }
 *                     without
 *                 } else {
 *                     bytes
 *                 };
 *                 if domain_name_without_trailing_dot.len() > 253 {
 *                     return false;
 *                 }
 *                 for label in domain_name_without_trailing_dot.split(|b| *b == b'.') {
 *                     if label.is_empty() {
 *                         return false;
 *                     }
 *                     if label.len() > 63 {
 *                         return false;
 *                     }
 *                 }
 *                 true
 *             }
 */
pub fn verify_dns_length(bytes: &[u8], allow_trailing_dot: bool) -> (r: bool)
    requires
        forall |i: int| 0 <= i < bytes.len() ==> bytes[i] < 0x80,
    ensures
        r == spec_verify_dns_length(bytes, allow_trailing_dot),
{
    /* strip_suffix is restructured as an effective-length limit; the scan
     * loop is transcribed with (label_start, current) index arithmetic,
     * mirroring the upstream split-plus-len rules.
     */
    let lim: usize = if bytes.len() >= 1 && bytes[bytes.len() - 1] == b'.' {
        if !allow_trailing_dot {
            return false;
        }
        bytes.len() - 1
    } else {
        bytes.len()
    };
    if lim > 253 {
        return false;
    }
    proof {
        // Case analysis mirroring the exec branch, so the spec model's own
        // effective limit evaluates to the exec-chosen value.
        if bytes.len() >= 1 && bytes[bytes.len() as int - 1] == b'.' {
            assert(lim as int == bytes.len() as int - 1);
            assert(spec_verify_dns_length(bytes, allow_trailing_dot) == (
                allow_trailing_dot
                    && (lim as int) <= 253
                    && dns_scan_ok(bytes, lim as int, 0, 0)
            ));
        } else {
            assert(lim as int == bytes.len() as int);
            assert(spec_verify_dns_length(bytes, allow_trailing_dot) == (
                (lim as int) <= 253
                    && dns_scan_ok(bytes, lim as int, 0, 0)
            ));
        }
    }
    let mut ls: usize = 0;
    let mut cur: usize = 0;
    while cur < lim
        invariant
            0 <= ls <= cur <= lim <= bytes.len(),
            dns_scan_ok(bytes, lim as int, ls as int, cur as int) == dns_scan_ok(bytes, lim as int, 0, 0),
            bytes.len() >= 1 && bytes[bytes.len() - 1] == b'.' ==> allow_trailing_dot,
            lim <= 253,
            // The effective limit stays equal to the exec-chosen branch value
            // across iterations (carried here since it must be used in-body).
            (lim as int) == (if bytes.len() >= 1 && bytes[bytes.len() as int - 1] == b'.' {
                bytes.len() as int - 1
            } else {
                bytes.len() as int
            }),
        decreases lim as int - cur as int
    {
        if bytes[cur] == b'.' {
            let label_len = cur - ls;
            proof {
                dot_step_lemma(bytes, lim as int, ls as int, cur as int);
                assert(dns_scan_ok(bytes, lim as int, ls as int, cur as int) == (1 <= cur - ls && cur - ls <= 63 && dns_scan_ok(bytes, lim as int, (cur + 1) as int, (cur + 1) as int)));
            }
            if label_len == 0 {
                proof {
                    assert(dns_scan_ok(bytes, lim as int, ls as int, cur as int) == false);
                    assert(dns_scan_ok(bytes, lim as int, 0, 0) == false);
                    if bytes.len() >= 1 && bytes[bytes.len() as int - 1] == b'.' {
                        dns_spec_scan_only(bytes, allow_trailing_dot, lim as int);
                    } else {
                        dns_spec_scan_only_no_dot(bytes, allow_trailing_dot, lim as int);
                    }
                    assert(spec_verify_dns_length(bytes, allow_trailing_dot) == false);
                }
                return false;
            }
            if label_len > 63 {
                proof {
                    assert(dns_scan_ok(bytes, lim as int, ls as int, cur as int) == false);
                    assert(dns_scan_ok(bytes, lim as int, 0, 0) == false);
                    if bytes.len() >= 1 && bytes[bytes.len() as int - 1] == b'.' {
                        dns_spec_scan_only(bytes, allow_trailing_dot, lim as int);
                    } else {
                        dns_spec_scan_only_no_dot(bytes, allow_trailing_dot, lim as int);
                    }
                    assert(spec_verify_dns_length(bytes, allow_trailing_dot) == false);
                }
                return false;
            }
            proof {
                assert(1 <= cur - ls && cur - ls <= 63);
            }
            let nls = cur + 1;
            ls = nls;
            cur = nls;
        } else {
            proof {
                scan_step_lemma(bytes, lim as int, ls as int, cur as int);
            }
            cur = cur + 1;
        }
    }
    // last label (or the empty whole-domain) check
    proof {
        scan_base_lemma(bytes, lim as int, ls as int, cur as int);
    }
    let label_len = lim - ls;
    if label_len == 0 {
        return false;
    }
    if label_len > 63 {
        return false;
    }
    true
}

// ---------------------------------------------------------------- ASCII fast-path scan tier (uts46.rs:1047-1085)

/// Upstream doc (uts46.rs:1047):
/// The part of `process` that doesn't need to be generic over the sink.
//
// Outcome of the ASCII fast-path scan tier of process_inner: either the whole
// input passed the fast path (upstream then returns (domain_name.len(),
// false, false)), or the first non-fast byte is deferred together with the
// most recently started label (upstream hands
// most_recent_label_start.as_slice() to process_innermost, which is the
// blocked deeper tier; this transcription returns the deferral start index).
// (PartialEq derive added for harness comparison; upstream's tier returns a
// raw triple so it has no enum to derive.)
#[derive(PartialEq, Eq, Copy, Clone)]
pub enum FastPathScan {
    FastPathPass,
    FastPathDefer(usize),
}

/// Fast-path byte: lower-case ASCII letter or dot.
pub open spec fn is_fast_byte(b: u8) -> bool {
    (b >= b'a' && b <= b'z') || b == b'.'
}

/// Position of the first non-fast byte, starting the search at j; len if none.
pub open spec fn first_non_fast(bytes: &[u8], j: int) -> int
    decreases bytes.len() - j
{
    if j >= bytes.len() as int {
        j
    } else if is_fast_byte(bytes[j]) {
        first_non_fast(bytes, j + 1)
    } else {
        j
    }
}

/// The most recent label starting at or before j: index 0, or the position
/// right after the most recent dot at index < j (upstream's
/// most_recent_label_start snapshot state made functional).
pub open spec fn defer_index_from(bytes: &[u8], j: int) -> int
    decreases j
{
    if j <= 0 {
        0
    } else if bytes[j - 1] == b'.' {
        j
    } else {
        defer_index_from(bytes, j - 1)
    }
}

/// Every byte before the first non-fast byte is fast (prefix unfolding of
/// the first_non_fast recursion).
proof fn first_non_fast_prefix_fast(bytes: &[u8], a: int)
    requires
        0 <= a,
    ensures
        forall |p: int| a <= p < first_non_fast(bytes, a)
            ==> is_fast_byte(bytes[p]),
    decreases first_non_fast(bytes, a) - a
{
    if a < first_non_fast(bytes, a) {
        assert(is_fast_byte(bytes[a]));
        first_non_fast_prefix_fast(bytes, a + 1);
        assert(first_non_fast(bytes, a) == first_non_fast(bytes, a + 1));
    }
}

/* Verus note: the upstream iterator/clone snapshot pattern is transcribed as
 * index arithmetic. most_recent_label_start starts as a snapshot of `iter`
 * before the loop (position 0) and is refreshed to the position after each
 * consumed dot, so on hitting the first non-fast byte at index i the deferral
 * tail starts at the most recent label start, which is index 0 or one past
 * the most recent dot. The deeper process_innermost call is blocked (see the
 * file-header ledger); only the deferral point is transcribed.
 * Origin Rust: fn process_inner<'a>(
 *                 &self,
 *                 domain_name: &'a [u8],
 *                 ascii_deny_list: AsciiDenyList,
 *                 hyphens: Hyphens,
 *                 fail_fast: bool,
 *                 domain_buffer: &mut SmallVec<[char; 253]>,
 *                 already_punycode: &mut SmallVec<[AlreadyAsciiLabel<'a>; 8]>,
 *             ) -> (usize, bool, bool) {
 *                 // Sadly, this even faster-path ASCII tier is needed to avoid regressing
 *                 // performance.
 *                 let mut iter = domain_name.iter();
 *                 let mut most_recent_label_start = iter.clone();
 *                 loop {
 *                     if let Some(&b) = iter.next() {
 *                         if in_inclusive_range8(b, b'a', b'z') {
 *                             continue;
 *                         }
 *                         if b == b'.' {
 *                             most_recent_label_start = iter.clone();
 *                             continue;
 *                         }
 *                         return self.process_innermost(
 *                             domain_name,
 *                             ascii_deny_list,
 *                             hyphens,
 *                             fail_fast,
 *                             domain_buffer,
 *                             already_punycode,
 *                             most_recent_label_start.as_slice(),
 *                         );
 *                     } else {
 *                         // Success! The whole input passes through on the fastest path!
 *                         return (domain_name.len(), false, false);
 *                     }
 *                 }
 *             }
 */
#[inline(always)]
pub fn process_inner_ascii_scan(domain_name: &[u8]) -> (r: FastPathScan)
    ensures
        (r == FastPathScan::FastPathPass)
            == (forall |p: int| 0 <= p < domain_name.len() ==> is_fast_byte(domain_name[p])),
        // Off the fast path, the deferral index is pinned to the functional
        // most-recent-label-start at the offending byte (this makes the
        // observable defer tail deterministic).
        (r != FastPathScan::FastPathPass)
            ==> r == FastPathScan::FastPathDefer(
                defer_index_from(domain_name, first_non_fast(domain_name, 0)) as usize,
            ),
        // On deferral: the offending byte is at first_non_fast(domain_name, 0)
        // < domain_name.len(); the deferral tail starts at the most recently
        // started label (index 0, or one past the most recent dot), and every
        // byte between that label start and the offending byte is fast.
        forall |idx: usize|
            r == FastPathScan::FastPathDefer(idx) ==>
            (0 <= idx as int
                && idx as int <= first_non_fast(domain_name, 0)
                && first_non_fast(domain_name, 0) < domain_name.len()
                && (idx == 0 || domain_name[idx as int - 1] == b'.')
                // When the deferral starts at 0, no dot was scanned before the
                // offending byte (otherwise the tail would start after that
                // dot); this pins the defer index to the most recent label
                // start, which upstream's most_recent_label_start snapshot
                // guarantees.
                && (idx == 0
                    ==> forall |p: int|
                        0 <= p < first_non_fast(domain_name, 0)
                            ==> domain_name[p] != b'.')
                && (forall |p: int| idx as int <= p < first_non_fast(domain_name, 0)
                    ==> is_fast_byte(domain_name[p]))),
{
    let mut i: usize = 0;
    let mut label_start: usize = 0;
    while i < domain_name.len()
        invariant
            i <= domain_name.len(),
            label_start <= i,
            label_start == 0 || domain_name[label_start - 1] == b'.',
            label_start == 0 ==> forall |p: int| 0 <= p < i ==> domain_name[p] != b'.',
            label_start as int == defer_index_from(domain_name, i as int),
            forall |p: int| 0 <= p < i ==> is_fast_byte(domain_name[p]),
        decreases domain_name.len() - i
    {
        let b = domain_name[i];
        if in_inclusive_range8(b, b'a', b'z') {
            // A fast letter is not a dot, so the functional label start is
            // unchanged when the scan advances.
            proof {
                assert(b != b'.');
                assert(defer_index_from(domain_name, (i + 1) as int)
                    == defer_index_from(domain_name, i as int));
            }
            i = i + 1;
        } else if b == b'.' {
            // After a dot, the most recent label starts at the next index.
            proof {
                assert(domain_name[i as int] == b'.');
                assert(defer_index_from(domain_name, (i + 1) as int)
                    == ((i + 1) as int));
            }
            label_start = i + 1;
            i = i + 1;
        } else {
            let idx = label_start;
            proof {
                assert(!is_fast_byte(domain_name[i as int]) && i < domain_name.len());
                assert(!(forall |p: int| 0 <= p < domain_name.len()
                    ==> is_fast_byte(domain_name[p])));
                first_non_fast_all_fast(domain_name, 0, i as int);
                first_non_fast_at_non_fast(domain_name, i as int);
                assert(first_non_fast(domain_name, 0) == i as int);
                assert(forall |p: int| idx as int <= p < i as int
                    ==> is_fast_byte(domain_name[p]));
                assert(idx as int <= first_non_fast(domain_name, 0)
                    && first_non_fast(domain_name, 0) < domain_name.len());
                // The pinned deferral index: the loop invariant is exactly the
                // functional most-recent-label-start at the offending byte.
                assert(idx as int
                    == defer_index_from(domain_name, first_non_fast(domain_name, 0)));
                if idx == 0 {
                    // Straight from the loop invariant: label_start still at 0
                    // means no dot was scanned before the offending byte.
                    assert(forall |p: int| 0 <= p < first_non_fast(domain_name, 0)
                        ==> domain_name[p] != b'.') by {
                        assert(first_non_fast(domain_name, 0) == i as int);
                    }
                }
            }
            return FastPathScan::FastPathDefer(idx);
        }
    }
    proof {
        first_non_fast_all_fast(domain_name, 0, domain_name.len() as int);
    }
    // Success! The whole input passes through on the fastest path!
    FastPathScan::FastPathPass
}

// ---------------------------------------------------------------- Uts46 pipeline helpers (uts46.rs:1638-1682)

/// Spec model of one position's is_bidi test: the scan gates of
/// uts46.rs:1659-1676 (below Hebrew, the pre-existing-script ranges,
/// and the planes never carrying RTL classes bypass the class lookup;
/// the disallowed U+200F is commented in upstream as impossible in
/// mapping output and its debug_assert is a release no-op).
pub open spec fn is_bidi_at(buffer: Seq<char>, k: int) -> bool {
    let c = buffer[k] as int;
    c >= 0x0590
        && !(c >= 0x0900 && c <= 0xFB1C)
        && !(c >= 0x1F000 && c <= 0x3FFFF)
        && !(c >= 0xFF00 && c <= 0x107FF)
        && !(c >= 0x11000 && c <= 0x1E7FF)
        && bc_in_rtl_mask(adapter_bidi_class_of(buffer[k]))
}

/// Recursive the-exists-scan view of is_bidi.
pub open spec fn has_rtl_from(buffer: Seq<char>, j: int) -> bool
    decreases buffer.len() - j
{
    if j >= buffer.len() {
        false
    } else {
        is_bidi_at(buffer, j) || has_rtl_from(buffer, j + 1)
    }
}

/// Definitional step of has_rtl_from.
proof fn has_rtl_step_lemma(buffer: Seq<char>, j: int)
    ensures
        has_rtl_from(buffer, j) == (if j >= buffer.len() {
            false
        } else {
            is_bidi_at(buffer, j) || has_rtl_from(buffer, j + 1)
        }),
{
}

/// If no position of [a, j) is an rtl-gate hit, the two scan views agree.
proof fn has_rtl_prefix_none(buffer: Seq<char>, a: int, j: int)
    requires
        a <= j,
        forall |p: int| a <= p < j ==> !is_bidi_at(buffer, p),
    ensures
        has_rtl_from(buffer, a) == has_rtl_from(buffer, j),
    decreases j - a
{
    if a < j {
        has_rtl_step_lemma(buffer, a);
        has_rtl_prefix_none(buffer, a + 1, j);
    }
}

/// Upstream doc (uts46.rs:1657):
/// (No rustdoc on is_bidi; the function decides whether the domain
/// needs the bidi rules, per UTS 46 CheckBidi: true iff some label
/// character falls into the RTL classes through the scan gates.)
pub fn is_bidi(buffer: &[char]) -> (r: bool)
    ensures
        r == has_rtl_from(buffer@, 0),
{
    /* Origin Rust: for &c in buffer {
     *                 if c < '\u{0590}' { continue; }
     *                 if in_inclusive_range_char(c, '\u{0900}', '\u{FB1C}') { continue; }
     *                 if in_inclusive_range_char(c, '\u{1F000}', '\u{3FFFF}') { continue; }
     *                 if in_inclusive_range_char(c, '\u{FF00}', '\u{107FF}') { continue; }
     *                 if in_inclusive_range_char(c, '\u{11000}', '\u{1E7FF}') { continue; }
     *                 if RTL_MASK.intersects(self.data.bidi_class(c).to_mask()) { return true; }
     *             }
     *             false
     * -- the five continue-gates degenerate to one conjunction
     * (the debug_assert_ne on U+200F is a release no-op; the
     * disallowed-character claim lives in the mapping face, which this
     * build deliberately does not inject - see the adapter banner).
     */
    let mut i: usize = 0;
    while i < buffer.len()
        invariant
            i <= buffer.len(),
            forall |p: int| 0 <= p < i ==> !is_bidi_at(buffer@, p),
            has_rtl_from(buffer@, i as int) == has_rtl_from(buffer@, 0),
        decreases buffer.len() - i
    {
        let c = buffer[i];
        let cv = c as u32;
        if cv < 0x0590
            || (cv >= 0x0900 && cv <= 0xFB1C)
            || (cv >= 0x1F000 && cv <= 0x3FFFF)
            || (cv >= 0xFF00 && cv <= 0x107FF)
            || (cv >= 0x11000 && cv <= 0x1E7FF)
        {
            // none of the scan gates passes: the class lookup is
            // bypassed exactly as upstream continues
            proof {
                assert(!is_bidi_at(buffer@, i as int));
                has_rtl_step_lemma(buffer@, i as int);
                has_rtl_prefix_none(buffer@, 0, i as int);
            }
            i += 1;
            continue;
        }
        let bc = adapter_bidi_class(c);
        proof {
            assert(is_bidi_at(buffer@, i as int)
                == bc_in_rtl_mask(adapter_bidi_class_of(buffer@[i as int])));
            has_rtl_step_lemma(buffer@, i as int);
            has_rtl_prefix_none(buffer@, 0, i as int);
        }
        if match bc {
            BcModel::R => true,
            BcModel::AL => true,
            BcModel::AN => true,
            _ => false,
        } {
            return true;
        }
        proof {
            has_rtl_step_lemma(buffer@, i as int);
            has_rtl_prefix_none(buffer@, 0, i as int);
        }
        i += 1;
    }
    proof {
        has_rtl_prefix_none(buffer@, 0, buffer.len() as int);
    }
    false
}

/// Spec model of one position of has_appropriately_joining_char's scan
/// (uts46.rs:1644-1653): a mask hit ends the scan with true, a
/// non-transparent miss ends it with false, transparent positions step.
pub open spec fn joining_hit_at(c: char, left: bool) -> bool {
    let jt = adapter_joining_type_of(c);
    (left && jt_in_left_or_dual(jt)) || (!left && jt_in_right_or_dual(jt))
}

/// Forward scan view (the tail direction of the ContextJ rule).
pub open spec fn joining_scan_ok_from(label: Seq<char>, j: int, left: bool) -> bool
    decreases label.len() - j
{
    if j >= label.len() {
        false
    } else {
        joining_hit_at(label[j], left)
            || (jt_is_transparent(adapter_joining_type_of(label[j]))
                && joining_scan_ok_from(label, j + 1, left))
    }
}

/// Backward scan view (the head direction: the upstream call iterates
/// head.iter().rev(), i.e. from the joiner toward the label start).
pub open spec fn joining_scan_ok_back(label: Seq<char>, j: int, left: bool) -> bool
    decreases j + 1
{
    if j < 0 {
        false
    } else {
        joining_hit_at(label[j], left)
            || (jt_is_transparent(adapter_joining_type_of(label[j]))
                && joining_scan_ok_back(label, j - 1, left))
    }
}

/// Definitional step of the forward view.
proof fn joining_scan_fwd_step(label: Seq<char>, j: int, left: bool)
    ensures
        joining_scan_ok_from(label, j, left)
            == (if j >= label.len() {
                false
            } else {
                joining_hit_at(label[j], left)
                    || (jt_is_transparent(adapter_joining_type_of(label[j]))
                        && joining_scan_ok_from(label, j + 1, left))
            }),
{
}

/// Definitional step of the backward view.
proof fn joining_scan_back_step(label: Seq<char>, j: int, left: bool)
    ensures
        joining_scan_ok_back(label, j, left)
            == (if j < 0 {
                false
            } else {
                joining_hit_at(label[j], left)
                    || (jt_is_transparent(adapter_joining_type_of(label[j]))
                        && joining_scan_ok_back(label, j - 1, left))
            }),
{
}

/// Upstream doc (uts46.rs:1638-1655, the trait-method shape condensed):
/// the ContextJ per-rule neighbor scan - does the nearest relevant
/// joiner toward the scanning direction carry the required joining
/// type before a non-transparent interrupt.
pub fn has_appropriately_joining_char_forward(
    label: &[char],
    from: usize,
    left: bool,
) -> (r: bool)
    requires
        from <= label.len(),
    ensures
        r == joining_scan_ok_from(label@, from as int, left),
{
    let mut j = from;
    while j < label.len()
        invariant
            j <= label.len(),
            joining_scan_ok_from(label@, j as int, left)
                == joining_scan_ok_from(label@, from as int, left),
        decreases label.len() - j
    {
        let jt = adapter_joining_type(label[j]);
        if match jt {
            JtModel::LeftJoining => left,
            JtModel::DualJoining => true,
            JtModel::RightJoining => !left,
            _ => false,
        } {
            proof {
                joining_scan_fwd_step(label@, j as int, left);
            }
            return true;
        }
        match jt {
            JtModel::Transparent => {
                proof {
                    joining_scan_fwd_step(label@, j as int, left);
                    assert(!joining_hit_at(label@[j as int], left));
                }
                j += 1;
            }
            _ => {
                proof {
                    joining_scan_fwd_step(label@, j as int, left);
                    assert(!joining_hit_at(label@[j as int], left));
                    assert(!jt_is_transparent(
                        adapter_joining_type_of(label@[j as int])));
                    assert(!jt_is_transparent(adapter_joining_type_of(label@[j as int])));
                }
                return false;
            }
        }
    }
    proof {
        joining_scan_fwd_step(label@, j as int, left);
    }
    false
}

/// The backward direction of the same neighbor scan (the upstream call
/// iterates the head reversed; the transcription walks indices
/// downward with the same interruption semantics).
pub fn has_appropriately_joining_char_backward(
    label: &[char],
    from_last: usize,
    left: bool,
) -> (r: bool)
    requires
        from_last < label.len(),
    ensures
        r == joining_scan_ok_back(
            label@, from_last as int, left),
{
    let mut j = from_last;
    loop
        invariant
            j < label.len(),
            joining_scan_ok_back(label@, j as int, left)
                == joining_scan_ok_back(label@, from_last as int, left),
        decreases j + 1
    {
        let jt = adapter_joining_type(label[j]);
        if match jt {
            JtModel::LeftJoining => left,
            JtModel::DualJoining => true,
            JtModel::RightJoining => !left,
            _ => false,
        } {
            proof {
                joining_scan_back_step(label@, j as int, left);
            }
            return true;
        }
        match jt {
            JtModel::Transparent => {
                proof {
                    joining_scan_back_step(label@, j as int, left);
                    assert(!joining_hit_at(label@[j as int], left));
                }
                if j == 0 {
                    proof {
                        joining_scan_back_step(label@, (j as int) - 1, left);
                    }
                    return false;
                }
                j -= 1;
            }
            _ => {
                proof {
                    joining_scan_back_step(label@, j as int, left);
                    assert(!joining_hit_at(label@[j as int], left));
                    assert(!jt_is_transparent(
                        adapter_joining_type_of(label@[j as int])));
                }
                return false;
            }
        }
    }
}

// ---------------------------------------------------------------- check_hyphens (uts46.rs:1685-1721)

/// Error predicate of check_hyphens over the pre-state label: hyphen at the
/// first position, at the last position (labels of length >= 2), or the
/// third+fourth positions when those checks are not allowed. (For length-4
/// labels the third+fourth pair is witnessed by the last-position clause.)
pub open spec fn hyphen_check_error(pre: Seq<char>, allow_third_fourth: bool) -> bool {
    (pre.len() >= 1 && pre[0] == '-')
        || (pre.len() >= 2 && pre[pre.len() - 1] == '-')
        || (!allow_third_fourth && pre.len() >= 4 && pre[2] == '-' && pre[3] == '-')
}

/// Which positions get overwritten with U+FFFD in the non-fail-fast mode,
/// reflecting the upstream order of checks (a length-4 "xy--" label has its
/// last hyphen replaced first, which makes the third+fourth test read
/// U+FFFD at index 3, so the 2/3 replacement only happens for length >= 5).
pub open spec fn hyphen_replaced_at(pre: Seq<char>, allow_third_fourth: bool, i: int) -> bool {
    (i == 0 && pre.len() >= 1 && pre[0] == '-')
        || (i == pre.len() - 1 && pre.len() >= 2 && pre[pre.len() - 1] == '-')
        || (i == 2 && !allow_third_fourth && pre.len() >= 5 && pre[2] == '-' && pre[3] == '-')
        || (i == 3 && !allow_third_fourth && pre.len() >= 5 && pre[2] == '-' && pre[3] == '-')
}

pub open spec fn hyphen_replaced_any(pre: Seq<char>, allow_third_fourth: bool) -> bool {
    (pre.len() >= 1 && pre[0] == '-')
        || (pre.len() >= 2 && pre[pre.len() - 1] == '-')
        || (!allow_third_fourth && pre.len() >= 5 && pre[2] == '-' && pre[3] == '-')
}

pub open spec fn hyphen_final_char(pre: Seq<char>, allow_third_fourth: bool, i: int) -> char {
    if hyphen_replaced_at(pre, allow_third_fourth, i) {
        '\u{FFFD}'
    } else {
        pre[i]
    }
}

/* first_mut/last_mut are not specced by vstd; the Option<&mut char> probes are
 * transcribed as guarded index accesses with the same order of side effects
 * (first, then last, then third+fourth), which is semantically load-bearing:
 * a length-4 label ending in "--" has the last hyphen replaced first.
 * Origin Rust: fn check_hyphens(
 *                 mut_label: &mut [char],
 *                 allow_third_fourth: bool,
 *                 fail_fast: bool,
 *                 had_errors: &mut bool,
 *             ) -> bool {
 *                 if let Some(first) = mut_label.first_mut() {
 *                     if *first == '-' {
 *                         if fail_fast {
 *                             return true;
 *                         }
 *                         *had_errors = true;
 *                         *first = '\u{FFFD}';
 *                     }
 *                 }
 *                 if let Some(last) = mut_label.last_mut() {
 *                     if *last == '-' {
 *                         if fail_fast {
 *                             return true;
 *                         }
 *                         *had_errors = true;
 *                         *last = '\u{FFFD}';
 *                     }
 *                 }
 *                 if allow_third_fourth {
 *                     return false;
 *                 }
 *                 if mut_label.len() >= 4 && mut_label[2] == '-' && mut_label[3] == '-' {
 *                     if fail_fast {
 *                         return true;
 *                     }
 *                     *had_errors = true;
 *                     mut_label[2] = '\u{FFFD}';
 *                     mut_label[3] = '\u{FFFD}';
 *                 }
 *                 false
 *             }
 */
pub fn check_hyphens(
    mut_label: &mut [char],
    allow_third_fourth: bool,
    fail_fast: bool,
    had_errors: &mut bool,
) -> (r: bool)
    ensures
        // The early-return boolean channel fires exactly in fail-fast mode
        // when a hyphen-position violation exists in the pre-state.
        r == (fail_fast && hyphen_check_error(old(mut_label)@, allow_third_fourth)),
        fail_fast ==> (final(mut_label)@ == old(mut_label)@ && *final(had_errors) == *old(had_errors)),
        !fail_fast ==> (
            r == false
            && final(mut_label)@.len() == old(mut_label)@.len()
            && *final(had_errors)
                == (*old(had_errors) || hyphen_replaced_any(old(mut_label)@, allow_third_fourth))
            && (forall |i: int| #![trigger final(mut_label)@[i]]
                0 <= i < final(mut_label)@.len() ==>
                final(mut_label)@[i] == hyphen_final_char(old(mut_label)@, allow_third_fourth, i))
        ),
{
    let len = mut_label.len();
    if len >= 1 {
        if mut_label[0] == '-' {
            if fail_fast {
                return true;
            }
            *had_errors = true;
            mut_label[0] = '\u{FFFD}';
        }
    }
    if len >= 1 {
        let last = len - 1;
        if mut_label[last] == '-' {
            if fail_fast {
                return true;
            }
            *had_errors = true;
            mut_label[last] = '\u{FFFD}';
        }
    }
    if allow_third_fourth {
        return false;
    }
    if len >= 4 && mut_label[2] == '-' && mut_label[3] == '-' {
        if fail_fast {
            return true;
        }
        *had_errors = true;
        mut_label[2] = '\u{FFFD}';
        mut_label[3] = '\u{FFFD}';
    }
    false
}

// ---------------------------------------------------------------- check_label (uts46.rs:1542-1636)

/// Spec view of `is_ascii` (uts46.rs:1625): every char of the sequence is
/// below the ASCII range.
pub open spec fn all_ascii_seq(s: Seq<char>) -> bool {
    forall |j: int| 0 <= j < s.len() ==> (s[j] as u32) < 0x80
}

/// Spec view of the `hyphens != Hyphens::Allow` gate of check_label
/// (uts46.rs:1552): derivable enum compares are not visible on the exec
/// side, so this is the value the exec transcription computes up front.
pub open spec fn hyphen_is_allow(hyphens: Hyphens) -> bool {
    match hyphens {
        Hyphens::Allow => true,
        _ => false,
    }
}

/// Spec view of `hyphens == Hyphens::CheckFirstLast` (uts46.rs:1555).
pub open spec fn hyphen_is_first_last(hyphens: Hyphens) -> bool {
    match hyphens {
        Hyphens::CheckFirstLast => true,
        _ => false,
    }
}

/// Spec model of one ContextJ-position decision inside check_label's
/// in-place loop (uts46.rs:1575-1622) over the CURRENT working sequence
/// (positions before p may have been marked U+FFFD by earlier iterations;
/// positions after p are as they entered the loop; the neighbor scans
/// read only positions <= p-1 and >= p+1 of this same sequence): does
/// this position get marked? Faithfulness note: a joiner marked earlier
/// takes part in later neighbor checks with its U+FFFD identity (the
/// upstream in-place mutation makes this observable), and the marking
/// read of that U+FFFD queries the same adapter faces with it, which is
/// exactly what the uninterpreted adapter functions above model.
pub open spec fn ctxj_mark_at(s: Seq<char>, p: int) -> bool {
    if !(0 <= p < s.len()) {
        false
    } else {
        let c = s[p];
        if !(c == '\u{200C}' || c == '\u{200D}') {
            false
        } else if p == 0 {
            // No preceding character: the joiner is marked unconditionally.
            true
        } else if adapter_is_virama_of(s[p - 1]) {
            // The virama-adjacent exemption shared by ZWNJ and ZWJ.
            false
        } else if c == '\u{200D}' {
            // ZWJ only has the virama rule.
            true
        } else {
            // ZWNJ additionally demands the LEFT scan backwards and the
            // RIGHT scan forwards (ContextJ, uts46.rs:1606-1618).
            !(joining_scan_ok_back(s, p - 1, true)
                && joining_scan_ok_from(s, p + 1, false))
        }
    }
}

/// Working sequence after the ContextJ pass has processed positions
/// [p, q) (each marked position replaced in place before moving on;
/// the replacement is visible to all later decisions).
pub open spec fn ctxj_apply_range(s: Seq<char>, p: int, q: int) -> Seq<char>
    decreases q - p
{
    if p >= q {
        s
    } else {
        let s2 = if ctxj_mark_at(s, p) {
            s.update(p, '\u{FFFD}')
        } else {
            s
        };
        ctxj_apply_range(s2, p + 1, q)
    }
}

/// Did the ContextJ pass over [p, q) mark any position? The state
/// threading is the same as ctxj_apply_range (the recursion only ever
/// continues along the no-mark path, where the state is unchanged, so
/// the boolean is the exists-mark fact of the traced run).
pub open spec fn ctxj_any_marked_range(s: Seq<char>, p: int, q: int) -> bool
    decreases q - p
{
    if p >= q {
        false
    } else {
        ctxj_mark_at(s, p)
            || ctxj_any_marked_range(
                if ctxj_mark_at(s, p) {
                    s.update(p, '\u{FFFD}')
                } else {
                    s
                },
                p + 1,
                q,
            )
    }
}

/// Working sequence after check_label's hyphen pass (uts46.rs:1552-1561):
/// the hyphen marks of check_hyphens when hyphens != Allow, else the label
/// unchanged.
pub open spec fn check_label_post_hyphens(orig: Seq<char>, hyphens: Hyphens) -> Seq<char> {
    if hyphen_is_allow(hyphens) {
        orig
    } else {
        let a34 = hyphen_is_first_last(hyphens);
        Seq::new(orig.len(), |j: int| hyphen_final_char(orig, a34, j))
    }
}

/// Working sequence after check_label's leading combining-mark check
/// (uts46.rs:1562-1572): the first char is marked when a combining-mark
/// check is requested and the adapter reports a Mark general category.
pub open spec fn check_label_post_mark_check(s: Seq<char>, first_needs: bool) -> Seq<char> {
    if first_needs && s.len() >= 1 && adapter_is_mark_of(s[0]) {
        s.update(0, '\u{FFFD}')
    } else {
        s
    }
}

/// Working sequence after check_label's ContextJ pass.
pub open spec fn check_label_post_ctxj(s: Seq<char>, needs_ctxj: bool) -> Seq<char> {
    if needs_ctxj {
        ctxj_apply_range(s, 0, s.len() as int)
    } else {
        s
    }
}

/// MarkErrors-mode final content of check_label (fail_fast == false):
/// hyphen pass, then leading-mark pass, then the ContextJ in-place pass,
/// then the quadratic-behavior length gate (uts46.rs:1625-1634, a
/// non-ASCII label longer than PUNYCODE_ENCODE_MAX_INPUT_LENGTH gets
/// position 1000 marked).
pub open spec fn check_label_marked_content(
    orig: Seq<char>,
    hyphens: Hyphens,
    first_needs: bool,
    needs_ctxj: bool,
) -> Seq<char> {
    let after_h = check_label_post_hyphens(orig, hyphens);
    let after_m = check_label_post_mark_check(after_h, first_needs);
    let after_j = check_label_post_ctxj(after_m, needs_ctxj);
    if !all_ascii_seq(after_j)
        && after_j.len() > PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int
    {
        after_j.update(PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int, '\u{FFFD}')
    } else {
        after_j
    }
}

/// Which validity conditions fired for check_label's MarkErrors mode:
/// had_errors ends up set iff one of these holds. Each disjunct reads the
/// same intermediate working content the upstream pass would see.
pub open spec fn check_label_error_conds(
    orig: Seq<char>,
    hyphens: Hyphens,
    first_needs: bool,
    needs_ctxj: bool,
) -> bool {
    let a34 = hyphen_is_first_last(hyphens);
    let after_h = check_label_post_hyphens(orig, hyphens);
    let after_m = check_label_post_mark_check(after_h, first_needs);
    let after_j = check_label_post_ctxj(after_m, needs_ctxj);
    (!hyphen_is_allow(hyphens) && hyphen_replaced_any(orig, a34))
        || (first_needs && after_h.len() >= 1 && adapter_is_mark_of(after_h[0]))
        || (needs_ctxj && ctxj_any_marked_range(after_m, 0, after_m.len() as int))
        || (!all_ascii_seq(after_j)
            && after_j.len() > PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int)
}

/// Fail-fast violation existence (the boolean channel r == fail_fast &&
/// (...)): in fail-fast mode check_label returns at the FIRST violation
/// without ever mutating, so every later check reads the pristine label
/// (the ContextJ scan of the pristine label is the same function with
/// the working state fixed to the input).
pub open spec fn check_label_ff_error(
    orig: Seq<char>,
    hyphens: Hyphens,
    first_needs: bool,
    needs_ctxj: bool,
) -> bool {
    let a34 = hyphen_is_first_last(hyphens);
    (!hyphen_is_allow(hyphens) && hyphen_check_error(orig, a34))
        || (first_needs && orig.len() >= 1 && adapter_is_mark_of(orig[0]))
        || (needs_ctxj && ctxj_any_marked_range(orig, 0, orig.len() as int))
        || (!all_ascii_seq(orig) && orig.len() > PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int)
}

/// Upstream doc (uts46.rs:1542, condensed; no rustdoc on the method):
/// check_label performs the per-label validity checks of the UTS 46
/// pipeline in place: the hyphen positional rules (CheckHyphens), the
/// leading combining-mark rule, the ContextJ rules for U+200C/U+200D,
/// and the punycode encode length gate; fail-fast returns true at the
/// first violation, MarkErrors annotates the label with U+FFFD.
/* The upstream method receiver (`&self`) only carries the adapter data
 * faces, which are the injected adapter_* shims here, so the
 * transcription is a free function like is_bidi above. head/tail
 * splitting (`split_at_mut`) plus `head.last()` become index reads;
 * `has_appropriately_joining_char` over head.iter().rev() and the tail
 * become the backward/forward exec helpers.
 * Origin Rust: fn check_label(
 *                 &self,
 *                 hyphens: Hyphens,
 *                 mut_label: &mut [char],
 *                 fail_fast: bool,
 *                 had_errors: &mut bool,
 *                 first_needs_combining_mark_check: bool,
 *                 needs_contextj_check: bool,
 *             ) -> bool {
 *                 if hyphens != Hyphens::Allow
 *                     && check_hyphens(
 *                         mut_label,
 *                         hyphens == Hyphens::CheckFirstLast,
 *                         fail_fast,
 *                         had_errors,
 *                     )
 *                 {
 *                     return true;
 *                 }
 *                 if first_needs_combining_mark_check {
 *                     if let Some(first) = mut_label.first_mut() {
 *                         if self.data.is_mark(*first) {
 *                             if fail_fast {
 *                                 return true;
 *                             }
 *                             *had_errors = true;
 *                             *first = '\u{FFFD}';
 *                         }
 *                     }
 *                 }
 *                 if needs_contextj_check {
 *                     // ContextJ
 *                     for i in 0..mut_label.len() {
 *                         let c = mut_label[i];
 *                         if !in_inclusive_range_char(c, '\u{200C}', '\u{200D}') {
 *                             continue;
 *                         }
 *                         let (head, joiner_and_tail) = mut_label.split_at_mut(i);
 *                         if let Some((joiner, tail)) = joiner_and_tail.split_first_mut() {
 *                             if let Some(previous) = head.last() {
 *                                 if self.data.is_virama(*previous) {
 *                                     continue;
 *                                 }
 *                             } else {
 *                                 // No preceding character
 *                                 if fail_fast {
 *                                     return true;
 *                                 }
 *                                 *had_errors = true;
 *                                 *joiner = '\u{FFFD}';
 *                                 continue;
 *                             }
 *                             if c == '\u{200D}' {
 *                                 // ZWJ only has the virama rule
 *                                 if fail_fast {
 *                                     return true;
 *                                 }
 *                                 *had_errors = true;
 *                                 *joiner = '\u{FFFD}';
 *                                 continue;
 *                             }
 *                             debug_assert_eq!(c, '\u{200C}');
 *                             if !self.has_appropriately_joining_char(
 *                                 head.iter().rev().copied(),
 *                                 LEFT_OR_DUAL_JOINING_MASK,
 *                             ) || !self.has_appropriately_joining_char(
 *                                 tail.iter().copied(),
 *                                 RIGHT_OR_DUAL_JOINING_MASK,
 *                             ) {
 *                                 if fail_fast {
 *                                     return true;
 *                                 }
 *                                 *had_errors = true;
 *                                 *joiner = '\u{FFFD}';
 *                             }
 *                         } else {
 *                             debug_assert!(false);
 *                         }
 *                     }
 *                 }
 *                 if !is_ascii(mut_label) && mut_label.len() > PUNYCODE_ENCODE_MAX_INPUT_LENGTH {
 *                     // Limit quadratic behavior
 *                     if fail_fast {
 *                         return true;
 *                     }
 *                     *had_errors = true;
 *                     mut_label[PUNYCODE_ENCODE_MAX_INPUT_LENGTH] = '\u{FFFD}';
 *                 }
 *                 false
 *             }
 */
#[allow(clippy::too_many_arguments)]
pub fn check_label(
    hyphens: Hyphens,
    mut_label: &mut [char],
    fail_fast: bool,
    had_errors: &mut bool,
    first_needs_combining_mark_check: bool,
    needs_contextj_check: bool,
) -> (r: bool)
    ensures
        r == (fail_fast && check_label_ff_error(old(mut_label)@, hyphens,
                first_needs_combining_mark_check, needs_contextj_check)),
        fail_fast ==> (final(mut_label)@ == old(mut_label)@
            && *final(had_errors) == *old(had_errors)),
        !fail_fast ==> (
            r == false
            && final(mut_label)@ == check_label_marked_content(old(mut_label)@,
                hyphens, first_needs_combining_mark_check, needs_contextj_check)
            && *final(had_errors) == (*old(had_errors)
                || check_label_error_conds(old(mut_label)@, hyphens,
                    first_needs_combining_mark_check, needs_contextj_check))
        ),
{
    let len: usize = mut_label.len();
    let ghost orig: Seq<char> = mut_label@;
    let ghost entry_had: bool = *had_errors;
    let hyphens_on: bool = match hyphens {
        Hyphens::Allow => false,
        _ => true,
    };
    let a34: bool = match hyphens {
        Hyphens::CheckFirstLast => true,
        _ => false,
    };
    proof {
        assert(hyphen_is_allow(hyphens) == !hyphens_on);
        assert(hyphen_is_first_last(hyphens) == a34);
    }
    // ---- hyphen pass (uts46.rs:1552-1561)
    if hyphens_on {
        let early = check_hyphens(mut_label, a34, fail_fast, had_errors);
        if early {
            proof {
                // check_hyphens only returns true in fail-fast mode, and
                // then exactly when the hyphen-position violation exists
                // in the pristine label.
                assert(fail_fast);
                assert(hyphen_check_error(orig, a34));
            }
            return true;
        }
    }
    proof {
        // Bookkeeping equation after the hyphen pass: the content is the
        // spec post-hyphens sequence and had_errors got the hyphen mark
        // existence OR-ed in (in fail-fast the pass completed without a
        // violation, so nothing was marked and nothing was OR-ed in).
        let post_h = check_label_post_hyphens(orig, hyphens);
        if hyphens_on {
            assert(mut_label@ == post_h) by {
                vstd::seq::lemma_seq_ext_equal(mut_label@, post_h);
            }
            if fail_fast {
                assert(!hyphen_check_error(orig, a34));
                lemma_hyphen_no_error_implies_content_unchanged(orig, a34);
                assert(!(hyphens_on && hyphen_replaced_any(orig, a34)));
            }
        } else {
            assert(post_h == orig);
        }
        assert(*had_errors == (entry_had
            || (hyphens_on && hyphen_replaced_any(orig, a34))));
    }
    let ghost after_h: Seq<char> = mut_label@;
    proof {
        if fail_fast {
            // In fail-fast the hyphen pass did not mutate (a violation
            // would have returned above), so the working content is
            // still the original label.
            if hyphens_on {
                let post_h = check_label_post_hyphens(orig, hyphens);
                assert(post_h == orig) by {
                    vstd::seq::lemma_seq_ext_equal(post_h, orig);
                }
            }
            assert(after_h == orig);
            assert(!(hyphens_on && hyphen_replaced_any(orig, a34)));
        }
    }
    // ---- leading combining-mark check (uts46.rs:1562-1572)
    if first_needs_combining_mark_check {
        if len >= 1 {
            let first = mut_label[0];
            if adapter_is_mark(first) {
                if fail_fast {
                    proof {
                        assert(adapter_is_mark_of(orig[0]));
                    }
                    return true;
                }
                proof {
                    assert(adapter_is_mark_of(after_h[0]));
                }
                *had_errors = true;
                mut_label[0] = '\u{FFFD}';
                proof {
                    vstd::seq::lemma_seq_ext_equal(mut_label@, after_h.update(0, '\u{FFFD}'));
                }
            }
        }
    }
    let ghost after_m: Seq<char> = mut_label@;
    proof {
        assert(after_m == check_label_post_mark_check(after_h, first_needs_combining_mark_check));
        assert(*had_errors == (entry_had
            || (hyphens_on && hyphen_replaced_any(orig, a34))
            || (first_needs_combining_mark_check
                && after_h.len() >= 1
                && adapter_is_mark_of(after_h[0]))));
    }
    // ---- ContextJ pass (uts46.rs:1573-1623)
    proof {
        if fail_fast {
            // In fail-fast nothing was marked so far (both earlier gates
            // returned before their mutations on this path), so the
            // working content is still the original label and no
            // error condition has fired yet.
            if hyphens_on {
                let post_h = check_label_post_hyphens(orig, hyphens);
                assert(post_h == orig) by {
                    vstd::seq::lemma_seq_ext_equal(post_h, orig);
                }
            }
            assert(after_m == orig);
            assert(!(hyphens_on && hyphen_replaced_any(orig, a34)));
            assert(!(first_needs_combining_mark_check
                && after_h.len() >= 1 && adapter_is_mark_of(after_h[0])));
        }
    }
    if needs_contextj_check {
        let mut i: usize = 0;
        while i < mut_label.len()
            invariant
                mut_label.len() == len,
                i <= len,
                needs_contextj_check == true,
                orig == old(mut_label)@,
                entry_had == *old(had_errors),
                mut_label@ == ctxj_apply_range(after_m, 0, i as int),
                fail_fast ==> mut_label@ == after_m,
                fail_fast ==> after_m == orig,
                fail_fast ==> after_h == orig,
                fail_fast ==> ctxj_any_marked_range(after_m, 0, i as int) == false,
                fail_fast ==> !(hyphens_on && hyphen_replaced_any(orig, a34)),
                fail_fast ==> !(first_needs_combining_mark_check
                    && after_h.len() >= 1 && adapter_is_mark_of(after_h[0])),
                *had_errors == (entry_had
                    || (hyphens_on && hyphen_replaced_any(orig, a34))
                    || (first_needs_combining_mark_check
                        && after_h.len() >= 1
                        && adapter_is_mark_of(after_h[0]))
                    || ctxj_any_marked_range(after_m, 0, i as int)),
            decreases len - i
        {
            let c = mut_label[i];
            proof {
                // The working state at position i: positions >= i are
                // untouched by the first i steps of the traced run.
                lemma_ctxj_apply_range_index_stable(after_m, 0, i as int, i as int);
                assert(mut_label@[i as int] == c);
            }
            if !(c == '\u{200C}' || c == '\u{200D}') {
                proof {
                    assert(ctxj_mark_at(mut_label@, i as int) == false);
                    lemma_ctxj_apply_range_snoc(after_m, i as int);
                    lemma_ctxj_any_marked_snoc(after_m, i as int);
                }
                i += 1;
                continue;
            }
            if i == 0 {
                // No preceding character
                if fail_fast {
                    proof {
                        assert(ctxj_mark_at(mut_label@, 0) == true);
                        assert(mut_label@ == orig);
                        assert(ctxj_apply_range(orig, 0, 0) == orig);
                        // The pristine traced run marks position 0, so the
                        // any up to 1 fires; the range then grows to the
                        // full label (the ff error disjunct).
                        lemma_ctxj_any_marked_snoc(orig, 0);
                        assert(ctxj_any_marked_range(orig, 0, 1) == true);
                        assert(orig.len() >= 1);
                        lemma_ctxj_any_marked_split(orig, 0, 1, orig.len() as int);
                        assert(ctxj_any_marked_range(orig, 0, orig.len() as int) == true);
                        assert(*had_errors == entry_had);
                        assert(check_label_ff_error(orig, hyphens,
                            first_needs_combining_mark_check, needs_contextj_check));
                    }
                    return true;
                }
                proof {
                    assert(ctxj_mark_at(mut_label@, 0) == true);
                }
                *had_errors = true;
                mut_label[0] = '\u{FFFD}';
                proof {
                    lemma_ctxj_apply_range_snoc(after_m, 0);
                    lemma_ctxj_any_marked_snoc(after_m, 0);
                }
                i += 1;
                continue;
            }
            let previous = mut_label[i - 1];
            if adapter_is_virama(previous) {
                // The virama exemption: this position is not marked.
                proof {
                    assert(adapter_is_virama_of(mut_label@[i as int - 1]));
                    assert(ctxj_mark_at(mut_label@, i as int) == false);
                    lemma_ctxj_apply_range_snoc(after_m, i as int);
                    lemma_ctxj_any_marked_snoc(after_m, i as int);
                }
                i += 1;
                continue;
            }
            if c == '\u{200D}' {
                // ZWJ only has the virama rule
                if fail_fast {
                    proof {
                        assert(adapter_is_virama_of(mut_label@[i as int - 1]) == false);
                        assert(ctxj_mark_at(mut_label@, i as int) == true);
                        assert(mut_label@ == orig);
                        assert(ctxj_apply_range(orig, 0, i as int) == orig);
                        // The pristine traced run (no fail-fast mutations)
                        // marks position i, so the ff error disjunct fires.
                        lemma_ctxj_any_marked_snoc(orig, i as int);
                        assert(ctxj_any_marked_range(orig, 0, i as int + 1) == true);
                        lemma_ctxj_any_marked_split(orig, 0, i as int + 1, orig.len() as int);
                        assert(ctxj_any_marked_range(orig, 0, orig.len() as int) == true);
                        assert(*had_errors == entry_had);
                        assert(check_label_ff_error(orig, hyphens,
                            first_needs_combining_mark_check, needs_contextj_check));
                    }
                    return true;
                }
                proof {
                    assert(ctxj_mark_at(mut_label@, i as int) == true);
                }
                *had_errors = true;
                mut_label[i] = '\u{FFFD}';
                proof {
                    lemma_ctxj_apply_range_snoc(after_m, i as int);
                    lemma_ctxj_any_marked_snoc(after_m, i as int);
                }
                i += 1;
                continue;
            }
            // ZWNJ (c == U+200C): both neighbor-joining scans. Upstream
            // short-circuits the disjunction after the first (backward)
            // scan; both scans are pure reads of the working label, so
            // evaluating both then combining is the same decision.
            proof {
                assert(c == '\u{200C}');
            }
            let hb = has_appropriately_joining_char_backward(mut_label, i - 1, true);
            let hf = has_appropriately_joining_char_forward(mut_label, i + 1, false);
            proof {
                assert(hb == joining_scan_ok_back(mut_label@, i as int - 1, true));
                assert(hf == joining_scan_ok_from(mut_label@, i as int + 1, false));
            }
            if !hb || !hf {
                if fail_fast {
                    proof {
                        assert(ctxj_mark_at(mut_label@, i as int) == true);
                        assert(mut_label@ == orig);
                        assert(ctxj_apply_range(orig, 0, i as int) == orig);
                        lemma_ctxj_any_marked_snoc(orig, i as int);
                        assert(ctxj_any_marked_range(orig, 0, i as int + 1) == true);
                        lemma_ctxj_any_marked_split(orig, 0, i as int + 1, orig.len() as int);
                        assert(ctxj_any_marked_range(orig, 0, orig.len() as int) == true);
                        assert(*had_errors == entry_had);
                        assert(check_label_ff_error(orig, hyphens,
                            first_needs_combining_mark_check, needs_contextj_check));
                    }
                    return true;
                }
                proof {
                    assert(ctxj_mark_at(mut_label@, i as int) == true);
                }
                *had_errors = true;
                mut_label[i] = '\u{FFFD}';
                proof {
                    lemma_ctxj_apply_range_snoc(after_m, i as int);
                    lemma_ctxj_any_marked_snoc(after_m, i as int);
                }
            } else {
                proof {
                    assert(ctxj_mark_at(mut_label@, i as int) == false);
                    lemma_ctxj_apply_range_snoc(after_m, i as int);
                    lemma_ctxj_any_marked_snoc(after_m, i as int);
                }
            }
            i += 1;
        }
    }
    // ---- length gate (uts46.rs:1625-1634)
    proof {
        if fail_fast && needs_contextj_check {
            assert(mut_label@ == after_m);
            assert(after_m == orig);
            assert(!ctxj_any_marked_range(orig, 0, orig.len() as int));
        }
        let post_j = check_label_post_ctxj(after_m, needs_contextj_check);
        assert(len as int == after_m.len());
        assert(mut_label@ == post_j);
    }
    let ascii_all = is_ascii(mut_label);
    proof {
        assert(ascii_all == all_ascii_seq(mut_label@));
    }
    if !ascii_all && len > PUNYCODE_ENCODE_MAX_INPUT_LENGTH {
        if fail_fast {
            // The length-gate violation exists in the pristine label:
            // this is the fail-fast boolean channel.
            proof {
                assert(!all_ascii_seq(orig));
                assert(orig.len() > PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int);
                assert(check_label_ff_error(orig, hyphens,
                    first_needs_combining_mark_check, needs_contextj_check));
            }
            return true;
        }
        let ghost after_j: Seq<char> = mut_label@;
        proof {
            assert(after_j == check_label_post_ctxj(after_m, needs_contextj_check));
            assert(!all_ascii_seq(after_j));
            assert(after_j.len() > PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int);
        }
        *had_errors = true;
        mut_label[PUNYCODE_ENCODE_MAX_INPUT_LENGTH] = '\u{FFFD}';
        proof {
            assert(final(mut_label)@ == after_j.update(
                PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int, '\u{FFFD}'));
        }
    }
    false
}

// ---------------------------------------------------------------- after_punycode_decode (uts46.rs:1496-1540)
// (Upstream defines this just before check_label; it is kept here after
// the check_label section since the two-tier context models share the
// check_hyphens/scan machinery above.)

/// Spec model of apply_ascii_deny_list_to_lower_cased_unicode as used on
/// the mapping-feed face of the pipeline (the per-char deny application
/// to the lower-cased mapping output).
pub open spec fn deny_apply_model(c: char, deny: u128) -> char {
    if (c as u32) >= 0x80 {
        c
    } else if bit_is_set(deny, (c as u32) as u8) {
        '\u{FFFD}'
    } else {
        c
    }
}

/// The appended-content model of after_punycode_decode's push phase:
/// the adapter normalize_validate stage (the P6 uninterpreted whole
/// sequence function) followed by the per-char deny application.
pub open spec fn after_pd_output(label: Seq<char>, deny: u128) -> Seq<char> {
    let nv = adapter_norm_valid_of(label);
    Seq::new(nv.len(), |k: int| deny_apply_model(nv[k], deny))
}

/// Index of the first U+FFFD of the out-sequence at or after j (None if
/// none); the fail-fast push phase stops right before it.
pub open spec fn first_fffd_from(out: Seq<char>, j: int) -> Option<int>
    decreases out.len() - j
{
    if j >= out.len() {
        Option::None
    } else if out[j] == '\u{FFFD}' {
        Option::Some(j)
    } else {
        first_fffd_from(out, j + 1)
    }
}

/// Push-phase bookkeeping view: did the first stage U+FFFD (if any)
/// already pass the advancing push frontier k?
pub open spec fn fffd_before(out: Seq<char>, k: int) -> bool {
    match first_fffd_from(out, 0) {
        Option::Some(f) => f < k,
        Option::None => false,
    }
}

/// Index of the first position where the out-sequence differs from the
/// decoded label within the zipped prefix (None if none): the upstream
/// zip pairs the appended content with label_buffer from position 0 and
/// stops at the shorter side.
pub open spec fn first_diff_from(out: Seq<char>, label: Seq<char>, j: int) -> Option<int>
    decreases out.len() - j
{
    if j >= out.len() || j >= label.len() {
        Option::None
    } else if out[j] != label[j] {
        Option::Some(j)
    } else {
        first_diff_from(out, label, j + 1)
    }
}

/// Final appended-content model of the comparison phase: exactly the
/// first difference (if any) is marked U+FFFD (the upstream
/// try_for_each short-circuits at the first Err).
pub open spec fn after_pd_marked(out: Seq<char>, label: Seq<char>) -> Seq<char> {
    match first_diff_from(out, label, 0) {
        Option::Some(d) => out.update(d, '\u{FFFD}'),
        Option::None => out,
    }
}

/// Positions after_punycode_decode's fail-fast push phase reaches: the
/// whole out sequence when it holds no U+FFFD, else the first U+FFFD
/// index.
pub open spec fn pd_prefix_len(out: Seq<char>) -> int {
    match first_fffd_from(out, 0) {
        Option::Some(f) => f,
        Option::None => out.len() as int,
    }
}

/// Upstream doc (uts46.rs:1496; no rustdoc, condensed): runs the
/// normalize_validate stage over the decoded punycode label with the
/// deny list applied, errors at any produced U+FFFD, and then compares
/// the appended content against the decoded label, marking the first
/// difference with U+FFFD (fail fast returns true at the first
/// violation instead).
/* SmallVec becomes Vec (the inline-capacity layer is not value
 * semantics). The zip pairing of `normalized` with label_buffer aligns
 * with the appended content because both upstream call sites enter
 * with domain_buffer truncated at the fresh label boundary; that
 * call-site guarantee is transcribed as the requires below. The
 * iterator fusion of the mapping and deny stages is decomposed into a
 * whole-sequence mapping call followed by a per-char loop (strict
 * in-order composition; same produced sequence).
 * Origin Rust: fn after_punycode_decode(
 *                 &self,
 *                 domain_buffer: &mut SmallVec<[char; 253]>,
 *                 current_label_start: usize,
 *                 label_buffer: &[char],
 *                 deny_list_deny_dot: u128,
 *                 fail_fast: bool,
 *                 had_errors: &mut bool,
 *             ) -> bool {
 *                 for c in self
 *                     .data
 *                     .normalize_validate(label_buffer.iter().copied())
 *                     .map(|c| apply_ascii_deny_list_to_lower_cased_unicode(c, deny_list_deny_dot))
 *                 {
 *                     if c == '\u{FFFD}' {
 *                         if fail_fast { return true; }
 *                         *had_errors = true;
 *                     }
 *                     domain_buffer.push(c);
 *                 }
 *                 let normalized = &mut domain_buffer[current_label_start..];
 *                 if let Err(()) =
 *                     normalized
 *                         .iter_mut()
 *                         .zip(label_buffer.iter())
 *                         .try_for_each(|(norm_c, decoded_c)| {
 *                             if *norm_c == *decoded_c {
 *                                 Ok(())
 *                             } else {
 *                                 // Mark the first difference
 *                                 *norm_c = '\u{FFFD}';
 *                                 Err(())
 *                             }
 *                         })
 *                 {
 *                     if fail_fast { return true; }
 *                     *had_errors = true;
 *                 }
 *                 false
 *             }
 */
pub fn after_punycode_decode(
    domain_buffer: &mut Vec<char>,
    current_label_start: usize,
    label_buffer: &[char],
    deny_list_deny_dot: u128,
    fail_fast: bool,
    had_errors: &mut bool,
) -> (r: bool)
    requires
        current_label_start == domain_buffer.len(),
        // the deny-dot image fact: dots map to U+FFFD, so the appended
        // content is dot-free (the E-CEN census channel below)
        bit_is_set(deny_list_deny_dot, b'.'),
    ensures
        // the label census of the sink walk (E-CEN feed): the appended
        // content is a deny-dot image of the decode model, hence
        // dot-free, so the census grows by at most one (the
        // empty-entry first-label allowance)
        lab_count(final(domain_buffer)@)
            <= lab_count(old(domain_buffer)@)
                + (if old(domain_buffer)@.len() == 0 { 1int } else { 0int }),
        // Fail-fast boolean channel
        r == (fail_fast && ({
            let out = after_pd_output(label_buffer@, deny_list_deny_dot);
            first_fffd_from(out, 0).is_some()
                || first_diff_from(out, label_buffer@, 0).is_some()
        })),
        fail_fast ==> *final(had_errors) == *old(had_errors),
        fail_fast ==> ({
            let out = after_pd_output(label_buffer@, deny_list_deny_dot);
            if r && first_fffd_from(out, 0).is_some() {
                // Stopped right before the first U+FFFD: only the pure
                // prefix got appended.
                final(domain_buffer)@.len()
                    == old(domain_buffer)@.len() + pd_prefix_len(out)
            } else {
                final(domain_buffer)@.len()
                    == old(domain_buffer)@.len() + out.len() as int
            }
        }),
        fail_fast ==> forall |p: int|
            #![trigger final(domain_buffer)@[p]]
            (0 <= p < old(domain_buffer)@.len()
                ==> final(domain_buffer)@[p] == old(domain_buffer)@.index(p)),
        // aggregate fail-fast content channel (call-site consumable
        // single equality per sub-case)
        fail_fast ==> ({
            let out = after_pd_output(label_buffer@, deny_list_deny_dot);
            if r && first_fffd_from(out, 0).is_some() {
                final(domain_buffer)@ == old(domain_buffer)@
                    .add(out.subrange(0, pd_prefix_len(out)))
            } else if r {
                final(domain_buffer)@ == old(domain_buffer)@
                    .add(after_pd_marked(out, label_buffer@))
            } else {
                final(domain_buffer)@ == old(domain_buffer)@.add(out)
            }
        }),
        fail_fast ==> ({
            let out = after_pd_output(label_buffer@, deny_list_deny_dot);
            if r && first_fffd_from(out, 0).is_some() {
                forall |q: int| 0 <= q < pd_prefix_len(out)
                    ==> final(domain_buffer)@[old(domain_buffer)@.len() + q]
                        == out.index(q)
            } else if r {
                forall |q: int| 0 <= q < out.len() as int
                    ==> final(domain_buffer)@[old(domain_buffer)@.len() + q]
                        == after_pd_marked(out, label_buffer@).index(q)
            } else {
                forall |q: int| 0 <= q < out.len() as int
                    ==> final(domain_buffer)@[old(domain_buffer)@.len() + q]
                        == out.index(q)
            }
        }),
        !fail_fast ==> (
            r == false
            && *final(had_errors) == (*old(had_errors) || ({
                let out = after_pd_output(label_buffer@, deny_list_deny_dot);
                first_fffd_from(out, 0).is_some()
                    || first_diff_from(out, label_buffer@, 0).is_some()
            }))
            && final(domain_buffer)@.len()
                == old(domain_buffer)@.len()
                    + ({
                        let out = after_pd_output(label_buffer@, deny_list_deny_dot);
                        out.len() as int
                    })
        ),
        !fail_fast ==> forall |p: int|
            #![trigger final(domain_buffer)@[p]]
            (0 <= p < old(domain_buffer)@.len()
                ==> final(domain_buffer)@[p] == old(domain_buffer)@.index(p)),
        !fail_fast ==> ({
            let out = after_pd_output(label_buffer@, deny_list_deny_dot);
            forall |q: int| 0 <= q < out.len() as int
                ==> final(domain_buffer)@[old(domain_buffer)@.len() + q]
                    == after_pd_marked(out, label_buffer@).index(q)
        }),
        // aggregate mark-errors content channel
        !fail_fast ==> ({
            let out = after_pd_output(label_buffer@, deny_list_deny_dot);
            final(domain_buffer)@ == old(domain_buffer)@
                .add(after_pd_marked(out, label_buffer@))
        }),
{
    let ghost b0: Seq<char> = old(domain_buffer)@;
    let ghost entry_had: bool = *had_errors;
    let validate = adapter_normalize_validate(label_buffer);
    let ghost out: Seq<char> = after_pd_output(label_buffer@, deny_list_deny_dot);
    proof {
        // P6 binding and the out-sequence length fact.
        assert(validate@ == adapter_norm_valid_of(label_buffer@));
        lemma_after_pd_output_len(label_buffer@, deny_list_deny_dot);
        lemma_first_fffd_index_bound(out, 0);
    }
    // ---- push phase (uts46.rs:1506-1518)
    let mut k: usize = 0;
    while k < validate.len()
        invariant
            k <= validate.len(),
            out.len() == validate@.len(),
            out == after_pd_output(label_buffer@, deny_list_deny_dot),
            current_label_start as int == b0.len(),
            b0 == old(domain_buffer)@,
            entry_had == *old(had_errors),
            domain_buffer@.len() == b0.len() + k as int,
            forall |j: int| 0 <= j < out.len()
                ==> out[j] == deny_apply_model(validate@[j], deny_list_deny_dot),
            forall |p: int| 0 <= p < b0.len() ==> domain_buffer@[p] == b0[p],
            forall |q: int| 0 <= q < k as int
                ==> domain_buffer@[b0.len() + q] == out[q],
            fail_fast ==> forall |q: int| 0 <= q < k as int ==> out[q] != '\u{FFFD}',
            forall |f: int| first_fffd_from(out, 0) == Option::Some(f)
                ==> (0 <= f < out.len()),
            *had_errors == (entry_had || fffd_before(out, k as int)),
            bit_is_set(deny_list_deny_dot, b'.'),
        decreases validate.len() - k
    {
        proof {
            lemma_first_fffd_index_bound(out, 0);
        }
        let c = apply_ascii_deny_list_to_lower_cased_unicode(
            validate[k],
            deny_list_deny_dot,
        );
        proof {
            assert(c == deny_apply_model(validate@[k as int], deny_list_deny_dot));
            assert(c == out[k as int]);
        }
        if c == '\u{FFFD}' {
            if fail_fast {
                proof {
                    // The pushed prefix is pure and this position holds a
                    // U+FFFD, so this is the first stage FFFD.
                    lemma_first_fffd_known(out, k as int);
                    assert(first_fffd_from(out, 0) == Option::Some(k as int));
                    assert(pd_prefix_len(out) == k as int);
                    // the census channel of the fired exit: the cut
                    // prefix is dot-free, so the census grew by at most
                    // the empty-entry allowance
                    lemma_after_pd_output_not_dot(
                        label_buffer@, deny_list_deny_dot);
                    lemma_first_fffd_index_bound(out, 0);
                    assert(0 <= pd_prefix_len(out)
                        && pd_prefix_len(out) <= out.len() as int);
                    let pref = out.subrange(0, pd_prefix_len(out));
                    assert(pref.len() as int == pd_prefix_len(out)) by {
                        vstd::seq::lemma_seq_subrange_len(
                            out, 0, pd_prefix_len(out));
                    }
                    assert forall |q: int| #![trigger pref[q]]
                        0 <= q < pref.len() as int ==> pref[q] != '.' by {
                        if 0 <= q && q < pref.len() as int {
                            assert(pref.len() as int == pd_prefix_len(out));
                            vstd::seq::lemma_seq_subrange_index(
                                out, 0, pd_prefix_len(out), q);
                        }
                    }
                    lemma_lab_count_append_dotfree(b0, pref);
                    assert(domain_buffer@ == b0.add(pref)) by {
                        assert(domain_buffer@.len() as int
                            == b0.len() as int + pref.len() as int) by {
                            assert(pd_prefix_len(out) == k as int);
                            vstd::seq::lemma_seq_add_len(b0, pref);
                        }
                        assert forall |q: int| #![trigger b0.add(pref)[q]]
                            0 <= q < domain_buffer@.len() as int
                            implies b0.add(pref)[q] == domain_buffer@[q] by {
                            if (b0.len() as int) <= q
                                && q < domain_buffer@.len() as int {
                                vstd::seq::lemma_seq_add_index2(b0, pref, q);
                                vstd::seq::lemma_seq_subrange_index(
                                    out, 0, pd_prefix_len(out),
                                    q - b0.len() as int);
                            }
                        }
                        vstd::seq::lemma_seq_ext_equal(b0.add(pref),
                            domain_buffer@);
                    }
                }
                return true;
            }
            proof {
                // The frontier crosses this U+FFFD position: the
                // bookkeeping view is true from k+1 on.
                lemma_fffd_before_step(out, k as int);
            }
            *had_errors = true;
        }
        if c != '\u{FFFD}' {
            proof {
                lemma_fffd_before_step_same(out, k as int);
            }
        }
        let ghost pb = domain_buffer@;
        domain_buffer.push(c);
        proof {
            assert(domain_buffer@ == pb.push(c));
            vstd::seq::lemma_seq_push_index_same(pb, c, (pb.len() as int));
            assert(domain_buffer@[pb.len() as int] == c);
        }
        k += 1;
    }
    proof {
        // Full push completed: the whole out-sequence is appended. In
        // the fail-fast mode the completed push also means the
        // out-sequence holds no U+FFFD at all (a first one had returned).
        if fail_fast {
            lemma_first_fffd_all_pure(out);
        }
    }
    // ---- zip comparison phase (uts46.rs:1519-1539)
    let zlen: usize = if validate.len() <= label_buffer.len() {
        validate.len()
    } else {
        label_buffer.len()
    };
    let mut j: usize = 0;
    while j < zlen
        invariant
            j <= zlen,
            zlen as int
                == (if out.len() <= label_buffer@.len() {
                    out.len()
                } else {
                    label_buffer@.len()
                }),
            out.len() == validate@.len(),
            out == after_pd_output(label_buffer@, deny_list_deny_dot),
            current_label_start as int == b0.len(),
            b0 == old(domain_buffer)@,
            entry_had == *old(had_errors),
            domain_buffer@.len() == b0.len() + out.len(),
            forall |p: int| 0 <= p < b0.len() ==> domain_buffer@[p] == b0[p],
            forall |q: int| 0 <= q < out.len()
                ==> domain_buffer@[b0.len() + q] == out[q],
            forall |q: int| 0 <= q < j as int ==> out[q] == label_buffer@[q],
            forall |f: int| first_fffd_from(out, 0) == Option::Some(f)
                ==> (0 <= f < out.len()),
            fail_fast ==> first_fffd_from(out, 0) == Option::None,
            *had_errors == (entry_had || first_fffd_from(out, 0).is_some()),
            bit_is_set(deny_list_deny_dot, b'.'),
        decreases zlen - j
    {
        proof {
            lemma_first_fffd_index_bound(out, 0);
            assert(j < out.len());
            assert((j as int) < (zlen as int));
            assert((j as int) < domain_buffer@.len() - b0.len());
            assert((current_label_start as int) + (j as int)
                < domain_buffer@.len());
            assert(domain_buffer.len() == domain_buffer@.len());
        }
        let idx: usize = current_label_start + j;
        let norm_c = domain_buffer[idx];
        let decoded_c = label_buffer[j];
        proof {
            assert(idx as int == b0.len() + j as int);
            assert(norm_c == out[j as int]);
        }
        if norm_c != decoded_c {
            proof {
                assert(out[j as int] != label_buffer@[j as int]);
            }
            let ghost pre = domain_buffer@;
            domain_buffer.set(idx, '\u{FFFD}');
            proof {
                assert(domain_buffer@ == pre.update(
                    idx as int, '\u{FFFD}'));
                assert(idx as int == b0.len() + j as int);
                // Zip stops at the first difference: the final content is
                // the marked model.
                lemma_first_diff_known(out, label_buffer@, j as int);
                assert(after_pd_marked(out, label_buffer@)
                    == out.update(j as int, '\u{FFFD}'));
                // the census channel of the diff exits: the marked
                // model is dot-free, so the census grew by at most the
                // empty-entry allowance
                lemma_after_pd_output_not_dot(
                    label_buffer@, deny_list_deny_dot);
                lemma_after_pd_marked_not_dot(out, label_buffer@);
                let mkd = out.update(j as int, '\u{FFFD}');
                assert forall |q: int| #![trigger mkd[q]]
                    0 <= q < mkd.len() as int ==> mkd[q] != '.' by {
                    vstd::seq::lemma_seq_update_len(out, j as int, '\u{FFFD}');
                    if q != j as int {
                        vstd::seq::lemma_seq_update_different(
                            out, q, j as int, '\u{FFFD}');
                    }
                }
                lemma_lab_count_append_dotfree(b0, mkd);
                assert(domain_buffer@ == b0.add(mkd)) by {
                    assert(domain_buffer@.len() as int
                        == b0.len() as int + mkd.len() as int) by {
                        vstd::seq::lemma_seq_update_len(
                            out, j as int, '\u{FFFD}');
                        vstd::seq::lemma_seq_add_len(b0, mkd);
                    }
                    assert forall |q: int| #![trigger b0.add(mkd)[q]]
                        0 <= q < domain_buffer@.len() as int
                        implies b0.add(mkd)[q] == domain_buffer@[q] by {
                        if (b0.len() as int) <= q
                            && q < domain_buffer@.len() as int {
                            vstd::seq::lemma_seq_add_index2(b0, mkd, q);
                        }
                    }
                    vstd::seq::lemma_seq_ext_equal(b0.add(mkd),
                        domain_buffer@);
                }
            }
            if fail_fast {
                return true;
            }
            *had_errors = true;
            return false;
        }
        j += 1;
    }
    // The zipped prefix matched up to min(out.len(), label.len()).
    proof {
        lemma_first_diff_matched_prefix(out, label_buffer@, j as int);
        assert(first_diff_from(out, label_buffer@, 0) == Option::None);
        assert(after_pd_marked(out, label_buffer@) == out);
        // the census channel of the clean exit: the full appended
        // content is dot-free
        lemma_after_pd_output_not_dot(label_buffer@, deny_list_deny_dot);
        lemma_after_pd_marked_not_dot(out, label_buffer@);
        lemma_lab_count_append_dotfree(b0, out);
        assert(domain_buffer@ == b0.add(out)) by {
            assert(domain_buffer@.len() as int
                == b0.len() as int + out.len() as int) by {
                vstd::seq::lemma_seq_add_len(b0, out);
            }
            assert forall |q: int| #![trigger b0.add(out)[q]]
                0 <= q < domain_buffer@.len() as int
                implies b0.add(out)[q] == domain_buffer@[q] by {
                if (b0.len() as int) <= q
                    && q < domain_buffer@.len() as int {
                    vstd::seq::lemma_seq_add_index2(b0, out, q);
                }
            }
            vstd::seq::lemma_seq_ext_equal(b0.add(out), domain_buffer@);
        }
    }
    false
}

// ---------------------------------------------------------------- WHATWG UTF-8 lossy decoder (uts46.rs:1254 feed tier)
//
// Origin: the `non_ascii.chars()` feed of process_innermost (uts46.rs:1252-
// 1255) iterates `utf8_iter::Utf8Chars` over the non-ASCII label suffix. That
// iterator is NOT part of the idna_adapter injection perimeter (it is not
// idna data), so per the adapter-contract design record (section 4) this
// tier is a *verified transcription* of the WHATWG Encoding Standard UTF-8
// decoder instead of an injected property; no new assumption is introduced
// here (the P1-P6 perimeter is unchanged).
//
// Provenance of the transcribed semantics (upstream pin utf8_iter 1.0.4,
// src/lib.rs): the crate's public `next()` fast path decodes through a
// generated lookup table, and every path it rejects falls through to
// `next_fallback()`, which is the normative WHATWG decoder without a table.
// The transcription below follows `next_fallback()` case for case, extended
// with the fourth completion check of the fused `next()` for four-byte
// sequences (a valid complete four-byte sequence is decoded by the fast
// path, never by the fallback; the acceptance condition there -- lead in
// 0xF0..=0xF4 with the F0/F4 second-byte windows and all continuation bytes
// in 0x80..=0xBF -- is exactly the WHATWG norm, and is the same condition
// this transcription checks). The table-vs-norm equivalence of the fast
// path is documented by the upstream crate as behavioral ("the same way as
// String::from_utf8_lossy", with the crate test asserting iterator-vs-std
// equality) and is recorded in the design record; it is a property of the
// upstream crate under test, not an assumption of this file. The runtime
// probe (out/poc/idna-rt-probe) exercised the real upstream pipeline
// end-to-end with zero mismatches on vectors whose non-ASCII segments cover
// this decoder's channels, and IdnaTestV2 row vectors in the samples panel
// pin the same end-to-end behavior formally.
//
// WHATWG step semantics as transcribed below (one emitted char plus the
// number of consumed bytes, 1..=4):
//   * lead byte 0x00..=0x7F: the ASCII char, one byte;
//   * lead outside 0xC2..=0xF4, or a lead at the very end of the input:
//     U+FFFD over that one byte;
//   * second byte outside the lead's window (E0: A0-BF, ED: 80-9F,
//     F0: 90-BF, F4: 80-8F, others 80-BF; these windows rule out overlong
//     forms, surrogates, and values above U+10FFFF): U+FFFD over the lead
//     byte alone;
//   * two-byte lead (0xC2..=0xDF) with in-window second byte: the code
//     point, two bytes;
//   * three-byte lead with in-window second byte but no third byte:
//     U+FFFD over both bytes;
//   * third byte outside 0x80..=0xBF: U+FFFD over the first two bytes;
//   * three-byte lead with valid continuation pair: the code point, three
//     bytes;
//   * four-byte lead (0xF0..=0xF4) with valid second and third bytes but
//     the sequence ends, or the fourth byte is outside 0x80..=0xBF:
//     U+FFFD over the first three bytes;
//   * four-byte lead with valid second, third, and fourth bytes: the code
//     point, four bytes.
// (Malformed maximal subparts therefore reproduce the same replacement
// stream as `String::from_utf8_lossy`, one U+FFFD per step, with skipped
// tail bytes re-decoded as fresh leads below.)

/// Spec model of one WHATWG decoder step at byte index `i`: the emitted
/// char and the number of consumed bytes. The valid-char code points are
/// written as lead/continuation window arithmetic instead of bit masks so
/// the model stays evaluatable (compute-friendly formulation) and linear
/// for the solver; each arm's windows make the masked form of the upstream
/// body equal to this form bit for bit.
pub open spec fn lossy_step(bytes: &[u8], i: int) -> (char, int)
{
    if !(0 <= i < bytes.len() as int) {
        // Out of the operating domain: callers reach lossy_step only for
        // in-bounds indices (the fold below guards, and the bound lemma
        // carries the domain as its requires).
        ('\u{FFFD}', 1)
    } else {
        let b0 = bytes[i] as int;
        if b0 < 0x80 {
            ((bytes[i] as u32) as char, 1)
        } else if !(0xC2 <= b0 <= 0xF4) || i + 1 >= bytes.len() as int {
            ('\u{FFFD}', 1)
        } else {
            let b1 = bytes[i + 1] as int;
            let lo: int = if b0 == 0xE0 {
                0xA0
            } else if b0 == 0xF0 {
                0x90
            } else {
                0x80
            };
            let hi: int = if b0 == 0xED {
                0x9F
            } else if b0 == 0xF4 {
                0x8F
            } else {
                0xBF
            };
            if !(lo <= b1 <= hi) {
                ('\u{FFFD}', 1)
            } else if b0 < 0xE0 {
                (
                    (((bytes[i] as u32) - 0xC0u32) * 64u32
                        + ((bytes[i + 1] as u32) - 0x80u32)) as char,
                    2,
                )
            } else if i + 2 >= bytes.len() as int {
                ('\u{FFFD}', 2)
            } else {
                let b2 = bytes[i + 2] as int;
                if !(0x80 <= b2 <= 0xBF) {
                    ('\u{FFFD}', 2)
                } else if b0 < 0xF0 {
                    (
                        (((bytes[i] as u32) - 0xE0u32) * 4096u32
                            + ((bytes[i + 1] as u32) - 0x80u32) * 64u32
                            + ((bytes[i + 2] as u32) - 0x80u32)) as char,
                        3,
                    )
                } else if i + 3 >= bytes.len() as int {
                    ('\u{FFFD}', 3)
                } else {
                    let b3 = bytes[i + 3] as int;
                    if !(0x80 <= b3 <= 0xBF) {
                        ('\u{FFFD}', 3)
                    } else {
                        (
                            (((bytes[i] as u32) - 0xF0u32) * 262144u32
                                + ((bytes[i + 1] as u32) - 0x80u32) * 4096u32
                                + ((bytes[i + 2] as u32) - 0x80u32) * 64u32
                                + ((bytes[i + 3] as u32) - 0x80u32)) as char,
                            4,
                        )
                    }
                }
            }
        }
    }
}

/// The WHATWG lossy decoding of `bytes`, folded from index `i` with the
/// accumulation `acc` (chars emitted for 0..i so far).
pub open spec fn lossy_chars_from(bytes: &[u8], i: int, acc: Seq<char>) -> (r: Seq<char>)
    decreases
        bytes.len() as int - i,
{
    if i < 0 || i >= bytes.len() as int {
        // Outside [0, len) the fold is its accumulator (the operating
        // domain is carried by the caller-side guard and the bound lemma).
        acc
    } else {
        let (rc, rn) = lossy_step(bytes, i);
        lossy_chars_from(bytes, i + rn, acc.push(rc))
    }
}

/// The full lossy decode of a byte string: the produced char sequence of
/// the WHATWG decoder, which upstream feeds into Adapter::map_normalize at
/// uts46.rs:1252-1255.
pub open spec fn lossy_chars_model(bytes: &[u8]) -> (r: Seq<char>) {
    lossy_chars_from(bytes, 0, Seq::empty())
}

/// Exec form of one WHATWG decoder step (the `next_fallback` case chain of
/// utf8_iter 1.0.4, fused with the complete-four-byte branch of the fast
/// path; see the section header). Index arithmetic over the slice replaces
/// the iterator's `remaining` cursor.
fn lossy_step_exec(bytes: &[u8], i: usize) -> (pair: (char, usize))
    requires
        0 <= i < bytes.len(),
    ensures
        (pair.0, pair.1 as int) == lossy_step(bytes, i as int),
{
    let first = bytes[i];
    if first < 0x80 {
        let c = first as char;
        proof {
            assert((c as u32) == first as u32);
        }
        return (c, 1);
    }
    /* Origin Rust (utf8_iter::Utf8Chars::next_fallback):
     *     if !in_inclusive_range8(first, 0xC2, 0xF4) || self.remaining.len() == 1 {
     *         self.remaining = &self.remaining[1..];
     *         return Some('\u{FFFD}');
     *     }
     */
    if !in_inclusive_range8(first, 0xC2, 0xF4) || bytes.len() - i == 1 {
        return ('\u{FFFD}', 1);
    }
    let second = bytes[i + 1];
    /* Origin Rust:
     *     let (lower_bound, upper_bound) = match first {
     *         0xE0 => (0xA0, 0xBF), 0xED => (0x80, 0x9F),
     *         0xF0 => (0x90, 0xBF), 0xF4 => (0x80, 0x8F),
     *         _ => (0x80, 0xBF),
     *     };
     *     if !in_inclusive_range8(second, lower_bound, upper_bound) {
     *         self.remaining = &self.remaining[1..];
     *         return Some('\u{FFFD}');
     *     }
     */
    let lo: u8 = if first == 0xE0 {
        0xA0
    } else if first == 0xF0 {
        0x90
    } else {
        0x80
    };
    let hi: u8 = if first == 0xED {
        0x9F
    } else if first == 0xF4 {
        0x8F
    } else {
        0xBF
    };
    if !in_inclusive_range8(second, lo, hi) {
        return ('\u{FFFD}', 1);
    }
    /* Origin Rust:
     *     if first < 0xE0 {
     *         self.remaining = &self.remaining[2..];
     *         let point = ((u32::from(first) & 0x1F) << 6) | (u32::from(second) & 0x3F);
     *         return Some(unsafe { char::from_u32_unchecked(point) });
     *     }
     * The unchecked construction is transcribed as the checked
     * std::char::from_u32 with the window bounds proving the checked form
     * cannot fail (overlongs are impossible: C2..DF leads put the value in
     * 0x80..=0x7FF).
     */
    if first < 0xE0 {
        // Verus note: vstd does not spec the bitwise form of the upstream
        // body, `((u32::from(first) & 0x1F) << 6) | (u32::from(second) &
        // 0x3F)`. On this arm first is in 0xC2..=0xDF and second in
        // 0x80..=0xBF (the windows checked above), so the 0x1F mask keeps
        // the low five bits of the lead (whose high part is exactly 0xC0),
        // the 0x3F mask keeps the low six bits of the continuation (whose
        // high part is exactly 0x80), the two groups occupy disjoint bit
        // ranges, and the shift-by-6 is the product by 64: the masked-or
        // form and the window arithmetic below are the same value bit for
        // bit. The transcription computes the window arithmetic (the same
        // technique as the wrapping_sub transcription of
        // in_inclusive_range8), keeping the bounds obligations live.
        let point = ((first as u32) - 0xC0) * 64 + ((second as u32) - 0x80);
        proof {
            assert((point as int)
                == ((first as int) - 0xC0) * 64 + ((second as int) - 0x80));
            assert((point as int) <= 0x7FF);
            assert(0x80 <= (point as int));
            assert(punycode_v::is_valid_code_point(point as int));
        }
        let c = match std::char::from_u32(point) {
            Option::Some(c) => c,
            Option::None => {
                proof {
                    // the window bounds prove the checked form total (no
                    // overlongs/surrogates/out-of-range values on this arm)
                    assert(punycode_v::is_valid_code_point(point as int));
                    assert(false);
                }
                '\u{FFFD}'
            }
        };
        proof {
            assert((c as u32) == point);
        }
        return (c, 2);
    }
    /* Origin Rust:
     *     if self.remaining.len() == 2 {
     *         self.remaining = &self.remaining[2..];
     *         return Some('\u{FFFD}');
     *     }
     */
    if bytes.len() - i == 2 {
        return ('\u{FFFD}', 2);
    }
    let third = bytes[i + 2];
    /* Origin Rust:
     *     if !in_inclusive_range8(third, 0x80, 0xBF) {
     *         self.remaining = &self.remaining[2..];
     *         return Some('\u{FFFD}');
     *     }
     */
    if !in_inclusive_range8(third, 0x80, 0xBF) {
        return ('\u{FFFD}', 2);
    }
    /* Origin Rust:
     *     if first < 0xF0 {
     *         self.remaining = &self.remaining[3..];
     *         let point = ((u32::from(first) & 0xF) << 12)
     *             | ((u32::from(second) & 0x3F) << 6) | (u32::from(third) & 0x3F);
     *         return Some(unsafe { char::from_u32_unchecked(point) });
     *     }
     * Checked here as above: the E0 window (>= 0xA0) rules out overlongs
     * (value >= 0x800) and the ED window (<= 0x9F) rules out surrogates
     * (value <= 0xD7FF), so the checked form cannot fail.
     */
    if first < 0xF0 {
        // Verus note: same transcription technique as the two-byte arm. The
        // upstream masked form `((u32::from(first) & 0xF) << 12) |
        // ((u32::from(second) & 0x3F) << 6) | (u32::from(third) & 0x3F)`
        // equals the window arithmetic below bit for bit (first is in
        // 0xE0..=0xEF here, so the 0xF mask is the subtraction by 0xE0; the
        // windows keep second and third in 0x80..=0xBF, so the 0x3F masks
        // are the subtractions by 0x80; the three groups are disjoint and
        // the shifts are the products).
        let point = ((first as u32) - 0xE0) * 4096
            + ((second as u32) - 0x80) * 64
            + ((third as u32) - 0x80);
        proof {
            assert((point as int)
                == ((first as int) - 0xE0) * 4096
                    + ((second as int) - 0x80) * 64
                    + ((third as int) - 0x80));
            // case knowledge for the window lets (the solver case-splits
            // the exec definitions on demand; make the bound chain local)
            assert((second as int) <= (hi as int));
            assert((hi as int) <= 0xBF);
            assert((second as int) <= 0xBF);
            assert((third as int) <= 0xBF);
            assert((first as int) <= 0xEF);
            assert((point as int) <= 0xF * 4096 + 63 * 64 + 63);
            assert((point as int) <= 0xFFFF);
            if first == 0xED {
                // the 80-9F second-byte window keeps the value below the
                // surrogate block (ED leads cannot produce surrogates)
                assert(((second as int) - 0x80) <= 0x1F);
                assert((point as int) <= 0xD * 4096 + 0x1F * 64 + 0x3F);
                assert(((point as int) < 0xD800));
            }
            if first == 0xE0 {
                // the A0-BF window rules out the overlong form
                assert(((second as int) - 0x80) >= 0x20);
                assert((point as int) >= 0x800);
            }
            assert(punycode_v::is_valid_code_point(point as int));
        }
        let c = match std::char::from_u32(point) {
            Option::Some(c) => c,
            Option::None => {
                proof {
                    // the window bounds prove the checked form total (no
                    // overlongs/surrogates/out-of-range values on this arm)
                    assert(punycode_v::is_valid_code_point(point as int));
                    assert(false);
                }
                '\u{FFFD}'
            }
        };
        proof {
            assert((c as u32) == point);
        }
        return (c, 3);
    }
    /* Origin Rust (the trailing comment of next_fallback): a valid three-
     * byte prefix of a four-byte sequence that has to be incomplete,
     * "because otherwise `next()` would have succeeded". The fused next()
     * succeeds exactly when a fourth byte exists and is a continuation,
     * completing the scalar (the F0 window keeps values >= 0x10000 and the
     * F4 window keeps them <= 0x10FFFF); this transcription checks the
     * fourth byte explicitly, which is the normative WHATWG condition and
     * is the only channel where the fused upstream behavior extends the
     * fallback body (see the section header provenance note).
     *
     *     // At this point, we have a valid 3-byte prefix of a
     *     // four-byte sequence that has to be incomplete, because
     *     // otherwise `next()` would have succeeded.
     *     self.remaining = &self.remaining[3..];
     *     Some('\u{FFFD}')
     */
    if bytes.len() - i == 3 {
        return ('\u{FFFD}', 3);
    }
    let fourth = bytes[i + 3];
    if !in_inclusive_range8(fourth, 0x80, 0xBF) {
        return ('\u{FFFD}', 3);
    }
    // Verus note: same transcription technique as the two-byte arm (the
    // upstream masked form with the 0x7/0x3F masks equals the window
    // arithmetic below bit for bit: first is in 0xF0..=0xF4 here so the
    // 0x7 mask is the subtraction by 0xF0, the windows keep the three
    // continuations in 0x80..=0xBF, and the groups are disjoint).
    let point = ((first as u32) - 0xF0) * 262144
        + ((second as u32) - 0x80) * 4096
        + ((third as u32) - 0x80) * 64
        + ((fourth as u32) - 0x80);
    proof {
        assert((point as int)
            == ((first as int) - 0xF0) * 262144
                + ((second as int) - 0x80) * 4096
                + ((third as int) - 0x80) * 64
                + ((fourth as int) - 0x80));
        assert((second as int) <= (hi as int));
        assert((hi as int) <= 0xBF);
        assert((second as int) <= 0xBF);
        assert((third as int) <= 0xBF);
        assert((fourth as int) <= 0xBF);
        assert((first as int) <= 0xF4);
        if first == 0xF0 {
            // the 90-BF second-byte window keeps the value out of the
            // overlong band (>= 0x10000, hence also not a surrogate)
            assert(lo == 0x90);
            assert((second as int) >= 0x90);
            assert(((second as int) - 0x80) >= 0x10);
            assert((point as int) >= 0x10 * 4096);
            assert((point as int) >= 0x10000);
        }
        assert((point as int) <= 4 * 262144 + 15 * 4096 + 63 * 64 + 63);
        assert((point as int) <= 0x10FFFF);
        assert(punycode_v::is_valid_code_point(point as int));
    }
    let c = match std::char::from_u32(point) {
        Option::Some(c) => c,
        Option::None => {
            proof {
                // the F0/F4 second-byte windows keep the scalar at or below
                // U+10FFFF (and at or above U+10000, so no surrogates)
                assert(punycode_v::is_valid_code_point(point as int));
                assert(false);
            }
            '\u{FFFD}'
        }
    };
    proof {
        assert((c as u32) == point);
    }
    (c, 4)
}

/// Verified transcription of the WHATWG lossy bytes->chars feed that
/// process_innermost hands to Adapter::map_normalize (uts46.rs:1252-1255):
/// produces exactly the model sequence. Iterator fusion upstream
/// (`map_normalize(non_ascii.chars()).map(deny)`) decomposes into this
/// verified decode followed by the (trusted, P5) mapping and the verified
/// deny-list application; each consumed char is a valid Rust char by
/// construction, and every byte is consumed in exactly one step.
pub fn utf8_lossy_chars(bytes: &[u8]) -> (r: Vec<char>)
    ensures
        r@ == lossy_chars_model(bytes),
{
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < bytes.len()
        invariant
            i <= bytes.len(),
            lossy_chars_model(bytes)
                == lossy_chars_from(bytes, i as int, out@),
        decreases
            bytes.len() - i,
    {
        let (c, n) = lossy_step_exec(bytes, i);
        proof {
            // One-step unfold of the fold at the current index: the
            // model's step equals the helper's result, so the fold
            // advances over exactly (c, n).
            assert(lossy_chars_from(bytes, i as int, out@)
                == lossy_chars_from(bytes, i as int + (n as int), out@.push(c))) by {
                reveal(lossy_step);
                reveal_with_fuel(lossy_chars_from, 1);
            };
            // Step-safety so the loop index stays in the fold's domain
            // and the variant decreases.
            lemma_lossy_step_bounds(bytes, i as int);
        }
        out.push(c);
        i = i + n;
    }
    out
}

/// Origin: uts46.rs:108-115 write_punycode_label -- the punycode emission
/// tier of the pipeline sink. Transcribed against the Vec<char> sink (the
/// core::fmt::Write -> push transcription of the batch B/C precedent; the
/// Sink error channel is unreachable through this sink, so the error type
/// is the encode length guard's). The output contract is the batch B/C
/// full-encode model anchored on the "xn--" literal prefix: on success the
/// sink holds exactly the anchor content of the model, and the error
/// channel is exactly the RFC 3492 section 6.4 one-shot product guard of
/// the internal-caller encode.
pub fn write_punycode_label(
    label: &[char],
    sink: &mut Vec<char>,
) -> (r: Result<(), punycode_v::PunycodeEncodeError>)
    requires
        label.len() <= u32::MAX as usize,
    ensures
        forall |q: int| 0 <= q < old(sink)@.len()
            ==> final(sink)@[q] == old(sink)@[q],
        final(sink)@.len() >= old(sink)@.len(),
        ({
            let anchor = old(sink)@
                .push('\u{78}')
                .push('\u{6E}')
                .push('\u{2D}')
                .push('\u{2D}');
            let m = punycode_v::encode_full_model(label@, anchor);
            if (((label.len() as u64) + 1) * punycode_v::RFC_ONE_SHOT_LIMIT
                > (u32::MAX as u64))
            {
                r.is_err() && final(sink)@ == anchor
            } else {
                r.is_ok()
                    && final(sink)@.len() == (m->0).len()
                    && (forall |p: int| 0 <= p < (m->0).len()
                        ==> final(sink)@[p] as int == (m->0)[p])
            }
        }),
{
    sink.push('x');
    sink.push('n');
    sink.push('-');
    sink.push('-');
    proof {
        // The four prefix pushes are the model anchor tail: the encode
        // callee's old(sink) is exactly outer-old + "xn--".
        let anchor4 = old(sink)@
            .push('x').push('n').push('-').push('-');
        assert(sink@ == anchor4);
    }
    punycode_v::encode_into_chars_internal(label, sink)
}

// ---------------------------------------------------------------- Bidi post-pass marking tier (uts46.rs:1385-1492)
/// The label-start index of position p (0, or one past the most recent dot).
pub open spec fn b_label_start(P: Seq<char>, p: int) -> (s: int)
    decreases p
{
    if p <= 0 {
        0
    } else if P[p - 1] == b'.' as char {
        p
    } else {
        b_label_start(P, p - 1)
    }
}

/// The first index at or after s that holds a dot, or the length.
pub open spec fn b_dot_or_end(P: Seq<char>, s: int) -> (e: int)
    decreases P.len() as int - s
{
    if s >= P.len() as int {
        s
    } else if P[s] == b'.' as char {
        s
    } else {
        b_dot_or_end(P, s + 1)
    }
}

/// The exclusive end of the label starting at s.
pub open spec fn b_label_end(P: Seq<char>, s: int) -> (e: int) {
    if s >= P.len() as int {
        s
    } else {
        b_dot_or_end(P, s + 1)
    }
}

/// Class readouts on the pre-pass content (P1 masks and predicates).
pub open spec fn b_nsm_at(P: Seq<char>, p: int) -> bool {
    bc_is_nsm(adapter_bidi_class_of(P[p]))
}
pub open spec fn b_first_mask_at(P: Seq<char>, p: int) -> bool {
    bc_in_first_mask(adapter_bidi_class_of(P[p]))
}
pub open spec fn b_is_ltr_at(P: Seq<char>, p: int) -> bool {
    bc_is_ltr(adapter_bidi_class_of(P[p]))
}
pub open spec fn b_last_ltr_at(P: Seq<char>, p: int) -> bool {
    bc_in_last_ltr(adapter_bidi_class_of(P[p]))
}
pub open spec fn b_last_rtl_at(P: Seq<char>, p: int) -> bool {
    bc_in_last_rtl(adapter_bidi_class_of(P[p]))
}
pub open spec fn b_middle_ltr_at(P: Seq<char>, p: int) -> bool {
    bc_in_middle_ltr(adapter_bidi_class_of(P[p]))
}
pub open spec fn b_middle_rtl_at(P: Seq<char>, p: int) -> bool {
    bc_in_middle_rtl(adapter_bidi_class_of(P[p]))
}
pub open spec fn b_en_at(P: Seq<char>, p: int) -> bool {
    bc_is_en(adapter_bidi_class_of(P[p]))
}
pub open spec fn b_an_at(P: Seq<char>, p: int) -> bool {
    bc_is_an(adapter_bidi_class_of(P[p]))
}

/// The rightmost position in [lo, hi) whose class is not NSM, or -1.
pub open spec fn b_last_non_nsm(P: Seq<char>, lo: int, hi: int) -> (q: int)
    decreases hi - lo
{
    if hi <= lo {
        -1
    } else if b_nsm_at(P, hi - 1) {
        b_last_non_nsm(P, lo, hi - 1)
    } else {
        hi - 1
    }
}

/// The RTL middle-scan numeral state after positions [s+1, k) of the label
/// starting at s (0 undecided, 1 European, 2 Arabic). A position that
/// violates MIDDLE_RTL_MASK takes no state update (upstream's state
/// match lives under the mask check's else, uts46.rs:1440-1466).
pub open spec fn b_numeral_state(P: Seq<char>, s: int, k: int) -> (st: int)
    decreases k - (s + 1)
{
    if k <= s + 1 {
        0
    } else {
        let st = b_numeral_state(P, s, k - 1);
        if !b_middle_rtl_at(P, k - 1) {
            st
        } else if st == 0 {
            if b_en_at(P, k - 1) {
                1
            } else if b_an_at(P, k - 1) {
                2
            } else {
                0
            }
        } else if st == 1 {
            // European stays European (an Arabic transition is a marking
            // violation, not a state change)
            1
        } else {
            // Arabic stays Arabic (symmetric)
            2
        }
    }
}

/// The RTL closing-numeral clash of uts46.rs:1469-1479: the accumulated
/// numeral state disagrees with the class of the (non-NSM) last character.
pub open spec fn b_numeral_clash(P: Seq<char>, s: int, q: int) -> (r: bool) {
    let st = b_numeral_state(P, s, q);
    (st == 1 && b_an_at(P, q)) || (st == 2 && b_en_at(P, q))
}

/// The RTL middle-scan marking condition for position p in (s, q): a
/// MIDDLE_RTL_MASK violation, or the numeral transition violation.
pub open spec fn b_mid_rtl_mark(P: Seq<char>, s: int, p: int) -> (r: bool) {
    if !b_middle_rtl_at(P, p) {
        true
    } else {
        let st = b_numeral_state(P, s, p);
        (st == 1 && b_an_at(P, p)) || (st == 2 && b_en_at(P, p))
    }
}

/// The positional marking predicate of the whole pass over pre-pass
/// content P: exactly the positions that receive U+FFFD. Faithfulness
/// structure notes: the first gate failing marks only the first position
/// (upstream `continue`s the label, so the label's remaining checks never
/// run); a label whose tail is entirely NSM gets no further checks (the
/// trim scan exhausts the label); dots are never label contents; and for
/// positions past the rightmost non-NSM character only the NSM trim
/// applied, with no marking.
pub open spec fn b_marked(P: Seq<char>, p: int) -> (r: bool) {
    if !(0 <= p < P.len() as int) || P[p] == b'.' as char {
        false
    } else {
        let s = b_label_start(P, p);
        let e = b_label_end(P, s);
        if p == s {
            !b_first_mask_at(P, p)
        } else if !b_first_mask_at(P, s) {
            // The label's first gate failed: the remaining checks never
            // ran for this label.
            false
        } else {
            let q = b_last_non_nsm(P, s + 1, e);
            if q < 0 {
                // The tail is all NSM: trim exhaustion, no further checks.
                false
            } else {
                let ltr = b_is_ltr_at(P, s);
                if p == q {
                    (ltr && !b_last_ltr_at(P, p))
                        || (!ltr
                            && (!b_last_rtl_at(P, p)
                                || b_numeral_clash(P, s, q)))
                } else {
                    (s < p
                        && p < q
                        && ((ltr && !b_middle_ltr_at(P, p))
                            || (!ltr && b_mid_rtl_mark(P, s, p))))
                }
            }
        }
    }
}

/// The whole-pass marking existence channel.
pub open spec fn b_any_marked(P: Seq<char>) -> (r: bool) {
    exists |p: int| 0 <= p < P.len() as int && b_marked(P, p)
}

/// The post-pass content, pointwise.
pub open spec fn b_final_at(P: Seq<char>, p: int) -> (c: char) {
    if b_marked(P, p) {
        '\u{FFFD}'
    } else {
        P[p]
    }
}

/// Exec readout helper: is the char's class NSM (match on the exec BcModel
/// readout; derived enum equality is not SMT-visible, so the membership
/// tests of the upstream masks are transcribed as matches).
#[inline(always)]
fn nsm_class_read(c: char) -> (r: bool)
    ensures
        r == bc_is_nsm(adapter_bidi_class_of(c)),
{
    match adapter_bidi_class(c) {
        BcModel::NSM => true,
        _ => false,
    }
}

/* Origin Rust: let is_bidi = self.is_bidi(domain_buffer);
 *             if is_bidi {
 *                 for label in domain_buffer.split_mut(|c| *c == '.') {
 *                     if let Some((first, tail)) = label.split_first_mut() {
 *                         ... the mask/numeral marking chain ...
 *                     }
 *                 }
 *             }
 * -- the is_bidi guard lives at the call site (process_innermost), as
 * upstream; this tier is the `if is_bidi { ... }` body. The per-label
 * body is lifted into `bidi_mark_label` below (the scan/marking statements
 * are unchanged; the lift keeps the per-label proof obligations in a
 * fresh frame, the same phase-extraction treatment the decode iterator
 * received in the punycode mirror). slice::split_first_mut/split_mut/
 * split_last_mut are not specced by vstd; the label and scan structure is
 * transcribed as index arithmetic, with the NSM trim scan walking from
 * the right. The label geometry (no interior dots, boundary dots) enters
 * the helper as requires, so every per-position model derivation inside
 * works against loop-free hypotheses.
 */
fn bidi_mark_label(
    domain_buffer: &mut Vec<char>,
    frozen: &[char],
    fail_fast: bool,
    had_in: bool,
    s: usize,
    e: usize,
) -> (ret: (bool, bool))
    requires
        s < e,
        e <= domain_buffer.len(),
        e <= frozen.len(),
        domain_buffer@.len() == frozen@.len(),
        // label boundaries and interior geometry (the scan result of the
        // caller loop)
        (s == 0 || frozen@[(s as int) - 1] == b'.' as char),
        ((e as int) >= frozen@.len() as int
            || frozen@[(e as int)] == b'.' as char),
        forall |t: int| (s as int) <= t < (e as int)
            ==> frozen@[t] != b'.' as char,
        // the label body is untouched at entry
        forall |t: int| (s as int) <= t < domain_buffer@.len() as int
            ==> domain_buffer@[t] == frozen@[t],
    ensures
        // the pass writes only in place: the length never changes
        final(domain_buffer)@.len() == old(domain_buffer)@.len(),
        // the stopped channel is exactly the fail-fast-with-a-marking case
        ret.0 == (fail_fast
            && (exists |p: int| (s as int) <= p < (e as int)
                && b_marked(frozen@, p))),
        // the prefix below the label is never touched
        forall |t: int| 0 <= t < (s as int)
            ==> final(domain_buffer)@[t] == old(domain_buffer)@[t],
        !ret.0 ==> (
            // the completed label holds the pointwise marked content
            (forall |t: int| (s as int) <= t < (e as int)
                ==> final(domain_buffer)@[t] == b_final_at(frozen@, t))
            // the tail above the label is untouched
            && (forall |t: int| (e as int) <= t < frozen@.len() as int
                ==> final(domain_buffer)@[t] == frozen@[t])
            // the had bit joins exactly the label's mark existence
            && (ret.1 == (had_in
                || (exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p))))
        ),
        // the fail-fast stop is write-free
        ret.0 ==> final(domain_buffer)@ == old(domain_buffer)@ && ret.1 == had_in,
{
    let ghost pre: Seq<char> = domain_buffer@;
    let ghost f0: Seq<char> = frozen@;
    let mut hr: bool = had_in;
    // ---- first-character gate (uts46.rs:1388-1398)
    let first_bc = adapter_bidi_class(domain_buffer[s]);
    let first_ok = match first_bc {
        BcModel::L => true,
        BcModel::R => true,
        BcModel::AL => true,
        _ => false,
    };
    proof {
        assert(first_ok == b_first_mask_at(frozen@, s as int));
        lemma_b_marked_at(frozen@, s as int, s as int, e as int);
        assert(b_marked(frozen@, s as int) == !first_ok);
    }
    if !first_ok {
        if fail_fast {
            proof {
                assert(exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p));
            }
            return (true, had_in);
        }
        hr = true;
        domain_buffer.set(s, '\u{FFFD}');
        proof {
            let ghost pw = domain_buffer@;
            assert(domain_buffer@ == pw.update(s as int, '\u{FFFD}'));
            assert(domain_buffer@[(s as int)] == b_final_at(frozen@, s as int));
            // the label's remaining positions never get checked when the
            // first gate failed (upstream `continue`s the label loop)
            assert(b_first_mask_at(frozen@, s as int) == false);
            assert forall |t: int| (s as int) < t < (e as int)
                implies (!b_marked(frozen@, t)) by {
                lemma_b_marked_at(frozen@, s as int, t, e as int);
            }
            // the stopped channel needs nothing more here: the
            // fail-fast arm returned above, so fail_fast is false on
            // this path and both channel values are false
            assert(fail_fast == false);
            assert(hr == (had_in
                || (exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p))));
            assert(forall |t: int| (e as int) <= t < frozen@.len() as int
                ==> domain_buffer@[t] == frozen@[t]);
        }
        return (false, hr);
    }
    // ---- NSM trim scan from the right (uts46.rs:1400-1409)
    if e == s + 1 {
        // One-character label: the trim scan has no tail and no
        // last/middle checks run (uts46.rs:1482-1487).
        proof {
            assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int)) == -1);
            assert(!b_marked(frozen@, s as int));
            assert(!(exists |p: int| (s as int) <= p < (e as int)
                && b_marked(frozen@, p)));
            assert(hr == had_in);
            assert(hr == (had_in
                || (exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p))));
            assert(forall |t: int| (s as int) <= t < (e as int)
                ==> domain_buffer@[t] == b_final_at(frozen@, t));
            assert(forall |t: int| (e as int) <= t < frozen@.len() as int
                ==> domain_buffer@[t] == frozen@[t]);
        }
        return (false, hr);
    }
    let mut j: usize = e - 1;
    while j > s && nsm_class_read(domain_buffer[j])
        invariant
            s <= j < e,
            e <= domain_buffer.len(),
            domain_buffer@.len() == frozen@.len(),
            domain_buffer@ == pre,
            pre == old(domain_buffer)@,
            frozen@ == f0,
            (s == 0 || frozen@[(s as int) - 1] == b'.' as char),
            ((e as int) >= frozen@.len() as int
                || frozen@[(e as int)] == b'.' as char),
            forall |t: int| (s as int) <= t < (e as int)
                ==> frozen@[t] != b'.' as char,
            hr == had_in,
            forall |t: int| (j as int) + 1 <= t < (e as int)
                ==> b_nsm_at(frozen@, t),
            forall |t: int| (s as int) <= t < (e as int)
                ==> domain_buffer@[t] == frozen@[t],
        decreases j - s
    {
        proof {
            // the guard read the class as NSM at the untouched position
            assert(b_nsm_at(frozen@, (j as int)));
        }
        j = j - 1;
    }
    if j == s {
        // The whole tail is NSM: trim exhaustion; no last/middle checks
        // (uts46.rs:1482-1487).
        proof {
            assert(forall |t: int| (s as int) + 1 <= t < (e as int)
                ==> b_nsm_at(frozen@, t));
            lemma_b_last_non_nsm_all_nsm(frozen@, (s as int) + 1, (e as int));
            assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int)) == -1);
            assert forall |t: int| (s as int) < t < (e as int)
                implies (!b_marked(frozen@, t)) by {
                lemma_b_marked_at(frozen@, s as int, t, e as int);
                assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int))
                    == -1);
            }
            assert(forall |t: int| (e as int) <= t < frozen@.len() as int
                ==> domain_buffer@[t] == frozen@[t]);
            assert(forall |t: int| 0 <= t < (s as int)
                ==> domain_buffer@[t] == pre[t]);
            assert(pre == old(domain_buffer)@);
            assert(forall |t: int| 0 <= t < (s as int)
                ==> domain_buffer@[t] == old(domain_buffer)@[t]);
            assert(hr == (had_in
                || (exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p))));
        }
        return (false, hr);
    }
    let q: usize = j;
    proof {
        assert(q >= s + 1);
        assert(!b_nsm_at(frozen@, q as int));
        assert(forall |t: int| (q as int) + 1 <= t < (e as int)
            ==> b_nsm_at(frozen@, t));
        lemma_b_last_non_nsm_scan(frozen@, (s as int) + 1, q as int, e as int);
        assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int)) == q as int);
    }
    // ---- last gate (uts46.rs:1410-1417)
    let is_ltr = match first_bc {
        BcModel::L => true,
        _ => false,
    };
    proof {
        assert(is_ltr == b_is_ltr_at(frozen@, s as int));
    }
    let last_bc = adapter_bidi_class(domain_buffer[q]);
    let last_ok = if is_ltr {
        match last_bc {
            BcModel::L => true,
            BcModel::EN => true,
            _ => false,
        }
    } else {
        match last_bc {
            BcModel::R => true,
            BcModel::AL => true,
            BcModel::EN => true,
            BcModel::AN => true,
            _ => false,
        }
    };
    proof {
        assert(last_ok == (if is_ltr {
            b_last_ltr_at(frozen@, q as int)
        } else {
            b_last_rtl_at(frozen@, q as int)
        }));
    }
    if !last_ok {
        proof {
            lemma_b_marked_at(frozen@, s as int, q as int, e as int);
            assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int))
                == q as int);
            assert(b_marked(frozen@, q as int) == ({
                let ltr = b_is_ltr_at(frozen@, s as int);
                if ltr { !b_last_ltr_at(frozen@, q as int) }
                else { !b_last_rtl_at(frozen@, q as int)
                    || b_numeral_clash(frozen@, s as int, q as int) }
            }));
            assert(b_marked(frozen@, q as int));
        }
        if fail_fast {
            proof {
                assert(exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p));
            }
            return (true, had_in);
        }
        hr = true;
        domain_buffer.set(q, '\u{FFFD}');
        proof {
            let ghost pw = domain_buffer@;
            assert(domain_buffer@ == pw.update(q as int, '\u{FFFD}'));
            assert(domain_buffer@[(q as int)] == b_final_at(frozen@, q as int));
        }
    }
    // ---- middle scan over [s+1, q) (uts46.rs:1418-1468)
    let ghost last_marked_b: bool = !last_ok;
    proof {
        // entry binding for the mid-loop had join: the last gate either
        // passed (hr untouched since the scans, which bind hr == had_in)
        // or marked exactly q (the model's clash arm at q is a future
        // event, so the join pins to the direct gate fact)
        if !last_ok {
            assert(hr == true);
            assert(!last_ok && b_marked(frozen@, (q as int)));
        } else {
            assert(hr == had_in);
            assert(last_ok);
        }
    }
    if is_ltr {
        proof {
            assert(is_ltr == true);
            assert(b_is_ltr_at(frozen@, (s as int)) == true);
            assert(hr == (had_in
                || (exists |p: int| (s as int) <= p
                    < ((s as int) + 1) && b_marked(frozen@, p))
                || (!last_ok && b_marked(frozen@, (q as int)))));
        }
        let mut k: usize = s + 1;
        while k < q
            invariant
                s + 1 <= k <= q,
                q < e,
                e <= domain_buffer.len(),
                domain_buffer@.len() == frozen@.len(),
                domain_buffer@.len() == pre.len(),
                frozen@ == f0,
                pre == old(domain_buffer)@,
                forall |t: int| 0 <= t < (s as int)
                    ==> domain_buffer@[t] == pre[t],
                b_last_non_nsm(frozen@, (s as int) + 1, (e as int))
                    == (q as int),
                b_is_ltr_at(frozen@, (s as int)) == true,
                b_first_mask_at(frozen@, (s as int)) == true,
                last_ok == b_last_ltr_at(frozen@, (q as int)),
                last_marked_b == !last_ok,
                (s == 0 || frozen@[(s as int) - 1] == b'.' as char),
                ((e as int) >= frozen@.len() as int
                    || frozen@[(e as int)] == b'.' as char),
                forall |t: int| (s as int) <= t < (e as int)
                    ==> frozen@[t] != b'.' as char,
                hr == (had_in
                    || (exists |p: int| (s as int) <= p < (k as int)
                        && b_marked(frozen@, p))
                    || (!last_ok && b_marked(frozen@, (q as int)))),
                fail_fast ==> domain_buffer@ == pre,
                fail_fast ==> hr == had_in,
                (domain_buffer@[(q as int)]
                    == (if last_marked_b {
                        '\u{FFFD}'
                    } else {
                        frozen@[(q as int)]
                    })),
                forall |t: int| (s as int) <= t < (k as int)
                    ==> domain_buffer@[t] == b_final_at(frozen@, t),
                forall |t: int| (k as int) <= t < frozen@.len() as int
                    && t != (q as int)
                    ==> domain_buffer@[t] == frozen@[t],
                fail_fast ==> (forall |t: int| (s as int) + 1 <= t < (k as int)
                    ==> !b_marked(frozen@, t)),
            decreases q - k
        {
            let mid_bc = adapter_bidi_class(domain_buffer[k]);
            let mid_ok = match mid_bc {
                BcModel::L => true,
                BcModel::EN => true,
                BcModel::NSM => true,
                BcModel::MidNeutral => true,
                _ => false,
            };
            proof {
                assert(mid_ok == b_middle_ltr_at(frozen@, k as int));
            }
            if !mid_ok {
                proof {
                    lemma_b_marked_at(frozen@, s as int, k as int, e as int);
                    assert(b_last_non_nsm(
                        frozen@, (s as int) + 1, (e as int)) == q as int);
                    assert((s as int) < (k as int) && (k as int) < (q as int));
                    assert(b_is_ltr_at(frozen@, s as int));
                    assert(!b_middle_ltr_at(frozen@, k as int));
                    assert(b_marked(frozen@, k as int));
                }
                if fail_fast {
                    proof {
                        assert(exists |p: int| (s as int) <= p < (e as int)
                            && b_marked(frozen@, p));
                    }
                    return (true, had_in);
                }
                hr = true;
                domain_buffer.set(k, '\u{FFFD}');
                proof {
                    let ghost pw = domain_buffer@;
                    assert(domain_buffer@ == pw.update(k as int, '\u{FFFD}'));
                    assert(domain_buffer@[(k as int)]
                        == b_final_at(frozen@, k as int));
                }
            }
            proof {
                // pass-path bookkeeping: the scanned position is final
                if mid_ok {
                    assert(!b_marked(frozen@, k as int)) by {
                        lemma_b_marked_at(
                            frozen@, s as int, k as int, e as int);
                        assert(b_last_non_nsm(
                            frozen@, (s as int) + 1, (e as int))
                            == q as int);
                        assert((s as int) < (k as int)
                            && (k as int) < (q as int));
                        assert(b_middle_ltr_at(frozen@, k as int));
                    }
                    assert(domain_buffer@[k as int]
                        == b_final_at(frozen@, k as int));
                }
            }
            k = k + 1;
        }
        // LTR label completion bookkeeping
        proof {
            assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int))
                == q as int);
            assert forall |t: int| (q as int) + 1 <= t < (e as int)
                implies (!b_marked(frozen@, t)) by {
                lemma_b_marked_at(frozen@, s as int, t, e as int);
            }
            assert(forall |t: int| (e as int) <= t < frozen@.len() as int
                    && t != (q as int)
                ==> domain_buffer@[t] == frozen@[t]);
            lemma_b_marked_at(frozen@, s as int, q as int, e as int);
            assert(b_is_ltr_at(frozen@, s as int));
            if last_marked_b {
                assert(!b_last_ltr_at(frozen@, q as int));
                assert(b_marked(frozen@, q as int));
            } else {
                assert(b_last_ltr_at(frozen@, q as int));
                assert(!b_marked(frozen@, q as int));
            }
            assert(domain_buffer@[(q as int)]
                == b_final_at(frozen@, q as int));
            assert(forall |t: int| (q as int) < t < (e as int)
                ==> domain_buffer@[t] == frozen@[t]);
            assert(forall |t: int| (s as int) <= t < (e as int)
                ==> domain_buffer@[t] == b_final_at(frozen@, t));
            assert(forall |t: int| (e as int) <= t < frozen@.len() as int
                ==> domain_buffer@[t] == frozen@[t]);
            assert(forall |t: int| 0 <= t < (s as int)
                ==> domain_buffer@[t] == pre[t]);
            assert(pre == old(domain_buffer)@);
            assert(forall |t: int| 0 <= t < (s as int)
                ==> domain_buffer@[t] == old(domain_buffer)@[t]);
            assert(hr == (had_in
                || (exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p))));
        }
        return (false, hr);
    }
    // the RTL middle scan with the numeral state machine
    proof {
        assert(is_ltr == false);
        assert(b_is_ltr_at(frozen@, (s as int)) == false);
        assert(hr == (had_in
            || (exists |p: int| (s as int) <= p
                < ((s as int) + 1) && b_marked(frozen@, p))
            || (!last_ok && b_marked(frozen@, (q as int)))));
    }
    let mut k: usize = s + 1;
    let mut numeral_state = RtlNumeralState::Undecided;
    while k < q
        invariant
            s + 1 <= k <= q,
            q < e,
            e <= domain_buffer.len(),
            domain_buffer@.len() == frozen@.len(),
            domain_buffer@.len() == pre.len(),
            frozen@ == f0,
            pre == old(domain_buffer)@,
            forall |t: int| 0 <= t < (s as int)
                ==> domain_buffer@[t] == pre[t],
            b_last_non_nsm(frozen@, (s as int) + 1, (e as int))
                == (q as int),
            b_is_ltr_at(frozen@, (s as int)) == false,
            b_first_mask_at(frozen@, (s as int)) == true,
            last_ok == b_last_rtl_at(frozen@, (q as int)),
            last_marked_b == !last_ok,
            (s == 0 || frozen@[(s as int) - 1] == b'.' as char),
            ((e as int) >= frozen@.len() as int
                || frozen@[(e as int)] == b'.' as char),
            forall |t: int| (s as int) <= t < (e as int)
                ==> frozen@[t] != b'.' as char,
            hr == (had_in
                || (exists |p: int| (s as int) <= p < (k as int)
                    && b_marked(frozen@, p))
                || (!last_ok && b_marked(frozen@, (q as int)))),
            fail_fast ==> domain_buffer@ == pre,
            fail_fast ==> hr == had_in,
            (domain_buffer@[(q as int)]
                == (if last_marked_b {
                    '\u{FFFD}'
                } else {
                    frozen@[(q as int)]
                })),
            forall |t: int| (s as int) <= t < (k as int)
                ==> domain_buffer@[t] == b_final_at(frozen@, t),
            forall |t: int| (k as int) <= t < frozen@.len() as int
                && t != (q as int)
                ==> domain_buffer@[t] == frozen@[t],
            fail_fast ==> (forall |t: int| (s as int) + 1 <= t < (k as int)
                ==> !b_marked(frozen@, t)),
            (match numeral_state {
                RtlNumeralState::Undecided => 0int,
                RtlNumeralState::European => 1int,
                RtlNumeralState::Arabic => 2int,
            }) == b_numeral_state(frozen@, s as int, k as int),
        decreases q - k
    {
        let mid_bc = adapter_bidi_class(domain_buffer[k]);
        let mid_ok = match mid_bc {
            BcModel::R => true,
            BcModel::AL => true,
            BcModel::AN => true,
            BcModel::EN => true,
            BcModel::NSM => true,
            BcModel::MidNeutral => true,
            _ => false,
        };
        let en_here = match mid_bc {
            BcModel::EN => true,
            _ => false,
        };
        let an_here = match mid_bc {
            BcModel::AN => true,
            _ => false,
        };
        proof {
            assert(mid_ok == b_middle_rtl_at(frozen@, k as int));
            assert(en_here == b_en_at(frozen@, k as int));
            assert(an_here == b_an_at(frozen@, k as int));
        }
        if !mid_ok {
            proof {
                lemma_b_marked_at(frozen@, s as int, k as int, e as int);
                assert(b_last_non_nsm(
                    frozen@, (s as int) + 1, (e as int)) == q as int);
                assert((s as int) < (k as int) && (k as int) < (q as int));
                assert(!b_is_ltr_at(frozen@, s as int));
                assert(!b_middle_rtl_at(frozen@, k as int));
                assert(b_mid_rtl_mark(frozen@, s as int, k as int));
                assert(b_marked(frozen@, k as int));
            }
            if fail_fast {
                proof {
                    assert(exists |p: int| (s as int) <= p < (e as int)
                        && b_marked(frozen@, p));
                }
                return (true, had_in);
            }
            hr = true;
            domain_buffer.set(k, '\u{FFFD}');
            proof {
                let ghost pw = domain_buffer@;
                assert(domain_buffer@ == pw.update(k as int, '\u{FFFD}'));
                assert(domain_buffer@[(k as int)]
                    == b_final_at(frozen@, k as int));
            }
            // no state update (the upstream branch structure)
        } else {
            // state transitions with the transition-violation marks
            // (uts46.rs:1440-1466)
            match numeral_state {
                RtlNumeralState::Undecided => {
                    if en_here {
                        numeral_state = RtlNumeralState::European;
                    } else if an_here {
                        numeral_state = RtlNumeralState::Arabic;
                    }
                    if mid_ok {
                        assert(!b_marked(frozen@, k as int)) by {
                            lemma_b_marked_at(frozen@, s as int,
                                k as int, e as int);
                            assert(b_last_non_nsm(
                                frozen@, (s as int) + 1, (e as int))
                                == q as int);
                            assert(b_first_mask_at(frozen@, (s as int)));
                            assert(!b_is_ltr_at(frozen@, s as int));
                            assert((s as int) < (k as int)
                                && (k as int) < (q as int));
                            assert(b_middle_rtl_at(frozen@, k as int));
                            assert(b_numeral_state(frozen@, (s as int),
                                (k as int)) == 0);
                            assert(b_mid_rtl_mark(frozen@, s as int,
                                k as int) == false);
                        }
                        assert(domain_buffer@[k as int]
                            == b_final_at(frozen@, k as int));
                    }
                }
                RtlNumeralState::European => {
                    if an_here {
                        proof {
                            lemma_b_marked_at(
                                frozen@, s as int, k as int, e as int);
                            assert(b_last_non_nsm(
                                frozen@, (s as int) + 1, (e as int))
                                == q as int);
                            assert((s as int) < (k as int)
                                && (k as int) < (q as int));
                            assert(!b_is_ltr_at(frozen@, s as int));
                            assert(b_middle_rtl_at(frozen@, k as int));
                            assert(b_numeral_state(frozen@, (s as int),
                                (k as int)) == 1);
                            assert(b_an_at(frozen@, (k as int)));
                            assert(b_mid_rtl_mark(frozen@, s as int,
                                k as int));
                            assert(b_marked(frozen@, k as int));
                        }
                        if fail_fast {
                            proof {
                                assert(exists |p: int|
                                    (s as int) <= p < (e as int)
                                    && b_marked(frozen@, p));
                            }
                            return (true, had_in);
                        }
                        hr = true;
                        domain_buffer.set(k, '\u{FFFD}');
                        proof {
                            let ghost pw = domain_buffer@;
                            assert(domain_buffer@
                                == pw.update(k as int, '\u{FFFD}'));
                            assert(domain_buffer@[(k as int)]
                                == b_final_at(frozen@, k as int));
                        }
                    } else {
                        if mid_ok {
                            assert(!b_marked(frozen@, k as int)) by {
                                lemma_b_marked_at(frozen@, s as int,
                                    k as int, e as int);
                                assert(b_last_non_nsm(
                                    frozen@, (s as int) + 1, (e as int))
                                    == q as int);
                                assert(b_first_mask_at(frozen@, (s as int)));
                                assert(!b_is_ltr_at(frozen@, s as int));
                                assert((s as int) < (k as int)
                                    && (k as int) < (q as int));
                                assert(b_middle_rtl_at(frozen@, k as int));
                                assert(b_numeral_state(frozen@, (s as int),
                                    (k as int)) == 1);
                                assert(!(b_numeral_state(frozen@,
                                    (s as int), (k as int)) == 1
                                    && b_an_at(frozen@, k as int)));
                                assert(b_mid_rtl_mark(frozen@, s as int,
                                    k as int) == false);
                            }
                            assert(domain_buffer@[k as int]
                                == b_final_at(frozen@, k as int));
                        }
                    }
                }
                RtlNumeralState::Arabic => {
                    if en_here {
                        proof {
                            lemma_b_marked_at(
                                frozen@, s as int, k as int, e as int);
                            assert(b_last_non_nsm(
                                frozen@, (s as int) + 1, (e as int))
                                == q as int);
                            assert((s as int) < (k as int)
                                && (k as int) < (q as int));
                            assert(!b_is_ltr_at(frozen@, s as int));
                            assert(b_middle_rtl_at(frozen@, k as int));
                            assert(b_numeral_state(frozen@, (s as int),
                                (k as int)) == 2);
                            assert(b_en_at(frozen@, (k as int)));
                            assert(b_mid_rtl_mark(frozen@, s as int,
                                k as int));
                            assert(b_marked(frozen@, k as int));
                        }
                        if fail_fast {
                            proof {
                                assert(exists |p: int|
                                    (s as int) <= p < (e as int)
                                    && b_marked(frozen@, p));
                            }
                            return (true, had_in);
                        }
                        hr = true;
                        domain_buffer.set(k, '\u{FFFD}');
                        proof {
                            let ghost pw = domain_buffer@;
                            assert(domain_buffer@
                                == pw.update(k as int, '\u{FFFD}'));
                            assert(domain_buffer@[(k as int)]
                                == b_final_at(frozen@, k as int));
                        }
                    } else {
                        if mid_ok {
                            assert(!b_marked(frozen@, k as int)) by {
                                lemma_b_marked_at(frozen@, s as int,
                                    k as int, e as int);
                                assert(b_last_non_nsm(
                                    frozen@, (s as int) + 1, (e as int))
                                    == q as int);
                                assert(b_first_mask_at(frozen@, (s as int)));
                                assert(!b_is_ltr_at(frozen@, s as int));
                                assert((s as int) < (k as int)
                                    && (k as int) < (q as int));
                                assert(b_middle_rtl_at(frozen@, k as int));
                                assert(b_numeral_state(frozen@, (s as int),
                                    (k as int)) == 2);
                                assert(!(b_numeral_state(frozen@,
                                    (s as int), (k as int)) == 2
                                    && b_en_at(frozen@, k as int)));
                                assert(b_mid_rtl_mark(frozen@, s as int,
                                    k as int) == false);
                            }
                            assert(domain_buffer@[k as int]
                                == b_final_at(frozen@, k as int));
                        }
                    }
                }
            }
        }

        proof {
            // the state coding advanced per the spec fold
            let st_next = match numeral_state {
                RtlNumeralState::Undecided => 0int,
                RtlNumeralState::European => 1int,
                RtlNumeralState::Arabic => 2int,
            };
            assert(st_next
                == b_numeral_state(frozen@, s as int, (k as int) + 1)) by {
                reveal_with_fuel(b_numeral_state, 1);
            };
        }
        k = k + 1;
    }
    // ---- closing numeral clash (uts46.rs:1469-1479)
    let st_code: u8 = match numeral_state {
        RtlNumeralState::Undecided => 0,
        RtlNumeralState::European => 1,
        RtlNumeralState::Arabic => 2,
    };
    let last_an = match last_bc {
        BcModel::AN => true,
        _ => false,
    };
    let last_en = match last_bc {
        BcModel::EN => true,
        _ => false,
    };
    proof {
        assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int)) == q as int);
        assert((st_code as int)
            == b_numeral_state(frozen@, s as int, q as int));
        assert(last_an == b_an_at(frozen@, q as int));
        assert(last_en == b_en_at(frozen@, q as int));
        assert(((st_code == 1 && last_an) || (st_code == 2 && last_en))
            == b_numeral_clash(frozen@, s as int, q as int));
    }
    if (st_code == 1 && last_an) || (st_code == 2 && last_en) {
        proof {
            assert(b_numeral_clash(frozen@, s as int, q as int));
            lemma_b_marked_at(frozen@, s as int, q as int, e as int);
            assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int))
                == q as int);
            assert(!b_is_ltr_at(frozen@, s as int));
            assert(b_last_rtl_at(frozen@, q as int));
            assert(b_numeral_state(frozen@, s as int, q as int) == 1
                || b_numeral_state(frozen@, s as int, q as int) == 2);
            assert(b_marked(frozen@, q as int));
        }
        if fail_fast {
            proof {
                assert(exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p));
            }
            return (true, had_in);
        }
        hr = true;
        domain_buffer.set(q, '\u{FFFD}');
        proof {
            let ghost pw = domain_buffer@;
            assert(domain_buffer@ == pw.update(q as int, '\u{FFFD}'));
            assert(domain_buffer@[(q as int)]
                == b_final_at(frozen@, q as int));
        }
    }
    // RTL label completion bookkeeping
    proof {
        assert forall |t: int| (q as int) + 1 <= t < (e as int)
            implies (!b_marked(frozen@, t)) by {
            lemma_b_marked_at(frozen@, s as int, t, e as int);
            assert(b_last_non_nsm(frozen@, (s as int) + 1, (e as int))
                == q as int);
        }
        assert(forall |t: int| (q as int) < t < (e as int)
            ==> domain_buffer@[t] == frozen@[t]);
        lemma_b_marked_at(frozen@, s as int, q as int, e as int);
        assert(!b_is_ltr_at(frozen@, s as int));
        // the gates' outcomes pin the model value at q
        if last_marked_b {
            assert(!b_last_rtl_at(frozen@, q as int));
            assert(b_marked(frozen@, q as int));
        } else {
            assert(b_last_rtl_at(frozen@, q as int));
            if !((st_code == 1 && last_an) || (st_code == 2 && last_en)) {
                assert(!b_numeral_clash(frozen@, s as int, q as int));
                assert(!b_marked(frozen@, q as int));
            } else {
                assert(b_numeral_clash(frozen@, s as int, q as int));
                assert(b_marked(frozen@, q as int));
            }
        }
        assert(domain_buffer@[(q as int)]
            == b_final_at(frozen@, q as int));
        assert(forall |t: int| (s as int) <= t < (e as int)
            ==> domain_buffer@[t] == b_final_at(frozen@, t));
        assert(forall |t: int| (e as int) <= t < frozen@.len() as int
            ==> domain_buffer@[t] == frozen@[t]);
        assert(forall |t: int| 0 <= t < (s as int)
            ==> domain_buffer@[t] == pre[t]);
        assert(pre == old(domain_buffer)@);
        assert(forall |t: int| 0 <= t < (s as int)
            ==> domain_buffer@[t] == old(domain_buffer)@[t]);
        assert(hr == (had_in
            || (exists |p: int| (s as int) <= p < (e as int)
                && b_marked(frozen@, p))));
    }
    (false, hr)
}

/// The whole-pass tier: label iteration over the pre-pass content. The
/// per-label tier above carries the marking semantics; this loop carries
/// the label geometry (dot sweep between labels, the passthrough of
/// empty labels) and the had/join bookkeeping across labels. Upstream's
/// body writes *had_errors at every marking site; this transcription
/// carries the same bit in a local register and writes the sink once at
/// the end (observably equivalent: the pass never reads the had bit
/// internally, and the final bit is exactly entry OR mark-existence).
pub fn bidi_marking_pass(
    domain_buffer: &mut Vec<char>,
    fail_fast: bool,
    had_errors: &mut bool,
) -> (r: bool)
    ensures
        final(domain_buffer)@.len() == old(domain_buffer)@.len(),
        r == (fail_fast && b_any_marked(old(domain_buffer)@)),
        // The fail-fast channel leaves everything untouched (every
        // fail-fast site returns before any write of the pass).
        fail_fast ==> final(domain_buffer)@ == old(domain_buffer)@
            && *final(had_errors) == *old(had_errors),
        // The marking channel installs the pointwise marked content.
        !fail_fast ==> r == false
            && (forall |p: int| 0 <= p < final(domain_buffer)@.len()
                ==> final(domain_buffer)@[p] == b_final_at(old(domain_buffer)@, p))
            && (*final(had_errors)
                == (*old(had_errors) || b_any_marked(old(domain_buffer)@))),
{
    let ghost orig: Seq<char> = domain_buffer@;
    let ghost len0: int = domain_buffer@.len() as int;
    let ghost entry_had: bool = *had_errors;
    let mut had_reg: bool = *had_errors;
    // Verification-level snapshot of the pre-pass content: upstream reads
    // the pre-pass values in place (no read observes a marking); this
    // mirror holds the same values for the per-label tier below. The
    // snapshot is never mutated after this loop.
    let mut frozen: Vec<char> = Vec::new();
    let mut ci: usize = 0;
    while ci < domain_buffer.len()
        invariant
            ci <= domain_buffer.len(),
            frozen@.len() == ci as int,
            domain_buffer@ == orig,
            forall |t: int| 0 <= t < ci as int
                ==> frozen@[t] == orig[t],
        decreases domain_buffer.len() - ci
    {
        let ghost pw = frozen@;
        frozen.push(domain_buffer[ci]);
        proof {
            assert(frozen@ == pw.push(domain_buffer@[ci as int]));
        }
        ci = ci + 1;
    }
    proof {
        assert(frozen@ == orig);
    }
    let frozen_slice: &[char] = &frozen;
    proof {
        // the reborrowed slice's view is the snapshot Vec's view
        assert(frozen_slice@.len() == frozen@.len());
    }
    assert(frozen_slice.len() == frozen.len());
    let mut s: usize = 0;
    while s < domain_buffer.len()
        invariant
            s <= domain_buffer.len(),
            domain_buffer@.len() == len0,
            orig == old(domain_buffer)@,
            len0 == old(domain_buffer)@.len() as int,
            entry_had == *old(had_errors),
            (s as int == len0 || s == 0
                || orig[(s as int) - 1] == b'.' as char),
            forall |p: int| 0 <= p < (s as int)
                ==> domain_buffer@[p] == b_final_at(orig, p),
            forall |p: int| (s as int) <= p < len0
                ==> domain_buffer@[p] == orig[p],
            frozen@ == orig,
            frozen_slice@ == frozen@,
            frozen_slice.len() == frozen.len(),
            fail_fast ==> domain_buffer@ == orig,
            fail_fast ==> forall |p: int| 0 <= p < (s as int)
                ==> !b_marked(orig, p),
            fail_fast ==> had_reg == entry_had,
            had_reg == (entry_had
                || (exists |p: int| 0 <= p < (s as int)
                    && b_marked(orig, p))),
        decreases domain_buffer.len() - s
    {
        if domain_buffer[s] == b'.' as char {
            // Empty label: no checks run (the marking predicate is
            // dot-suppressed).
            proof {
                assert(orig[(s as int)] == b'.' as char);
                assert(!b_marked(orig, s as int));
            }
            s = s + 1;
            continue;
        }
        // e: the exclusive end of the current label (first dot at or after
        // s+1, or the length)
        let mut e: usize = s + 1;
        while e < domain_buffer.len() && domain_buffer[e] != b'.' as char
            invariant
                s + 1 <= e <= domain_buffer.len(),
                domain_buffer@.len() == len0,
                frozen_slice@ == frozen@,
                frozen_slice.len() == frozen.len(),
                frozen@ == orig,
                // the label sweep has not written anything
                forall |t: int| (s as int) <= t < len0
                    ==> domain_buffer@[t] == orig[t],
                forall |t: int| (s as int) + 1 <= t < (e as int)
                    ==> orig[t] != b'.' as char,
            decreases domain_buffer.len() - e
        {
            proof {
                // the guard saw a non-dot, in the untouched region
                assert(domain_buffer@[(e as int)] == orig[(e as int)]);
                assert(orig[(e as int)] != b'.' as char);
            }
            e = e + 1;
        }
        proof {
            lemma_b_dot_or_end_scan(orig, (s as int) + 1, (e as int));
            assert(b_label_end(orig, s as int) == (e as int));
        }
        proof {
            // geometry instantiations from the outer invariants for the
            // helper's requires
            assert(frozen@ == orig);
            assert(domain_buffer@.len() == frozen@.len());
            assert(frozen.len() == domain_buffer.len());
            assert(e <= domain_buffer.len());
            assert(e <= frozen.len());
            assert(s == 0 || frozen@[(s as int) - 1] == b'.' as char);
            assert((e as int) >= frozen@.len() as int
                || frozen@[(e as int)] == b'.' as char);
            assert(forall |t: int| (s as int) <= t < (e as int)
                ==> frozen@[t] != b'.' as char);
            assert(forall |t: int| (s as int)
                <= t < domain_buffer@.len() as int
                ==> domain_buffer@[t] == frozen@[t]);
        }
        let mark_res = bidi_mark_label(
            domain_buffer, frozen_slice, fail_fast, had_reg, s, e);
        if mark_res.0 {
            proof {
                // the helper's stop channel pins a label mark; whole-pass
                // existence follows
                assert(frozen@ == orig);
                assert(exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(frozen@, p));
                assert(exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(orig, p));
                assert(b_any_marked(orig));
                assert(had_reg == entry_had);
            }
            *had_errors = had_reg;
            return true;
        }
        had_reg = mark_res.1;
        // fold the helper's completed-label picture into the outer state,
        // then step over the separator dot (or stop at the length)
        proof {
            assert(domain_buffer@.len() == len0);
            assert(frozen@ == orig);
            assert(forall |t: int| (e as int) <= t < len0
                ==> domain_buffer@[t] == orig[t]);
            // the separator dot itself: never marked, and untouched by
            // the helper
            if e < domain_buffer.len() {
                assert(domain_buffer@[(e as int)] == orig[(e as int)]);
                assert(orig[(e as int)] == b'.' as char);
                assert(!b_marked(orig, (e as int))) by {
                    reveal(b_marked);
                }
                assert(domain_buffer@[(e as int)]
                    == b_final_at(orig, (e as int)));
            }
            // the completed labels region [0, e) is final
            assert(forall |p: int| 0 <= p < (e as int)
                ==> domain_buffer@[p] == b_final_at(orig, p));
            if fail_fast {
                assert(frozen@ == orig);
                assert(forall |p: int| 0 <= p < (s as int)
                    ==> !b_marked(orig, p));
                assert(!(exists |p: int| (s as int) <= p < (e as int)
                    && b_marked(orig, p)));
                assert(forall |p: int| 0 <= p < (e as int)
                    ==> !b_marked(orig, p));
                // therefore every completed position holds its original
                // value and the buffer is the pre-pass content
                assert(forall |p: int| 0 <= p < (e as int)
                    ==> b_final_at(orig, p) == orig[p]);
                assert(forall |p: int| 0 <= p < (e as int)
                    ==> domain_buffer@[p] == orig[p]);
                assert(forall |p: int| (e as int) <= p < len0
                    ==> domain_buffer@[p] == orig[p]);
                assert(domain_buffer@ == orig);
            }
            assert(had_reg == (entry_had
                || (exists |p: int| 0 <= p < (e as int)
                    && b_marked(orig, p))));
        }
        if e < domain_buffer.len() {
            s = e + 1;
        } else {
            s = e;
        }
    }
    proof {
        // Everything is processed: the pointwise final content and the
        // whole-pass had join.
        assert(s as int == len0);
        assert(forall |p: int| 0 <= p < len0
            ==> domain_buffer@[p] == b_final_at(orig, p));
        assert(b_any_marked(orig) == (exists |p: int| 0 <= p < len0
            && b_marked(orig, p)));
        if fail_fast {
            // In fail-fast the loop ran to completion only when no model
            // mark exists anywhere: the stopped channel of the helper is
            // exactly fail-fast-with-a-marking, and each completed label
            // therefore had none.
            assert(forall |p: int| 0 <= p < len0 ==> !b_marked(orig, p));
            assert(!(exists |p: int| 0 <= p < len0 && b_marked(orig, p)));
            assert(!b_any_marked(orig));
            assert(had_reg == entry_had);
        }
        assert(had_reg == (entry_had
            || (exists |p: int| 0 <= p < len0 && b_marked(orig, p))));
    }
    *had_errors = had_reg;
    false
}

// ============================================================================
// Independent proof lemmas (bit_vector-mode maintenance and induction facts)
// ============================================================================

/// The dot-scan characterization of b_dot_or_end: walking k forward with
/// no dot seen and the terminator (length, or a dot at e) pins the
/// functional result.
proof fn lemma_b_dot_or_end_scan(P: Seq<char>, k: int, e: int)
    requires
        0 <= k <= e <= P.len() as int,
        forall |t: int| k <= t < e ==> P[t] != b'.' as char,
        e >= P.len() as int || P[e] == b'.' as char,
    ensures
        b_dot_or_end(P, k) == e,
    decreases e - k
{
    if k == e {
        assert(b_dot_or_end(P, k) == k) by {
            reveal(b_dot_or_end);
        }
        assert(b_dot_or_end(P, k) == e);
    } else {
        assert(P[k] != b'.' as char);
        lemma_b_dot_or_end_scan(P, k + 1, e);
        assert(b_dot_or_end(P, k) == e) by {
            reveal(b_dot_or_end);
        }
    }
}

/// b_label_start within a dot-free label prefix: the label start of any
/// position inside [s, e) is s itself.
proof fn lemma_b_label_start_in_range(P: Seq<char>, s: int, p: int, e: int)
    requires
        0 <= s <= p < e <= P.len() as int,
        p >= s,
        (s == 0 || P[s - 1] == b'.' as char),
        forall |t: int| s <= t < p ==> P[t] != b'.' as char,
    ensures
        b_label_start(P, p) == s,
    decreases p - s
{
    if p == s {
        if s == 0 {
            assert(b_label_start(P, p) == 0) by {
                reveal(b_label_start);
            }
        } else {
            assert(b_label_start(P, p) == p) by {
                reveal(b_label_start);
            }
        }
    } else {
        assert(P[p - 1] != b'.' as char);
        lemma_b_label_start_in_range(P, s, p - 1, e);
        assert(b_label_start(P, p) == s) by {
            reveal(b_label_start);
        }
    }
}

/// The rightmost-non-NSM scan characterization: no NSM-past positions and
/// a non-NSM at q pins the recursion result.
proof fn lemma_b_last_non_nsm_scan(P: Seq<char>, lo: int, q: int, hi: int)
    requires
        lo <= q < hi <= P.len() as int,
        !b_nsm_at(P, q),
        forall |t: int| q < t < hi ==> b_nsm_at(P, t),
    ensures
        b_last_non_nsm(P, lo, hi) == q,
    decreases hi - q
{
    if hi == q + 1 {
        // hi <= lo is impossible here (q >= lo and hi == q + 1)
        assert(hi >= lo + 1);
        assert(b_last_non_nsm(P, lo, hi) == q) by {
            reveal(b_last_non_nsm);
        }
    } else {
        assert(b_nsm_at(P, hi - 1));
        lemma_b_last_non_nsm_scan(P, lo, q, hi - 1);
        assert(b_last_non_nsm(P, lo, hi) == q) by {
            reveal(b_last_non_nsm);
        }
    }
}

/// All-NSM tail: the rightmost-non-NSM scan is -1 over an entirely NSM
/// range.
proof fn lemma_b_last_non_nsm_all_nsm(P: Seq<char>, lo: int, hi: int)
    requires
        0 <= lo <= hi <= P.len() as int,
        forall |t: int| lo <= t < hi ==> b_nsm_at(P, t),
    ensures
        b_last_non_nsm(P, lo, hi) == -1,
    decreases hi - lo
{
    if hi <= lo {
        assert(b_last_non_nsm(P, lo, hi) == -1) by {
            reveal(b_last_non_nsm);
        }
    } else {
        lemma_b_last_non_nsm_all_nsm(P, lo, hi - 1);
        assert(b_last_non_nsm(P, lo, hi) == -1) by {
            reveal(b_last_non_nsm);
        }
    }
}
/// Full unfold of the positional marking predicate at a label position:
/// reduces b_marked to the label's geometry, first-gate readout, and the
/// rightmost-non-NSM scan value (the NSM/numeral subpredicates stay
/// abstract; every marking site instantiates its specific case).
proof fn lemma_b_marked_at(P: Seq<char>, s: int, t: int, e: int)
    requires
        0 <= s <= t < e <= P.len() as int,
        (s == 0 || P[s - 1] == b'.' as char),
        (e >= P.len() as int || P[e] == b'.' as char),
        forall |u: int| s <= u < e ==> P[u] != b'.' as char,
    ensures
        b_marked(P, t) == ({
            if t == s {
                !b_first_mask_at(P, t)
            } else if !b_first_mask_at(P, s) {
                false
            } else {
                let q = b_last_non_nsm(P, s + 1, e);
                if q < 0 {
                    false
                } else {
                    let ltr = b_is_ltr_at(P, s);
                    if t == q {
                        (ltr && !b_last_ltr_at(P, t))
                            || (!ltr
                                && (!b_last_rtl_at(P, t)
                                    || b_numeral_clash(P, s, q)))
                    } else {
                        s < t && t < q
                            && ((ltr && !b_middle_ltr_at(P, t))
                                || (!ltr && b_mid_rtl_mark(P, s, t)))
                    }
                }
            }
        })
{
    lemma_b_dot_or_end_scan(P, s + 1, e);
    reveal(b_label_end);
    assert(b_label_end(P, s) == e);
    if s == t {
        if s == 0 {
            assert(b_label_start(P, t) == 0) by {
                reveal(b_label_start);
            }
        } else {
            assert(b_label_start(P, t) == t) by {
                reveal(b_label_start);
            }
        }
    } else {
        lemma_b_label_start_in_range(P, s, t, e);
    }
    reveal(b_marked);
    // mirror each branch of the definition explicitly
    let q = b_last_non_nsm(P, s + 1, e);
    let ltr = b_is_ltr_at(P, s);
    if t == s {
        assert(b_marked(P, t) == !b_first_mask_at(P, t));
    } else if !b_first_mask_at(P, s) {
        assert(b_marked(P, t) == false);
    } else if q < 0 {
        assert(b_marked(P, t) == false);
    } else if t == q {
        assert(b_marked(P, t) == ((ltr && !b_last_ltr_at(P, t))
            || (!ltr
                && (!b_last_rtl_at(P, t)
                    || b_numeral_clash(P, s, q)))));
    } else {
        assert(b_marked(P, t) == (s < t && t < q
            && ((ltr && !b_middle_ltr_at(P, t))
                || (!ltr && b_mid_rtl_mark(P, s, t)))));
    }
}

/// A WHATWG decoder step consumes between one and four bytes and never
/// runs past the end of the input (each arm's length guards pin the
/// consumed width).
proof fn lemma_lossy_step_bounds(bytes: &[u8], i: int)
    requires
        0 <= i < bytes.len() as int,
    ensures
        ({
            let (rc, rn) = lossy_step(bytes, i);
            1 <= rn && rn <= 4 && i + rn <= bytes.len() as int
        }),
{
    let (rc, rn) = lossy_step(bytes, i);
    assert(rn == 1 || rn == 2 || rn == 3 || rn == 4) by {
        reveal(lossy_step);
    };
}

/// Zero has no bits set (bit_vector machine fact).
proof fn zero_bits_lemma()
    ensures
        forall |k: u8| k < 128 ==> !bit_is_set(0u128, k),
{
    assert(forall |k: u8| k < 128 ==> !bit_is_set(0u128, k)) by (bit_vector);
}

/// Setting bit b of old_bits yields new_bits: bit b becomes set and every
/// other bit is unchanged (bit_vector machine fact; the requires equation is
/// discharged reflexively at exec call sites).
proof fn set_bit_lemma(old_bits: u128, new_bits: u128, b: u8) by (bit_vector)
    requires
        b < 128,
        new_bits == old_bits | (1u128 << b),
    ensures
        bit_is_set(new_bits, b) == true,
        forall |k: u8| k < 128 && k != b ==> bit_is_set(new_bits, k) == bit_is_set(old_bits, k),
{
}

/// Bitwise OR is pointwise disjunction on bit membership.
proof fn or_bits_lemma(x: u128, y: u128, z: u128) by (bit_vector)
    requires
        z == x | y,
    ensures
        forall |k: u8| k < 128 ==> bit_is_set(z, k) == (bit_is_set(x, k) || bit_is_set(y, k)),
{
}

/// Machine-checked binding of the transcribed const literals to their spec
/// models (UPPER_CASE_MASK / GLYPHLESS_MASK / LDH_MASK; see the const notes
/// above; the consts replace const-fn initializers that verus cannot
/// verify). Visibility note: opened to `pub` for the assertion harness
/// (see LDH_MASK).
pub proof fn mask_const_lemmas() by (bit_vector)
    ensures
        forall |k: u8| k < 128 ==> bit_is_set(UPPER_CASE_MASK, k) == upper_case_pred(k),
        forall |k: u8| k < 128 ==> bit_is_set(GLYPHLESS_MASK, k) == glyphless_pred(k),
        forall |k: u8| k < 128 ==> bit_is_set(LDH_MASK, k) == ldh_pred(k),
{
}

/// Definitional step of dns_scan_ok over a dot byte.
proof fn dot_step_lemma(bytes: &[u8], lim: int, ls: int, cur: int)
    requires
        0 <= cur < lim,
        bytes[cur] == b'.',
    ensures
        dns_scan_ok(bytes, lim, ls, cur) == ((1 <= cur - ls && cur - ls <= 63) && dns_scan_ok(bytes, lim, cur + 1, cur + 1)),
{
}

/// Definitional unfold of dns_scan_ok at the base position (cur == lim).
proof fn scan_base_lemma(bytes: &[u8], lim: int, ls: int, cur: int)
    requires
        cur >= lim,
    ensures
        dns_scan_ok(bytes, lim, ls, cur) == (1 <= cur - ls && cur - ls <= 63),
{
}

/// Definitional step of dns_scan_ok over a non-dot byte.
proof fn scan_step_lemma(bytes: &[u8], lim: int, ls: int, cur: int)
    requires
        0 <= cur < lim,
        bytes[cur] != b'.',
    ensures
        dns_scan_ok(bytes, lim, ls, cur) == dns_scan_ok(bytes, lim, ls, cur + 1),
{
}

/// Definitional step of first_non_fast.
proof fn first_non_fast_step_lemma(bytes: &[u8], j: int)
    requires
        0 <= j < bytes.len(),
        is_fast_byte(bytes[j]),
    ensures
        first_non_fast(bytes, j) == first_non_fast(bytes, j + 1),
{
}

/// Definitional step of first_non_fast at a non-fast byte.
proof fn first_non_fast_at_non_fast(bytes: &[u8], j: int)
    requires
        0 <= j < bytes.len(),
        !is_fast_byte(bytes[j]),
    ensures
        first_non_fast(bytes, j) == j,
{
}

/// If every byte of [a, j) is fast, the first non-fast byte does not move
/// when the search start advances from a to j.
proof fn first_non_fast_all_fast(bytes: &[u8], a: int, j: int)
    requires
        0 <= a <= j <= bytes.len(),
        forall |p: int| a <= p < j ==> is_fast_byte(bytes[p]),
    ensures
        first_non_fast(bytes, a) == first_non_fast(bytes, j),
    decreases j - a
{
    if a < j {
        first_non_fast_all_fast(bytes, a + 1, j);
        first_non_fast_step_lemma(bytes, a);
    }
}

// ============================================================================
// ContextJ working-state lemmas (check_label's in-place pass)
// ============================================================================

/// Sequential application splits at an interior index: the traced
/// content run over [c, q) composes over the consecutive ranges
/// [c, b) and [b, q).
proof fn lemma_ctxj_apply_range_split(s0: Seq<char>, c: int, b: int, q: int)
    requires
        c <= b,
        b <= q,
    ensures
        ctxj_apply_range(s0, c, q)
            == ctxj_apply_range(ctxj_apply_range(s0, c, b), b, q)
    decreases b - c
{
    if c == b {
        assert(ctxj_apply_range(s0, c, b) == s0);
    } else {
        let s1 = if ctxj_mark_at(s0, c) { s0.update(c, '\u{FFFD}') } else { s0 };
        assert(ctxj_apply_range(s0, c, q) == ctxj_apply_range(s1, c + 1, q));
        assert(ctxj_apply_range(s0, c, b) == ctxj_apply_range(s1, c + 1, b));
        lemma_ctxj_apply_range_split(s1, c + 1, b, q);
    }
}

/// One more step of the traced content run, expressed against the
/// sequence reached after the first p steps (the loop maintenance form).
proof fn lemma_ctxj_apply_range_snoc(s0: Seq<char>, p: int)
    requires
        0 <= p,
    ensures
        ctxj_apply_range(s0, 0, p + 1)
            == (if ctxj_mark_at(ctxj_apply_range(s0, 0, p), p) {
                ctxj_apply_range(s0, 0, p).update(p, '\u{FFFD}')
            } else {
                ctxj_apply_range(s0, 0, p)
            })
{
    lemma_ctxj_apply_range_split(s0, 0, p, p + 1);
    let W = ctxj_apply_range(s0, 0, p);
    let s2 = if ctxj_mark_at(W, p) { W.update(p, '\u{FFFD}') } else { W };
    assert(ctxj_apply_range(W, p, p + 1) == ctxj_apply_range(s2, p + 1, p + 1));
    assert(ctxj_apply_range(s2, p + 1, p + 1) == s2);
}

/// Positions at or beyond the processed range keep their content.
proof fn lemma_ctxj_apply_range_index_stable(s0: Seq<char>, b: int, p: int, j: int)
    requires
        0 <= b <= p,
        p <= j,
    ensures
        ctxj_apply_range(s0, b, p)[j] == s0[j]
    decreases p - b
{
    if b == p {
        assert(ctxj_apply_range(s0, b, p) == s0);
    } else {
        let s1 = if ctxj_mark_at(s0, b) { s0.update(b, '\u{FFFD}') } else { s0 };
        assert(s1[j] == s0[j]);
        assert(ctxj_apply_range(s0, b, p) == ctxj_apply_range(s1, b + 1, p));
        lemma_ctxj_apply_range_index_stable(s1, b + 1, p, j);
    }
}

/// Length is invariant under the traced content run.
proof fn lemma_ctxj_apply_range_len(s0: Seq<char>, p: int, q: int)
    requires
        p <= q,
    ensures
        ctxj_apply_range(s0, p, q).len() == s0.len()
    decreases q - p
{
    if p == q {
        assert(ctxj_apply_range(s0, p, q) == s0);
    } else {
        let s1 = if ctxj_mark_at(s0, p) { s0.update(p, '\u{FFFD}') } else { s0 };
        assert(s1.len() == s0.len());
        assert(ctxj_apply_range(s0, p, q) == ctxj_apply_range(s1, p + 1, q));
        lemma_ctxj_apply_range_len(s1, p + 1, q);
    }
}

/// The traced marked-any composes over consecutive ranges the same way.
proof fn lemma_ctxj_any_marked_split(s0: Seq<char>, c: int, b: int, q: int)
    requires
        c <= b,
        b <= q,
    ensures
        ctxj_any_marked_range(s0, c, q)
            == (ctxj_any_marked_range(s0, c, b)
                || ctxj_any_marked_range(ctxj_apply_range(s0, c, b), b, q))
    decreases b - c
{
    if c == b {
        assert(ctxj_any_marked_range(s0, c, b) == false);
        assert(ctxj_apply_range(s0, c, b) == s0);
    } else {
        let s1 = if ctxj_mark_at(s0, c) { s0.update(c, '\u{FFFD}') } else { s0 };
        assert(ctxj_any_marked_range(s0, c, q)
            == (ctxj_mark_at(s0, c) || ctxj_any_marked_range(s1, c + 1, q)));
        assert(ctxj_any_marked_range(s0, c, b)
            == (ctxj_mark_at(s0, c) || ctxj_any_marked_range(s1, c + 1, b)));
        assert(ctxj_apply_range(s0, c, b) == ctxj_apply_range(s1, c + 1, b));
        lemma_ctxj_any_marked_split(s1, c + 1, b, q);
    }
}

/// Loop maintenance form of the traced marked-any: one more step ORs in
/// the decision at position p over the traced working sequence.
proof fn lemma_ctxj_any_marked_snoc(s0: Seq<char>, p: int)
    requires
        0 <= p,
    ensures
        ctxj_any_marked_range(s0, 0, p + 1)
            == (ctxj_any_marked_range(s0, 0, p)
                || ctxj_mark_at(ctxj_apply_range(s0, 0, p), p))
{
    lemma_ctxj_any_marked_split(s0, 0, p, p + 1);
    let W = ctxj_apply_range(s0, 0, p);
    let s2 = if ctxj_mark_at(W, p) { W.update(p, '\u{FFFD}') } else { W };
    assert(ctxj_any_marked_range(W, p, p + 1)
        == (ctxj_mark_at(W, p) || ctxj_any_marked_range(s2, p + 1, p + 1)));
    assert(ctxj_any_marked_range(s2, p + 1, p + 1) == false);
}

/// Some-result bound of first_fffd_from: any found index lies in the
/// scanned range.
proof fn lemma_first_fffd_index_bound(out: Seq<char>, j: int)
    requires
        0 <= j,
    ensures
        forall |f: int| first_fffd_from(out, j) == Option::Some(f)
            ==> (j <= f < out.len()),
    decreases out.len() - j
{
    if j >= out.len() {
    } else {
        lemma_first_fffd_index_bound(out, j + 1);
    }
}

/// Prefix fold of first_fffd_from over positions with no U+FFFD.
proof fn lemma_first_fffd_fold(out: Seq<char>, a: int, j: int)
    requires
        0 <= a <= j,
        forall |q: int| a <= q < j && q < out.len() ==> out[q] != '\u{FFFD}',
    ensures
        first_fffd_from(out, a) == first_fffd_from(out, j)
    decreases j - a
{
    if a == j {
    } else {
        assert(first_fffd_from(out, a) == first_fffd_from(out, a + 1));
        lemma_first_fffd_fold(out, a + 1, j);
    }
}

/// Characterization: the index reported by first_fffd_from has no
/// U+FFFD strictly before it in the scanned range.
proof fn lemma_first_fffd_characterize(out: Seq<char>, j: int)
    requires
        0 <= j,
    ensures
        forall |f: int| first_fffd_from(out, j) == Option::Some(f)
            ==> (j <= f < out.len()
                && out[f] == '\u{FFFD}'
                && forall |q: int| j <= q < f ==> out[q] != '\u{FFFD}'),
    decreases out.len() - j
{
    if j >= out.len() {
    } else if out[j] == '\u{FFFD}' {
        assert(first_fffd_from(out, j) == Option::Some(j));
    } else {
        assert(first_fffd_from(out, j) == first_fffd_from(out, j + 1));
        lemma_first_fffd_characterize(out, j + 1);
        match first_fffd_from(out, j + 1) {
            Option::Some(f) => {
                assert(out[f] == '\u{FFFD}');
                assert(j + 1 <= f < out.len());
                assert(forall |q: int| j + 1 <= q < f ==> out[q] != '\u{FFFD}');
                assert(forall |q: int| j <= q < f ==> out[q] != '\u{FFFD}');
            }
            Option::None => {}
        }
    }
}

/// Frontier step of the bookkeeping view: after crossing position k
/// (which holds no U+FFFD), the view is unchanged.
proof fn lemma_fffd_before_step_same(out: Seq<char>, k: int)
    requires
        0 <= k < out.len(),
        out[k] != '\u{FFFD}',
    ensures
        fffd_before(out, k + 1) == fffd_before(out, k)
{
    lemma_first_fffd_characterize(out, 0);
}

/// Frontier step of the bookkeeping view when position k does hold a
/// U+FFFD (the push continues over it in MarkErrors mode); the view is
/// true from k+1 on.
proof fn lemma_fffd_before_step(out: Seq<char>, k: int)
    requires
        0 <= k < out.len(),
        out[k] == '\u{FFFD}',
    ensures
        fffd_before(out, k + 1),
{
    lemma_first_fffd_characterize(out, 0);
    match first_fffd_from(out, 0) {
        Option::Some(f) => {
            assert(out[f] == '\u{FFFD}');
            assert(f < out.len());
            assert(forall |q: int| 0 <= q < f ==> out[q] != '\u{FFFD}');
            assert(f <= k);
            assert(f < k + 1);
        }
        Option::None => {
            lemma_first_fffd_none_implies_pure(out, 0);
            assert(first_fffd_from(out, 0) == Option::Some(k));
            assert(k < k + 1);
        }
    }
}

/// Reverse characterization of the None result: no U+FFFD in the
/// scanned range.
proof fn lemma_first_fffd_none_implies_pure(out: Seq<char>, j: int)
    requires
        0 <= j,
        first_fffd_from(out, j) == Option::None,
    ensures
        forall |q: int| j <= q < out.len() ==> out[q] != '\u{FFFD}',
    decreases out.len() - j
{
    if j >= out.len() {
    } else {
        assert(out[j] != '\u{FFFD}');
        lemma_first_fffd_none_implies_pure(out, j + 1);
    }
}

/// first_fffd_from is decided at a known first U+FFFD position.
proof fn lemma_first_fffd_known(out: Seq<char>, k: int)
    requires
        0 <= k < out.len(),
        out[k] == '\u{FFFD}',
        forall |j: int| 0 <= j < k ==> out[j] != '\u{FFFD}',
    ensures
        first_fffd_from(out, 0) == Option::Some(k)
{
    lemma_first_fffd_fold(out, 0, k);
    assert(first_fffd_from(out, k) == Option::Some(k));
}

/// first_fffd_from is None when the hold-out sequence has no U+FFFD.
proof fn lemma_first_fffd_all_pure(out: Seq<char>)
    requires
        forall |j: int| 0 <= j < out.len() ==> out[j] != '\u{FFFD}',
    ensures
        first_fffd_from(out, 0) == Option::None
{
    lemma_first_fffd_fold(out, 0, out.len() as int);
}

/// Prefix fold of first_diff_from over positions that matched.
proof fn lemma_first_diff_fold(
    out: Seq<char>,
    label: Seq<char>,
    a: int,
    j: int,
)
    requires
        0 <= a <= j,
        forall |q: int| a <= q < j && q < out.len() && q < label.len()
            ==> out[q] == label[q],
    ensures
        first_diff_from(out, label, a) == first_diff_from(out, label, j)
    decreases j - a
{
    if a == j {
    } else {
        assert(first_diff_from(out, label, a) == first_diff_from(out, label, a + 1));
        lemma_first_diff_fold(out, label, a + 1, j);
    }
}

/// first_diff_from is decided at a known first-difference position.
proof fn lemma_first_diff_known(out: Seq<char>, label: Seq<char>, k: int)
    requires
        0 <= k < out.len(),
        k < label.len(),
        out[k] != label[k],
        forall |j: int| 0 <= j < k ==> out[j] == label[j],
    ensures
        first_diff_from(out, label, 0) == Option::Some(k)
{
    lemma_first_diff_fold(out, label, 0, k);
    assert(first_diff_from(out, label, k) == Option::Some(k));
}

/// first_diff_from is None when every zipped position matched up to the
/// min of the two lengths.
proof fn lemma_first_diff_matched_prefix(
    out: Seq<char>,
    label: Seq<char>,
    j: int,
)
    requires
        0 <= j,
        j >= out.len() || j >= label.len(),
        forall |q: int| 0 <= q < j && q < out.len() && q < label.len()
            ==> out[q] == label[q],
    ensures
        first_diff_from(out, label, 0) == Option::None
{
    lemma_first_diff_fold(out, label, 0, j);
    assert(first_diff_from(out, label, j) == Option::None);
}

/// Length fact of the out-sequence model: the deny application is
/// length-preserving, so the model has the stage's length.
proof fn lemma_after_pd_output_len(label: Seq<char>, deny: u128)
    ensures
        after_pd_output(label, deny).len() == adapter_norm_valid_of(label).len(),
{
    vstd::seq::lemma_seq_new_len(
        adapter_norm_valid_of(label).len() as nat,
        |k: int| deny_apply_model(adapter_norm_valid_of(label)[k], deny),
    );
}

/// Dot-freeness of the lower-case deny application: a non-dot char
/// never maps to the separator dot (the label census of the pipeline
/// content channels consumes this).
proof fn lemma_deny_apply_model_not_dot(c: char, deny: u128)
    ensures
        deny_apply_model(c, deny) == '.'
            ==> (c == '.' && (c as u32) < 0x80
                && !bit_is_set(deny, (c as u32) as u8)),
{
    // branch unfold of the model; the non-ASCII branch returns the char
    // itself (never the dot), the denied branch returns FFFD
}

/// The after_punycode_decode push-phase output over a dot-denying list
/// is dot-free: every separator dot of the stage output is deny-mapped
/// to FFFD, so a decoded punycode label can never smuggle a label
/// separator into the buffer.
proof fn lemma_after_pd_output_not_dot(label: Seq<char>, deny: u128)
    requires
        bit_is_set(deny, b'.'),
    ensures
        forall |p: int| 0 <= p < after_pd_output(label, deny).len() as int
            ==> after_pd_output(label, deny)[p] != '.',
{
    let nv = adapter_norm_valid_of(label);
    let out = after_pd_output(label, deny);
    lemma_after_pd_output_len(label, deny);
    assert(out.len() as int == nv.len() as int);
    assert forall |p: int| #![trigger out[p]]
        0 <= p < out.len() as int
        implies out[p] != '.' by {
        if 0 <= p && p < out.len() as int {
            assert(out[p] == deny_apply_model(nv[p], deny));
            if nv[p] == '.' {
                assert((nv[p] as u32) == 0x2E);
                assert((nv[p] as u32) < 0x80);
                assert(bit_is_set(deny, (nv[p] as u32) as u8));
                assert(out[p] == '\u{FFFD}');
            }
        }
    }
}

/// The first-difference zip marking preserves dot-freeness (the one
/// marked cell becomes FFFD, everything else carries over).
proof fn lemma_after_pd_marked_not_dot(out: Seq<char>, label: Seq<char>)
    requires
        forall |p: int| 0 <= p < out.len() as int ==> out[p] != '.',
    ensures
        forall |p: int| 0 <= p < after_pd_marked(out, label).len() as int
            ==> after_pd_marked(out, label)[p] != '.',
{
    let m = after_pd_marked(out, label);
    let d = first_diff_from(out, label, 0);
    if d.is_some() {
        assert(m == out.update((d->0), '\u{FFFD}'));
        assert(m.len() as int == out.len() as int);
        assert forall |p: int| #![trigger m[p]]
            0 <= p < m.len() as int
            implies m[p] != '.' by {
            if 0 <= p && p < m.len() as int {
                if p == (d->0) {
                    assert(m[p] == '\u{FFFD}');
                }
            }
        }
    }
}

/// In-place dot-freeness preservation of a one-cell FFFD update.
proof fn lemma_update_fffd_not_dot(s: Seq<char>, p: int)
    requires
        0 <= p < s.len() as int,
        forall |q: int| 0 <= q < s.len() as int ==> s[q] != '.',
    ensures
        forall |q: int| 0 <= q < s.update(p, '\u{FFFD}').len() as int
            ==> s.update(p, '\u{FFFD}')[q] != '.',
{
    let m = s.update(p, '\u{FFFD}');
    assert(m.len() as int == s.len() as int);
    assert forall |q: int| #![trigger m[q]]
        0 <= q < m.len() as int
        implies m[q] != '.' by {
        if 0 <= q && q < m.len() as int {
            if q == p {
                assert(m[q] == '\u{FFFD}');
            }
        }
    }
}

/// The ContextJ in-place pass preserves dot-freeness over its processed
/// range (every mark writes FFFD).
proof fn lemma_ctxj_apply_range_not_dot(s: Seq<char>, p0: int, q0: int)
    requires
        0 <= p0 <= q0,
        q0 <= s.len() as int,
        forall |k: int| 0 <= k < s.len() as int ==> s[k] != '.',
    ensures
        forall |k: int|
            0 <= k < ctxj_apply_range(s, p0, q0).len() as int
            ==> ctxj_apply_range(s, p0, q0)[k] != '.',
    decreases q0 - p0
{
    if p0 < q0 {
        let s2 = if ctxj_mark_at(s, p0) {
            s.update(p0, '\u{FFFD}')
        } else {
            s
        };
        assert(s2.len() as int == s.len() as int);
        if ctxj_mark_at(s, p0) {
            lemma_update_fffd_not_dot(s, p0);
        }
        // one-step unfold of the pass at the recursion head (the
        // def-fuel does not fire by itself here)
        assert(ctxj_apply_range(s, p0, q0)
            == ctxj_apply_range(s2, p0 + 1, q0)) by {
            reveal_with_fuel(ctxj_apply_range, 1);
        }
        lemma_ctxj_apply_range_not_dot(s2, p0 + 1, q0);
    }
}

/// The MarkErrors-mode check_label content model preserves the dot
/// freedom of its input label (hyphen marks, the leading-mark mark, the
/// ContextJ marks, and the length-gate mark all write FFFD). The label
/// census of the innermost consumes this on the punycode tier arms.
proof fn lemma_check_label_marked_not_dot(
    orig: Seq<char>,
    hyphens: Hyphens,
    first_needs: bool,
    needs_ctxj: bool,
)
    requires
        forall |k: int| 0 <= k < orig.len() as int ==> orig[k] != '.',
    ensures
        ({
            let f = check_label_marked_content(
                orig, hyphens, first_needs, needs_ctxj);
            forall |k: int| 0 <= k < f.len() as int ==> f[k] != '.'
        }),
{
    let after_h = check_label_post_hyphens(orig, hyphens);
    let after_m = check_label_post_mark_check(after_h, first_needs);
    let after_j = check_label_post_ctxj(after_m, needs_ctxj);
    // hyphen stage
    if !hyphen_is_allow(hyphens) {
        assert(after_h.len() as int == orig.len() as int);
        assert forall |k: int| #![trigger after_h[k]]
            0 <= k < after_h.len() as int
            implies after_h[k] != '.' by {
            if hyphen_replaced_at(
                orig, hyphen_is_first_last(hyphens), k)
            {
                assert(after_h[k] == '\u{FFFD}');
            }
        }
    }
    // leading-mark stage
    if first_needs
        && after_h.len() >= 1
        && adapter_is_mark_of(after_h[0])
    {
        lemma_update_fffd_not_dot(after_h, 0);
    }
    assert(after_m.len() as int == after_h.len() as int);
    // ContextJ stage
    lemma_ctxj_apply_range_not_dot(
        after_m, 0, after_m.len() as int);
    // length gate
    if !all_ascii_seq(after_j)
        && after_j.len() > PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int
    {
        lemma_update_fffd_not_dot(
            after_j, PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int);
    }
}

/// From "no hyphen-position violation" to "the hyphen pass marks
/// nothing": every hyphen_replaced_at conjunct is a hyphen_check_error
/// conjunct (length-4 labels ending in "--" are covered by the
/// last-position clause of the error predicate).
proof fn lemma_hyphen_no_error_implies_content_unchanged(orig: Seq<char>, a34: bool)
    requires
        !hyphen_check_error(orig, a34),
    ensures
        forall |j: int| 0 <= j < orig.len() ==> hyphen_final_char(orig, a34, j) == orig[j],
        !hyphen_replaced_any(orig, a34),
{
    assert(!(orig.len() >= 1 && orig[0] == '-'));
    assert(!(orig.len() >= 2 && orig[orig.len() - 1] == '-'));
    assert(!(!a34 && orig.len() >= 4 && orig[2] == '-' && orig[3] == '-'));
    assert(forall |j: int| hyphen_replaced_at(orig, a34, j) ==> false);
    assert(!hyphen_replaced_any(orig, a34));
}

/// ---------------------------------------------------------------- process_innermost (uts46.rs:1092-1492)
//
// Origin: fn process_innermost (uts46.rs:1092-1492) is the label state
// machine of the pipeline: the passthrough-prefix bookkeeping, the
// per-label dispatch across the pure-ASCII path, the pre-existing-punycode
// decode branch, and the normalization mapping window with the in-label
// "xn--" rediscovery, finishing with the is_bidi scan and the CheckBidi
// post-pass. The transcription follows the batch-E four-piece economic
// route: each branch body is lifted into a helper frame (entry geometry
// and state in requires), the cross-loop facts are re-bound at every loop
// head in explicit invariants, and the error bit travels as a local
// register joined per helper (upstream's single `had_errors` local).
//
// Representation (established precedents): SmallVec<[char; 253]> and
// SmallVec<[char; 59]> become Vec<char>; SmallVec<[AlreadyAsciiLabel; 8]>
// becomes Vec<AlreadyAsciiLabel>; the fused mapping iterator
// `self.data.map_normalize(non_ascii.chars()).map(apply_ascii_deny_list_
// to_lower_cased_unicode)` is decomposed per the documented batch-E
// arrangement into the WHATWG lossy decoder (utf8_lossy_chars, no
// injection) followed by the whole-sequence P5 call plus the per-position
// deny application; the inlined CheckBidi tail pass calls the
// bidi_marking_pass extraction of batch E (the same statements lifted
// then).
//
// Boundary note (machine-checked bridge, not an assumption): the verified
// in-place tiers check_label/check_hyphens take &mut [char]. This build
// leaves the caller-side content of a `&mut v[s..t]` Range borrow
// unconstrained (the SliceIndex Mut postcondition pins final sub-slice
// content only through the callee's own ensures; out/probe/batchF-slice-
// enum-probe*.rs), while Vec::as_mut_slice has the full two-way bound
// spec `final(slice)@ == final(vec)@`. The window wrappers below route
// through that bridge: clone the window out into a fresh Vec (view ==
// the subrange), call the tier on it via as_mut_slice, write the marked
// window back per position with Vec::set.

/// Spec model of apply_ascii_deny_list_to_potentially_upper_case_ascii
/// (uts46.rs:253-267): pass-through when the deny bit is clear, folded
/// lower case for denied upper-case ASCII, U+FFFD otherwise.
pub open spec fn deny_ascii_model(b: u8, deny: u128) -> char {
    if !bit_is_set(deny, b) {
        (b as u32) as char
    } else if b >= b'A' && b <= b'Z' {
        (((b as u32) - 0x41u32) + 0x61u32) as char
    } else {
        '\u{FFFD}'
    }
}

/// Dot-freeness of the ASCII deny map: a non-dot input byte never maps
/// to the separator dot (the dot only survives undenied, and a denied
/// byte becomes FFFD or a lower-case letter). The label census of the
/// pipeline consumes this on every ASCII content channel.
proof fn lemma_deny_ascii_model_not_dot(b: u8, deny: u128)
    ensures
        deny_ascii_model(b, deny) == '.'
            ==> (b == b'.' && !bit_is_set(deny, b)),
{
    // branch unfold of the model; every other image cell differs from
    // the dot; the FFFD and the lower-case images agree by value
}

/// The mapped-append model of the ASCII deny push loop over the byte
/// range j..f: deny_ascii_model applied position by position.
pub open spec fn ascii_deny_map_range(bytes: &[u8], deny: u128, j: int, f: int) -> Seq<char> {
    Seq::new((f - j) as nat, |k: int| deny_ascii_model(bytes[j + k], deny))
}

/// The mapped-append model over the whole suffix from j.
pub open spec fn ascii_deny_map_from(bytes: &[u8], deny: u128, j: int) -> Seq<char> {
    ascii_deny_map_range(bytes, deny, j, bytes.len() as int)
}

/// Index of the first model FFFD in the mapped append at or after j
/// (None if none): the fail-fast channel of the push loop stops right
/// before the character at this index.
pub open spec fn ascii_deny_first_fffd(bytes: &[u8], deny: u128, j: int) -> Option<int>
    decreases bytes.len() - j
{
    if j >= bytes.len() as int {
        Option::None
    } else if deny_ascii_model(bytes[j], deny) == '\u{FFFD}' {
        Option::Some(j)
    } else {
        ascii_deny_first_fffd(bytes, deny, j + 1)
    }
}

/// Binding of the exec deny application to the model above (documented
/// here; established at the exec call sites). Verus note: an exec
/// function cannot be called from proof mode in this build, so the
/// binding `result == deny_ascii_model(bytes[k], deny)` is derived at
/// each exec call site from the callee ensures (three-case split on
/// bit_is_set with the upper-case arm closed by the u32 window identity
/// ((b - 0x41) + 0x61 == b + 0x20)).

/// Length preservation of the check_label MarkErrors final content: the
/// hyphen pass is a Seq::new at the original length, the leading-mark,
/// ContextJ, and length-gate stages only update in place.
proof fn lemma_check_label_marked_content_len(
    orig: Seq<char>,
    hyphens: Hyphens,
    first_needs: bool,
    needs_ctxj: bool,
)
    ensures
        check_label_marked_content(orig, hyphens, first_needs, needs_ctxj).len()
            == orig.len(),
{
    let after_h = check_label_post_hyphens(orig, hyphens);
    vstd::seq::lemma_seq_new_len(
        orig.len() as nat,
        |j: int| hyphen_final_char(orig, hyphen_is_first_last(hyphens), j),
    );
    if !hyphen_is_allow(hyphens) {
        assert(check_label_post_hyphens(orig, hyphens).len() == orig.len());
    }
    let after_m = check_label_post_mark_check(after_h, first_needs);
    vstd::seq::lemma_seq_update_len(
        after_h, 0, '\u{FFFD}');
    let after_j = check_label_post_ctxj(after_m, needs_ctxj);
    if needs_ctxj {
        lemma_ctxj_apply_range_len(after_m, 0, after_m.len() as int);
        assert(check_label_post_ctxj(after_m, true).len() == after_m.len());
    }
    vstd::seq::lemma_seq_update_len(
        after_j, PUNYCODE_ENCODE_MAX_INPUT_LENGTH as int, '\u{FFFD}');
    assert(check_label_marked_content(orig, hyphens, first_needs, needs_ctxj).len()
        == after_j.len());
    assert(after_m.len() == after_h.len());
}

/// Seq::add associativity (pointwise index assembly): used by the
/// branch frames that chain two aggregate appends.
proof fn lemma_seq_add_assoc(s1: Seq<char>, s2: Seq<char>, s3: Seq<char>)
    ensures
        (s1.add(s2)).add(s3) == s1.add(s2.add(s3)),
{
    vstd::seq::lemma_seq_add_len(s1, s2);
    vstd::seq::lemma_seq_add_len(s2, s3);
    vstd::seq::lemma_seq_add_len(s1, s2.add(s3));
    vstd::seq::lemma_seq_add_len(s1.add(s2), s3);
    let l1 = s1.len() as int;
    let l2 = s2.len() as int;
    let l3 = s3.len() as int;
    assert((s1.add(s2)).add(s3).len() == l1 + l2 + l3) by {
        vstd::seq::lemma_seq_add_len(s1.add(s2), s3);
    }
    assert(s1.add(s2.add(s3)).len() == l1 + l2 + l3);
    assert forall |q: int| #![trigger (s1.add(s2)).add(s3)[q]]
        0 <= q < l1 + l2 + l3
        implies ((s1.add(s2)).add(s3)[q] == s1.add(s2.add(s3))[q]) by {
        if q < l1 {
            vstd::seq::lemma_seq_add_index1(s1, s2, q);
            vstd::seq::lemma_seq_add_index1(s1.add(s2), s3, q);
            vstd::seq::lemma_seq_add_index1(s1, s2.add(s3), q);
        } else if q < l1 + l2 {
            let i2 = q - l1;
            vstd::seq::lemma_seq_add_index2(s1, s2, q);
            vstd::seq::lemma_seq_add_index1(s1.add(s2), s3, q);
            vstd::seq::lemma_seq_add_index2(s1, s2.add(s3), q);
            vstd::seq::lemma_seq_add_index1(s2, s3, i2);
        } else {
            let i3 = q - l1 - l2;
            vstd::seq::lemma_seq_add_index2(s1.add(s2), s3, q);
            vstd::seq::lemma_seq_add_index2(s1, s2.add(s3), q);
            vstd::seq::lemma_seq_add_index2(s2, s3, q - l1);
            assert((s2.add(s3))[l2 + i3] == s3[i3]);
        }
    }
    vstd::seq::lemma_seq_ext_equal((s1.add(s2)).add(s3), s1.add(s2.add(s3)));
}

//// Clone-out half of the window bridge: a fresh Vec holding
//// domain_buffer[start..] (entry content, view == the subrange).
fn pim_win_extract(domain_buffer: &mut Vec<char>, start: usize) -> (win: Vec<char>)
    requires
        start <= domain_buffer.len(),
    ensures
        final(domain_buffer)@ == old(domain_buffer)@,
        win@ == old(domain_buffer)@.subrange(
            start as int, old(domain_buffer)@.len() as int),
        win@.len() == old(domain_buffer)@.len() - start as int,
        forall |q: int| 0 <= q < win@.len() as int
            ==> win@[q] == old(domain_buffer)@[start as int + q],
{
    let ghost pre: Seq<char> = domain_buffer@;
    let mut w: Vec<char> = Vec::new();
    let mut i: usize = start;
    while i < domain_buffer.len()
        invariant
            start <= i <= domain_buffer.len(),
            domain_buffer@ == pre,
            w@.len() == (i - start) as int,
            forall |q: int| 0 <= q < w@.len() as int
                ==> w@[q] == pre[start as int + q],
        decreases domain_buffer.len() - i
    {
        let cv = domain_buffer[i];
        let ghost pw: Seq<char> = w@;
        w.push(cv);
        proof {
            assert(w@ == pw.push(cv));
            assert(w@[(i - start) as int] == cv);
        }
        i = i + 1;
    }
    proof {
        // length and content pinning of the window entry state
        assert(w@.len() == pre.len() - start as int);
        assert forall |q: int| #![trigger w@[q]]
            0 <= q < w@.len() as int
            implies w@[q] == pre.subrange(start as int, pre.len() as int)[q] by {
            vstd::seq::lemma_seq_subrange_index(pre, start as int, pre.len() as int, q);
            assert(pre.subrange(start as int, pre.len() as int)[q]
                == pre[start as int + q]);
        }
        assert(w@ == pre.subrange(start as int, pre.len() as int));
    }
    w
}

//// Copy-back half of the window bridge: write the window back at
//// domain_buffer[start..] position by position (Vec::set).
fn pim_win_storeback(domain_buffer: &mut Vec<char>, win: &[char], start: usize)
    requires
        start <= domain_buffer.len(),
        win@.len() == domain_buffer@.len() - start as int,
    ensures
        final(domain_buffer)@.len() == old(domain_buffer)@.len(),
        forall |p: int| 0 <= p < start as int
            ==> final(domain_buffer)@[p] == old(domain_buffer)@[p],
        forall |p: int| start as int <= p < final(domain_buffer)@.len() as int
            ==> final(domain_buffer)@[p] == win@[p - start as int],
{
    let ghost pre: Seq<char> = domain_buffer@;
    let ghost pre_len: int = domain_buffer@.len() as int;
    let mut j: usize = 0;
    while j < win.len()
        invariant
            j <= win.len(),
            win@.len() == pre_len - start as int,
            start + j <= domain_buffer.len(),
            domain_buffer@.len() == pre_len,
            forall |p: int| start as int <= p < (start + j) as int
                ==> domain_buffer@[p] == win@[p - start as int],
            forall |p: int| 0 <= p < start as int
                ==> domain_buffer@[p] == pre[p],
            forall |p: int| (start + j) as int <= p < pre_len
                ==> domain_buffer@[p] == pre[p],
        decreases win.len() - j
    {
        let wv = win[j];
        proof {
            assert(wv == win@[j as int]);
        }
        domain_buffer.set(start + j, wv);
        proof {
            let ghost pv = domain_buffer@;
            assert(domain_buffer@ == pv.update((start + j) as int, wv));
            assert(domain_buffer@[(start + j) as int] == wv);
            assert forall |p: int| start as int <= p < ((start + j) as int + 1)
                implies domain_buffer@[p] == win@[p - start as int] by {
                if p == (start + j) as int {
                    assert(win@[j as int] == wv);
                } else {
                    assert(pv[p] == win@[p - start as int]);
                }
            }
        }
        j = j + 1;
    }
}

/// Suffix subrange of an add: (a.add(m))[..a.len] == a.
proof fn lemma_add_subrange_parts(a: Seq<char>, m: Seq<char>)
    ensures
        m.len() > 0 ==> a.add(m)[a.len() as int] == m[0],
        (a.add(m)).subrange(0, a.len() as int) == a,
        (a.add(m)).subrange(a.len() as int, (a.add(m)).len() as int) == m,
{
    vstd::seq::lemma_seq_add_len(a, m);
    if m.len() > 0 {
        vstd::seq::lemma_seq_add_index2(a, m, a.len() as int);
        assert(m[0] == m[0]);
        // parts needle: pointwise for both subranges
        assert((a.add(m)).subrange(0, a.len() as int).len() == a.len());
        assert forall |q: int|
            0 <= q < a.len() as int
            implies ((a.add(m)).subrange(0, a.len() as int))[q] == a[q] by {
            vstd::seq::lemma_seq_subrange_index(
                a.add(m), 0, a.len() as int, q);
            vstd::seq::lemma_seq_add_index1(a, m, q);
        }
        vstd::seq::lemma_seq_ext_equal(
            (a.add(m)).subrange(0, a.len() as int), a);
        let al = a.len() as int;
        let tot = al + m.len() as int;
        assert(((a.add(m)).subrange(al, tot)).len() == m.len()) by {
            assert((a.add(m)).len() == tot);
        }
        assert forall |q: int|
            0 <= q < m.len() as int
            implies ((a.add(m)).subrange(al, tot))[q] == m[q] by {
            vstd::seq::lemma_seq_subrange_index(a.add(m), al, tot, q);
            vstd::seq::lemma_seq_add_index2(a, m, al + q);
        }
        vstd::seq::lemma_seq_ext_equal(
            (a.add(m)).subrange(al, tot), m);
    }
}

//// Vec-level window form of check_hyphens (the uts46.rs:1233-1240 call
//// site): the check_hyphens ensures shifted to absolute buffer positions.
fn pim_check_hyphens_dom(
    domain_buffer: &mut Vec<char>,
    start: usize,
    allow_third_fourth: bool,
    fail_fast: bool,
    had_errors: &mut bool,
) -> (r: bool)
    requires
        start <= domain_buffer.len(),
    ensures
        r == (fail_fast
            && hyphen_check_error(
                old(domain_buffer)@.subrange(
                    start as int, old(domain_buffer)@.len() as int),
                allow_third_fourth)),
        fail_fast ==> (
            final(domain_buffer)@ == old(domain_buffer)@
            && *final(had_errors) == *old(had_errors)
        ),
        !fail_fast ==> (
            r == false
            && final(domain_buffer)@.len() == old(domain_buffer)@.len()
            && *final(had_errors)
                == (*old(had_errors)
                    || hyphen_replaced_any(
                        old(domain_buffer)@.subrange(
                            start as int, old(domain_buffer)@.len() as int),
                        allow_third_fourth))
            && (forall |p: int| 0 <= p < start as int
                ==> final(domain_buffer)@.index(p) == old(domain_buffer)@.index(p))
            && (forall |p: int| start as int <= p < final(domain_buffer)@.len() as int
                ==> final(domain_buffer)@.index(p)
                    == hyphen_final_char(
                        old(domain_buffer)@.subrange(
                            start as int, old(domain_buffer)@.len() as int),
                        allow_third_fourth, p - start as int))
        ),
{
    let ghost pre: Seq<char> = domain_buffer@;
    let mut win = pim_win_extract(domain_buffer, start);
    proof {
        assert(win@ == pre.subrange(start as int, pre.len() as int));
    }
    let early = check_hyphens(win.as_mut_slice(), allow_third_fourth, fail_fast, had_errors);
    proof {
        // the as_mut_slice bridge: the callee leaves the window length
        // fixed (both of its channels), so the storeback precondition
        // still holds on the caller's Vec view
        assert(win@.len() == pre.len() - start as int);
    }
    pim_win_storeback(domain_buffer, win.as_slice(), start);
    early
}

//// Vec-level window form of check_label (the uts46.rs:1277-1284 and
//// uts46.rs:1313-1320 call sites): the check_label ensures shifted to
//// absolute buffer positions.
fn pim_check_label_dom(
    hyphens: Hyphens,
    domain_buffer: &mut Vec<char>,
    start: usize,
    fail_fast: bool,
    had_errors: &mut bool,
    first_needs_combining_mark_check: bool,
    needs_contextj_check: bool,
) -> (r: bool)
    requires
        start <= domain_buffer.len(),
    ensures
        ({
            let win = old(domain_buffer)@.subrange(
                start as int, old(domain_buffer)@.len() as int);
            r == (fail_fast
                && check_label_ff_error(win, hyphens,
                    first_needs_combining_mark_check, needs_contextj_check))
        }),
        fail_fast ==> (
            final(domain_buffer)@ == old(domain_buffer)@
            && *final(had_errors) == *old(had_errors)
        ),
        !fail_fast ==> (
            r == false
            && final(domain_buffer)@.len() == old(domain_buffer)@.len()
            && (forall |p: int| 0 <= p < start as int
                ==> final(domain_buffer)@.index(p) == old(domain_buffer)@.index(p))
            && (forall |p: int| start as int <= p < final(domain_buffer)@.len() as int
                ==> final(domain_buffer)@.index(p)
                    == check_label_marked_content(
                        old(domain_buffer)@.subrange(
                            start as int, old(domain_buffer)@.len() as int),
                        hyphens, first_needs_combining_mark_check,
                        needs_contextj_check).index(p - start as int))
            && *final(had_errors) == (*old(had_errors)
                || check_label_error_conds(
                    old(domain_buffer)@.subrange(
                        start as int, old(domain_buffer)@.len() as int),
                    hyphens, first_needs_combining_mark_check,
                    needs_contextj_check))
        ),
        // aggregate mark-errors content channel (call-site consumable
        // single equality, prefix form)
        !fail_fast ==> ({
            check_label_marked_content(
                    old(domain_buffer)@.subrange(
                        start as int, old(domain_buffer)@.len() as int),
                    hyphens, first_needs_combining_mark_check,
                    needs_contextj_check).len() as int
                == old(domain_buffer)@.len() - start as int
            && final(domain_buffer)@ == old(domain_buffer)@.subrange(
                    0, start as int).add(
                check_label_marked_content(
                    old(domain_buffer)@.subrange(
                        start as int, old(domain_buffer)@.len() as int),
                    hyphens, first_needs_combining_mark_check,
                    needs_contextj_check))
        }),
{
    let ghost pre: Seq<char> = domain_buffer@;
    let mut win = pim_win_extract(domain_buffer, start);
    proof {
        assert(win@ == pre.subrange(start as int, pre.len() as int));
    }
    let early = check_label(
        hyphens,
        win.as_mut_slice(),
        fail_fast,
        had_errors,
        first_needs_combining_mark_check,
        needs_contextj_check,
    );
    if !fail_fast {
        proof {
            lemma_check_label_marked_content_len(
                pre.subrange(start as int, pre.len() as int),
                hyphens,
                first_needs_combining_mark_check,
                needs_contextj_check,
            );
        }
    }
    proof {
        // the as_mut_slice bridge: the callee leaves the window length
        // fixed on both of its channels, so the storeback precondition
        // still holds on the caller's Vec view
        assert(win@.len() == pre.len() - start as int);
    }
    pim_win_storeback(domain_buffer, win.as_slice(), start);
    if !fail_fast {
        proof {
            // aggregate content assembly: the tier rewrote the window in
            // place to the marked content, the storeback wrote it back
            let w0 = pre.subrange(start as int, pre.len() as int);
            let clm = check_label_marked_content(
                w0, hyphens, first_needs_combining_mark_check,
                needs_contextj_check);
            // the tier's own window view, directly in this frame
            assert(win@ == clm) by {
                vstd::seq::lemma_seq_ext_equal(win@, clm);
            }
            let fin = domain_buffer@;
            let pref = pre.subrange(0, start as int);
            assert(fin.len() == pref.len() + clm.len() as int) by {
                assert(fin.len() == pre.len());
                assert(pref.len() == start as int);
            }
            assert forall |q: int| #![trigger fin[q]]
                0 <= q < fin.len() as int
                implies fin[q] == (pref.add(clm))[q] by {
                if q < pref.len() as int {
                    vstd::seq::lemma_seq_add_index1(pref, clm, q);
                    vstd::seq::lemma_seq_subrange_index(pre, 0, start as int, q);
                } else {
                    vstd::seq::lemma_seq_add_index2(pref, clm, q);
                }
            }
            vstd::seq::lemma_seq_ext_equal(fin, pref.add(clm));
        }
    }
    early
}


/// One-step unfold of the mapped-append model: extending the range by
/// one byte appends that byte's model character.
proof fn lemma_ascii_map_range_step(bytes: &[u8], deny: u128, a: int, j: int)
    requires
        a <= j,
        j < bytes.len() as int,
    ensures
        ascii_deny_map_range(bytes, deny, a, j + 1)
            == ascii_deny_map_range(bytes, deny, a, j).push(
                deny_ascii_model(bytes[j], deny)),
{
    let n = j - a;
    let f = |k: int| deny_ascii_model(bytes[a + k], deny);
    vstd::seq::lemma_seq_new_len((n + 1) as nat, f);
    vstd::seq::lemma_seq_new_len(n as nat, f);
    assert(ascii_deny_map_range(bytes, deny, a, j + 1).len() == n + 1);
    let wj = ascii_deny_map_range(bytes, deny, a, j);
    vstd::seq::lemma_seq_push_len(wj, deny_ascii_model(bytes[j], deny));
    assert(wj.push(deny_ascii_model(bytes[j], deny)).len() == n + 1);
    assert forall |q: int| #![trigger ascii_deny_map_range(bytes, deny, a, j + 1)[q]]
        0 <= q < n + 1
        implies ascii_deny_map_range(bytes, deny, a, j + 1)[q]
            == wj.push(deny_ascii_model(bytes[j], deny))[q] by {
        vstd::seq::lemma_seq_new_index((n + 1) as nat, f, q);
        vstd::seq::lemma_seq_push_index_same(wj, deny_ascii_model(bytes[j], deny), n);
        if q < n {
            vstd::seq::lemma_seq_push_index_different(
                wj, deny_ascii_model(bytes[j], deny), q);
            vstd::seq::lemma_seq_new_index(n as nat, f, q);
        } else {
            assert(q == n);
        }
    }
    vstd::seq::lemma_seq_ext_equal(
        ascii_deny_map_range(bytes, deny, a, j + 1),
        wj.push(deny_ascii_model(bytes[j], deny)));
}

/// Does the mapped append over [a, f) contain a model U+FFFD?
pub open spec fn ascii_map_has_fffd(bytes: &[u8], deny: u128, a: int, f: int) -> bool {
    exists |k: int| a <= k < f && deny_ascii_model(bytes[k], deny) == '\u{FFFD}'
}

/// The append of a push byte through the entry accumulator: pushing the
/// one-byte extension through the add wrapper (Seq::add right-append
/// fact, derived pointwise).
proof fn lemma_add_push_tail(base: Seq<char>, w: Seq<char>, c: char)
    ensures
        base.add(w).push(c) == base.add(w.push(c)),
{
    // lengths first
    assert(base.add(w).push(c).len() == base.add(w).len() + 1);
    let bw = base.add(w);
    let wp = w.push(c);
    vstd::seq::lemma_seq_add_len(base, wp);
    assert(base.add(wp).len() == base.len() + wp.len() as int);
    let _ = bw;
    assert(base.add(w).push(c).len() == base.add(w.push(c)).len());
    assert forall |q: int| #![trigger base.add(w).push(c)[q]]
        0 <= q < base.add(w).push(c).len() as int
        implies base.add(w).push(c)[q] == base.add(w.push(c))[q] by {
        let bl = base.len() as int;
        let wl = w.len() as int;
        if q < bl + wl {
            // below the pushed position: both sides agree through bw/wp
            if q < bl {
                vstd::seq::lemma_seq_add_index1(base, w, q);
                vstd::seq::lemma_seq_add_index1(base, wp, q);
                vstd::seq::lemma_seq_push_index_different(
                    base.add(w), c, q);
            } else {
                assert(w[q - bl] == wp[q - bl]) by {
                    vstd::seq::lemma_seq_push_index_different(w, c, q - bl);
                }
                vstd::seq::lemma_seq_add_index2(base, w, q);
                vstd::seq::lemma_seq_add_index2(base, wp, q);
                vstd::seq::lemma_seq_push_index_different(
                    base.add(w), c, q);
            }
        } else {
            assert(q == bl + wl);
            vstd::seq::lemma_seq_push_index_same(base.add(w), c, bl + wl);
            assert(base.add(wp)[q] == wp[wl]) by {
                vstd::seq::lemma_seq_add_index2(base, wp, q);
                vstd::seq::lemma_seq_push_index_same(w, c, wl);
            }
        }
    }
    vstd::seq::lemma_seq_ext_equal(base.add(w).push(c), base.add(w.push(c)));
}

/// First-FFFD witness walk: with no model U+FFFD in [q, j) and the model
/// U+FFFD exactly at j, ascii_deny_first_fffd(q) is Some(j).
proof fn lemma_ascii_first_fffd_witness(bytes: &[u8], deny: u128, q: int, j: int)
    requires
        q <= j,
        j < bytes.len() as int,
        forall |p: int| q <= p < j ==> deny_ascii_model(bytes[p], deny) != '\u{FFFD}',
        deny_ascii_model(bytes[j], deny) == '\u{FFFD}',
    ensures
        ascii_deny_first_fffd(bytes, deny, q) == Option::Some(j),
    decreases j - q
{
    if q == j {
        assert(ascii_deny_first_fffd(bytes, deny, q)
            == Option::Some(q));
    } else {
        lemma_ascii_first_fffd_witness(bytes, deny, q + 1, j);
        assert(deny_ascii_model(bytes[q], deny) != '\u{FFFD}');
        assert(ascii_deny_first_fffd(bytes, deny, q)
            == ascii_deny_first_fffd(bytes, deny, q + 1));
    }
}

/// No-FFFD none-arm walk: with no model U+FFFD in [q, len), the
/// first-FFFD model is None.
proof fn lemma_ascii_first_fffd_none_local(bytes: &[u8], deny: u128, q: int)
    requires
        q <= bytes.len() as int,
        forall |p: int| q <= p < bytes.len() as int
            ==> deny_ascii_model(bytes[p], deny) != '\u{FFFD}',
    ensures
        ascii_deny_first_fffd(bytes, deny, q) == Option::None,
    decreases bytes.len() - q
{
    if q < bytes.len() as int {
        assert(deny_ascii_model(bytes[q], deny) != '\u{FFFD}');
        lemma_ascii_first_fffd_none_local(bytes, deny, q + 1);
        assert(ascii_deny_first_fffd(bytes, deny, q)
            == ascii_deny_first_fffd(bytes, deny, q + 1));
    } else {
        assert(ascii_deny_first_fffd(bytes, deny, q) == Option::None);
    }
}

/// No-first-FFFD implies none-in-range: when the first-FFFD model from a is
/// None, no position of [a, f) maps to U+FFFD. Proven by strong induction on
/// the range length, unfolding the first_fffd recursion directly (the
/// None model at a with a < f unfolds to a non-FFFD byte and the None
/// model at a + 1).
proof fn lemma_ascii_fffd_none_implies_none(bytes: &[u8], deny: u128, a: int, f: int)
    requires
        a <= f,
        f <= bytes.len() as int,
        ascii_deny_first_fffd(bytes, deny, a) == Option::None,
    ensures
        !ascii_map_has_fffd(bytes, deny, a, f),
    decreases f - a
{
    if a < f {
        // the None model at a (with a in range) unfolds: byte a does not
        // map to U+FFFD, and the model is None from a + 1 onward
        assert(a < bytes.len() as int);
        assert(deny_ascii_model(bytes[a], deny) != '\u{FFFD}');
        assert(ascii_deny_first_fffd(bytes, deny, a + 1) == Option::None);
        lemma_ascii_fffd_none_implies_none(bytes, deny, a + 1, f);
        assert(!ascii_map_has_fffd(bytes, deny, a + 1, f));
        // the witness split: any U+FFFD witness in [a, f) is either a
        // (contradicted above) or in [a + 1, f) (contradicted by the IH)
        assert(!ascii_map_has_fffd(bytes, deny, a, f)) by {
            assert forall |k: int|
                #![trigger deny_ascii_model(bytes[k], deny)]
                a <= k < f
                implies deny_ascii_model(bytes[k], deny) != '\u{FFFD}' by {
                if a <= k && k < f {
                    if k == a {
                        assert(deny_ascii_model(bytes[a], deny) != '\u{FFFD}');
                    } else {
                        // the witness lands in the recurse range [a+1, f)
                        assert(!ascii_map_has_fffd(bytes, deny, a + 1, f));
                        assert(a + 1 <= k && k < f);
                    }
                }
            }
        }
    } else {
        // a == f: the range is empty, so the existential has no witness
        assert(a == f);
        assert(!ascii_map_has_fffd(bytes, deny, a, f));
    }
}

/// Position scan of the first model U+FFFD in bytes[from..]: the returned
/// index is the first position whose deny application is U+FFFD, or the
/// length. The scan carries the no-FFFD-prefix fact for the push tiers.
fn pim_first_fffd_pos(bytes: &[u8], deny: u128, from: usize) -> (pos: usize)
    requires
        from <= bytes.len(),
        forall |q: int| from as int <= q < bytes.len() as int ==> bytes[q] < 0x80,
    ensures
        from <= pos,
        pos <= bytes.len(),
        pos < bytes.len() as int
            ==> deny_ascii_model(bytes[pos as int], deny) == '\u{FFFD}',
        forall |p: int| from as int <= p < pos as int
            ==> deny_ascii_model(bytes[p], deny) != '\u{FFFD}',
        ascii_deny_first_fffd(bytes, deny, from as int)
            == (if pos < bytes.len() as int {
                Option::Some(pos as int)
            } else {
                Option::None
            }),
{
    let mut j: usize = from;
    while j < bytes.len()
        invariant
            from <= j <= bytes.len(),
            forall |q: int| from as int <= q < bytes.len() as int
                ==> bytes[q] < 0x80,
            forall |p: int| from as int <= p < j as int
                ==> deny_ascii_model(bytes[p], deny) != '\u{FFFD}',
        ensures
            // the break edge carries the firing read (the join drops
            // non-invariant path facts, so the discriminator is ensured
            // here per the loop-ensures channel)
            j < bytes.len() as int
                ==> deny_ascii_model(bytes[j as int], deny) == '\u{FFFD}',
        decreases bytes.len() - j
    {
        let bv = bytes[j];
        let mv = apply_ascii_deny_list_to_potentially_upper_case_ascii(bv, deny);
        proof {
            let m = deny_ascii_model(bytes[j as int], deny);
            assert(m == mv) by {
                if !bit_is_set(deny, bv) {
                    assert(mv as u32 == bv as u32);
                    assert(m == (bv as u32) as char);
                } else if bv >= b'A' && bv <= b'Z' {
                    assert(mv as u32 == (bv as u32) + 0x20);
                    assert(m == (((bv as u32) - 0x41u32) + 0x61u32) as char);
                    assert(((bv as u32) - 0x41u32) + 0x61u32 == (bv as u32) + 0x20);
                } else {
                    assert(m == '\u{FFFD}');
                }
            }
        }
        if mv == '\u{FFFD}' {
            proof {
                // the edge fact for the loop ensures channel
                assert(deny_ascii_model(bytes[j as int], deny) == '\u{FFFD}');
            }
            break;
        } else {
            j = j + 1;
        }
    }
    proof {
        if j < bytes.len() as int {
            lemma_ascii_first_fffd_witness(bytes, deny, from as int, j as int);
        } else {
            // no model U+FFFD anywhere in [from, len): the none-arm walk
            assert(forall |p: int| from as int <= p < bytes.len() as int
                ==> deny_ascii_model(bytes[p], deny) != '\u{FFFD}');
            lemma_ascii_first_fffd_none_local(bytes, deny, from as int);
        }
    }
    j
}

/// The per-position ASCII deny push loop (uts46.rs:1215-1222 and the
/// decode-error tail at uts46.rs:1178-1191): appends
/// apply_ascii_deny_list_to_potentially_upper_case_ascii(bytes[k], deny)
/// for k from `from` onward, with the U+FFFD fail-fast cut (the offending
/// character is not appended) and the saw-a-FFFD error channel. Return
/// channels: ret.0 == fired, ret.1 == saw a model U+FFFD in the scanned
/// range (false on the fired channel).
fn pim_ascii_deny_push(
    domain_buffer: &mut Vec<char>,
    bytes: &[u8],
    from: usize,
    deny: u128,
    fail_fast: bool,
) -> (ret: (bool, bool))
    requires
        from <= bytes.len(),
        forall |q: int| from as int <= q < bytes.len() as int
            ==> bytes[q] < 0x80,
        // the appended range is a tail split item region: no separator
        // byte inside (the E-CEN census channel below)
        forall |q: int| from as int <= q < bytes.len() as int
            ==> bytes[q] != b'.',
    ensures
        // fired fires only in fail-fast mode, with the first model FFFD
        // existing and the clean-cut prefix appended
        ret.0 ==> (fail_fast
            && ({
                let f0 = ascii_deny_first_fffd(bytes, deny, from as int);
                f0.is_some()
                    && final(domain_buffer)@
                        == old(domain_buffer)@.add(ascii_deny_map_range(
                            bytes, deny, from as int, (f0->0)))
            })),
        // the converse: in fail-fast mode the first model FFFD always
        // fires the cut (the saw channel of the clean completion is
        // false exactly because the scan never met an FFFD)
        fail_fast && ascii_deny_first_fffd(bytes, deny, from as int).is_some()
            ==> ret.0,
        // clean channel: the full mapped suffix appended
        !ret.0 ==> final(domain_buffer)@
            == old(domain_buffer)@.add(ascii_deny_map_from(bytes, deny, from as int)),
        // prefix preservation (both channels)
        final(domain_buffer)@.len() >= old(domain_buffer)@.len(),
        forall |p: int| 0 <= p < old(domain_buffer)@.len() as int
            ==> final(domain_buffer)@[p] == old(domain_buffer)@[p],
        // the saw channel binds to the model (clean channel only; the
        // fired channel never pushes a U+FFFD)
        !ret.0 ==> ret.1 == ascii_map_has_fffd(
            bytes, deny, from as int, bytes.len() as int),
        ret.0 ==> ret.1 == false,
        !ret.0 ==> final(domain_buffer)@.len()
            == old(domain_buffer)@.len() + (bytes.len() - from) as int,
        ret.0 ==> final(domain_buffer)@.len()
            == old(domain_buffer)@.len()
                + (ascii_deny_first_fffd(bytes, deny, from as int)->0
                    - from as int),
        // the label census of the sink walk (E-CEN feed): the appended
        // block is the deny model image of a dot-free byte range, hence
        // dot-free, so the census grows by at most one (the
        // empty-entry first-label allowance)
        !ret.0 ==> lab_count(final(domain_buffer)@)
            <= lab_count(old(domain_buffer)@)
                + (if old(domain_buffer)@.len() == 0 { 1int } else { 0int }),
{
    let ghost base: Seq<char> = domain_buffer@;
    let f = pim_first_fffd_pos(bytes, deny, from);
    let lim: usize = if fail_fast { f } else { bytes.len() };
    let mut j: usize = from;
    while j < lim
        invariant
            from <= j <= lim,
            lim <= bytes.len(),
            forall |q: int| from as int <= q < bytes.len() as int
                ==> bytes[q] < 0x80,
            domain_buffer@ == base
                .add(ascii_deny_map_range(bytes, deny, from as int, j as int)),
        decreases lim - j
    {
        let bv = bytes[j];
        let cv = apply_ascii_deny_list_to_potentially_upper_case_ascii(bv, deny);
        proof {
            let m = deny_ascii_model(bytes[j as int], deny);
            assert(m == cv) by {
                if !bit_is_set(deny, bv) {
                    assert(cv as u32 == bv as u32);
                    assert(m == (bv as u32) as char);
                } else if bv >= b'A' && bv <= b'Z' {
                    assert(cv as u32 == (bv as u32) + 0x20);
                    assert(m == (((bv as u32) - 0x41u32) + 0x61u32) as char);
                    assert(((bv as u32) - 0x41u32) + 0x61u32 == (bv as u32) + 0x20);
                } else {
                    assert(m == '\u{FFFD}');
                }
            }
            assert(cv == deny_ascii_model(bytes[j as int], deny));
        }
        proof {
            lemma_ascii_map_range_step(bytes, deny, from as int, j as int);
        }
        let ghost pre_push: Seq<char> = domain_buffer@;
        domain_buffer.push(cv);
        proof {
            assert(domain_buffer@ == pre_push.push(cv));
            assert(pre_push == base
                .add(ascii_deny_map_range(bytes, deny, from as int, j as int)));
            let wj = ascii_deny_map_range(bytes, deny, from as int, j as int);
            assert(wj.push(cv) == ascii_deny_map_range(
                bytes, deny, from as int, j as int + 1));
            lemma_add_push_tail(base, wj, cv);
            assert(base.add(wj).push(cv) == base.add(wj.push(cv)));
            assert(domain_buffer@ == base
                .add(ascii_deny_map_range(
                    bytes, deny, from as int, j as int + 1)));
        }
        j = j + 1;
    }
    proof {
        vstd::seq::lemma_seq_add_len(base, ascii_deny_map_range(
            bytes, deny, from as int, j as int));
    }
    if fail_fast && f < bytes.len() {
        // fired channel: the cut prefix appended, no FFFD pushed
        (true, false)
    } else {
        // clean channel: saw reflects the scan result over the full
        // suffix (the mark-errors FFFD characters themselves being
        // appended above); the appended block is the dot-free deny
        // model image, so the census grew by at most the
        // empty-entry allowance
        proof {
            let blk = ascii_deny_map_from(bytes, deny, from as int);
            lemma_ascii_map_range_not_dot(
                bytes, deny, from as int, bytes.len() as int);
            lemma_lab_count_append_dotfree(base, blk);
            assert(final(domain_buffer)@ == base.add(blk));
            assert(base.add(blk) == old(domain_buffer)@.add(
                ascii_deny_map_from(bytes, deny, from as int)));
        }
        (false, f < bytes.len())
    }
}


/// Decoded-content model of the label_buffer at uts46.rs:1156-1159: the
/// decode_bytes_internal view of the punycode core (the decode model
/// lower-cased to chars position by position). Empty when the decode
/// model rejects the core.
pub open spec fn pim_pw_decode_chars(core: Seq<u8>) -> Seq<char> {
    match punycode_v::decode_model(core) {
        Option::None => Seq::empty(),
        Option::Some(codes) => Seq::new(
            codes.len() as nat,
            |k: int| ((punycode_v::lower_ascii_letter(codes[k])) as u32) as char,
        ),
    }
}

/// The after_punycode_decode error condition over a decoded label.
pub open spec fn after_pd_err(label: Seq<char>, deny: u128) -> bool {
    let out = after_pd_output(label, deny);
    first_fffd_from(out, 0).is_some() || first_diff_from(out, label, 0).is_some()
}

/// Pointwise prefix equality assembles into the aggregate subrange
/// equality (the tag prefix channel of the pipeline tiers).
proof fn lemma_pointwise_prefix_eq<'a>(
    s: Seq<AlreadyAsciiLabel<'a>>,
    t: Seq<AlreadyAsciiLabel<'a>>,
)
    requires
        t.len() as int <= s.len() as int,
        forall |i: int| 0 <= i < t.len() as int
            ==> s.index(i) == t.index(i),
    ensures
        s.subrange(0, t.len() as int) == t,
{
    assert(s.subrange(0, t.len() as int).len() == t.len()) by {}
    assert forall |i: int|
        #![trigger s.subrange(0, t.len() as int)[i]]
        0 <= i < t.len() as int
        implies s.subrange(0, t.len() as int)[i] == t[i] by {
        vstd::seq::lemma_seq_subrange_index(s, 0, t.len() as int, i);
        if 0 <= i && i < t.len() as int {
            assert(s.index(i) == t.index(i));
        }
    }
    vstd::seq::lemma_seq_ext_equal(
        s.subrange(0, t.len() as int), t);
}

/// Pointwise prefix preservation plus an Other-filled extension
/// assembles into the aggregate add form (the window tag channel).
proof fn lemma_pointwise_extend_eq<'a>(
    s: Seq<AlreadyAsciiLabel<'a>>,
    t: Seq<AlreadyAsciiLabel<'a>>,
)
    requires
        t.len() as int <= s.len() as int,
        forall |i: int| 0 <= i < t.len() as int
            ==> s.index(i) == t.index(i),
        forall |i: int| t.len() as int <= i < s.len() as int
            ==> s.index(i) == AlreadyAsciiLabel::Other,
    ensures
        s == t.add(Seq::new((s.len() - t.len()) as nat,
            |k: int| AlreadyAsciiLabel::Other)),
{
    let block = Seq::new((s.len() - t.len()) as nat,
        |k: int| AlreadyAsciiLabel::Other);
    vstd::seq::lemma_seq_add_len(t, block);
    vstd::seq::lemma_seq_new_len(block.len() as nat,
        |k: int| AlreadyAsciiLabel::Other);
    assert(t.add(block).len() == s.len());
    assert forall |i: int| #![trigger t.add(block)[i]]
        0 <= i < s.len() as int
        implies t.add(block)[i] == s.index(i) by {
        if 0 <= i && i < s.len() as int {
            if i < t.len() as int {
                vstd::seq::lemma_seq_add_index1(t, block, i);
            } else {
                vstd::seq::lemma_seq_add_index2(t, block, i);
                vstd::seq::lemma_seq_new_index(
                    block.len() as nat, |k: int| AlreadyAsciiLabel::Other,
                    i - t.len() as int);
            }
        }
    }
    vstd::seq::lemma_seq_ext_equal(s, t.add(block));
}

//// Branch: the pure-ASCII label with a punycode prefix in valid form
//// (uts46.rs:1141-1198): the pre-existing-punycode decode tier. The
//// label is not empty, pure ASCII, "xn--"-prefixed (case-insensitive),
//// does not end in a hyphen, and its core passes the DoS length gate.
//// The helper consumes the closed assets decode_bytes_internal,
//// after_punycode_decode, and the check_label window wrapper; on both
//// decode outcomes it pushes exactly one MixedCasePunycode tag. Return
//// channels: ret.0 == fired, ret.1 == had_out, ret.2 == handled (always
//// true under the requires).
fn pim_label_ascii_punycode<'a>(
    deny: u128,
    deny_dot: u128,
    hyphens: Hyphens,
    fail_fast: bool,
    domain_buffer: &mut Vec<char>,
    tags: &mut Vec<AlreadyAsciiLabel<'a>>,
    had_in: bool,
    label: &'a [u8],
) -> (ret: (bool, bool, bool))
    requires
        label.len() >= 4,
        label.len() - 4 <= PUNYCODE_DECODE_MAX_INPUT_LENGTH,
        forall |i: int| 0 <= i < label.len() ==> label[i] < 0x80,
        // the label is a tail split item: no separator byte inside
        // (the E-CEN census channels of the tier and of its deny push)
        forall |i: int| 0 <= i < label.len() ==> label[i] != b'.',
        spec_has_punycode_prefix(label),
        // the deny-dot image fact (the census channel of the decode arm)
        bit_is_set(deny_dot, b'.'),
        label[label.len() - 1] != b'-',
    ensures
        ret.0 ==> fail_fast,
        ret.2,
        // one tag on every non-fired arm (both decode outcomes)
        !ret.0 ==> final(tags)@
            == old(tags)@.push(AlreadyAsciiLabel::MixedCasePunycode(label)),
        // tags untouched on the fired arm
        ret.0 ==> final(tags)@ == old(tags)@,
        // the tag content below the entry is preserved position by
        // position on every arm (the tier only appends)
        final(tags)@.subrange(0, old(tags)@.len() as int)
            == old(tags)@,
        final(tags)@.len() >= old(tags)@.len(),
        // the buffer never shrinks below the entry content, and the
        // entry content is preserved position by position
        final(domain_buffer)@.len() >= old(domain_buffer)@.len(),
        forall |p: int| 0 <= p < old(domain_buffer)@.len() as int
            ==> final(domain_buffer)@.index(p) == old(domain_buffer)@.index(p),
        // exact branch content, split on the decode model of the core:
        // the decode-Ok arm composes after_punycode_decode's push/zip
        // marking (after_pd_marked) with the check_label marking pass
        ({
            let core = label@.subrange(4, label.len() as int);
            let lbv = pim_pw_decode_chars(core);
            let outv = after_pd_output(lbv, deny_dot);
            let marked0 = after_pd_marked(outv, lbv);
            let fctx = check_label_marked_content(marked0, hyphens, true, true);
            // the content package holds in mark-errors mode (in the
            // fail-fast clean run the caller discards the buffer on the
            // ValidityError channel, and the had register stays put)
            (!ret.0) && !fail_fast
                && punycode_v::decode_model(core).is_some() ==>
                (final(domain_buffer)@
                    == old(domain_buffer)@.add(fctx)
                    && ret.1 == (had_in
                        || after_pd_err(lbv, deny_dot)
                        || check_label_error_conds(marked0, hyphens, true, true))
                    && final(domain_buffer)@.len()
                        == old(domain_buffer)@.len()
                            + fctx.len() as int)
        }),
        ({
            let core = label@.subrange(4, label.len() as int);
            (!ret.0) && punycode_v::decode_model(core).is_none() ==>
                (final(domain_buffer)@
                    == old(domain_buffer)@.add(Seq::empty().push('\u{FFFD}').add(
                        ascii_deny_map_range(
                            label, deny, 1, label.len() as int)))
                    && ret.1 == true
                    && final(domain_buffer)@.len()
                        == old(domain_buffer)@.len() + label.len() as int)
        }),
        // the fired arm fires with had untouched, and on every non-fired
        // arm in fail-fast mode the had register also passes through
        // unchanged (fail-fast never marks)
        ret.0 ==> ret.1 == had_in,
        fail_fast ==> ret.1 == had_in,
{
    let ghost base: Seq<char> = domain_buffer@;
    let ghost t_entry: Seq<AlreadyAsciiLabel<'a>> = tags@;
    let cls: usize = domain_buffer.len();
    // the punycode core sub-slice
    let core: &[u8] = &label[4..];
    proof {
        // slice-of-slice view fact (the indexing spec of this build)
        assert(core@.len() == label.len() - 4);
        assert(core@ == label@.subrange(4, label.len() as int));
    }
    let dec = punycode_v::decode_bytes_internal(core);
    match dec {
        Option::Some(label_buffer) => {
            proof {
                let codes = punycode_v::decode_model(core@)->0;
                let lbm = pim_pw_decode_chars(core@);
                assert(label_buffer@.len() == codes.len() as int);
                assert(lbm.len() == codes.len() as int);
                assert forall |q: int| #![trigger label_buffer@[q]]
                    0 <= q < label_buffer@.len() as int
                    implies label_buffer@[q] == lbm[q] by {
                    let mch = ((punycode_v::lower_ascii_letter(codes[q])) as u32) as char;
                    assert(((label_buffer@[q]) as int)
                        == punycode_v::lower_ascii_letter(codes[q]));
                    assert(mch as int == punycode_v::lower_ascii_letter(codes[q]));
                    assert(lbm[q] == mch);
                }
                assert(label_buffer@ == lbm);
            }
            let mut had_reg: bool = had_in;
            let early1 = after_punycode_decode(
                domain_buffer, cls, &label_buffer, deny_dot, fail_fast,
                &mut had_reg,
            );
            // snapshot of the post-push/zip state (the ghost carries the
            // aggregate content fact across the wrapper call below)
            let ghost m1: Seq<char> = domain_buffer@;
            if early1 {
                // fired via after_punycode_decode (fail-fast only): had
                // unchanged, prefix untouched, length grew by the clean
                // prefix or the full output
                proof {
                    assert(fail_fast);
                    assert(had_reg == had_in);
                    let outz = after_pd_output(label_buffer@, deny_dot);
                    lemma_after_pd_output_len(label_buffer@, deny_dot);
                    if first_fffd_from(outz, 0).is_some() {
                        // the found index is in range, so the clean
                        // prefix length is nonnegative
                        lemma_first_fffd_index_bound(outz, 0);
                        assert(pd_prefix_len(outz) >= 0);
                        assert(domain_buffer@.len()
                            == base.len() + pd_prefix_len(outz));
                    } else {
                        assert(pd_prefix_len(outz) == outz.len() as int);
                        assert(domain_buffer@.len()
                            == base.len() + outz.len() as int);
                    }
                }
                proof {
                    lemma_pointwise_prefix_eq(tags@, t_entry);
                }
                return (true, had_reg, true);
            }
            // pre-wrapper view snapshot (names the callee-old value
            // for the assembly below)
            let ghost pre_w: Seq<char> = domain_buffer@;
            let early2 = pim_check_label_dom(
                hyphens, domain_buffer, cls, fail_fast,
                &mut had_reg, true, true,
            );
            if early2 {
                // fired via the check_label window (fail-fast only): the
                // wrapper leaves the buffer content untouched and the
                // had register unchanged
                proof {
                    assert(fail_fast);
                    assert(domain_buffer@.len() >= base.len());
                }
                proof {
                    lemma_pointwise_prefix_eq(tags@, t_entry);
                }
                return (true, had_reg, true);
            }
            if !fail_fast {
            proof {
                // good-path assembly over the aggregate channels: the
                // snapshot m1 is the zip-marked append of the decoded
                // label (after_punycode_decode's mark-errors aggregate
                // channel); the wrapper then rewrote m1's window in
                // place to the marked content. The assembly is a
                // mark-errors-mode fact (the branch content package
                // guards on !fail_fast; the fail-fast clean run needs
                // no content channel here).
                assert(m1 == base.add(after_pd_marked(
                    after_pd_output(label_buffer@, deny_dot),
                    label_buffer@)));
                let lbm = pim_pw_decode_chars(core@);
                let outv = after_pd_output(lbm, deny_dot);
                let marked0 = after_pd_marked(outv, lbm);
                assert(label_buffer@ == lbm);
                assert(after_pd_output(label_buffer@, deny_dot) == outv);
                assert(after_pd_marked(
                    after_pd_output(label_buffer@, deny_dot),
                    label_buffer@) == marked0);
                assert(m1 == base.add(marked0)) by {
                    // one rewrite step of the equality above
                }
                lemma_add_subrange_parts(base, marked0);
                assert(cls as int == base.len() as int);
                let fin = domain_buffer@;
                assert(pre_w == m1);
                // the wrapper's aggregate channel, instantiated at its
                // call with the entry view pre_w
                assert(fin == pre_w.subrange(0, cls as int).add(
                    check_label_marked_content(
                        pre_w.subrange(cls as int, pre_w.len() as int),
                        hyphens, true, true)));
                assert(m1.subrange(0, cls as int) == base);
                assert(m1.subrange(cls as int, m1.len() as int)
                    == marked0);
                let fctx = check_label_marked_content(
                    marked0, hyphens, true, true);
                assert(fin == base.add(fctx));
            }
            }
            tags.push(AlreadyAsciiLabel::MixedCasePunycode(label));
            proof {
                assert forall |i: int| #![trigger tags@.index(i)]
                    0 <= i < t_entry.len() as int
                    implies tags@.index(i) == t_entry.index(i) by {
                    if 0 <= i && i < t_entry.len() as int {
                        assert(tags@ == t_entry.push(
                            AlreadyAsciiLabel::MixedCasePunycode(label)));
                        vstd::seq::lemma_seq_push_index_different(
                            t_entry,
                            AlreadyAsciiLabel::MixedCasePunycode(label),
                            i);
                    }
                }
                lemma_pointwise_prefix_eq(tags@, t_entry);
            }
            (false, had_reg, true)
        }
        Option::None => {

            if fail_fast {
                proof {
                    lemma_pointwise_prefix_eq(tags@, t_entry);
                }
                return (true, had_in, true);
            }
            let ghost pre_err: Seq<char> = domain_buffer@;
            domain_buffer.push('\u{FFFD}');
            proof {
                assert(domain_buffer@ == pre_err.push('\u{FFFD}'));
            }
            proof {
                // the deny push require: the mapped range is dot-free
                assert forall |q: int| 1 <= q < label.len() as int
                    ==> label[q] != b'.' by {
                }
            }
            let push_res = pim_ascii_deny_push(
                domain_buffer, label, 1, deny, false,
            );
            proof {
                assert(push_res.0 == false);
                assert(push_res.1 == ascii_map_has_fffd(
                    label, deny, 1, label.len() as int));
                assert(pre_err == base);
                let mapped = ascii_deny_map_range(
                    label, deny, 1, label.len() as int);
                // base.push(FFFD).add(mapped) == base.add([FFFD] ++
                // mapped): the add/push index laws (the [FFFD] cell and
                // the mapped tail)
                let lhs = base.push('\u{FFFD}').add(mapped);
                let rhs = base.add(Seq::empty().push('\u{FFFD}').add(mapped));
                assert(domain_buffer@ == lhs);
                vstd::seq::lemma_seq_push_len(Seq::empty(), '\u{FFFD}');
                vstd::seq::lemma_seq_add_len(Seq::empty().push('\u{FFFD}'), mapped);
                vstd::seq::lemma_seq_add_len(base.push('\u{FFFD}'), mapped);
                vstd::seq::lemma_seq_add_len(base, Seq::empty().push('\u{FFFD}').add(mapped));
                assert(lhs.len() == rhs.len());
                let single = Seq::empty().push('\u{FFFD}');
                assert(single.len() == 1);
                assert(single[0] == '\u{FFFD}') by {
                    // the push lemma indexes the pre-push length
                    vstd::seq::lemma_seq_push_index_same(
                        Seq::empty(), '\u{FFFD}', 0);
                }
                vstd::seq::lemma_seq_add_len(single, mapped);
                assert forall |q: int| #![trigger single.add(mapped)[q]]
                    0 <= q < (1 + mapped.len() as int)
                    implies single.add(mapped)[q]
                        == (if q == 0 {
                            '\u{FFFD}'
                        } else {
                            mapped[q - 1]
                        }) by {
                    if q == 0 {
                        vstd::seq::lemma_seq_add_index1(single, mapped, 0);
                    } else {
                        vstd::seq::lemma_seq_add_index2(single, mapped, q);
                    }
                }
                assert forall |q: int| #![trigger lhs[q]]
                    0 <= q < lhs.len() as int
                    implies lhs[q] == rhs[q] by {
                    let bl = base.len() as int;
                    if q < bl {
                        vstd::seq::lemma_seq_add_index1(base.push('\u{FFFD}'), mapped, q);
                        vstd::seq::lemma_seq_add_index1(base, single.add(mapped), q);
                    } else if q == bl {
                        // the FFFD cell
                        vstd::seq::lemma_seq_add_index1(base.push('\u{FFFD}'), mapped, q);
                        vstd::seq::lemma_seq_push_index_same(base, '\u{FFFD}', bl);
                        vstd::seq::lemma_seq_add_index2(base, single.add(mapped), q);
                    } else {
                        // the mapped tail
                        vstd::seq::lemma_seq_add_index2(base.push('\u{FFFD}'), mapped, q);
                        vstd::seq::lemma_seq_add_index2(base, single.add(mapped), q);
                    }
                }
                vstd::seq::lemma_seq_ext_equal(lhs, rhs);
                assert(lhs == rhs);
                assert(domain_buffer@ == rhs);
            }
            tags.push(AlreadyAsciiLabel::MixedCasePunycode(label));
            proof {
                assert forall |i: int| #![trigger tags@.index(i)]
                    0 <= i < t_entry.len() as int
                    implies tags@.index(i) == t_entry.index(i) by {
                    if 0 <= i && i < t_entry.len() as int {
                        assert(tags@ == t_entry.push(
                            AlreadyAsciiLabel::MixedCasePunycode(label)));
                        vstd::seq::lemma_seq_push_index_different(
                            t_entry,
                            AlreadyAsciiLabel::MixedCasePunycode(label),
                            i);
                    }
                }
                lemma_pointwise_prefix_eq(tags@, t_entry);
            }
            (false, true, true)
        }
    }
}


/// Dot census of the mapped feed up to (excluding) index j.
pub open spec fn dots_up_to(m: Seq<char>, j: int) -> int
    decreases j
{
    if j <= 0 {
        0
    } else {
        dots_up_to(m, j - 1) + (if m[j - 1] == '.' { 1int } else { 0int })
    }
}

/// Dot census of a byte feed up to (excluding) index j.
pub open spec fn dots8_up_to(m: Seq<u8>, j: int) -> int
    decreases j
{
    if j <= 0 {
        0
    } else {
        dots8_up_to(m, j - 1) + (if m[j - 1] == b'.' { 1int } else { 0int })
    }
}

/// The byte dot census never exceeds the scanned range.
proof fn lemma_dots8_up_bound(m: Seq<u8>, j: int)
    requires
        0 <= j,
    ensures
        dots8_up_to(m, j) <= j,
    decreases j
{
    if j > 0 {
        lemma_dots8_up_bound(m, j - 1);
    }
}

/// Nonnegativity of the byte dot census.
proof fn lemma_dots8_up_nonneg(m: Seq<u8>, j: int)
    requires
        0 <= j,
    ensures
        0 <= dots8_up_to(m, j),
    decreases j
{
    if j > 0 {
        lemma_dots8_up_nonneg(m, j - 1);
    }
}

/// Nonnegativity of the dot census.
proof fn lemma_dots_up_nonneg(m: Seq<char>, j: int)
    requires
        0 <= j,
    ensures
        0 <= dots_up_to(m, j),
    decreases j
{
    if j > 0 {
        lemma_dots_up_nonneg(m, j - 1);
    }
}

/// One-step unfold of the dot census.
proof fn lemma_dots_step(m: Seq<char>, j: int)
    requires
        0 <= j < m.len() as int,
    ensures
        dots_up_to(m, j + 1)
            == dots_up_to(m, j) + (if m[j] == '.' { 1int } else { 0int }),
{
    // definitional at j + 1
}

/// Index transfer of the dot census over a push: below the pushed index
/// the pushed sequence counts exactly the original's dots.
proof fn lemma_dots_up_push(m: Seq<char>, c: char, j: int)
    requires
        0 <= j <= m.len() as int,
    ensures
        dots_up_to(m.push(c), j) == dots_up_to(m, j),
    decreases j
{
    if j > 0 {
        lemma_dots_up_push(m, c, j - 1);
        vstd::seq::lemma_seq_push_index_different(
            m, c, j - 1);
    }
}

/// The label census of the '.'-split of a character sequence: the
/// empty sequence has no split items, and a nonempty sequence always
/// has exactly one more split item than separator dots. (The sink
/// walk of Uts46::process consumes the assembled buffer through this
/// split; the walk never runs on an empty buffer -- the pristine
/// passthrough return precedes it -- so the equation below is the
/// indexing basis of the per-label tag read.)
pub open spec fn lab_count(s: Seq<char>) -> int
{
    if s.len() == 0 {
        0
    } else {
        1 + dots_up_to(s, s.len() as int)
    }
}

/// Pushing a non-dot character keeps the census (and starts the first
/// label of an empty sequence).
proof fn lemma_lab_count_push_char(s: Seq<char>, c: char)
    requires
        c != '.',
    ensures
        lab_count(s.push(c))
            == (if s.len() == 0 { 1 } else { lab_count(s) }),
{
    lemma_dots_up_push(s, c, s.len() as int);
    lemma_dots_step(s.push(c), s.len() as int);
}

/// Pushing a separator dot adds one split item.
proof fn lemma_lab_count_push_dot(s: Seq<char>)
    ensures
        lab_count(s.push('.'))
            == (if s.len() == 0 { 2 } else { lab_count(s) + 1 }),
{
    lemma_dots_up_push(s, '.', s.len() as int);
    lemma_dots_step(s.push('.'), s.len() as int);
}

/// Dot-census index transfer over the append seam: up to j the appended
/// sequence counts the prefix's dots.
proof fn lemma_dots_up_add_prefix(s: Seq<char>, blk: Seq<char>, j: int)
    requires
        0 <= j <= s.len() as int,
    ensures
        dots_up_to(s.add(blk), j) == dots_up_to(s, j),
    decreases j
{
    if j > 0 {
        lemma_dots_up_add_prefix(s, blk, j - 1);
        vstd::seq::lemma_seq_add_index1(s, blk, j - 1);
    }
}

/// Dot-census total additivity of the append seam.
proof fn lemma_dots_add_total(s: Seq<char>, blk: Seq<char>)
    requires
        0 <= blk.len() as int,
    ensures
        dots_up_to(s.add(blk), s.len() as int + blk.len() as int)
            == dots_up_to(s, s.len() as int) + dots_up_to(blk, blk.len() as int),
    decreases blk.len() as int
{
    lemma_dots_up_add_prefix(s, blk, s.len() as int);
    if blk.len() > 0 {
        let pre = blk.subrange(0, blk.len() as int - 1);
        let last = blk[blk.len() as int - 1];
        lemma_seq_tail_split(blk);
        lemma_seq_add_push_assoc(s, pre, last);
        lemma_dots_add_total(s, pre);
        vstd::seq::lemma_seq_add_len(s, pre);
        // the folded fact packages: through the association the top of
        // the extended sequence is the pushed last char, the block's own
        // census unfolds at its last index, and the block-prefix census
        // transfers below the pushed index
        dots_up_to_step_seq_push(s.add(pre), last);
        lemma_dots_up_push(pre, last, pre.len() as int);
        lemma_dots_step(blk, blk.len() as int - 1);
    }
}

/// One-step census unfold at the final index of a push.
proof fn dots_up_to_step_seq_push(m: Seq<char>, c: char)
    ensures
        dots_up_to(m.push(c), m.len() as int + 1)
            == dots_up_to(m, m.len() as int) + (if c == '.' { 1int } else { 0int }),
{
    lemma_dots_up_push(m, c, m.len() as int);
    lemma_dots_step(m.push(c), m.len() as int);
}

/// A sequence with a final element splits as prefix-block plus one
/// push (the block-last association).
proof fn lemma_seq_tail_split(blk: Seq<char>)
    requires
        blk.len() > 0,
    ensures
        blk == blk.subrange(0, blk.len() as int - 1)
            .push(blk[blk.len() as int - 1]),
{
    let pre = blk.subrange(0, blk.len() as int - 1);
    assert(pre.len() as int == blk.len() as int - 1);
    assert((pre.push(blk[blk.len() as int - 1])).len() as int
        == blk.len() as int) by {
        vstd::seq::lemma_seq_push_len(pre, blk[blk.len() as int - 1]);
    }
    assert forall |q: int|
        #![trigger (pre.push(blk[blk.len() as int - 1]))[q]]
        0 <= q < blk.len() as int
        implies (pre.push(blk[blk.len() as int - 1]))[q] == blk[q] by {
        if 0 <= q && q < blk.len() as int {
            if q < blk.len() as int - 1 {
                vstd::seq::lemma_seq_push_index_different(
                    pre, blk[blk.len() as int - 1], q);
                vstd::seq::lemma_seq_subrange_index(
                    blk, 0, blk.len() as int - 1, q);
            } else {
                assert(q == blk.len() as int - 1);
                vstd::seq::lemma_seq_push_index_same(
                    pre, blk[blk.len() as int - 1], q);
            }
        }
    }
    vstd::seq::lemma_seq_ext_equal(
        pre.push(blk[blk.len() as int - 1]), blk);
}

/// Append-then-push association: appending a block that ends with a
/// known final char equals appending the prefix block and then pushing
/// that char.
proof fn lemma_seq_add_push_assoc(s: Seq<char>, pre: Seq<char>, c: char)
    ensures
        s.add(pre.push(c)) == (s.add(pre)).push(c),
{
    assert(s.add(pre.push(c)).len() as int
        == s.len() as int + pre.len() as int + 1) by {
        vstd::seq::lemma_seq_add_len(s, pre.push(c));
        vstd::seq::lemma_seq_push_len(pre, c);
    }
    assert(((s.add(pre)).push(c)).len() as int
        == s.len() as int + pre.len() as int + 1) by {
        vstd::seq::lemma_seq_add_len(s, pre);
        vstd::seq::lemma_seq_push_len(s.add(pre), c);
    }
    assert forall |q: int|
        #![trigger ((s.add(pre)).push(c))[q]]
        0 <= q < s.len() as int + pre.len() as int + 1
        implies ((s.add(pre)).push(c))[q] == (s.add(pre.push(c)))[q] by {
        if 0 <= q && q < s.len() as int + pre.len() as int + 1 {
            if q < s.len() as int + pre.len() as int {
                vstd::seq::lemma_seq_push_index_different(
                    s.add(pre), c, q);
                if q < s.len() as int {
                    vstd::seq::lemma_seq_add_index1(s, pre, q);
                    vstd::seq::lemma_seq_add_index1(s, pre.push(c), q);
                } else {
                    vstd::seq::lemma_seq_add_index2(s, pre, q);
                    vstd::seq::lemma_seq_add_index2(s, pre.push(c), q);
                }
            } else {
                assert(q == s.len() as int + pre.len() as int);
                vstd::seq::lemma_seq_push_index_same(s.add(pre), c, q);
                vstd::seq::lemma_seq_add_index2(s, pre.push(c), q);
                vstd::seq::lemma_seq_push_index_same(pre, c, pre.len() as int);
            }
        }
    }
    vstd::seq::lemma_seq_ext_equal(
        (s.add(pre)).push(c), s.add(pre.push(c)));
}

/// Append form of the label census: appending a dot-free block keeps
/// the census of a nonempty prefix (the block extends its last label)
/// and starts exactly the first label of an empty prefix.
proof fn lemma_lab_count_add_block(s: Seq<char>, blk: Seq<char>)
    requires
        forall |q: int| 0 <= q < blk.len() as int ==> blk[q] != '.',
    ensures
        lab_count(s.add(blk))
            == (if s.len() == 0 {
                    (if blk.len() == 0 { 0 } else { 1 })
                } else {
                    lab_count(s)
                }),
{
    if s.len() == 0 {
        // empty add: the block itself; the dot-free block is one label
        if blk.len() > 0 {
            assert(s.add(blk) == blk) by {
                vstd::seq::lemma_seq_add_len(s, blk);
                assert forall |q: int|
                    #![trigger (s.add(blk))[q]]
                    0 <= q < blk.len() as int
                    implies (s.add(blk))[q] == blk[q] by {
                    if 0 <= q && q < blk.len() as int {
                        vstd::seq::lemma_seq_add_index2(s, blk, q);
                    }
                }
                vstd::seq::lemma_seq_ext_equal(s.add(blk), blk);
            }
            assert(dots_up_to(s.add(blk), (s.add(blk)).len() as int)
                == dots_up_to(blk, blk.len() as int));
            assert(dots_up_to(blk, blk.len() as int) == 0) by {
                lemma_dots_up_none(blk, blk.len() as int);
            }
            assert(lab_count(s.add(blk)) == 1) by {
                assert(lab_count(blk) == 1);
            }
        }
    } else {
        lemma_dots_add_total(s, blk);
        assert(dots_up_to(s.add(blk), s.len() as int + blk.len() as int)
            == dots_up_to(s, s.len() as int)
                + dots_up_to(blk, blk.len() as int));
        assert(s.add(blk).len() as int
            == s.len() as int + blk.len() as int) by {
            vstd::seq::lemma_seq_add_len(s, blk);
        }
        assert(dots_up_to(blk, blk.len() as int) == 0) by {
            lemma_dots_up_none(blk, blk.len() as int);
        }
    }
}

/// A dot-free sequence has a zero dot census.
proof fn lemma_dots_up_none(m: Seq<char>, j: int)
    requires
        0 <= j <= m.len() as int,
        forall |q: int| 0 <= q < j ==> m[q] != '.',
    ensures
        dots_up_to(m, j) == 0,
    decreases j
{
    if j > 0 {
        lemma_dots_up_none(m, j - 1);
    }
}

// ---------------------------------------------------------------- the label census of the sink walk (E-CEN feed)
//
// The sink write walk of Uts46::process pairs the i-th '.'-split item of
// the assembled buffer with the i-th tag cell of already_punycode
// (upstream reads the tag vector through a per-label iterator whose
// unwrap is justified by the equal-counts invariant). The verified feed
// for that read is the label census lab_count(buf) <= tags.len(): E-CEN
// on process_innermost/process_inner, consumed by the process walk. The
// per-helper channels are stated in the sharp form (growth bounded by
// the appended dot-free content, with the one-label allowance only on an
// empty entry buffer), which is what lets the per-site step close
// without mid-iteration side conditions.

/// Monotonicity of the dot census in the scanned range end.
proof fn lemma_dots_up_mono_j(m: Seq<char>, a: int, b: int)
    requires
        0 <= a <= b <= m.len() as int,
    ensures
        dots_up_to(m, a) <= dots_up_to(m, b),
    decreases b - a
{
    if a < b {
        lemma_dots_up_mono_j(m, a, b - 1);
        if m[b - 1] == '.' {
            assert(dots_up_to(m, b) == dots_up_to(m, b - 1) + 1) by {
                lemma_dots_step(m, b - 1);
            }
        } else {
            assert(dots_up_to(m, b) == dots_up_to(m, b - 1)) by {
                lemma_dots_step(m, b - 1);
            }
        }
    }
}

/// Index transfer of the dot census over a prefix subrange.
proof fn lemma_dots_up_subrange_prefix(s: Seq<char>, k: int, j: int)
    requires
        0 <= j <= k <= s.len() as int,
    ensures
        dots_up_to(s.subrange(0, k), j) == dots_up_to(s, j),
    decreases j
{
    if j > 0 {
        lemma_dots_up_subrange_prefix(s, k, j - 1);
        vstd::seq::lemma_seq_subrange_index(s, 0, k, j - 1);
    }
}

/// Split form of the dot census over a subrange cut.
proof fn lemma_dots_up_split(s: Seq<char>, k: int)
    requires
        0 <= k <= s.len() as int,
    ensures
        dots_up_to(s, s.len() as int)
            == dots_up_to(s, k)
                + dots_up_to(s.subrange(k, s.len() as int),
                    s.len() as int - k),
{
    let pre = s.subrange(0, k);
    let suf = s.subrange(k, s.len() as int);
    assert(s == pre.add(suf)) by {
        vstd::seq::lemma_seq_subrange_len(s, 0, k);
        vstd::seq::lemma_seq_subrange_len(s, k, s.len() as int);
        vstd::seq::lemma_seq_add_len(pre, suf);
        assert(pre.add(suf).len() as int == s.len() as int);
        assert forall |q: int| #![trigger pre.add(suf)[q]]
            0 <= q < s.len() as int implies pre.add(suf)[q] == s[q] by {
            if 0 <= q && q < s.len() as int {
                if q < k {
                    vstd::seq::lemma_seq_add_index1(pre, suf, q);
                    vstd::seq::lemma_seq_subrange_index(s, 0, k, q);
                } else {
                    vstd::seq::lemma_seq_add_index2(pre, suf, q);
                    vstd::seq::lemma_seq_subrange_index(
                        s, k, s.len() as int, q - k);
                }
            }
        }
        vstd::seq::lemma_seq_ext_equal(pre.add(suf), s);
    }
    lemma_dots_up_subrange_prefix(s, k, k);
    lemma_dots_add_total(pre, suf);
    vstd::seq::lemma_seq_subrange_len(s, 0, k);
    vstd::seq::lemma_seq_subrange_len(s, k, s.len() as int);
    assert(pre.len() as int == k);
    assert(suf.len() as int == s.len() as int - k);
    assert(dots_up_to(s, s.len() as int)
        == dots_up_to(pre.add(suf), s.len() as int));
}

/// Split form of the dot census at an arbitrary range end.
proof fn lemma_dots_up_split_end(s: Seq<char>, k: int, e: int)
    requires
        0 <= k <= e <= s.len() as int,
    ensures
        dots_up_to(s, e)
            == dots_up_to(s, k)
                + dots_up_to(s.subrange(k, s.len() as int), e - k),
    decreases e - k
{
    if k < e {
        lemma_dots_up_split_end(s, k, e - 1);
        lemma_dots_step(s, e - 1);
        vstd::seq::lemma_seq_subrange_len(s, k, s.len() as int);
        assert(s.subrange(k, s.len() as int)[e - 1 - k] == s[e - 1]) by {
            vstd::seq::lemma_seq_subrange_index(
                s, k, s.len() as int, e - 1 - k);
        }
        assert(dots_up_to(s.subrange(k, s.len() as int), e - k)
            == dots_up_to(s.subrange(k, s.len() as int), e - 1 - k)
                + (if s.subrange(k, s.len() as int)[e - 1 - k] == '.' {
                    1int
                } else {
                    0int
                })) by {
            lemma_dots_step(s.subrange(k, s.len() as int), e - 1 - k);
        }
    }
}

/// Appending a dot-free block grows the label census by at most one
/// (the block extends the last label; on an empty buffer it starts the
/// single first label).
proof fn lemma_lab_count_append_dotfree(s: Seq<char>, x: Seq<char>)
    requires
        forall |q: int| 0 <= q < x.len() as int ==> x[q] != '.',
    ensures
        lab_count(s.add(x))
            <= lab_count(s) + (if s.len() == 0 { 1int } else { 0int }),
{
    lemma_lab_count_add_block(s, x);
    assert(lab_count(s.add(x))
        == (if s.len() == 0 {
                (if x.len() == 0 { 0 } else { 1 })
            } else {
                lab_count(s)
            }));
    if s.len() == 0 {
        assert(lab_count(s) == 0);
    }
}

/// The census of a buffer truncated to a prefix is at most the census
/// of the whole buffer.
proof fn lemma_lab_count_shrink_to_prefix(s: Seq<char>, k: int)
    requires
        0 <= k <= s.len() as int,
    ensures
        lab_count(s.subrange(0, k)) <= lab_count(s),
{
    if s.len() == 0 {
        vstd::seq::lemma_seq_subrange_len(s, 0, k);
        assert(s.subrange(0, k).len() as int == 0);
        assert(lab_count(s.subrange(0, k)) == 0);
        assert(lab_count(s) == 0);
    } else {
        assert(lab_count(s) == 1 + dots_up_to(s, s.len() as int));
        lemma_dots_up_split(s, k);
        assert(s.subrange(0, k).len() as int == k) by {
            vstd::seq::lemma_seq_subrange_len(s, 0, k);
        }
        lemma_dots_up_mono_j(s, k, s.len() as int);
        if k == 0 {
            assert(s.subrange(0, k).len() as int == 0);
            assert(lab_count(s.subrange(0, k)) == 0);
        } else {
            assert(lab_count(s.subrange(0, k))
                == 1 + dots_up_to(s.subrange(0, k), k));
            lemma_dots_up_subrange_prefix(s, k, k);
        }
    }
}

/// Pointwise dot-subset transfer: a sequence whose dots sit on dots of
/// an equal-length other carries a no-larger dot census.
proof fn lemma_dots_up_le_pointwise(a: Seq<char>, b: Seq<char>)
    requires
        a.len() == b.len(),
        forall |p: int| 0 <= p < a.len() as int
            ==> (a[p] == '.' ==> b[p] == '.'),
    ensures
        dots_up_to(a, a.len() as int) <= dots_up_to(b, b.len() as int),
    decreases a.len() as int
{
    if a.len() as int > 0 {
        let la = a.subrange(0, a.len() as int - 1);
        let lb = b.subrange(0, b.len() as int - 1);
        assert(la.len() == lb.len()) by {
            vstd::seq::lemma_seq_subrange_len(a, 0, a.len() as int - 1);
            vstd::seq::lemma_seq_subrange_len(b, 0, b.len() as int - 1);
        }
        assert forall |p: int| #![trigger la[p]]
            0 <= p < la.len() as int
            implies (la[p] == '.' ==> lb[p] == '.') by {
            vstd::seq::lemma_seq_subrange_index(a, 0, a.len() as int - 1, p);
            vstd::seq::lemma_seq_subrange_index(b, 0, b.len() as int - 1, p);
        }
        lemma_dots_up_le_pointwise(la, lb);
        lemma_dots_up_subrange_prefix(a, a.len() as int - 1,
            a.len() as int - 1);
        lemma_dots_up_subrange_prefix(b, b.len() as int - 1,
            b.len() as int - 1);
        assert(dots_up_to(a, a.len() as int)
            == dots_up_to(a, a.len() as int - 1)
                + (if a[a.len() as int - 1] == '.' { 1int } else { 0int })) by {
            lemma_dots_step(a, a.len() as int - 1);
        }
        assert(dots_up_to(b, b.len() as int)
            == dots_up_to(b, b.len() as int - 1)
                + (if b[b.len() as int - 1] == '.' { 1int } else { 0int })) by {
            lemma_dots_step(b, b.len() as int - 1);
        }
        assert(a[a.len() as int - 1] == '.'
            ==> b[b.len() as int - 1] == '.');
    }
}

/// The dot-free model image of an ASCII deny push over a dot-free byte
/// range (the appended block of the pure-ASCII tier and of the punycode
/// tier's decode-failure arm).
proof fn lemma_ascii_map_range_not_dot(
    bytes: &[u8],
    deny: u128,
    j0: int,
    j1: int,
)
    requires
        0 <= j0 <= j1 <= bytes.len() as int,
        forall |q: int| j0 <= q < j1 ==> bytes[q] != b'.',
    ensures
        forall |q: int|
            #![trigger ascii_deny_map_range(bytes, deny, j0, j1)[q]]
            0 <= q < ascii_deny_map_range(bytes, deny, j0, j1).len() as int
            ==> ascii_deny_map_range(bytes, deny, j0, j1)[q] != '.',
{
    assert(ascii_deny_map_range(bytes, deny, j0, j1).len() as int
        == j1 - j0);
    assert forall |q: int|
        #![trigger ascii_deny_map_range(bytes, deny, j0, j1)[q]]
        0 <= q < j1 - j0
        implies ascii_deny_map_range(bytes, deny, j0, j1)[q] != '.' by {
        vstd::seq::lemma_seq_new_index((j1 - j0) as nat,
            |k: int| deny_ascii_model(bytes[j0 + k], deny), q);
        assert(bytes[j0 + q] != b'.');
        lemma_deny_ascii_model_not_dot(bytes[j0 + q], deny);
    }
}

/// The sharp dot-free append bound (the shared workhorse of the helper
/// census channels).
proof fn lemma_lab_count_add_dotfree_sharp(s: Seq<char>, blk: Seq<char>)
    requires
        forall |q: int| 0 <= q < blk.len() as int ==> blk[q] != '.',
    ensures
        lab_count(s.add(blk))
            <= lab_count(s) + (if s.len() == 0 { 1int } else { 0int }),
{
    lemma_lab_count_add_block(s, blk);
    if s.len() == 0 {
        assert(lab_count(s) == 0);
        assert(lab_count(s.add(blk)) == (if blk.len() == 0 { 0int } else { 1int }));
    } else {
        assert(lab_count(s.add(blk)) == lab_count(s));
    }
}

/// bit_is_set on the dot bit of an OR-ed DOT_MASK (the deny-dot image
/// fact consumed by every mapped-content census channel).
proof fn lemma_bit_is_set_dot_or(deny: u128)
    ensures
        bit_is_set(deny | DOT_MASK, b'.'),
{
    assert(((deny | DOT_MASK) & (1u128 << b'.')) != 0) by (bit_vector);
    assert((((deny | DOT_MASK) & (1u128 << b'.')) != 0)
        == bit_is_set(deny | DOT_MASK, b'.')) by (bit_vector);
}

/// The per-site census step of the process_innermost label loop (the
/// C1 re-establishment): the head census, the at-most-one separator
/// push, the site's own sharp census channel over the site's tag
/// growth, and the tag count close the invariant at the next back-edge.
/// The empty-head + separator case leans on the C2 companion invariant
/// (the tag rope is never empty past the prefix).
proof fn lemma_census_site_restore(
    h: Seq<char>,
    t_h: int,
    b1: Seq<char>,
    f: Seq<char>,
    d_site: int,
    t_f: int,
    sep_pushed: bool,
)
    requires
        lab_count(h) <= t_h,
        !sep_pushed ==> b1 == h,
        sep_pushed ==> (b1 == h.push('.')
            && lab_count(b1) == lab_count(h)
                + (if h.len() == 0 { 2int } else { 1int })),
        (sep_pushed && h.len() == 0) ==> t_h >= 1,
        lab_count(f) <= lab_count(b1) + d_site
            + (if b1.len() == 0 { 1int } else { 0int }),
        t_f >= t_h + d_site + 1,
    ensures
        lab_count(f) <= t_f,
{
    lemma_lab_count_push_dot(h);
    if sep_pushed {
        assert(h.push('.').len() as int == h.len() as int + 1) by {
            vstd::seq::lemma_seq_push_len(h, '.');
        }
        if h.len() == 0 {
            assert(t_h >= 1);
            assert(lab_count(b1) == 2);
            assert(b1.len() as int == 1);
            assert(b1.len() != 0);
            assert(lab_count(f) <= 2 + d_site);
            assert(lab_count(f) <= t_h + d_site + 1);
        } else {
            assert(lab_count(b1) == lab_count(h) + 1);
            assert(lab_count(f) <= lab_count(h) + 1 + d_site);
            assert(lab_count(f) <= t_h + d_site + 1);
        }
    } else {
        assert(b1 == h);
        if b1.len() == 0 {
            assert(lab_count(f) <= d_site + 1);
            assert(lab_count(f) <= t_h + d_site + 1);
        } else {
            assert(lab_count(f) <= lab_count(h) + d_site);
            assert(lab_count(f) <= t_h + d_site);
        }
    }
}

//// Mapping-window label event (uts46.rs:1262-1360, the xn--
//// rediscovery and the per-sub-label validity pass). The caller
//// maintains: cls is the current sub-label window start, everything
//// below cls is call-stable. The event possibly rewrites the window
//// in place (marking), or rediscover-decodes the window when it
//// spells "xn--...", and then runs the check_label window pass.
//// Return channels: ret.0 == fired (only in fail-fast mode, with the
//// had register unchanged), ret.1 == had_out.
fn pim_map_event(
    deny_dot: u128,
    hyphens: Hyphens,
    fail_fast: bool,
    domain_buffer: &mut Vec<char>,
    had_in: bool,
    cls: usize,
    first_needs_combining_mark_check: bool,
    needs_contextj_check: bool,
) -> (ret: (bool, bool))
    requires
        cls <= domain_buffer.len(),
        // the deny-dot image fact (the census channel of the decode
        // re-emission)
        bit_is_set(deny_dot, b'.'),
        // the window [cls..len) is dot-free at entry (the caller's
        // content since the label start: mapped non-dots and dot-free
        // re-emissions; the separator dots sit below cls)
        forall |q: int| cls as int <= q < old(domain_buffer)@.len() as int
            ==> old(domain_buffer)@.index(q) != '.',
    ensures
        ret.0 ==> fail_fast,
        // the had register is preserved through every fail-fast channel
        // (fire or clean pass): fail-fast never marks
        fail_fast ==> ret.1 == had_in,
        // everything below the window is call-stable; the buffer never
        // shrinks below the window start (the rediscovery decode
        // legitimately truncates the window content back to cls and
        // re-emits, so the event length can be below the entry length)
        final(domain_buffer)@.len() >= cls as int,
        forall |p: int| 0 <= p < cls as int
            ==> final(domain_buffer)@[p] == old(domain_buffer)@[p],
        // the window stays dot-free on the clean channel (the caller's
        // per-window census invariant)
        !ret.0 ==> forall |q: int| cls as int <= q
            < final(domain_buffer)@.len() as int
            ==> final(domain_buffer)@.index(q) != '.',
{
    let ghost entry: Seq<char> = domain_buffer@;
    let mut had_reg: bool = had_in;
    let mut fncc: bool = first_needs_combining_mark_check;
    let mut ncc: bool = needs_contextj_check;
    /* Origin Rust (uts46.rs:1262-1268):
     *     if domain_buffer[current_label_start..]
     *         .starts_with(&['x', 'n', '-', '-'])
     *     {
     *         let mut punycode_precondition_failed = false;
     */
    if domain_buffer.len() - cls >= 4
        && domain_buffer[cls] == 'x'
        && domain_buffer[cls + 1] == 'n'
        && domain_buffer[cls + 2] == '-'
        && domain_buffer[cls + 3] == '-'
    {
        let ghost entry_marks_len: int = domain_buffer@.len() as int;
        let mut pcf: bool = false;
        // ---- non-ASCII marking within the window (uts46.rs:1268-1276).
        // The marking pass replaces every non-ASCII char of the window
        // with U+FFFD; the pass is a no-op iff the window is pristine
        // ASCII (which also carries the decode precondition below).
        // U+FFFD itself is non-ASCII: it only appears here as the mark.
        let mut t: usize = cls + 4;
        while t < domain_buffer.len()
            invariant
                cls + 4 <= t <= domain_buffer.len(),
                domain_buffer@.len() == entry_marks_len,
                entry == old(domain_buffer)@,
                fail_fast ==> had_reg == had_in,
                // fail-fast writes nothing anywhere (the fire returns
                // before any set)
                fail_fast ==> domain_buffer@ == entry,
                forall |p: int| 0 <= p < cls as int + 4
                    ==> domain_buffer@.index(p) == entry.index(p),
                // the pass-reality equation: pcf is true iff some
                // position of [cls+4, t) was non-ASCII in the entry
                // content (the marks replaced exactly those positions)
                pcf == (exists |q: int| (cls + 4) as int <= q < t as int
                    && ((entry.index(q)) as u32) >= 0x80),
                forall |q: int| (cls + 4) as int <= q < t as int
                    ==> (domain_buffer@.index(q) == entry.index(q)
                        || (domain_buffer@.index(q) == '\u{FFFD}'
                            && ((entry.index(q)) as u32) >= 0x80)),
                forall |q: int| t as int <= q < domain_buffer@.len() as int
                    ==> domain_buffer@.index(q)
                        == entry.index(q),
                // the window stays dot-free (the entry window is
                // dot-free; the marks write U+FFFD at non-dot positions)
                forall |q: int| cls as int <= q
                    < domain_buffer@.len() as int
                    ==> domain_buffer@.index(q) != '.',
            decreases domain_buffer.len() - t
        {
            let ch = domain_buffer[t as usize];
            proof {
                // the unmodified-tail invariant pins the read value
                assert(ch == entry.index(t as int));
            }
            if (ch as u32) >= 0x80 {
                if fail_fast {
                    proof {
                        // the fire-exit channel: the loop invariants
                        // hold with final == the current state
                        assert(entry == old(domain_buffer)@);
                    }
                    assert forall |p: int|
                        #![trigger domain_buffer@.index(p)]
                        0 <= p < cls as int
                        implies domain_buffer@[p] == old(domain_buffer)@[p] by {
                        if 0 <= p && p < cls as int {
                            assert(domain_buffer@[p] == entry.index(p));
                        }
                    }
                    // the marking fires exactly in fail-fast
                    return (true, had_reg);
                }
                let ghost pv: Seq<char> = domain_buffer@;
                domain_buffer.set(t, '\u{FFFD}');
                had_reg = true;
                pcf = true;
            }
            t = t + 1;
        }
        // pass end: !pcf states the pristine ASCII window (the decode
        // precondition of the rediscovery below). No proof{} nesting:
        // the by-blocks sit at the exec statement level of the branch.
        if pcf == false {
            // (a) nothing was marked: the content held over the window
            // equals the entry content position by position
            assert forall |q: int| #![trigger domain_buffer@.index(q)]
                (cls + 4) as int <= q < domain_buffer@.len() as int
                implies domain_buffer@.index(q) == entry.index(q) by {
                if (cls + 4) as int <= q && q < domain_buffer@.len() as int {
                    if domain_buffer@.index(q) != entry.index(q) {
                        // the marked disjunct of the content invariant:
                        // a non-ASCII entry char witnesses pcf
                        let q0 = q;
                        let e0 = entry.index(q0);
                        assert(e0 as u32 >= 0x80);
                        assert(pcf);
                        assert(false);
                    }
                }
            }
            // (b) the entry window content is all ASCII (the pcf
            // equation negates a non-ASCII witness at q)
            assert forall |q: int| #![trigger domain_buffer@.index(q)]
                (cls + 4) as int <= q < domain_buffer@.len() as int
                implies ((domain_buffer@.index(q) as u32) < 0x80) by {
                if (cls + 4) as int <= q && q < domain_buffer@.len() as int {
                    if domain_buffer@.index(q) != entry.index(q) {
                        let q0 = q;
                        let e0 = entry.index(q0);
                        assert(e0 as u32 >= 0x80);
                        assert(pcf);
                        assert(false);
                    }
                    let e1 = entry.index(q);
                    assert(e1 as u32 <= 0x7F);
                }
            }
        }
        // ---- trailing-hyphen marking (uts46.rs:1277-1292)
        // upstream: if let Some(last) = domain_buffer.last_mut()
        // (the buffer cannot be empty here: it holds "xn--" at least)
        let last_idx: usize = domain_buffer.len() - 1;
        if domain_buffer[last_idx] == '-' {
            if fail_fast {
                return (true, had_reg);
            }
            had_reg = true;
            pcf = true;
            let ghost pv: Seq<char> = domain_buffer@;
                domain_buffer.set(last_idx, '\u{FFFD}');
                proof {
                assert(domain_buffer@
                    == pv.update(last_idx as int, '\u{FFFD}'));
                assert(cls as int != last_idx as int);
                vstd::seq::lemma_seq_update_different(
                    pv, cls as int, last_idx as int, '\u{FFFD}');
                assert(domain_buffer@.index(cls as int)
                    == pv.index(cls as int));
                // the window stays dot-free (the marked position
                // held the hyphen)
                    assert forall |q: int| #![trigger domain_buffer@.index(q)]
                        cls as int <= q < domain_buffer@.len() as int
                        implies domain_buffer@.index(q) != '.' by {
                        assert(pv.index(last_idx as int) == '-');
                    if q != last_idx as int {
                        vstd::seq::lemma_seq_update_different(
                            pv, q, last_idx as int, '\u{FFFD}');
                    }
                }
            }
        }
        // ---- DoS length gate (uts46.rs:1294-1306)
        if (domain_buffer.len() - cls - 4) > PUNYCODE_DECODE_MAX_INPUT_LENGTH {
            if fail_fast {
                return (true, had_reg);
            }
            had_reg = true;
            pcf = true;
            let mark_pos: usize = cls + 4 + PUNYCODE_DECODE_MAX_INPUT_LENGTH;
            let ghost pv: Seq<char> = domain_buffer@;
                domain_buffer.set(mark_pos, '\u{FFFD}');
                proof {
                assert(domain_buffer@
                    == pv.update(mark_pos as int, '\u{FFFD}'));
                assert(cls as int != mark_pos as int);
                vstd::seq::lemma_seq_update_different(
                    pv, cls as int, mark_pos as int, '\u{FFFD}');
                assert(domain_buffer@.index(cls as int)
                    == pv.index(cls as int));
                // the window stays dot-free (the marked position is
                // inside the dot-free window)
                    assert((mark_pos as int) < (pv.len() as int));
                    assert forall |q: int| #![trigger domain_buffer@.index(q)]
                        cls as int <= q < domain_buffer@.len() as int
                        implies domain_buffer@.index(q) != '.' by {
                        assert(pv.index(mark_pos as int) != '.');
                    if q != mark_pos as int {
                        vstd::seq::lemma_seq_update_different(
                            pv, q, mark_pos as int, '\u{FFFD}');
                    }
                }
            }
        }
        // ---- rediscovery decode (uts46.rs:1308-1338)
        if !pcf {
            // the window tail is all-ASCII by the marking pass above;
            // clone it out for the decode tier
            proof {
                assert(domain_buffer@[cls as int] == 'x');
            }
            let mut win_core: Vec<char> = Vec::new();
            let mut k: usize = cls + 4;
            while k < domain_buffer.len()
                invariant
                    cls + 4 <= k <= domain_buffer.len(),
                    domain_buffer@.len() == entry_marks_len,
                    entry == old(domain_buffer)@,
                    fail_fast ==> domain_buffer@ == entry,
                    win_core@.len() == k - (cls + 4),
                    forall |q: int| 0 <= q < win_core@.len() as int
                        ==> win_core@.index(q)
                            == domain_buffer@.index((cls + 4) as int + q),
                    (domain_buffer@.len() - (cls + 4) as int)
                        <= PUNYCODE_DECODE_MAX_INPUT_LENGTH as int,
                    fail_fast ==> had_reg == had_in,
                    forall |p: int| 0 <= p < cls as int
                        ==> domain_buffer@.index(p) == entry.index(p),
                    domain_buffer@.index(cls as int) == 'x',
                decreases domain_buffer.len() - k
            {
                let ch = domain_buffer[k as usize];
                win_core.push(ch);
                k = k + 1;
            }
            let dec = punycode_v::decode_char_internal(win_core.as_slice());
            match dec {
                Option::Some(decoded) => {
                    fncc = true;
                    ncc = true;
                    // discard the window's xn-- content and re-emit the
                    // decoded label through after_punycode_decode
                    let ghost pre_tr: Seq<char> = domain_buffer@;
                    domain_buffer.truncate(cls as usize);
                    proof {
                        assert(domain_buffer@.len() as int == cls as int);
                        // the truncation drops a dot-free region: the
                        // census only shrinks
                        assert(domain_buffer@
                            == pre_tr.subrange(0, cls as int));
                        lemma_lab_count_shrink_to_prefix(
                            pre_tr, cls as int);
                        // the marked window was dot-free, so the
                        // pre-truncation census equals the entry census
                        assert(lab_count(pre_tr) == lab_count(entry)) by {
                            assert(pre_tr.len() as int
                                == entry.len() as int);
                            assert forall |p: int|
                                #![trigger pre_tr.index(p)]
                                0 <= p < pre_tr.len() as int
                                implies (pre_tr.index(p) == '.'
                                    ==> entry.index(p) == '.') by {
                                if (cls as int) <= p
                                    && p < pre_tr.len() as int {
                                    // a dot-free window position
                                } else {
                                    // below the window: untouched
                                    assert(pre_tr.index(p)
                                        == entry.index(p));
                                }
                            }
                            lemma_dots_up_le_pointwise(pre_tr, entry);
                            assert forall |p: int|
                                #![trigger entry.index(p)]
                                0 <= p < entry.len() as int
                                implies (entry.index(p) == '.'
                                    ==> pre_tr.index(p) == '.') by {
                                if (cls as int) <= p
                                    && p < entry.len() as int {
                                    // the window was dot-free at entry
                                } else {
                                    assert(entry.index(p)
                                        == pre_tr.index(p));
                                }
                            }
                            lemma_dots_up_le_pointwise(entry, pre_tr);
                        }
                    }
                    let early_pd = after_punycode_decode(
                        domain_buffer, cls as usize, decoded.as_slice(),
                        deny_dot, fail_fast, &mut had_reg,
                    );
                    proof {
                        // the re-emitted window is dot-free (the
                        // deny-dot image of the decode model)
                        let outz = after_pd_output(decoded@, deny_dot);
                        lemma_after_pd_output_not_dot(decoded@, deny_dot);
                        assert forall |q: int| #![trigger domain_buffer@.index(q)]
                            cls as int <= q < domain_buffer@.len() as int
                            implies domain_buffer@.index(q) != '.' by {
                            let trc = pre_tr.subrange(0, cls as int);
                            assert(trc.len() as int == cls as int) by {
                                vstd::seq::lemma_seq_subrange_len(
                                    pre_tr, 0, cls as int);
                            }
                            assert((q - cls as int) >= 0);
                            lemma_first_fffd_index_bound(outz, 0);
                            assert(0 <= pd_prefix_len(outz)
                                && pd_prefix_len(outz) <= outz.len() as int);
                            if fail_fast {
                                if early_pd {
                                    assert(first_fffd_from(outz, 0).is_some()
                                        || first_diff_from(outz, decoded@, 0).is_some());
                                    if first_fffd_from(outz, 0).is_some() {
                                        let cutz = outz.subrange(0, pd_prefix_len(outz));
                                        assert(cutz.len() as int
                                            == pd_prefix_len(outz)) by {
                                            vstd::seq::lemma_seq_subrange_len(
                                                outz, 0, pd_prefix_len(outz));
                                        }
                                        assert(domain_buffer@ == trc.add(cutz));
                                        assert((q - cls as int) < cutz.len() as int)
                                            by {
                                            vstd::seq::lemma_seq_add_len(trc, cutz);
                                        }
                                        vstd::seq::lemma_seq_add_index2(
                                            trc, cutz, q);
                                        vstd::seq::lemma_seq_subrange_index(
                                            outz, 0, pd_prefix_len(outz),
                                            q - cls as int);
                                    } else {
                                        let mkz = after_pd_marked(outz, decoded@);
                                        assert(domain_buffer@ == trc.add(mkz));
                                        lemma_after_pd_marked_not_dot(
                                            outz, decoded@);
                                        assert((q - cls as int) < mkz.len() as int)
                                            by {
                                            vstd::seq::lemma_seq_add_len(trc, mkz);
                                        }
                                        vstd::seq::lemma_seq_add_index2(
                                            trc, mkz, q);
                                    }
                                } else {
                                    let mkz = after_pd_marked(outz, decoded@);
                                    assert(domain_buffer@ == trc.add(mkz));
                                    lemma_after_pd_marked_not_dot(outz, decoded@);
                                    assert((q - cls as int) < mkz.len() as int)
                                        by {
                                        vstd::seq::lemma_seq_add_len(trc, mkz);
                                    }
                                    vstd::seq::lemma_seq_add_index2(
                                        trc, mkz, q);
                                }
                            } else {
                                let mkz = after_pd_marked(outz, decoded@);
                                assert(domain_buffer@ == trc.add(mkz));
                                lemma_after_pd_marked_not_dot(outz, decoded@);
                                assert((q - cls as int) < mkz.len() as int) by {
                                    vstd::seq::lemma_seq_add_len(trc, mkz);
                                }
                                vstd::seq::lemma_seq_add_index2(
                                    trc, mkz, q);
                            }
                        }
                    }
                    if early_pd {
                        return (true, had_reg);
                    }
                }
                Option::None => {
                    if fail_fast {
                        return (true, had_reg);
                    }
                    had_reg = true;
                    ncc = false;
                    fncc = false;
                    let ghost pv: Seq<char> = domain_buffer@;
                    domain_buffer.set(cls as usize, '\u{FFFD}');
                    proof {
                        assert(domain_buffer@
                            == pv.update(cls as int, '\u{FFFD}'));
                        assert(pv.index(cls as int) == entry.index(cls as int));
                        assert(entry.index(cls as int) == 'x');
                        assert forall |q: int| #![trigger domain_buffer@.index(q)]
                            cls as int <= q < domain_buffer@.len() as int
                            implies domain_buffer@.index(q) != '.' by {
                            if q != cls as int {
                                vstd::seq::lemma_seq_update_different(
                                    pv, q, cls as int, '\u{FFFD}');
                            }
                        }
                    }
                }
            }
        } else {
            fncc = false;
            ncc = false;
        }
    }
    // ---- check_label window pass (uts46.rs:1348-1357)
    let ghost pre_cl: Seq<char> = domain_buffer@;
    let early_cl = pim_check_label_dom(
        hyphens, domain_buffer, cls as usize, fail_fast,
        &mut had_reg, fncc, ncc,
    );
    if early_cl {
        return (true, had_reg);
    }
    proof {
        // the census channel at the clean exit
        assert forall |q: int| #![trigger domain_buffer@.index(q)]
            cls as int <= q < domain_buffer@.len() as int
            implies domain_buffer@.index(q) != '.' by {
            // the window pass rewrote the dot-free window into
            // non-dots (marks) on the mark-errors channel and left
            // the buffer untouched on the fail-fast channel
            let wpre = pre_cl;
            assert forall |t: int| cls as int <= t < wpre.len() as int
                implies wpre.index(t) != '.' by {
                if cls as int <= t && t < wpre.len() as int {
                }
            }
            if fail_fast {
                assert(domain_buffer@ == wpre);
            } else {
                let w0x = wpre.subrange(cls as int, wpre.len() as int);
                assert(w0x.len() as int
                    == wpre.len() as int - cls as int) by {
                    vstd::seq::lemma_seq_subrange_len(
                        wpre, cls as int, wpre.len() as int);
                }
                assert forall |t: int| #![trigger w0x[t]]
                    0 <= t < w0x.len() as int ==> w0x[t] != '.' by {
                    if 0 <= t && t < w0x.len() as int {
                        assert(w0x.len() as int
                            == wpre.len() as int - cls as int);
                        vstd::seq::lemma_seq_subrange_index(
                            wpre, cls as int, wpre.len() as int, t);
                    }
                }
                lemma_check_label_marked_not_dot(w0x, hyphens,
                    fncc, ncc);
                let clmx = check_label_marked_content(
                    w0x, hyphens, fncc, ncc);
                assert forall |t: int| #![trigger clmx[t]]
                    0 <= t < clmx.len() as int ==> clmx[t] != '.' by {
                    lemma_check_label_marked_not_dot(w0x, hyphens,
                        fncc, ncc);
                }
                let pref2 = wpre.subrange(0, cls as int);
                assert(pref2.len() as int == cls as int) by {
                    vstd::seq::lemma_seq_subrange_len(wpre, 0, cls as int);
                }
                assert(domain_buffer@ == pref2.add(clmx));
                assert((q - cls as int) >= 0);
                assert((q - cls as int) < clmx.len() as int) by {
                    vstd::seq::lemma_seq_add_len(pref2, clmx);
                    assert(domain_buffer@.len() as int == wpre.len() as int);
                }
                vstd::seq::lemma_seq_add_index2(pref2, clmx, q);
                assert(domain_buffer@.index(q)
                    == clmx[q - cls as int]);
            }
        }
        assert forall |p: int| #![trigger domain_buffer@.index(p)]
            0 <= p < cls as int
            implies domain_buffer@.index(p) == entry.index(p) by {
        }
    }
    (false, had_reg)
}

//// Mapping window (uts46.rs:1250-1360): walks the mapped feed
//// character by character (pushes, the U+FFFD error channel), and on
//// every '.' or end label boundary runs the label event above; the
//// '.' boundary also reopens the window (new label start, fresh
//// context flags, one Other tag per completed interior sub-label).
//// Return channels: ret.0 == fired, ret.1 == had_out.
fn pim_map_window<'a2>(
    deny_dot: u128,
    hyphens: Hyphens,
    fail_fast: bool,
    mapped: &[char],
    domain_buffer: &mut Vec<char>,
    tags: &mut Vec<AlreadyAsciiLabel<'a2>>,
    had_in: bool,
    cls_in: usize,
    first_needs_combining_mark_check_in: bool,
    needs_contextj_check_in: bool,
) -> (ret: (bool, bool))
    requires
        cls_in <= domain_buffer.len(),
        // the deny-dot image fact (the census channel of the label
        // events' decode re-emissions)
        bit_is_set(deny_dot, b'.'),
        // the window [cls_in..len) is dot-free at entry (the caller's
        // deny-mapped ASCII prefix; the separator dots sit below cls)
        forall |q: int| cls_in as int <= q < old(domain_buffer)@.len() as int
            ==> old(domain_buffer)@.index(q) != '.',
    ensures
        ret.0 ==> fail_fast,
        fail_fast ==> ret.1 == had_in,
        // the window never shrinks below its label start; the interior
        // region (the label content accumulated so far) may be
        // rewritten in place by the rediscovery decode
        final(domain_buffer)@.len() >= cls_in as int,
        final(tags)@.len() >= old(tags)@.len(),
        // the clean completion pushed exactly one Other tag per
        // completed interior sub-label (the feed's dot census)
        !ret.0 ==> final(tags)@.len() == old(tags)@.len()
            + dots_up_to(mapped@, mapped.len() as int),
        // every tag the window adds is the Other sentinel and the tags
        // below the entry are preserved position by position (the final
        // content is the entry content extended by an Other-filled
        // block; aggregate add form, both the clean and the fired
        // channels)
        final(tags)@ == old(tags)@.add(Seq::new(
            (final(tags)@.len() - old(tags)@.len()) as nat,
            |i: int| AlreadyAsciiLabel::Other)),
        // the preserved prefix as its own channel (the subrange cut)
        final(tags)@.subrange(0, old(tags)@.len() as int)
            == old(tags)@,
        forall |p: int| 0 <= p < cls_in as int
            ==> final(domain_buffer)@.index(p) == old(domain_buffer)@.index(p),
{
    let ghost entry_below_cls: Seq<char> = domain_buffer@.subrange(
        0, cls_in as int);
    let ghost entry: Seq<char> = domain_buffer@;
    let ghost tags_entry: Seq<AlreadyAsciiLabel<'a2>> = tags@;
    let ghost mapped_ghost: Seq<char> = mapped@;
    proof {
        // entry geometry from the requires
        assert(entry.len() as int >= cls_in as int);
    }
    let mut had_reg: bool = had_in;
    let mut cls: usize = cls_in;
    let mut fncc: bool = first_needs_combining_mark_check_in;
    let mut ncc: bool = needs_contextj_check_in;
    let mut j: usize = 0;
    while j < mapped.len()
        invariant
            j <= mapped.len(),
            mapped@ == mapped_ghost,
            domain_buffer@.len() >= cls_in as int,
            entry == old(domain_buffer)@,
            entry.len() as int >= cls_in as int,
            entry_below_cls == entry.subrange(0, cls_in as int),
            entry_below_cls
                == old(domain_buffer)@.subrange(0, cls_in as int),
            forall |p: int| 0 <= p < cls_in as int
                ==> domain_buffer@.index(p) == entry_below_cls.index(p),
            tags_entry == old(tags)@,
            tags@.len() == tags_entry.len() + dots_up_to(mapped@, j as int),
            bit_is_set(deny_dot, b'.'),
            forall |q: int| cls as int <= q < domain_buffer@.len() as int
                ==> domain_buffer@.index(q) != '.',
            // the tag content below the entry is preserved (appends only)
            forall |i: int| 0 <= i < tags_entry.len() as int
                ==> tags@.index(i) == tags_entry.index(i),
            // every tag the window has added so far is the Other sentinel
            forall |i: int| tags_entry.len() as int
                <= i < tags@.len() as int
                ==> tags@.index(i) == AlreadyAsciiLabel::Other,
            fail_fast ==> had_reg == had_in,
            cls_in <= cls,
            cls <= domain_buffer.len(),
        decreases mapped.len() - j
    {
        let c = mapped[j as usize];
        if c == '.' {
            let ghost pre_ev: Seq<char> = domain_buffer@;
            let (fired_ev, had_ev) = pim_map_event(
                deny_dot, hyphens, fail_fast, domain_buffer,
                had_reg, cls, fncc, ncc,
            );
            had_reg = had_ev;
            if fired_ev {
                // fire-exit channels: the tags census and the prefix law
                // bridge from the loop invariants
                proof {
                    lemma_dots_up_nonneg(mapped@, j as int);
                }
                assert forall |p: int|
                    #![trigger domain_buffer@.index(p)]
                    0 <= p < cls_in as int
                    implies domain_buffer@.index(p)
                        == old(domain_buffer)@.index(p) by {
                    if 0 <= p < cls_in as int {
                        assert(domain_buffer@.index(p)
                            == entry_below_cls.index(p));
                        assert(entry_below_cls
                            == old(domain_buffer)@.subrange(
                                0, cls_in as int));
                        assert(cls_in as int <= entry.len()) by {}
                        assert(entry == old(domain_buffer)@);
                        vstd::seq::lemma_seq_subrange_index(
                            entry, 0, cls_in as int, p);
                    }
                }
                    proof {
                        lemma_pointwise_extend_eq(tags@, tags_entry);
                        lemma_pointwise_prefix_eq(tags@, tags_entry);
                    }
                return (true, had_reg);
            }
            // the '.' boundary: reopen the window and tag the
            // completed sub-label (uts46.rs:1359-1363)
            proof {
                // chains from the event ensures: below the window start
                // nothing changed, and the buffer did not shrink below
                // the window start
                assert(cls_in <= cls);
                assert(domain_buffer@.len() >= cls as int);
                assert(domain_buffer@.len() >= cls_in as int);
                assert forall |p: int| #![trigger domain_buffer@.index(p)]
                    0 <= p < cls_in as int
                    implies domain_buffer@.index(p)
                        == entry_below_cls.index(p) by {
                    if 0 <= p && p < cls_in as int {
                        assert(p < cls as int);
                        // the event preserved < cls over its own frame
                        assert(domain_buffer@.index(p)
                            == pre_ev.index(p));
                        assert(pre_ev.index(p) == entry_below_cls.index(p));
                    }
                }
            }
            let ghost pb: Seq<char> = domain_buffer@;
            domain_buffer.push('.');
            proof {
                assert(domain_buffer@ == pb.push('.'));
                assert(domain_buffer@.len() >= cls_in as int);
            }
            cls = domain_buffer.len();
            fncc = true;
            ncc = true;
            let ghost pt: Seq<AlreadyAsciiLabel<'a2>> = tags@;
            tags.push(AlreadyAsciiLabel::Other);
            proof {
                assert(tags@ == pt.push(AlreadyAsciiLabel::Other));
                lemma_dots_step(mapped@, j as int);
                assert(dots_up_to(mapped@, (j + 1) as int)
                    == dots_up_to(mapped@, j as int) + 1);
                // the new-tags-Other equation extends through the pushed
                // cell
                assert forall |i: int|
                    #![trigger tags@.index(i)]
                    tags_entry.len() as int <= i < tags@.len() as int
                    implies tags@.index(i)
                        == AlreadyAsciiLabel::Other by {
                    if tags_entry.len() as int <= i
                        && i < tags@.len() as int {
                        if i < pt.len() as int {
                            assert(pt.len() == tags_entry.len()
                                + dots_up_to(mapped@, j as int));
                        } else {
                            assert(i == pt.len() as int);
                        }
                    }
                }
                assert forall |i: int|
                    #![trigger tags@.index(i)]
                    0 <= i < tags_entry.len() as int
                    implies tags@.index(i) == pt.index(i) by {
                    if 0 <= i && i < tags_entry.len() as int {
                        lemma_dots_up_nonneg(mapped@, j as int);
                        assert(pt.len() == tags_entry.len()
                            + dots_up_to(mapped@, j as int));
                        assert(i < pt.len() as int);
                        vstd::seq::lemma_seq_push_index_different(
                            pt, AlreadyAsciiLabel::Other, i);
                    }
                }
            }
            j = j + 1;
        } else {
            // the plain mapped-char push with the U+FFFD error channel
            // (uts46.rs:1355-1361 as the Some(c) arm)
            if c == '\u{FFFD}' {
                if fail_fast {
                    // fire-exit channels bridged from the invariants
                proof {
                    lemma_dots_up_nonneg(mapped@, j as int);
                }
                assert forall |p: int|
                    #![trigger domain_buffer@.index(p)]
                    0 <= p < cls_in as int
                    implies domain_buffer@.index(p)
                        == old(domain_buffer)@.index(p) by {
                    if 0 <= p < cls_in as int {
                        assert(domain_buffer@.index(p)
                            == entry_below_cls.index(p));
                        assert(entry_below_cls
                            == old(domain_buffer)@.subrange(
                                0, cls_in as int));
                        assert(cls_in as int <= entry.len()) by {}
                        assert(entry == old(domain_buffer)@);
                        vstd::seq::lemma_seq_subrange_index(
                            entry, 0, cls_in as int, p);
                    }
                }
                proof {
                    lemma_pointwise_extend_eq(tags@, tags_entry);
                    lemma_pointwise_prefix_eq(tags@, tags_entry);
                }
                return (true, had_reg);
                }
                had_reg = true;
            }
            let ghost pb: Seq<char> = domain_buffer@;
            domain_buffer.push(c);
            proof {
                assert(domain_buffer@ == pb.push(c));
                assert(domain_buffer@.len() >= cls_in as int);
                assert(pb.len() >= cls_in as int);
                // the window stays dot-free (the pushed char is a
                // non-separator mapped char)
                assert(c != '.');
                assert forall |q: int| #![trigger domain_buffer@.index(q)]
                    cls as int <= q < domain_buffer@.len() as int
                    implies domain_buffer@.index(q) != '.' by {
                    if q == pb.len() as int {
                        assert(domain_buffer@.index(q) == c);
                    }
                }
            }
            j = j + 1;
        }
    }
    // the terminal label event of the feed (the n == None arm)
    let ghost pre_end: Seq<char> = domain_buffer@;
    let (fired_end, had_end) = pim_map_event(
        deny_dot, hyphens, fail_fast, domain_buffer,
        had_reg, cls, fncc, ncc,
    );
    proof {
        // the loop-end channels continue through the terminal event
        lemma_dots_up_nonneg(mapped@, mapped.len() as int);
        assert(cls_in <= cls);
        assert(forall |p: int| 0 <= p < cls_in as int
            ==> pre_end.index(p) == entry_below_cls.index(p)) by {
            assert forall |p: int| #![trigger pre_end.index(p)]
                0 <= p < cls_in as int
                implies pre_end.index(p) == entry_below_cls.index(p) by {
                if 0 <= p < cls_in as int {
                }
            }
        }
        assert(forall |p: int| 0 <= p < cls_in as int
            ==> domain_buffer@.index(p) == pre_end.index(p)) by {
            assert forall |p: int| #![trigger domain_buffer@.index(p)]
                0 <= p < cls_in as int
                implies domain_buffer@.index(p) == pre_end.index(p) by {
                if 0 <= p < cls_in as int {
                    assert(p < cls as int);
                }
            }
        }
        assert forall |p: int| #![trigger domain_buffer@.index(p)]
            0 <= p < cls_in as int
            implies domain_buffer@.index(p) == entry_below_cls.index(p) by {
            if 0 <= p < cls_in as int {
                assert(domain_buffer@.index(p) == pre_end.index(p));
                assert(pre_end.index(p) == entry_below_cls.index(p));
            }
        }
        assert forall |p: int| #![trigger domain_buffer@.index(p)]
            0 <= p < cls_in as int
            implies domain_buffer@.index(p) == old(domain_buffer)@.index(p) by {
            if 0 <= p < cls_in as int {
                assert(domain_buffer@.index(p)
                    == entry_below_cls.index(p));
                assert(entry_below_cls
                    == old(domain_buffer)@.subrange(0, cls_in as int));
                vstd::seq::lemma_seq_subrange_index(
                    old(domain_buffer)@, 0, cls_in as int, p);
            }
        }
    }
    if fired_end {
        proof {
            lemma_pointwise_extend_eq(tags@, tags_entry);
            lemma_pointwise_prefix_eq(tags@, tags_entry);
        }
        return (true, had_end);
    }
    proof {
        assert(dots_up_to(mapped@, mapped.len() as int)
            == tags@.len() - tags_entry.len());
        lemma_pointwise_extend_eq(tags@, tags_entry);
        lemma_pointwise_prefix_eq(tags@, tags_entry);
    }
    (false, had_end)
}

/// The empty label always passes through (the passthrough spec's empty
/// disjunct). Used by the outer label loop to show that the label leaving
/// the passthrough prefix is nonempty.
proof fn lemma_passthrough_empty(label: &[u8])
    requires
        label@.len() == 0,
    ensures
        spec_is_passthrough_ascii_label(label),
{
    assert(label.len() as int == 0);
}

/// Every byte of a passthrough label is ASCII (the first byte is a-z and
/// the rest are a-z/0-9/hyphen in the spec model).
proof fn lemma_is_passthrough_ascii(label: &[u8])
    requires
        spec_is_passthrough_ascii_label(label),
    ensures
        forall |q: int| 0 <= q < label.len() as int
            ==> label[q] < 0x80,
{
    if label.len() as int == 0 {
    } else {
        assert(label[0] as int >= b'a' as int
            && label[0] as int <= b'z' as int);
        assert forall |q: int| #![trigger label[q]]
            0 <= q < label.len() as int
            implies label[q] < 0x80 by {
            if 0 <= q && q < label.len() as int {
                if q == 0 {
                    assert(label[0] >= b'a' && label[0] <= b'z');
                } else {
                    assert((label[q] >= b'a' && label[q] <= b'z')
                        || (label[q] >= b'0' && label[q] <= b'9')
                        || label[q] == b'-');
                }
            }
        }
    }
}

//// The outer label state machine of process_innermost (uts46.rs:1093-
//// 1493): the tail label motor with the passthrough-prefix accounting, the
//// per-label dispatch (the pre-existing punycode tier, the pure-ASCII
//// tier, the normalization mapping window, the empty label), and the
//// is_bidi + CheckBidi post-pass tail wiring. Return channels:
//// ret.0 == passthrough_up_to (a prefix length of domain_name; the
//// pre-tail offset plus the tail's passthrough labels), ret.1 == is_bidi
//// of the final buffer, ret.2 == had_errors.
////
//// Entry geometry (faithful to the single upstream caller): process_inner
//// delegates with a freshly empty domain_buffer (uts46.rs:773-1045), so
//// the transcription requires the entry buffer to be empty; upstream
//// would otherwise observe an is_bidi/trailing-watermark of the entry
//// content that the pipeline never produces.
////
//// Accounting note (value-equal rearrangement of upstream 1108-1145): the
//// separator dot of the passthrough prefix is pre-consumed at the
//// preceding label's advance (upstream defers it to the next label head
//// via the seen_label register). Every passthrough label counts its own
//// bytes plus its trailing dot (when one exists), so the passthrough
//// counter is exactly dn_off + pos while the prefix lasts, and freezes
//// strictly below domain_name.len() once a label leaves the prefix (the
//// leaving label is nonempty, because empty labels always pass through).
//// The frozen bound also carries the fired-channel nonempty-domain law at
//// the bidi marking fire exit.
////
//// Dispatch note (upstream 1150-1217): non_punycode_ascii_label is true
//// exactly for the pure-ASCII label that never touched the punycode tier
//// (no "xn--" prefix; the invalid-form punycode fall-through keeps it
//// false and routes to the mapping window, where the rediscovery
//// re-derives the punycode violation). The hyphens check of the
//// pure-ASCII tier runs only when hyphens != Allow (upstream 1232).
fn process_innermost<'a>(
    domain_name: &'a [u8],
    ascii_deny_list: AsciiDenyList,
    hyphens: Hyphens,
    fail_fast: bool,
    domain_buffer: &mut Vec<char>,
    already_punycode: &mut Vec<AlreadyAsciiLabel<'a>>,
    tail: &'a [u8],
) -> (ret: (usize, bool, bool))
    requires
        domain_name.len() >= tail.len(),
        old(domain_buffer)@.len() == 0,
        // upstream geometry (uts46.rs:784-786: process enters with
        // fresh SmallVecs and process_inner forwards them): the tag
        // vector enters empty, so the sink-walk tiling channel of the
        // ensures below is anchored at a single entry boundary
        old(already_punycode)@.len() == 0,
        // upstream geometry: the tail is the suffix slice of domain_name
        // from the most recent label start (process_inner's iterator
        // snapshot), so the tail bytes ARE domain_name bytes
        tail@ == domain_name@.subrange(
            (domain_name.len() - tail.len()) as int,
            domain_name.len() as int),
    ensures
        ret.0 <= domain_name.len(),
        // the passthrough prefix of the tail region is pure ASCII (the
        // passthrough labels are lower-case/digit/hyphen bytes and the
        // separators are dots); the pre-tail region is ASCII by the
        // fast-path scan of the caller
        forall |p: int| (domain_name.len() - tail.len()) as int
            <= p < ret.0 as int
            ==> domain_name[p] < 0x80,
        // every tag added holds a pure-ASCII mixed-case payload or is
        // the Other sentinel (the sink pass re-emits raw tag bytes as
        // chars, so the payload domain is carried through the tags)
        forall |i: int| old(already_punycode)@.len() as int
            <= i < final(already_punycode)@.len() as int
            ==> tag_payload_ascii(final(already_punycode)@.index(i)),
        // the fired channel is fail-fast only, with the passthrough
        // counter reset and no is_bidi scan performed
        fail_fast && ret.2 == true ==> (ret.0 == 0 && ret.1 == false),
        // fail-fast never marks on its clean channel
        fail_fast ==> ret.2 == false || (ret.0 == 0 && ret.1 == false),
        // fires only happen with a nonempty domain: inside the nonempty
        // complex label tier, or (the marking fire) past the prefix freeze
        fail_fast && ret.2 == true ==> domain_name.len() > 0,
        // the pristine passthrough channel: the whole tail passed
        // through, so nothing was written and no error occurred
        ret.0 == domain_name.len()
            ==> (final(domain_buffer)@ == old(domain_buffer)@
                && final(already_punycode)@ == old(already_punycode)@
                && ret.1 == false
                && ret.2 == false),
        // the buffer never shrinks below the entry content, and the
        // entry content is preserved position by position
        final(domain_buffer)@.len() >= old(domain_buffer)@.len(),
        forall |p: int| 0 <= p < old(domain_buffer)@.len() as int
            ==> final(domain_buffer)@.index(p) == old(domain_buffer)@.index(p),
        final(already_punycode)@.len() >= old(already_punycode)@.len(),
        // the sink-walk tiling (E-TILE): every tag cell on the clean
        // channel tiles the raw input at its fold position counted from
        // the returned passthrough boundary (the unflushed register
        // arithmetic of the walk, upstream 826/844/858/899/913; Other
        // cells break the chain -- the walk flushes at the first
        // Other-tagged label -- and cells past input exhaustion are the
        // empty trailing-label ones). The fire channels (ret.2 == true)
        // return before the walk completes, so the claim is
        // clean-channel only.
        // the walk of Uts46::process consumes the two feeds below on
        // every non-fire return (the gate excludes exactly the
        // fail-fast fire channel, whose early return leaves the tiling
        // boundary unconstrained; the mark-errors completion keeps the
        // correct passthrough boundary)
        ret.2 == false || !fail_fast ==>
            forall |j: int|
                0 <= j < final(already_punycode)@.len() as int
                ==> align_cell_ok(domain_name@,
                    final(already_punycode)@, j, ret.0 as int),
{
    let deny: u128 = ascii_deny_list.bits;
    let deny_dot: u128 = deny | DOT_MASK;
    proof {
        // the deny-dot image fact consumed by the census channels of
        // the mapping window below
        lemma_bit_is_set_dot_or(deny);
        assert(deny_dot == deny | DOT_MASK);
        assert(bit_is_set(deny_dot, b'.'));
    }
    let dn_off: usize = domain_name.len() - tail.len();
    let ghost buf_entry: Seq<char> = domain_buffer@;
    let ghost bngh: int = buf_entry.len() as int;
    let ghost tags_entry: Seq<AlreadyAsciiLabel<'a>> = already_punycode@;
    let ghost tail_ghost: Seq<u8> = tail@;
    proof {
        assert(domain_name.len() == dn_off + tail.len());
        assert(bngh == 0);
        // the entry tag rope is the empty rope (the single-caller
        // geometry); carried as a persistent fact for the
        // leave-iteration lanes of the tiling push sites below
        assert(tags_entry == old(already_punycode)@);
        assert(tags_entry.len() as int == 0);
    }
    // Iteration structure (value-equal rearrangement of the upstream
    // split-iterator label walk): one label per iteration, plus one extra
    // trailing iteration exactly when the last byte of the tail is a dot
    // (the trailing empty string of the split). The upstream counts the
    // labels up front as dots + 1, a usize counter whose increment this
    // build cannot discharge against usize::MAX; the last_done register
    // encodes the same boundary without a counter, and on every input,
    // including an empty tail, the two forms process the same label
    // sequence and return the same triple (an empty tail gives upstream
    // one passthrough of the empty label, which writes nothing and
    // leaves ptu at dn_off == domain_name.len(); here the loop runs
    // zero iterations with the same return).
    let mut had: bool = false;
    let mut ptu: usize = dn_off;
    let mut seen_label: bool = false;
    let mut in_prefix: bool = true;
    let mut pos: usize = 0;
    let mut last_done: bool = false;
    // transcription helper register (the value of the tag-chain fold
    // being alive: no Other cell has been pushed since the prefix was
    // left; the sink walk's tiling obligations ride on it)
    let mut tile_live: bool = true;
    while pos < tail.len()
        || (!last_done
            && tail.len() > 0
            && tail[tail.len() - 1] == b'.')
        invariant
            pos <= tail.len(),
            domain_name.len() >= tail.len(),
            dn_off as int + tail.len() as int == domain_name.len() as int,
            tail_ghost == tail@,
            tail_ghost == domain_name@.subrange(
                dn_off as int, domain_name.len() as int),
            forall |q: int| 0 <= q < tail_ghost.len() as int
                ==> tail_ghost[q] == domain_name[(dn_off as int + q)],
            // the consumed passthrough prefix of the tail region is
            // pure ASCII
            forall |p: int| dn_off as int <= p < ptu as int
                ==> domain_name[p] < 0x80,
            // every tag added so far holds an ASCII payload or Other
            forall |i: int| tags_entry.len() as int
                <= i < already_punycode@.len() as int
                ==> tag_payload_ascii(already_punycode@.index(i)),
            buf_entry == old(domain_buffer)@,
            bngh == buf_entry.len() as int,
            domain_buffer@.len() >= bngh,
            forall |p: int| 0 <= p < bngh
                ==> domain_buffer@.index(p) == buf_entry.index(p),
            tags_entry == old(already_punycode)@,
            already_punycode@.len() >= tags_entry.len(),
            fail_fast ==> had == false,
            // while in the prefix nothing was ever written and no tag was
            // pushed: the pristine-passthrough channel
            in_prefix == true ==> (domain_buffer@ == buf_entry
                && already_punycode@ == tags_entry
                && had == false),
            // the entry rope is empty (the single-caller geometry), so
            // the pristine channel leaves no tags (the leave-iteration
            // lane of the tiling push sites below consumes this)
            in_prefix == true ==> already_punycode@.len() as int == 0,
            // the passthrough counter is exactly the consumed prefix
            // boundary (the separator dots are pre-consumed at the
            // preceding label's advance)
            in_prefix == true ==> ptu as int == dn_off as int + pos as int,
            // once the prefix is left, the counter froze strictly below
            // the domain end (the label that left the prefix is nonempty)
            in_prefix == false ==> (ptu as int) < domain_name.len() as int,
            // the sink-walk tiling: every cell pushed so far carries
            // its walk-side alignment obligation at the frozen boundary
            in_prefix == false ==> (
                forall |j: int|
                    #![trigger align_cell_ok(domain_name@,
                        already_punycode@, j, ptu as int)]
                    0 <= j < already_punycode@.len() as int
                    ==> align_cell_ok(domain_name@, already_punycode@,
                        j, ptu as int)
            ),
            // while the chain is alive the fold tip sits exactly at the
            // raw start of the label under processing (the push sites
            // below extend the chain through it); the last_done gate
            // voids the claim on the terminal-iteration exit, where the
            // final cell's separator limb overcounts past the input end
            // (never read: the walk has returned by then)
            (in_prefix == false && tile_live && last_done == false) ==> (
                align_cell_a(already_punycode@,
                    already_punycode@.len() as int, ptu as int)
                == (dn_off as int + pos as int)
            ),
            // a dead chain has a poisoned fold tip (the Other push and
            // the Other-filled window block both pin the tip to -1)
            (in_prefix == false && tile_live == false) ==> (
                align_cell_a(already_punycode@,
                    already_punycode@.len() as int, ptu as int) == -1
            ),
            // the chain register only dies after the prefix was left
            tile_live == true || in_prefix == false,
            last_done == false || pos == tail.len(),
            // the label census of the sink walk (E-CEN): the buffer
            // never holds more '.'-split labels than the tag rope
            // holds cells (every label path pushes at least its top
            // cell, and every buffer dot is matched by a cell)
            // the deny facts re-bound at every loop head (loop heads
            // havoc the locals; the census channels of the mapping
            // window and the punycode tier consume them in the arms)
            deny == ascii_deny_list.bits,
            deny_dot == deny | DOT_MASK,
            bit_is_set(deny_dot, b'.'),
        decreases (tail.len() - pos) as int,
            if last_done { 0int } else { 1int }
    {
        // the head-state tiling snapshot, captured while the loop
        // invariants are in force over the untouched rope; the push
        // sites below consume these ghost facts (the tag rope is
        // untouched until a site's own push, so the head fold is that
        // site's pre-push fold)
        let ghost head_tags: Seq<AlreadyAsciiLabel<'a>> = already_punycode@;
        let ghost head_ptu: int = ptu as int;
        let ghost head_pos: int = pos as int;
        let ghost head_in_prefix: bool = in_prefix;
        let ghost head_tip: int = align_cell_a(head_tags,
            head_tags.len() as int, head_ptu);
        let ghost head_buf: Seq<char> = domain_buffer@;
        let ghost head_tags_len: int = already_punycode@.len() as int;
        proof {
            assert(head_tags == already_punycode@);
            assert(head_buf == domain_buffer@);
            assert(head_tags_len == already_punycode@.len() as int);
            assert(head_ptu == ptu as int);
            assert(head_pos == pos as int);
            assert(head_tip == align_cell_a(already_punycode@,
                already_punycode@.len() as int, ptu as int));
            if in_prefix == false {
                assert forall |j: int|
                    #![trigger align_cell_ok(domain_name@, head_tags,
                        j, head_ptu)]
                    0 <= j < head_tags.len() as int
                    implies align_cell_ok(domain_name@, head_tags, j,
                        head_ptu) by {
                }
                if tile_live && last_done == false {
                    assert(head_tip == dn_off as int + head_pos);
                }
                if tile_live == false {
                    assert(head_tip == -1);
                }
            }
        }
        // the label boundary scan from pos
        let mut le: usize = pos;
        while le < tail.len() && tail[le] != b'.'
            invariant
                pos <= le <= tail.len(),
                forall |q: int| pos as int <= q < le as int
                    ==> tail@[q] != b'.',
            decreases tail.len() - le
        {
            le = le + 1;
        }
        let label: &'a [u8] = &tail[pos..le];
        proof {
            assert(label@.len() == le - pos);
            assert(label@ == tail@.subrange(pos as int, le as int));
            assert((le as int) <= tail_ghost.len() as int);
            // the register cannot be set inside the loop: it forces pos
            // to the tail end, which voids the loop condition
            assert(last_done == false);
            // the scan exit evidence: a non-terminal label sits on a dot
            assert((le as int) == tail_ghost.len() as int
                || tail_ghost.index(le as int) == b'.');
        }
        // ---- passthrough tier (uts46.rs:1127-1136)
        let pspt = is_passthrough_ascii_label(label);
        if in_prefix && pspt {
            seen_label = true;
            // the label bytes are pure ASCII (the passthrough spec), and
            // they sit at [dn_off + pos, dn_off + le) of domain_name
            proof {
                lemma_is_passthrough_ascii(label);
                assert forall |r: int|
                    #![trigger label[r]]
                    0 <= r < (le - pos) as int
                    implies label[r] < 0x80 by {
                    if 0 <= r && r < (le - pos) as int {
                        // definitional instantiation of the lemma channel
                    }
                }
                assert forall |q: int|
                    #![trigger domain_name[q]]
                    (dn_off as int + pos as int) <= q
                        < (dn_off as int + le as int)
                    implies domain_name[q] < 0x80 by {
                    if (dn_off as int + pos as int) <= q
                        && q < (dn_off as int + le as int) {
                        // the transfer to the label view and the
                        // passthrough ASCII lemma
                        assert(domain_name[q]
                            == label[q - dn_off as int - pos as int]);
                    }
                }
                if le < tail.len() {
                    // the trailing dot, in domain_name coordinates
                    assert(tail_ghost[le as int] == b'.');
                    assert(domain_name[(dn_off as int + le as int)]
                        == tail_ghost[le as int]);
                }
                // the consumed-prefix equation still holds here (the
                // passthrough counter has not moved yet)
                assert(ptu as int == dn_off as int + pos as int);
            }
            let ghost old_ptu: int = ptu as int;
            let ghost old_pos: int = pos as int;
            if le < tail.len() {
                proof {
                    // int-space feed for ptu + (le - pos) + 1: the new
                    // value is dn_off + (le + 1) == dn_off + the new pos
                    assert(ptu as int + (le - pos) as int + 1
                        == dn_off as int + (le as int + 1));
                    assert((le - pos) as int + 1 >= 0);
                    assert(((le + 1) as int) <= tail_ghost.len() as int);
                    assert(dn_off as int + (le as int + 1)
                        <= dn_off as int + tail_ghost.len() as int);
                    assert(dn_off as int + tail_ghost.len() as int
                        == domain_name.len() as int);
                }
                ptu = ptu + (le - pos) + 1;
                pos = le + 1;
            } else {
                proof {
                    assert(le as int == tail_ghost.len() as int);
                    assert(ptu as int + (le - pos) as int
                        == dn_off as int + tail_ghost.len() as int);
                    assert(dn_off as int + tail_ghost.len() as int
                        == domain_name.len() as int);
                }
                ptu = ptu + (le - pos);
                pos = tail.len();
            }
            proof {
                // entry facts: the consumed-prefix equation advanced in
                // lockstep with pos
                assert(ptu as int == dn_off as int + pos as int);
                // the passthrough prefix ASCII channel extends over the
                // newly consumed span (the label bytes plus the trailing
                // dot when one was consumed): old_ptu == dn_off + the
                // pre-update pos, so the old prefix, the label span, and
                // (when consumed) the trailing dot tile the new range
                assert(old_ptu == dn_off as int + old_pos);
                assert(old_pos <= le as int);
                assert forall |p: int|
                    #![trigger domain_name[p]]
                    dn_off as int <= p < ptu as int
                    implies domain_name[p] < 0x80 by {
                    if dn_off as int <= p && p < ptu as int {
                        if p < old_ptu {
                            // the previously consumed prefix
                        } else if p < (dn_off as int + le as int) {
                            // inside the newly consumed label (the per
                            // iteration ASCII computation above)
                        } else if le < tail.len() {
                            // the trailing dot position
                            assert(p == dn_off as int + le as int);
                            assert(domain_name[p] == b'.');
                        } else {
                            assert(p == dn_off as int + le as int);
                        }
                    }
                }
            }
            if pos == tail.len() {
                last_done = true;
            }
            continue;
        }
        // ---- dot emission (uts46.rs:1137-1145): the separator dot of a
        // fully in-buffer label goes to the buffer; the in-prefix leaver
        // separator is already accounted (the consumed-prefix equation)
        let mut left_now: bool = false;
        if in_prefix {
            proof {
                // the leaving label is nonempty: empty labels always pass
                // through, and the passthrough tier above did not take it
                assert(pspt == false);
                if label@.len() == 0 {
                    lemma_passthrough_empty(label);
                    assert(spec_is_passthrough_ascii_label(label));
                    assert(false);
                }
                assert(label@.len() > 0);
                assert((pos as int) < (le as int));
                assert((le as int) <= tail_ghost.len() as int);
                // the freeze bound: the counter stops strictly below the
                // domain end because the leaving label occupies
                // [pos, le) inside the tail
                assert(ptu as int == dn_off as int + pos as int);
                assert((ptu as int) < domain_name.len() as int);
            }
            left_now = true;
            in_prefix = false;
        }
        let mut sep_pushed: bool = false;
        if seen_label && !in_prefix && !left_now {
            let ghost pb: Seq<char> = domain_buffer@;
            domain_buffer.push('.');
            sep_pushed = true;
            proof {
                assert(domain_buffer@ == pb.push('.'));
            }
        }
        let ghost b1_buf: Seq<char> = domain_buffer@;
        seen_label = true;
        let cls: usize = domain_buffer.len();
        if label.len() != 0 {
            // ---- the complex-label tier (uts46.rs:1148-1378)
            let (ascii, non_ascii) = split_ascii_fast_path_prefix(label);
            let mut npa: bool = false;
            if non_ascii.len() == 0 {
                let hp = has_punycode_prefix(ascii);
                if hp {
                    proof {
                        assert(ascii.len() as int >= 4);
                    }
                    if ascii[ascii.len() - 1] != b'-'
                        && ascii.len() - 4
                            <= PUNYCODE_DECODE_MAX_INPUT_LENGTH
                    {
                        // the valid-form gate holds: the pre-existing
                        // punycode tier consumes this label completely
                        proof {
                            assert(ascii.len() as int
                                + non_ascii.len() as int
                                == label.len() as int);
                            assert(ascii.len() as int
                                == label.len() as int);
                            assert(label.len() >= 4);
                            assert(label[0] == ascii[0]);
                            assert(label[1] == ascii[1]);
                            assert(label[2] == ascii[2]);
                            assert(label[3] == ascii[3]);
                            assert(spec_has_punycode_prefix(label));
                            assert(label[label.len() - 1]
                                == ascii[ascii.len() - 1]);
                            assert(label[label.len() - 1] != b'-');
                            assert(label.len() - 4
                                <= PUNYCODE_DECODE_MAX_INPUT_LENGTH);
                            assert forall |q: int|
                                #![trigger label[q]]
                                0 <= q < label.len()
                                implies label[q] < 0x80 by {
                                if 0 <= q && q < label.len() {
                                    assert(label[q] == ascii[q]);
                                    assert(label[q] < 0x80);
                                }
                            }
                        }
                        let ghost t_pre_pc: Seq<AlreadyAsciiLabel<'a>>
                            = already_punycode@;
                        proof {
                            assert(last_done == false);
                            // the pre-call fold tip through the head
                            // snapshot: the rope is untouched so the fold
                            // at the head value is this site's pre-call
                            // fold
                            assert(t_pre_pc == head_tags);
                            // the two lanes of the head gate
                            if head_in_prefix {
                                // the leave-iteration lane: the pristine
                                // channel still holds -- the rope is the
                                // empty entry rope and the fold sits at
                                // the consumed prefix boundary (one
                                // definitional step of the fold)
                                assert(already_punycode@ == tags_entry);
                                assert(t_pre_pc.len() as int == 0);
                                assert(tile_live == true);
                                assert(ptu as int
                                    == dn_off as int + pos as int);
                                reveal_with_fuel(align_cell_a, 1);
                                assert(align_cell_a(t_pre_pc,
                                    t_pre_pc.len() as int, ptu as int)
                                    == ptu as int);
                            } else {
                                // the later-iteration lane: the
                                // invariant gate is live at the head
                            }
                            // the label-scan geometry (the payload value
                            // equality and the separator-or-end evidence)
                            lemma_raw_label_tiled(domain_name@, tail_ghost,
                                dn_off as int, pos as int, le as int, label);
                            if tile_live {
                                assert(align_cell_a(t_pre_pc,
                                    t_pre_pc.len() as int, ptu as int)
                                    == dn_off as int + pos as int);
                            } else {
                                assert(align_cell_a(t_pre_pc,
                                    t_pre_pc.len() as int, ptu as int) == -1);
                            }
                            assert(aligned_payload(domain_name@, label@,
                                align_cell_a(t_pre_pc,
                                    t_pre_pc.len() as int, ptu as int)));
                            // E-TILE: the pushed MixedCasePunycode cell
                            // extends the alignment chain (stated before
                            // the call so the loop invariants are in force
                            // over the untouched rope; the ensures facts
                            // ride on the ghost pushed-rope term)
                            lemma_tile_push_cell(domain_name@, t_pre_pc,
                                AlreadyAsciiLabel::MixedCasePunycode(label),
                                ptu as int);
                        }
                        proof {
                            // the tier requires (re-derived inside the
                            // loop body: loop heads havoc the fn-top
                            // facts): the deny-dot image fact, and the
                            // tail split item holding no separator byte
                            lemma_bit_is_set_dot_or(deny);
                            assert(deny_dot == deny | DOT_MASK);
                            assert(bit_is_set(deny_dot, b'.'));
                            assert forall |q: int|
                                #![trigger label[q]]
                                0 <= q < label.len() as int
                                implies label[q] != b'.' by {
                            }
                        }
                        proof {
                            // the tier require: a tail split item holds
                            // no separator byte
                            assert forall |q: int|
                                #![trigger label[q]]
                                0 <= q < label.len() as int
                                implies label[q] != b'.' by {
                            }
                        }
                        let (fired_br, had_br, _handled_br)
                            = pim_label_ascii_punycode(
                                deny, deny_dot, hyphens, fail_fast,
                                domain_buffer, already_punycode,
                                had, label,
                            );
                        proof {
                            if fail_fast {
                                assert(had_br == had);
                            }
                        }
                        had = had_br;
                        if fired_br {
                            proof {
                                // a fired return implies a nonempty
                                // domain: the fire sits inside the
                                // nonempty complex label tier
                                assert(fail_fast);
                                assert(label.len() > 0);
                                assert((pos as int) < (le as int));
                                assert(le as int
                                    <= tail_ghost.len() as int);
                                assert(domain_name.len()
                                    >= tail_ghost.len());
                                assert(domain_name.len() > 0);
                            }
                            return (0, false, true);
                        }
                        proof {
                            // the tier appended exactly one MixedCasePunycode
                            // tag holding this all-ASCII label below the
                            // preserved prefix
                            assert(already_punycode@ == t_pre_pc.push(
                                AlreadyAsciiLabel::MixedCasePunycode(label)));
                            vstd::seq::lemma_seq_push_len(
                                t_pre_pc,
                                AlreadyAsciiLabel::MixedCasePunycode(label));
                            assert(already_punycode@.len()
                                == t_pre_pc.len() + 1);
                            assert forall |k: int|
                                #![trigger already_punycode@.index(k)]
                                tags_entry.len() as int
                                    <= k < already_punycode@.len() as int
                                implies tag_payload_ascii(
                                    already_punycode@.index(k)) by {
                                if tags_entry.len() as int <= k
                                    && k < already_punycode@.len() as int {
                                    if k < t_pre_pc.len() as int {
                                        // a preserved cell: the tier's
                                        // append keeps pre-call content,
                                        // and the pre-call cells carry
                                        // the channel by the invariant
                                        vstd::seq::lemma_seq_push_index_different(
                                            t_pre_pc,
                                            AlreadyAsciiLabel::
                                                MixedCasePunycode(label),
                                            k);
                                        assert(already_punycode@.index(k)
                                            == t_pre_pc.index(k));
                                    } else {
                                        assert(k == t_pre_pc.len() as int);
                                        vstd::seq::lemma_seq_push_index_same(
                                            t_pre_pc,
                                            AlreadyAsciiLabel::
                                                MixedCasePunycode(label),
                                            k);
                                        assert(already_punycode@.index(k)
                                            == AlreadyAsciiLabel::
                                                MixedCasePunycode(label));
                                        assert(tag_payload_ascii(
                                            already_punycode@.index(k)));
                                    }
                                }
                            }
                        }
                        // handled: the tier consumed the label (the
                        // upstream continue at 1205)
                        pos = if le < tail.len() {
                            le + 1
                        } else {
                            tail.len()
                        };
                        if pos == tail.len() {
                            last_done = true;
                        }
                        continue;
                    } else {
                        // the invalid-form punycode label: fail-fast
                        // fires right away; otherwise fall through to
                        // the complex path and rediscover the error in
                        // the mapping window (npa stays false, upstream
                        // 1206-1216)
                        if fail_fast {
                            proof {
                                assert(label.len() > 0);
                                assert((pos as int) < (le as int));
                                assert(le as int
                                    <= tail_ghost.len() as int);
                                assert(domain_name.len()
                                    >= tail_ghost.len());
                                assert(domain_name.len() > 0);
                            }
                            return (0, false, true);
                        }
                    }
                } else {
                    npa = true;
                }
            }
            // ---- the ASCII deny push (uts46.rs:1218-1230)
            proof {
                assert forall |q: int| #![trigger ascii[q]]
                    0 <= q < ascii.len() as int
                    implies ascii[q] < 0x80 by {
                    if 0 <= q && q < ascii.len() as int {
                        assert(ascii[q] == label[q]);
                    }
                }
            }
            proof {
                // the deny push require: the ASCII prefix of a tail
                // split item holds no separator byte
                assert forall |q: int| #![trigger ascii[q]]
                    0 <= q < ascii.len() as int
                    implies ascii[q] != b'.' by {
                    assert(ascii[q] == label[q]);
                }
            }
            let (fired_p, saw_p) = pim_ascii_deny_push(
                domain_buffer, ascii, 0, deny, fail_fast,
            );
            if fired_p {
                proof {
                    assert(fail_fast);
                    assert(label.len() > 0);
                    assert((pos as int) < (le as int));
                    assert((le as int) <= tail_ghost.len() as int);
                    assert(domain_name.len() >= tail_ghost.len());
                    assert(domain_name.len() > 0);
                }
                return (0, false, true);
            }
            proof {
                if fail_fast {
                    // the clean fail-fast completion met no model FFFD,
                    // so the saw channel is false and the had register
                    // keeps the invariant
                    lemma_ascii_fffd_none_implies_none(
                        ascii, deny, 0, ascii.len() as int);
                    assert(ascii_map_has_fffd(
                        ascii, deny, 0, ascii.len() as int) == false);
                    assert(saw_p == false);
                }
            }
            had = had || saw_p;
            if npa {
                // ---- pure-ASCII tier (uts46.rs:1231-1247)
                let allow: bool = match hyphens {
                    Hyphens::Allow => true,
                    _ => false,
                };
                if !allow {
                    let a34: bool = match hyphens {
                        Hyphens::CheckFirstLast => true,
                        _ => false,
                    };
                    let fired_h = pim_check_hyphens_dom(
                        domain_buffer, cls, a34, fail_fast, &mut had,
                    );
                    if fired_h {
                        proof {
                            assert(fail_fast);
                            assert(label.len() > 0);
                            assert((pos as int) < (le as int));
                            assert(le as int
                                <= tail_ghost.len() as int);
                            assert(domain_name.len()
                                >= tail_ghost.len());
                            assert(domain_name.len() > 0);
                        }
                        return (0, false, true);
                    }
                }
                let ghost pt: Seq<AlreadyAsciiLabel<'a>>
                    = already_punycode@;
                proof {
                    assert(last_done == false);
                    // the pre-push fold tip through the head snapshot
                    assert(pt == head_tags);
                    // the two lanes of the head gate
                    if head_in_prefix {
                        // the leave-iteration lane: the pristine channel
                        // still holds -- the rope is the empty entry rope
                        // and the fold sits at the consumed prefix
                        // boundary (one definitional step of the fold;
                        // the deny scan of this same iteration may already
                        // have marked, so both push branches stay live)
                        assert(already_punycode@ == tags_entry);
                        assert(pt.len() as int == 0);
                        assert(tile_live == true);
                        assert(ptu as int == dn_off as int + pos as int);
                        reveal_with_fuel(align_cell_a, 1);
                        assert(align_cell_a(pt, pt.len() as int,
                            ptu as int) == ptu as int);
                    } else {
                        // the later-iteration lane: the invariant gate is
                        // live at the head
                    }
                    // the label-scan geometry (the payload value equality
                    // and the separator-or-end evidence)
                    lemma_raw_label_tiled(domain_name@, tail_ghost,
                        dn_off as int, pos as int, le as int, label);
                    if tile_live {
                        assert(align_cell_a(pt, pt.len() as int,
                            ptu as int) == dn_off as int + pos as int);
                    } else {
                        assert(align_cell_a(pt, pt.len() as int,
                            ptu as int) == -1);
                    }
                    assert(aligned_payload(domain_name@, label@,
                        align_cell_a(pt, pt.len() as int, ptu as int)));
                    // E-TILE: the push envelope, stated before the push
                    // so the loop invariants are in force over the
                    // untouched rope (the Other sentinel kills the chain
                    // and poisons the tip; the clean channel's
                    // MixedCaseAscii cell tiles the raw label window)
                    if had {
                        lemma_tile_push_cell(domain_name@, pt,
                            AlreadyAsciiLabel::Other, ptu as int);
                    } else {
                        lemma_tile_push_cell(domain_name@, pt,
                            AlreadyAsciiLabel::MixedCaseAscii(label),
                            ptu as int);
                    }
                }
                if had {
                    already_punycode
                        .push(AlreadyAsciiLabel::Other);
                    tile_live = false;
                } else {
                    already_punycode.push(
                        AlreadyAsciiLabel::MixedCaseAscii(label));
                }
                proof {
                    assert(already_punycode@.len()
                        == pt.len() + 1);
                    // the pushed tag holds this all-ASCII label (the
                    // pure-ASCII tier) or the Other sentinel
                    assert(tag_payload_ascii(
                        already_punycode@.index(
                            already_punycode@.len() as int - 1)));
                    assert forall |i: int|
                        #![trigger already_punycode@.index(i)]
                        tags_entry.len() as int
                            <= i < already_punycode@.len() as int
                        implies tag_payload_ascii(
                            already_punycode@.index(i)) by {
                        if tags_entry.len() as int <= i
                            && i < already_punycode@.len() as int {
                            if i < (already_punycode@.len() as int - 1) {
                            } else {
                                assert(already_punycode@.index(i)
                                    == if had {
                                        AlreadyAsciiLabel::Other
                                    } else {
                                        AlreadyAsciiLabel::
                                            MixedCaseAscii(label)
                                    });
                            }
                        }
                    }
                }
                pos = if le < tail.len() {
                    le + 1
                } else {
                    tail.len()
                };
                if pos == tail.len() {
                    last_done = true;
                }
                continue;
            }
            // ---- the mapping window tier (uts46.rs:1249-1361)
            let ghost ptw: Seq<AlreadyAsciiLabel<'a>>
                = already_punycode@;
            proof {
                // the two lanes of the head gate for the push envelope's
                // family requirement
                if head_in_prefix {
                    // the leave-iteration lane: the pristine rope is the
                    // empty entry rope, so the family is vacuous
                    assert(already_punycode@ == tags_entry);
                    assert(ptw.len() as int == 0);
                } else {
                    // the later-iteration lane: the invariant family
                    // applies at the live gate
                }
                // E-TILE: the Other sentinel kills the chain and poisons
                // the fold tip to -1 (stated before the push so the loop
                // invariants are in force over the untouched rope)
                lemma_tile_push_cell(domain_name@, ptw,
                    AlreadyAsciiLabel::Other, ptu as int);
            }
            already_punycode.push(AlreadyAsciiLabel::Other);
            // the mapping window's per-label tag is the Other sentinel:
            // the alignment chain dies here (the sink walk flushes its
            // prefix register at the first Other-tagged label)
            tile_live = false;
            proof {
                assert(already_punycode@ == ptw.push(
                    AlreadyAsciiLabel::Other));
                assert(already_punycode@.len() == ptw.len() + 1);
                assert(tag_payload_ascii(already_punycode@.index(
                    already_punycode@.len() as int - 1)));
            }
            let fncc_in: bool = ascii.len() == 0;
            let ncc_in: bool = non_ascii.len() != 0;
            // the mapped feed: the lossy decoder over the non-ASCII
            // suffix, the whole-sequence P5 mapping, then the
            // per-position deny application (the documented batch-E
            // decomposition of the fused upstream iterator)
            let lossy = utf8_lossy_chars(non_ascii);
            let stage0 = adapter_map_normalize(lossy.as_slice());
            let mut mapped: Vec<char> = Vec::new();
            let mut mi: usize = 0;
            while mi < stage0.len()
                invariant
                    mi <= stage0.len(),
                    mapped@.len() == mi,
                    forall |j: int| 0 <= j < mi as int
                        ==> mapped@.index(j)
                            == deny_apply_model(stage0@[j], deny),
                decreases stage0.len() - mi
            {
                let c0 = stage0[mi];
                let c1 = apply_ascii_deny_list_to_lower_cased_unicode(
                    c0, deny);
                proof {
                    assert(c1 == deny_apply_model(c0, deny));
                }
                let ghost pm: Seq<char> = mapped@;
                mapped.push(c1);
                proof {
                    vstd::seq::lemma_seq_push_len(pm, c1);
                    assert(mapped@ == pm.push(c1));
                    assert(mapped@.len() == pm.len() + 1);
                    assert forall |j: int|
                        #![trigger mapped@.index(j)]
                        0 <= j < mapped@.len() as int
                        implies mapped@.index(j)
                            == deny_apply_model(stage0@[j], deny) by {
                        if 0 <= j && j < mapped@.len() as int {
                            if j == mi as int {
                                assert(mapped@.index(j) == c1);
                                assert(c1
                                    == deny_apply_model(
                                        stage0@[j], deny));
                            } else {
                                assert(j < mi as int);
                                assert(mapped@.index(j)
                                    == pm.index(j));
                                assert(pm.index(j)
                                    == deny_apply_model(
                                        stage0@[j], deny));
                            }
                        }
                    }
                    assert((mi + 1) as int == mapped@.len() as int);
                }
                mi = mi + 1;
            }
            let ghost t_pre_w: Seq<AlreadyAsciiLabel<'a>>
                = already_punycode@;
            proof {
                // the pre-window tiling state, captured while it is in
                // force over the untouched rope: the family from the
                // Other push's envelope above, and the poisoned tip
                assert(t_pre_w == ptw.push(AlreadyAsciiLabel::Other));
                assert(forall |j: int|
                    0 <= j < t_pre_w.len() as int
                    ==> align_cell_ok(domain_name@, t_pre_w, j,
                        ptu as int));
                assert(align_cell_a(t_pre_w, t_pre_w.len() as int,
                    ptu as int) == -1);
            }
            proof {
                // the window requires (re-derived inside the loop body):
                // the deny-dot image fact, and the label window holding
                // the deny-mapped ASCII prefix, dot-free
                lemma_bit_is_set_dot_or(deny);
                assert(deny_dot == deny | DOT_MASK);
                assert(bit_is_set(deny_dot, b'.'));
                assert(cls as int == b1_buf.len() as int);
                assert(domain_buffer@ == b1_buf.add(
                    ascii_deny_map_from(ascii, deny, 0)));
                assert(ascii_deny_map_from(ascii, deny, 0)
                    == ascii_deny_map_range(ascii, deny, 0,
                        ascii.len() as int));
                assert forall |q: int| #![trigger domain_buffer@.index(q)]
                    cls as int <= q < domain_buffer@.len() as int
                    implies domain_buffer@.index(q) != '.' by {
                    lemma_ascii_map_range_not_dot(ascii, deny, 0,
                        ascii.len() as int);
                    if cls as int <= q
                        && q < domain_buffer@.len() as int {
                        assert((q - b1_buf.len() as int) >= 0);
                        assert((q - b1_buf.len() as int)
                            < ascii_deny_map_range(ascii, deny, 0,
                                ascii.len() as int).len() as int) by {
                            vstd::seq::lemma_seq_add_len(b1_buf,
                                ascii_deny_map_from(ascii, deny, 0));
                        }
                        vstd::seq::lemma_seq_add_index2(b1_buf,
                            ascii_deny_map_from(ascii, deny, 0), q);
                    }
                }
            }
            let (fired_w, had_w) = pim_map_window(
                deny_dot, hyphens, fail_fast, mapped.as_slice(),
                domain_buffer, already_punycode, had, cls,
                fncc_in, ncc_in,
            );
            proof {
                if fail_fast {
                    assert(had_w == had);
                }
                // the window appended an Other-filled block below the
                // preserved prefix: compose the channel over the whole
                // extended range
                let ghost blk_w: Seq<AlreadyAsciiLabel<'a>> = Seq::new(
                    (already_punycode@.len() - t_pre_w.len()) as nat,
                    |k: int| AlreadyAsciiLabel::Other);
                assert(already_punycode@ == t_pre_w.add(blk_w));
                vstd::seq::lemma_seq_add_len(t_pre_w, blk_w);
                assert forall |i: int|
                    #![trigger already_punycode@.index(i)]
                    tags_entry.len() as int
                        <= i < already_punycode@.len() as int
                    implies tag_payload_ascii(already_punycode@.index(i)) by {
                    if tags_entry.len() as int <= i
                        && i < already_punycode@.len() as int {
                        if i < t_pre_w.len() as int {
                            // a preserved cell: the pre-call content, by
                            // the add prefix and the in-place channel
                            vstd::seq::lemma_seq_add_index1(
                                t_pre_w, blk_w, i);
                            if i < ptw.len() as int {
                                // the loop-invariant cell (the head range)
                            } else {
                                // the tier's own Other cell
                                assert(i == ptw.len() as int);
                                assert(t_pre_w == ptw.push(
                                    AlreadyAsciiLabel::Other));
                                vstd::seq::lemma_seq_push_index_same(
                                    ptw, AlreadyAsciiLabel::Other, i);
                            }
                        } else {
                            // a window-added cell: Other
                            vstd::seq::lemma_seq_add_index2(
                                t_pre_w, blk_w, i);
                            vstd::seq::lemma_seq_new_index(
                                blk_w.len() as nat,
                                |k: int| AlreadyAsciiLabel::Other,
                                i - t_pre_w.len() as int);
                        }
                    }
                }
                // E-TILE: the window's Other-filled append keeps the
                // front obligations (the append-front fold stability) and
                // adds only vacuous Other cells; the (already poisoned)
                // fold tip stays -1 on both block shapes
                assert(t_pre_w == ptw.push(AlreadyAsciiLabel::Other));
                assert forall |k: int|
                    #![trigger tile_other_cell(blk_w.index(k))]
                    0 <= k < blk_w.len() as int
                    implies tile_other_cell(blk_w.index(k)) by {
                    if 0 <= k && k < blk_w.len() as int {
                        vstd::seq::lemma_seq_new_index(
                            blk_w.len() as nat,
                            |i: int| AlreadyAsciiLabel::Other, k);
                    }
                }
                lemma_tile_append_others(domain_name@, t_pre_w, blk_w,
                    ptu as int);
                if blk_w.len() as int == 0 {
                    lemma_align_cell_a_append_front(t_pre_w, blk_w,
                        t_pre_w.len() as int, ptu as int);
                    assert(align_cell_a(t_pre_w.add(blk_w),
                        t_pre_w.len() as int, ptu as int) == -1);
                }
            }
            had = had_w;
            if fired_w {
                proof {
                    assert(fail_fast);
                    assert(label.len() > 0);
                    assert((pos as int) < (le as int));
                    assert((le as int) <= tail_ghost.len() as int);
                    assert(domain_name.len() >= tail_ghost.len());
                    assert(domain_name.len() > 0);
                }
                return (0, false, true);
            }
        } else {
            // ---- the empty label (uts46.rs:1379-1382)
            let ghost pte: Seq<AlreadyAsciiLabel<'a>>
                = already_punycode@;
            proof {
                assert(last_done == false);
                // the pre-push fold tip through the head snapshot
                assert(pte == head_tags);
                // the raw geometry: an empty label at this arm always
                // sits on a separator position (the scan exit evidence;
                // the position itself is the whole raw span)
                lemma_raw_label_tiled(domain_name@, tail_ghost,
                    dn_off as int, pos as int, le as int, label);
                if tile_live {
                    assert(align_cell_a(pte, pte.len() as int,
                        ptu as int) == dn_off as int + pos as int);
                } else {
                    assert(align_cell_a(pte, pte.len() as int,
                        ptu as int) == -1);
                }
                assert(aligned_payload(domain_name@, label@,
                    align_cell_a(pte, pte.len() as int, ptu as int)));
                // E-TILE: the empty MixedCaseAscii cell tiles the (empty)
                // raw window at the fold tip (stated before the push so
                // the loop invariants are in force over the untouched
                // rope)
                lemma_tile_push_cell(domain_name@, pte,
                    AlreadyAsciiLabel::MixedCaseAscii(label), ptu as int);
            }
            already_punycode
                .push(AlreadyAsciiLabel::MixedCaseAscii(label));
            proof {
                assert(already_punycode@ == pte.push(
                    AlreadyAsciiLabel::MixedCaseAscii(label)));
                assert(already_punycode@.len() == pte.len() + 1);
                // the empty label payload is vacuously ASCII
                assert forall |q: int| #![trigger label[q]]
                    0 <= q < label.len() as int
                    implies label[q] < 0x80 by {
                    if 0 <= q && q < label.len() as int {
                        assert(label.len() as int == 0);
                    }
                }
                assert(tag_payload_ascii(already_punycode@.index(
                    already_punycode@.len() as int - 1)));
                assert forall |i: int|
                    #![trigger already_punycode@.index(i)]
                    tags_entry.len() as int
                        <= i < already_punycode@.len() as int
                    implies tag_payload_ascii(already_punycode@.index(i)) by {
                    if tags_entry.len() as int <= i
                        && i < already_punycode@.len() as int {
                        if i < (already_punycode@.len() as int - 1) {
                        } else {
                            assert(already_punycode@.index(i)
                                == AlreadyAsciiLabel::MixedCaseAscii(label));
                        }
                    }
                }
            }
        }
        pos = if le < tail.len() {
            le + 1
        } else {
            tail.len()
        };
        if pos == tail.len() {
            last_done = true;
        }
    }
    // ---- the is_bidi scan and the CheckBidi post-pass (uts46.rs:1385-1493)
    let bidi_scan = is_bidi(domain_buffer.as_slice());
    let ghost pre_scan: Seq<char> = domain_buffer@;
    proof {
        assert(bidi_scan == has_rtl_from(pre_scan, 0));
    }
    if bidi_scan {
        let fired_m = bidi_marking_pass(
            domain_buffer, fail_fast, &mut had,
        );
        if fired_m {
            proof {
                assert(fail_fast);
                // the fail-fast marking channel leaves the buffer as it
                // was scanned
                assert(domain_buffer@ == pre_scan);
                if in_prefix {
                    // the pristine prefix kept the (entry-empty) buffer
                    // empty, so the scan saw the empty buffer and could
                    // not report bidi: this exit is unreachable
                    assert(domain_buffer@ == buf_entry);
                    assert(buf_entry.len() == 0);
                    has_rtl_step_lemma(pre_scan, 0);
                    assert(has_rtl_from(pre_scan, 0) == false);
                    assert(bidi_scan == false);
                    assert(false);
                } else {
                    // past the prefix freeze the passthrough counter is
                    // strictly below the domain end: the domain is
                    // nonempty
                    assert((ptu as int)
                        < domain_name.len() as int);
                    assert(domain_name.len() > 0);
                }
            }
            return (0, false, true);
        }
    }
    proof {
        if in_prefix {
            // the whole tail passed through: nothing was written and the
            // buffer stayed at its (entry-empty) value
            assert(domain_buffer@ == buf_entry);
            assert(ptu as int == dn_off as int + pos as int);
            assert(pos as int <= tail_ghost.len() as int);
            assert(dn_off as int + tail_ghost.len() as int
                == domain_name.len() as int);
            assert(ptu as int <= domain_name.len() as int);
            if ptu as int == domain_name.len() as int {
                // the pristine passthrough return channel
                assert(domain_buffer@ == old(domain_buffer)@);
                assert(already_punycode@ == tags_entry);
                assert(already_punycode@ == old(already_punycode)@);
                assert(had == false);
                has_rtl_step_lemma(pre_scan, 0);
                assert(has_rtl_from(pre_scan, 0) == false);
                assert(bidi_scan == false);
            }
        } else {
            assert((ptu as int) < domain_name.len() as int);
        }
        // the E-TILE ensure: past the prefix the per-cell family is the
        // loop invariant at the returned boundary; on the pristine
        // passthrough channel the entry tag rope is empty (the
        // single-caller geometry), so the range is vacuous
        if in_prefix == false {
            assert forall |j: int|
                #![trigger align_cell_ok(domain_name@,
                    already_punycode@, j, ptu as int)]
                0 <= j < already_punycode@.len() as int
                implies align_cell_ok(domain_name@,
                    already_punycode@, j, ptu as int) by {
            }
        } else {
            assert(already_punycode@ == tags_entry);
            assert(tags_entry.len() as int == 0);
        }
    }
    (ptu, bidi_scan, had)
}

//// The ASCII fast-path wrapper process_inner (uts46.rs:773-826): the
//// all-fast-byte input (lower-case ASCII letters and dots) passes
//// through on the fastest path; otherwise the scan defers to
//// process_innermost with the tail from the most recent label start
//// (index 0, or one past the most recent dot). The upstream
//// iterator/clone snapshot state is transcribed as the
//// process_inner_ascii_scan defer index (the functional
//// most-recent-label-start model). The passthrough return of the whole
//// domain (the fast pass) has the same channel shape as the innermost
//// pristine channel.
////
//// ASCII prefix channel (composed for the sink pass): every byte before
//// the returned passthrough boundary is pure ASCII: [0, idx) by the
//// fast scan, [idx, ptu) by the innermost passthrough-tier channel.
fn process_inner<'a>(
    domain_name: &'a [u8],
    ascii_deny_list: AsciiDenyList,
    hyphens: Hyphens,
    fail_fast: bool,
    domain_buffer: &mut Vec<char>,
    already_punycode: &mut Vec<AlreadyAsciiLabel<'a>>,
) -> (ret: (usize, bool, bool))
    requires
        old(domain_buffer)@.len() == 0,
        // upstream geometry (uts46.rs:784-786: process forwards fresh
        // SmallVecs into process_inner): the tag vector enters empty
        // here too, anchoring the sink-walk tiling channel at this
        // single entry boundary
        old(already_punycode)@.len() == 0,
    ensures
        ret.0 <= domain_name.len(),
        // the consumed prefix is pure ASCII (the sink pass re-emits the
        // passthrough prefix bytes directly as chars)
        forall |p: int| 0 <= p < ret.0 as int
            ==> domain_name[p] < 0x80,
        // every tag added holds a pure-ASCII payload or the Other
        // sentinel
        forall |i: int| old(already_punycode)@.len() as int
            <= i < final(already_punycode)@.len() as int
            ==> tag_payload_ascii(final(already_punycode)@.index(i)),
        // the fired channel is fail-fast only, with the passthrough
        // counter reset
        fail_fast && ret.2 == true ==> (ret.0 == 0 && ret.1 == false),
        fail_fast ==> ret.2 == false || (ret.0 == 0 && ret.1 == false),
        fail_fast && ret.2 == true ==> domain_name.len() > 0,
        // the pristine passthrough channel
        ret.0 == domain_name.len()
            ==> (final(domain_buffer)@ == old(domain_buffer)@
                && final(already_punycode)@ == old(already_punycode)@
                && ret.1 == false
                && ret.2 == false),
        final(domain_buffer)@.len() >= old(domain_buffer)@.len(),
        forall |p: int| 0 <= p < old(domain_buffer)@.len() as int
            ==> final(domain_buffer)@.index(p) == old(domain_buffer)@.index(p),
        final(already_punycode)@.len() >= old(already_punycode)@.len(),
        // the sink-walk tiling (E-TILE), propagated from the innermost
        // call (the fast pass adds no tags: the range is vacuous there)
        ret.2 == false || !fail_fast ==>
            forall |j: int|
                0 <= j < final(already_punycode)@.len() as int
                ==> align_cell_ok(domain_name@,
                    final(already_punycode)@, j, ret.0 as int),
{
    let scan = process_inner_ascii_scan(domain_name);
    match scan {
        FastPathScan::FastPathPass => {
            // the fastest path: the whole input passes through
            (domain_name.len(), false, false)
        }
        FastPathScan::FastPathDefer(idx) => {
            let tail: &'a [u8] = &domain_name[idx..];
            proof {
                // the tail is the suffix slice; the innermost geometry
                // requires hold by the scan channels
                assert(idx <= domain_name.len());
                assert(tail@.len() == domain_name.len() - idx);
                assert(tail@ == domain_name@.subrange(
                    idx as int, domain_name.len() as int));
                // the [0, idx) prefix is fast (hence ASCII): every byte
                // before the first non-fast byte is fast
                first_non_fast_prefix_fast(domain_name, 0);
                assert forall |p: int| #![trigger domain_name[p]]
                    0 <= p < idx as int
                    implies domain_name[p] < 0x80 by {
                    if 0 <= p && p < idx as int {
                        assert(is_fast_byte(domain_name[p]));
                    }
                }
            }
            let (ptu, is_bd, had_e) = process_innermost(
                domain_name, ascii_deny_list, hyphens, fail_fast,
                domain_buffer, already_punycode, tail,
            );
            proof {
                // the composed prefix-ASCII channel: [0, idx) from the
                // scan (ASCII), [idx, ptu) from the innermost
                // passthrough-tier channel
                assert forall |p: int| #![trigger domain_name[p]]
                    0 <= p < ptu as int
                    implies domain_name[p] < 0x80 by {
                    if 0 <= p && p < ptu as int {
                        if p < idx as int {
                        } else {
                            assert(p >= idx as int);
                        }
                    }
                }
            }
            (ptu, is_bd, had_e)
        }
    }
}




} // verus!

fn main() {}
