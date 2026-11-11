//! harness: wpt sample theorems for the parse entry (src zone: ../src/lib.rs)
//!
//! Data-driven sampling of the WPT corpus (code/url/tests/urltestdata.json,
//! 869 records): the sampled records become verus assertion theorems over
//! the verified parse entry and the parser's own assembly faces. The
//! sampling is class-restricted (the batch-C discipline, every narrowing
//! spelled here):
//!
//! - authority samples (wn_auth_class): lowercase-letter scheme (special
//!   or non-special, pinned per sample), "://", a letter host run in the
//!   in-tree host_split_form sense (no '@', no '%', no brackets -- the
//!   idna and ipv6 deep-water faces stay outside), an arbitrary ASCII
//!   tail. Per-sample faces: the entry-face certificate (Url::parse
//!   admission), the Ok-branch structural invariant, the
//!   authority-region serialization face (the drive returns the exact
//!   scheme+"://"+host bytes the assembly writes), and the full-chain
//!   invariant face (the wrap-up Ok branch, conditional on the wrap-up's
//!   exported Overflow-only error face). Port samples (":815" etc.) take
//!   the serialization face only: the default-port rewrite happens
//!   behind the parse_host_and_port wrapper the drive does not cross.
//! - anarchist samples (wn_anar_class): non-special scheme without the
//!   "//" authority form -- the entry face's NotSpecial arm is the
//!   vacuous "//"-conditional; parse + Ok-branch invariant.
//! - file samples (wn_file_class): the "file" scheme over the wall-split
//!   class the in-tree file_state_entry_face names; parse + Ok-branch
//!   invariant.
//! - bare samples (wn_bare_class): the "//"-led no-scheme records (the
//!   entry face's scheme-grammar antecedent is false on them); parse +
//!   error-disjunction face.
//!
//! Sample provenance: every sampled input is a verbatim record of
//! urltestdata.json (success-expected). Reference-style organization:
//! `#[path]` includes verified/src/lib.rs; no spec or lemma copies from
//! the src zone.

#[path = "../src/lib.rs"]
mod urllib;

use urllib::*;
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use {
    vstd::seq::group_seq_lemmas,
    vstd::std_specs::vec::group_vec_axioms,
    vstd::slice::group_slice_axioms,
    vstd::std_specs::vec::lemma_vec_obeys_view_eq::<u8>,
};

fn main() {}

/* ------------------------------------------------------------
 * The sampled classes
 * ------------------------------------------------------------ */

/// The authority sample split: lowercase scheme (k bytes, not "file"),
/// ':' at k, the "//", and a letter host run of length h (>= 1) in the
/// in-tree host_split_form sense (the run classed, the terminator byte
/// at h), with no '@' anywhere in the post-"//" tail (the userinfo
/// peel's no-write arm).
pub open spec fn wn_auth_split(s: Seq<u8>, k: int, h: int, special: bool) -> bool {
    &&& 1 <= k
    &&& 1 <= h
    &&& k + 3 + h <= (s.len() as int)
    &&& (forall|i: int| #![trigger s.index(i)]
            0 <= i < k ==> 0x61 <= s.index(i) <= 0x7A)
    &&& s.index(k) == 0x3Au8
    &&& s.index(k + 1) == 0x2Fu8
    &&& s.index(k + 2) == 0x2Fu8
    &&& ({
        let st = parser::scheme_type_of(parser::lowered_prefix(s.subrange(0, k), k));
        &&& st != parser::SchemeType::File
        &&& parser::is_special(st) == special
    })
    &&& parser::host_split_form(s.subrange(k + 3, (s.len() as int)), h, special)
    &&& (forall|i: int| #![trigger s.index(i)]
            k + 3 <= i < (s.len() as int) ==> s.index(i) != 0x40u8)
}

pub open spec fn wn_auth_class(s: Seq<u8>, special: bool) -> bool {
    &&& parser::machine_domain(s)
    &&& 20 * (s.len() as int) + 400 <= 0xFFFF_FFFF
    &&& (exists|k: int, h: int| wn_auth_split(s, k, h, special))
}

/// The anarchist sample split: lowercase non-special scheme, ':' at k,
/// and a tail that does not open with the "//" authority form (the
/// entry face's NotSpecial arm is then the vacuous "//"-conditional).
pub open spec fn wn_anar_split(s: Seq<u8>, k: int) -> bool {
    &&& 1 <= k
    &&& k + 1 <= (s.len() as int)
    &&& (forall|i: int| #![trigger s.index(i)]
            0 <= i < k ==> 0x61 <= s.index(i) <= 0x7A)
    &&& s.index(k) == 0x3Au8
    &&& parser::scheme_type_of(parser::lowered_prefix(s.subrange(0, k), k))
        == parser::SchemeType::NotSpecial
    &&& ({
        let rem2 = s.subrange(k + 1, (s.len() as int));
        &&& ((rem2.len() as int) < 2
            || rem2.index(0) != 0x2Fu8
            || rem2.index(1) != 0x2Fu8)
    })
}

pub open spec fn wn_anar_class(s: Seq<u8>) -> bool {
    &&& parser::machine_domain(s)
    &&& 20 * (s.len() as int) + 400 <= 0xFFFF_FFFF
    &&& (exists|k: int| wn_anar_split(s, k))
}

/// The file sample split: the "file" scheme over a tail admitted by the
/// in-tree file_state_entry_face (the wall-split class of the file-host
/// scan).
pub open spec fn wn_file_split(s: Seq<u8>, k: int) -> bool {
    &&& 1 <= k
    &&& k + 1 <= (s.len() as int)
    &&& (forall|i: int| #![trigger s.index(i)]
            0 <= i < k ==> 0x61 <= s.index(i) <= 0x7A)
    &&& s.index(k) == 0x3Au8
    &&& parser::scheme_type_of(parser::lowered_prefix(s.subrange(0, k), k))
        == parser::SchemeType::File
    &&& parser::file_state_entry_face(s.subrange(k + 1, (s.len() as int)))
}

pub open spec fn wn_file_class(s: Seq<u8>) -> bool {
    &&& parser::machine_domain(s)
    &&& 20 * (s.len() as int) + 400 <= 0xFFFF_FFFF
    &&& (exists|k: int| wn_file_split(s, k))
}

/// The bare sample class: the "//"-led no-scheme records -- the entry
/// face's scheme-grammar antecedent (an alpha scheme head) is false on
/// every split.
pub open spec fn wn_bare_class(s: Seq<u8>) -> bool {
    &&& parser::machine_domain(s)
    &&& 20 * (s.len() as int) + 400 <= 0xFFFF_FFFF
    &&& 1 <= (s.len() as int)
    &&& 0x20u8 < s.index(0)
    &&& !urllib::is_ascii_alpha(s.index(0))
}

/* ------------------------------------------------------------
 * The shared grammar shape and its uniqueness
 * ------------------------------------------------------------ */

pub open spec fn wn_shape(s: Seq<u8>, k: int) -> bool {
    &&& 1 <= k
    &&& k <= (s.len() as int)
    &&& urllib::is_ascii_alpha(s.index(0))
    &&& (forall|j: int| 1 <= j < k ==> urllib::is_scheme_char(s.index(j)))
    &&& s.index(k) == 0x3Au8
}

proof fn wn_shape_unique(s: Seq<u8>, k1: int, k2: int)
    requires
        wn_shape(s, k1),
        wn_shape(s, k2),
    ensures
        k1 == k2,
{
    if k1 < k2 {
        assert(1 <= k1 < k2);
        assert(urllib::is_scheme_char(s.index(k1)));
        assert(s.index(k1) == 0x3Au8);
        assert(!urllib::is_scheme_char(0x3Au8));
        assert(false);
    } else if k2 < k1 {
        assert(1 <= k2 < k1);
        assert(urllib::is_scheme_char(s.index(k2)));
        assert(s.index(k2) == 0x3Au8);
        assert(!urllib::is_scheme_char(0x3Au8));
        assert(false);
    }
}

proof fn wn_shape_of_auth(s: Seq<u8>, k: int, h: int, special: bool)
    requires
        wn_auth_split(s, k, h, special),
    ensures
        wn_shape(s, k),
{
    assert forall|j: int| 1 <= j < k implies urllib::is_scheme_char(s.index(j)) by {
        assert(0x61 <= s.index(j) <= 0x7A);
    }
    assert(urllib::is_ascii_alpha(s.index(0)));
}

proof fn wn_shape_of_anar(s: Seq<u8>, k: int)
    requires
        wn_anar_split(s, k),
    ensures
        wn_shape(s, k),
{
    assert forall|j: int| 1 <= j < k implies urllib::is_scheme_char(s.index(j)) by {
        assert(0x61 <= s.index(j) <= 0x7A);
    }
    assert(urllib::is_ascii_alpha(s.index(0)));
}

proof fn wn_shape_of_file(s: Seq<u8>, k: int)
    requires
        wn_file_split(s, k),
    ensures
        wn_shape(s, k),
{
    assert forall|j: int| 1 <= j < k implies urllib::is_scheme_char(s.index(j)) by {
        assert(0x61 <= s.index(j) <= 0x7A);
    }
    assert(urllib::is_ascii_alpha(s.index(0)));
}

/// The authority sample's (k, h) is unique (the grammar split by the
/// ':' argument, the host run by the in-tree host_split uniqueness).
proof fn wn_auth_split_unique(s: Seq<u8>, k1: int, h1: int, k2: int, h2: int, special: bool)
    requires
        wn_auth_split(s, k1, h1, special),
        wn_auth_split(s, k2, h2, special),
    ensures
        k1 == k2,
        h1 == h2,
{
    wn_shape_of_auth(s, k1, h1, special);
    wn_shape_of_auth(s, k2, h2, special);
    wn_shape_unique(s, k1, k2);
    let tail = s.subrange(k1 + 3, (s.len() as int));
    assert(parser::host_split_form(tail, h1, special));
    assert(parser::host_split_form(tail, h2, special));
    parser::host_split_unique(tail, special, h1, h2);
}


/* ------------------------------------------------------------
 * The entry-face certificates (thin: the per-split arm work lives in
 * the split helpers, mirroring the round-trip harness structure)
 * ------------------------------------------------------------ */

/// The grammar shape admits no second ':' (a lowercase-letter prefix
/// carries none, and the '/' at k+1 is not a scheme char, cutting all
/// longer candidates).
proof fn wn_other_splits(s: Seq<u8>, k: int)
    requires
        wn_shape(s, k),
    ensures
        (forall|kk: int|
            #![trigger s.subrange(kk, s.len() as int)]
            (0 <= kk)
                && (kk + 1 <= (s.len() as int))
                && ((s.subrange(kk, s.len() as int).len() as int)
                    <= (s.len() as int))
                && urllib::is_ascii_alpha(s.index(0))
                && (forall|j: int| 1 <= j < kk
                    ==> urllib::is_scheme_char(s.index(j)))
                && s.index(kk) == 0x3Au8
            ==> kk == k),
{
    assert forall|kk: int|
        #![trigger s.subrange(kk, s.len() as int)]
        (0 <= kk)
            && (kk + 1 <= (s.len() as int))
            && ((s.subrange(kk, s.len() as int).len() as int)
                <= (s.len() as int))
            && urllib::is_ascii_alpha(s.index(0))
            && (forall|j: int| 1 <= j < kk
                ==> urllib::is_scheme_char(s.index(j)))
            && s.index(kk) == 0x3Au8
        implies kk == k by {
        if kk < k {
            assert(0x61 <= s.index(kk) <= 0x7A);
            assert(s.index(kk) != 0x3Au8);
            assert(false);
        } else if kk > k {
            assert(1 <= k < kk);
            assert(urllib::is_scheme_char(s.index(k)));
            assert(!urllib::is_scheme_char(0x3Au8));
            assert(false);
        }
    }
}

/// The three-arm conclusion shape shared by the split helpers (the
/// entry-face implication's body at the helper's own split).
pub open spec fn wn_face_arms(s: Seq<u8>, k: int) -> bool {
    let st = parser::scheme_type_of(
        parser::lowered_prefix(s.subrange(0, k), k));
    let rem2 = s.subrange(k + 1, (s.len() as int));
    (st == parser::SchemeType::File
        ==> (parser::file_state_entry_face(rem2)
            && (k + 1) + 20 * (rem2.len() as int) + 176
                <= 0xFFFF_FFFF))
    && (st == parser::SchemeType::SpecialNotFile
        ==> (forall|c: int|
                #![trigger rem2.subrange(c, rem2.len() as int)]
                (0 <= c && c <= (rem2.len() as int)
                    && ((rem2.subrange(c, rem2.len() as int).len()
                        as int) <= (rem2.len() as int))
                    && parser::slash_run_prefix(rem2, c)
                    && ((c == rem2.len() as int)
                        || (rem2.index(c) != 0x2Fu8
                            && rem2.index(c) != 0x5Cu8)))
                ==> (parser::authority_entry_class(
                        rem2.subrange(c, rem2.len() as int),
                        true)
                    && (k + 1)
                        + 16 * ((rem2.len() as int) - c) + 74
                        <= 0xFFFF_FFFF)))
    && (st == parser::SchemeType::NotSpecial ==> (
        (((rem2.len() as int) >= 2
            && rem2.index(0) == 0x2Fu8
            && rem2.index(1) == 0x2Fu8)
            ==> parser::authority_entry_class(
                rem2.subrange(2, rem2.len() as int), false))
        && (k + 1) + 16 * (rem2.len() as int) + 74
            <= 0xFFFF_FFFF
        && (k + 1) + 11 * (rem2.len() as int) + 30
            <= 0xFFFF_FFFF))
}

/// The authority sample's entry-face arm at its own split: the
/// special / non-special class analysis over the "//" tail (the classed
/// host split is the authority-class witness; the '@' closure is free
/// on the '@'-free tail; the c >= 3 slash-run prefixes die on the host
/// letter head).
#[verifier::rlimit(40)]
proof fn wn_auth_face_split(s: Seq<u8>, k: int, h: int, special: bool)
    requires
        wn_auth_split(s, k, h, special),
        20 * (s.len() as int) + 400 <= 0xFFFF_FFFF,
    ensures
        wn_face_arms(s, k),
{
    let n = (s.len() as int);
    let st = parser::scheme_type_of(parser::lowered_prefix(s.subrange(0, k), k));
    assert(st != parser::SchemeType::File);
    assert(parser::is_special(st) == special);
    assert(0 <= k + 1);
    assert(k + 1 <= n);
    let rem2 = s.subrange(k + 1, n);
    vstd::seq::lemma_seq_subrange_len(s, k + 1, n);
    assert((rem2.len() as int) == n - (k + 1));
    assert(rem2.index(0) == 0x2Fu8);
    assert(rem2.index(1) == 0x2Fu8);
    assert((rem2.len() as int) >= 2);
    let tail = rem2.subrange(2, rem2.len() as int);
    assert(tail == s.subrange(k + 3, n));
    assert(parser::host_split_form(tail, h, special));
    // the authority entry class over the tail (the classed split is the
    // witness; the '@' closure is free on the '@'-free tail)
    assert(parser::host_split_class(tail, special));
    assert(tail.index(0) != 0x40u8) by {
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < (tail.len() as int)
            implies tail.index(j) != 0x40u8 by {
            assert(s.index((k + 3) + j) != 0x40u8);
        }
    }
    assert forall|kk2: int| #![trigger tail.subrange(kk2, tail.len() as int)]
        1 <= kk2 && kk2 < (tail.len() as int)
        && tail.index(kk2) == 0x40u8
        implies parser::host_split_class(
            tail.subrange(kk2 + 1, tail.len() as int), special) by {
        assert(s.index((k + 3) + kk2) != 0x40u8);
        assert(false);
    }
    assert(parser::authority_entry_class(tail, special));
    // the empty-run split witnesses the c = 0 / c = 1 slash-run
    // prefixes (the leading '/' is the terminator of the empty run)
    assert(parser::host_split_form(rem2, 0, special)) by {
        assert(parser::host_run_class(rem2.subrange(0, 0)));
        assert(parser::host_term_byte(rem2.index(0), special));
    }
    assert(parser::host_split_form(rem2.subrange(1, rem2.len() as int), 0, special));
    assert(parser::host_split_class(rem2, special));
    assert(parser::host_split_class(rem2.subrange(1, rem2.len() as int), special));
    assert(parser::host_split_class(rem2.subrange(2, rem2.len() as int), special));
    if special {
        // the special arm: the authority class at every slash-run head
        assert(st == parser::SchemeType::SpecialNotFile);
        assert forall|c: int| #![trigger rem2.subrange(c, rem2.len() as int)]
            (0 <= c && c <= (rem2.len() as int)
                && ((rem2.subrange(c, rem2.len() as int).len() as int)
                    <= (rem2.len() as int))
                && parser::slash_run_prefix(rem2, c)
                && ((c == rem2.len() as int)
                    || (rem2.index(c) != 0x2Fu8
                        && rem2.index(c) != 0x5Cu8)))
            implies (parser::authority_entry_class(
                    rem2.subrange(c, rem2.len() as int), true)
                && (k + 1) + 16 * ((rem2.len() as int) - c) + 74
                    <= 0xFFFF_FFFF) by {
            parser::slash_run_prefix_iff(rem2, c);
            if c <= 2 {
                if c == 2 {
                    assert(parser::authority_entry_class(
                        rem2.subrange(2, rem2.len() as int), true));
                } else {
                    // the empty run against the leading '/' terminator
                    assert(parser::host_split_class(
                        rem2.subrange(c, rem2.len() as int), true));
                    assert(rem2.subrange(c, rem2.len() as int).index(0)
                        == 0x2Fu8);
                    assert(rem2.subrange(c, rem2.len() as int).index(0)
                        != 0x40u8);
                }
            } else {
                // the run would have to cross the host's letter head
                assert(rem2.index(2) != 0x2Fu8 && rem2.index(2) != 0x5Cu8);
                assert(!parser::slash_run_prefix(rem2, c));
                assert(false);
            }
            assert((k + 1) + 16 * ((rem2.len() as int) - c) + 74
                <= 16 * n + 75);
            assert(16 * n + 75 <= 20 * n + 400);
            assert((k + 1) + 16 * ((rem2.len() as int) - c) + 74
                <= 0xFFFF_FFFF);
        }
    } else {
        // the NotSpecial arm: the "//"-conditional is met at c = 2
        assert(st == parser::SchemeType::NotSpecial);
        assert((k + 1) + 16 * (rem2.len() as int) + 74 <= 16 * n + 75);
        assert(16 * n + 75 <= 20 * n + 400);
        assert((k + 1) + 16 * (rem2.len() as int) + 74 <= 0xFFFF_FFFF);
        assert((k + 1) + 11 * (rem2.len() as int) + 30 <= 11 * n + 31);
        assert(11 * n + 31 <= 20 * n + 400);
        assert((k + 1) + 11 * (rem2.len() as int) + 30 <= 0xFFFF_FFFF);
    }
}

/// The anarchist sample's entry-face arm at its own split (the NotSpecial
/// classification with the vacuous "//"-conditional).
proof fn wn_anar_face_split(s: Seq<u8>, k: int)
    requires
        wn_anar_split(s, k),
        20 * (s.len() as int) + 400 <= 0xFFFF_FFFF,
    ensures
        wn_face_arms(s, k),
{
    let n = (s.len() as int);
    let st = parser::scheme_type_of(parser::lowered_prefix(s.subrange(0, k), k));
    assert(st == parser::SchemeType::NotSpecial);
    assert(0 <= k + 1);
    assert(k + 1 <= n);
    let rem2 = s.subrange(k + 1, n);
    vstd::seq::lemma_seq_subrange_len(s, k + 1, n);
    assert((rem2.len() as int) == n - (k + 1));
    assert(((rem2.len() as int) < 2
        || rem2.index(0) != 0x2Fu8
        || rem2.index(1) != 0x2Fu8));
    assert((k + 1) + 16 * (rem2.len() as int) + 74 <= 16 * n + 75);
    assert(16 * n + 75 <= 20 * n + 400);
    assert((k + 1) + 16 * (rem2.len() as int) + 74 <= 0xFFFF_FFFF);
    assert((k + 1) + 11 * (rem2.len() as int) + 30 <= 11 * n + 31);
    assert(11 * n + 31 <= 20 * n + 400);
    assert((k + 1) + 11 * (rem2.len() as int) + 30 <= 0xFFFF_FFFF);
}

/// The file sample's entry-face arm at its own split (the File arm with
/// the wall-split class the sample carried).
proof fn wn_file_face_split(s: Seq<u8>, k: int)
    requires
        wn_file_split(s, k),
        20 * (s.len() as int) + 400 <= 0xFFFF_FFFF,
    ensures
        wn_face_arms(s, k),
{
    let n = (s.len() as int);
    let st = parser::scheme_type_of(parser::lowered_prefix(s.subrange(0, k), k));
    assert(st == parser::SchemeType::File);
    assert(0 <= k + 1);
    assert(k + 1 <= n);
    let rem2 = s.subrange(k + 1, n);
    assert(parser::file_state_entry_face(rem2));
    vstd::seq::lemma_seq_subrange_len(s, k + 1, n);
    assert((rem2.len() as int) == n - (k + 1));
    assert((k + 1) + 20 * (rem2.len() as int) + 176
        <= 20 * n + 400 - 19 * k - 19);
    assert(20 * n + 400 - 19 * k - 19 <= 20 * n + 400);
    assert((k + 1) + 20 * (rem2.len() as int) + 176 <= 0xFFFF_FFFF);
}

/// The authority sample certificate: admission by the verified parse
/// entry (the transcription domain, the u32 length bound, the
/// no-leading-trim premise, and the full entry face).
proof fn wn_auth_certificate(s: Seq<u8>, special: bool)
    requires
        wn_auth_class(s, special),
    ensures
        parser::machine_domain(s),
        (s.len() as int) <= 0xFFFF_FFFF,
        0x20u8 < s.index(0),
        parser::url_parse_entry_face(s),
{
    let (k, h) = choose|kk: int, hh: int| wn_auth_split(s, kk, hh, special);
    wn_shape_of_auth(s, k, h, special);
    let n = (s.len() as int);
    wn_other_splits(s, k);
    wn_auth_face_split(s, k, h, special);
    assert(parser::machine_domain(s));
    assert(0x20u8 < s.index(0));
    assert(parser::url_parse_entry_face(s)) by {
        assert(s.subrange(k, n).len() <= n);
        assert(s.index(k) == 0x3Au8);
    }
}

/// The anarchist sample certificate.
proof fn wn_anar_certificate(s: Seq<u8>)
    requires
        wn_anar_class(s),
    ensures
        parser::machine_domain(s),
        (s.len() as int) <= 0xFFFF_FFFF,
        0x20u8 < s.index(0),
        parser::url_parse_entry_face(s),
{
    let k = choose|kk: int| wn_anar_split(s, kk);
    wn_shape_of_anar(s, k);
    let n = (s.len() as int);
    wn_other_splits(s, k);
    wn_anar_face_split(s, k);
    assert(parser::machine_domain(s));
    assert(0x20u8 < s.index(0));
    assert(parser::url_parse_entry_face(s)) by {
        assert(s.subrange(k, n).len() <= n);
        assert(s.index(k) == 0x3Au8);
    }
}

/// The file sample certificate.
proof fn wn_file_certificate(s: Seq<u8>)
    requires
        wn_file_class(s),
    ensures
        parser::machine_domain(s),
        (s.len() as int) <= 0xFFFF_FFFF,
        0x20u8 < s.index(0),
        parser::url_parse_entry_face(s),
{
    let k = choose|kk: int| wn_file_split(s, kk);
    wn_shape_of_file(s, k);
    let n = (s.len() as int);
    wn_other_splits(s, k);
    wn_file_face_split(s, k);
    assert(parser::machine_domain(s));
    assert(0x20u8 < s.index(0));
    assert(parser::url_parse_entry_face(s)) by {
        assert(s.subrange(k, n).len() <= n);
        assert(s.index(k) == 0x3Au8);
    }
}

/// The bare sample certificate: the entry face's scheme-grammar
/// antecedent is false on the non-alpha head.
proof fn wn_bare_certificate(s: Seq<u8>)
    requires
        wn_bare_class(s),
    ensures
        parser::machine_domain(s),
        (s.len() as int) <= 0xFFFF_FFFF,
        0x20u8 < s.index(0),
        parser::url_parse_entry_face(s),
{
    let n = (s.len() as int);
    assert(parser::machine_domain(s));
    assert(0x20u8 < s.index(0));
    assert(!urllib::is_ascii_alpha(s.index(0)));
    assert(parser::url_parse_entry_face(s)) by {
        assert forall|kk: int|
            #![trigger s.subrange(kk, n)]
            (0 <= kk)
                && (kk + 1 <= n)
                && ((s.subrange(kk, n).len() as int) <= n)
                && urllib::is_ascii_alpha(s.index(0))
                && (forall|j: int| 1 <= j < kk
                    ==> urllib::is_scheme_char(s.index(j)))
                && s.index(kk) == 0x3Au8
            implies wn_face_arms(s, kk)
        by {
            assert(!urllib::is_ascii_alpha(s.index(0)));
            assert(false);
        }
    }
}

/* ------------------------------------------------------------
 * The authority assembly drive and the full-chain face
 * (the parser's own faces on the sampled class: the scheme scan, the
 * ':' and "//" writes, the userinfo peel -- arm A on the '@'-free
 * tail -- the host scan (the class witness, by the maximality post),
 * the host write arm (the parse_host_and_port write path; its Err face
 * demands b == a, refuted by the non-empty sample run), and the path
 * stage plus wrap-up for the full-chain face. The wrapper arithmetic
 * (the to_u32 offsets) and the dead colon/port gate of
 * parse_host_and_port stay outside the drive -- ledgered here)
 * ------------------------------------------------------------ */

#[verifier::rlimit(400)]
exec fn wn_authority_drive(input: &[u8], special: bool) -> (r: Option<(Vec<u8>, usize, usize)>)
    requires
        wn_auth_class(input@, special),
    ensures
        r.is_some() ==> ({
            let ser = r.unwrap().0;
            let k = r.unwrap().1;
            let h = r.unwrap().2;
            &&& 1 <= (k as int)
            &&& 1 <= (h as int)
            &&& (k as int) + 3 + (h as int) <= (input@.len() as int)
            &&& wn_auth_split(input@, (k as int), (h as int), special)
            &&& ser.view() == input@.subrange(0, (k as int) + 3 + (h as int))
        }),
{
    proof {
        wn_auth_certificate(input@, special);
        assert((input@.len() as int) <= 0xFFFF_FFFF);
    }
    let mut p = parser::Parser {
        serialization: Vec::new(),
        base_url: Option::None,
        context: parser::Context::UrlParser,
    };
    let inp = parser::Input { bytes: input, pos: 0 };
    proof {
        assert(parser::input_rem(&inp) == input@) by {
            let n = (input@.len() as int);
            vstd::seq::lemma_seq_subrange_len(input@, 0, n);
            assert forall|j: int| 0 <= j < n
                implies parser::input_rem(&inp).index(j) == input@.index(j) by {
                vstd::seq::lemma_seq_subrange_index(input@, 0, n, j);
            }
        }
        assert(parser::input_ok(&inp));
        assert(parser::machine_domain(parser::input_rem(&inp)));
        assert((parser::input_rem(&inp).len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_wf(&inp));
    }
    let r1 = p.parse_scheme(inp);
    if r1.is_err() {
        proof {
            let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
            wn_shape_of_auth(input@, kw, hh, special);
            assert(parser::scheme_split_err_refute(input@, kw, parser::Context::UrlParser));
            let srem = parser::input_rem(&inp);
            assert(srem == input@);
            assert(parser::scheme_split_err_refute(srem, kw, parser::Context::UrlParser) == false);
            assert(false);
        }
    }
    assert(r1.is_ok());
    let se: usize = p.serialization.len();
    proof {
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        wn_shape_of_auth(input@, kw, hh, special);
        assert(1 <= kw);
        assert(kw <= (input@.len() as int));
        let srem = parser::input_rem(&inp);
        assert(srem == input@);
        wn_shape(srem, kw);
        assert(p.serialization.view() == parser::lowered_prefix(input@.subrange(0, kw), kw)) by {
            let k0 = choose|kk: int|
                1 <= kk && kk <= srem.len()
                && p.serialization.view() == parser::lowered_prefix(srem.subrange(0, kk), kk)
                && urllib::is_ascii_alpha(srem.index(0))
                && (forall|j: int| 1 <= j < kk ==> urllib::is_scheme_char(srem.index(j)))
                && ((kk < srem.len() && srem.index(kk) == 0x3Au8) || kk == srem.len());
            wn_shape(srem, k0);
            wn_shape_unique(srem, k0, kw);
            assert(p.serialization.view() == parser::lowered_prefix(srem.subrange(0, kw), kw));
        }
        assert(parser::lowered_prefix(input@.subrange(0, kw), kw)
            == input@.subrange(0, kw)) by {
            let lp = parser::lowered_prefix(input@.subrange(0, kw), kw);
            assert((lp.len() as int) == kw);
            assert forall|i: int| 0 <= i < kw
                implies lp.index(i) == input@.index(i) by {
                assert(parser::lower_byte(input@.index(i)) == input@.index(i));
            }
        }
        assert(p.serialization.view() == input@.subrange(0, kw));
        assert((p.serialization.view().len() as int) == kw);
        assert((se as int) == kw);
        assert(parser::input_rem(&r1.unwrap())
            == input@.subrange(kw + 1, (input@.len() as int)));
    }
    let se32: u32 = se as u32;
    proof {
        assert((se as int) <= 0xFFFF_FFFF);
    }
    // the ':' push (parse_with_scheme's scheme write, parser.rs:431)
    let ghost pre_colon = p.serialization.view();
    p.serialization.push(0x3Au8);
    proof {
        let colon = seq![0x3Au8];
        assert(parser::machine_domain(colon));
        parser::machine_domain_add(pre_colon, colon);
        assert(p.serialization.view() == pre_colon + colon);
        assert(p.serialization.view() == input@.subrange(0, (se as int) + 1)) by {
            assert(pre_colon == input@.subrange(0, (se as int)));
            let lhs = p.serialization.view();
            let rhs = input@.subrange(0, (se as int) + 1);
            vstd::seq::lemma_seq_add_len(pre_colon, colon);
            assert((lhs.len() as int) == (rhs.len() as int));
            assert forall|i: int| 0 <= i < (lhs.len() as int)
                implies lhs.index(i) == rhs.index(i) by {
                if i < pre_colon.len() {
                    vstd::seq::lemma_seq_add_index1(pre_colon, colon, i);
                } else {
                    vstd::seq::lemma_seq_add_index2(pre_colon, colon, i);
                }
                vstd::seq::lemma_seq_subrange_index(input@, 0, (se as int) + 1, i);
            }
        }
    }
    // the "//" push (the ads_authority_uinfo entry write, parser.rs:829-830)
    p.serialization.push(0x2Fu8);
    p.serialization.push(0x2Fu8);
    proof {
        let slashes = seq![0x2Fu8, 0x2Fu8];
        assert(parser::machine_domain(slashes));
        let after_colon = input@.subrange(0, (se as int) + 1);
        parser::machine_domain_add(after_colon, slashes);
        assert(p.serialization.view() == after_colon + slashes);
        assert(p.serialization.view() == input@.subrange(0, (se as int) + 3)) by {
            let lhs = p.serialization.view();
            let rhs = input@.subrange(0, (se as int) + 3);
            vstd::seq::lemma_seq_add_len(after_colon, slashes);
            assert((lhs.len() as int) == (rhs.len() as int));
            assert forall|i: int| 0 <= i < (lhs.len() as int)
                implies lhs.index(i) == rhs.index(i) by {
                if i < after_colon.len() {
                    vstd::seq::lemma_seq_add_index1(after_colon, slashes, i);
                    vstd::seq::lemma_seq_subrange_index(input@, 0, (se as int) + 3, i);
                } else {
                    vstd::seq::lemma_seq_add_index2(after_colon, slashes, i);
                    vstd::seq::lemma_seq_subrange_index(input@, 0, (se as int) + 3, i);
                }
            }
        }
        let tail = input@.subrange((se + 3) as int, (input@.len() as int));
        parser::machine_domain_subrange(input@, (se + 3) as int, (input@.len() as int));
        assert(parser::machine_domain(tail));
        assert(((se + 3) as int) + 3 * (tail.len() as int) + 3
            <= 20 * (input@.len() as int) + 400);
        assert(((se + 3) as int) + 3 * (tail.len() as int) + 3 <= 0xFFFF_FFFF);
    }
    // the userinfo peel (arm A on the '@'-free sample tail)
    let inp2 = parser::Input { bytes: input, pos: se + 3 };
    proof {
        let tail = input@.subrange((se + 3) as int, (input@.len() as int));
        assert(parser::input_rem(&inp2) == tail) by {
            parser::rem_shift(input, 0, (se + 3) as int);
        }
        assert(parser::input_ok(&inp2));
        assert(parser::machine_domain(parser::input_rem(&inp2)));
        assert((parser::input_rem(&inp2).len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_wf(&inp2));
        assert(parser::machine_domain(p.serialization.view()));
    }
    // the runtime scheme type (the class's lowered scheme bytes)
    let schv = bytes_slice(&p.serialization, 0, se32);
    proof {
        assert(schv.view() == p.serialization.view().subrange(0, se32 as int));
        assert(schv.view() == input@.subrange(0, (se as int)));
    }
    let st = parser::scheme_type_from(&schv);
    proof {
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        assert(st == parser::scheme_type_of(input@.subrange(0, kw))) by {
            assert(schv.view() == input@.subrange(0, (se as int)));
            assert((se as int) == kw);
        }
        assert(st == parser::scheme_type_of(
            parser::lowered_prefix(input@.subrange(0, kw), kw))) by {
            let lp = parser::lowered_prefix(input@.subrange(0, kw), kw);
            assert(lp == input@.subrange(0, kw)) by {
                assert((lp.len() as int) == kw);
                assert forall|i: int| 0 <= i < kw
                    implies lp.index(i) == input@.index(i) by {
                    assert(parser::lower_byte(input@.index(i)) == input@.index(i));
                }
            }
        }
        assert(parser::is_special(st) == special);
        assert(st != parser::SchemeType::File);
    }
    let ui = p.parse_userinfo(inp2, st);
    if ui.is_err() {
        // the peel's contract-admissible EmptyHost face (its leading-'@'
        // arm): the sample tail carries no '@', so the runtime arm is
        // the no-write one -- the None branch is the exported-face
        // boundary, recorded
        return Option::None;
    }
    let (ue32, rest_u) = ui.unwrap();
    proof {
        let tail = input@.subrange((se + 3) as int, (input@.len() as int));
        let before = input@.subrange(0, (se + 3) as int);
        // pin the no-write arm: arms B and C both demand an '@' in the
        // tail, and the class tail carries none
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < (tail.len() as int)
            implies tail.index(j) != 0x40u8 by {
            assert((se + 3) + j < (input@.len() as int));
        }
        assert(tail.index(0) != 0x40u8);
        let arm_b = (tail.len() >= 1 && tail.index(0) == 0x40u8);
        let arm_c = (exists|kk: int| #![trigger tail.index(kk)]
            1 <= kk && kk < (tail.len() as int) && tail.index(kk) == 0x40u8);
        assert(!arm_b);
        assert(!arm_c) by {
            if arm_c {
                let kk = choose|kk: int|
                    1 <= kk && kk < (tail.len() as int)
                        && tail.index(kk) == 0x40u8;
                assert(tail.index(kk) != 0x40u8);
                assert(false);
            }
        }
        // arm A of the peel post
        assert(p.serialization.view() == before);
        assert((ue32 as int) == ((se + 3) as int));
        assert(parser::input_rem(&rest_u) == tail);
        assert(((se + 3) as int) + (tail.len() as int) + 40
            <= 20 * (input@.len() as int) + 400);
        assert(((se + 3) as int) + (tail.len() as int) + 40 <= 0xFFFF_FFFF);
    }
    // the host scan: its maximal split is the class witness (the run
    // bytes are host-simple, disjoint from the terminator set)
    let scan = parser::host_scan_walls(inp2, special);
    proof {
        let tail = input@.subrange((se + 3) as int, (input@.len() as int));
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        assert((se as int) == kw);
        assert(tail == input@.subrange(kw + 3, (input@.len() as int)));
        assert(parser::host_split_form(tail, hh, special));
        let hs = scan.0 as int;
        assert(hs <= (tail.len() as int));
        if hs < hh {
            assert(hs < (tail.len() as int));
            assert(parser::host_term_byte(tail.index(hs), special));
            assert forall|j: int| #![trigger tail.index(j)]
                0 <= j < hh implies !parser::host_term_byte(tail.index(j), special) by {}
            assert(false);
        }
        if hs > hh {
            assert(hh < hs);
            if hh < (tail.len() as int) {
                assert(parser::host_term_byte(tail.index(hh), special));
                assert forall|j: int| #![trigger tail.index(j)]
                    0 <= j < hs implies !parser::host_term_byte(tail.index(j), special) by {}
                assert(false);
            } else {
                assert(hh == (tail.len() as int));
                assert(hs <= (tail.len() as int));
                assert(false);
            }
        }
        assert(hs == hh);
    }
    // the host write arm (the parse_host_and_port write path); its Err
    // face demands b == a, refuted by the non-empty sample run
    let a_us: usize = se + 3;
    let b_us: usize = se + 3 + scan.0;
    let after = parser::Input { bytes: input, pos: b_us };
    proof {
        let run = input@.subrange((se + 3) as int, (b_us as int));
        assert((a_us as int) <= (b_us as int));
        assert((b_us as int) <= (input@.len() as int));
        parser::machine_domain_subrange(input@, (se + 3) as int, (b_us as int));
        assert(parser::machine_domain(run));
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        assert((b_us as int) == (kw + 3 + hh));
        assert(run == input@.subrange(kw + 3, kw + 3 + hh));
        let tail = input@.subrange(kw + 3, (input@.len() as int));
        assert(parser::host_split_form(tail, hh, special));
        assert(run == tail.subrange(0, hh));
        assert(parser::host_run_class(run));
        assert(parser::input_rem(&after)
            == input@.subrange((b_us as int), (input@.len() as int))) by {
            parser::rem_shift(input, 0, (se + 3) as int);
        }
        parser::machine_domain_subrange(input@, (b_us as int),
            (input@.len() as int));
        assert(parser::machine_domain(parser::input_rem(&after)));
        assert(parser::input_ok(&after));
        assert(parser::input_wf(&after));
        assert(parser::machine_domain(p.serialization.view()));
        assert((p.serialization.view().len() as int) + (run.len() as int) + 8
            <= 20 * (input@.len() as int) + 400);
        assert((p.serialization.view().len() as int) + (run.len() as int) + 8
            <= 0xFFFF_FFFF);
    }
    let hw = parser::host_write_arm(&mut p.serialization, input, a_us, b_us,
        special, after);
    if hw.is_err() {
        proof {
            let run = input@.subrange((se + 3) as int, (b_us as int));
            assert(hw == Result::Err(parser::ParseError::EmptyHost));
            assert((b_us as int) == (a_us as int));
            assert((run.len() as int) >= 1);
            assert(false);
        }
    }
    let (he32, htag) = hw.unwrap();
    proof {
        let run = input@.subrange((se + 3) as int, (b_us as int));
        assert(p.serialization.view()
            == input@.subrange(0, (se + 3) as int) + run) by {
            vstd::seq::lemma_seq_subrange_composition(input@, 0,
                (input@.len() as int), 0, (se + 3) as int);
            vstd::seq::lemma_seq_subrange_composition(input@, 0,
                (input@.len() as int), (se + 3) as int, (b_us as int));
        }
        assert((htag == HostInternal::Domain) == ((run.len() as int) > 0));
        assert((run.len() as int) >= 1);
        assert(htag == HostInternal::Domain);
        assert((he32 as int) == (p.serialization.view().len() as int));
        // the split facts at the drive's own (se, scan.0)
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        assert((se as int) == kw);
        assert((scan.0 as int) == hh);
        assert(wn_auth_split(input@, (se as int), (scan.0 as int), special));
    }
    let ser_copy = parser::bytes_own(&p.serialization);
    proof {
        assert(ser_copy.view() == p.serialization.view());
        // the written bytes are the input's own scheme + "://" + host
        // prefix (the composition of the survived prefix and the run)
        let n = (input@.len() as int);
        vstd::seq::lemma_seq_subrange_composition(input@, 0, n,
            0, (se + 3) as int);
        vstd::seq::lemma_seq_subrange_composition(input@, 0, n,
            (se + 3) as int, (b_us as int));
        assert(ser_copy.view() == input@.subrange(0, (b_us as int)));
        assert((b_us as int) == (se as int) + 3 + (scan.0 as int));
    }
    Option::Some((ser_copy, se, scan.0))
}

/// The full-chain face: the drive continued into the path stage and the
/// wrap-up (ads_authority_path_wq -- the parser's own record
/// construction). The wrap-up Ok branch carries the structural
/// invariant; the wrap-up's only exported error face is Overflow, which
/// its contract does not allow refuting -- the Err branch is the
/// exported-face boundary, recorded in the file header.
#[verifier::rlimit(400)]
exec fn wn_full_chain(input: &[u8], special: bool)
    requires
        wn_auth_class(input@, special),
{
    proof {
        wn_auth_certificate(input@, special);
        assert((input@.len() as int) <= 0xFFFF_FFFF);
    }
    let mut p = parser::Parser {
        serialization: Vec::new(),
        base_url: Option::None,
        context: parser::Context::UrlParser,
    };
    let inp = parser::Input { bytes: input, pos: 0 };
    proof {
        assert(parser::input_rem(&inp) == input@) by {
            let n = (input@.len() as int);
            vstd::seq::lemma_seq_subrange_len(input@, 0, n);
            assert forall|j: int| 0 <= j < n
                implies parser::input_rem(&inp).index(j) == input@.index(j) by {
                vstd::seq::lemma_seq_subrange_index(input@, 0, n, j);
            }
        }
        assert(parser::input_ok(&inp));
        assert(parser::machine_domain(parser::input_rem(&inp)));
        assert((parser::input_rem(&inp).len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_wf(&inp));
    }
    let r1 = p.parse_scheme(inp);
    if r1.is_err() {
        proof {
            let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
            wn_shape_of_auth(input@, kw, hh, special);
            assert(parser::scheme_split_err_refute(input@, kw, parser::Context::UrlParser));
            let srem = parser::input_rem(&inp);
            assert(srem == input@);
            assert(parser::scheme_split_err_refute(srem, kw, parser::Context::UrlParser) == false);
            assert(false);
        }
    }
    assert(r1.is_ok());
    let se: usize = p.serialization.len();
    proof {
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        wn_shape_of_auth(input@, kw, hh, special);
        assert(1 <= kw);
        assert(kw <= (input@.len() as int));
        let srem = parser::input_rem(&inp);
        assert(srem == input@);
        wn_shape(srem, kw);
        assert(p.serialization.view() == parser::lowered_prefix(input@.subrange(0, kw), kw)) by {
            let k0 = choose|kk: int|
                1 <= kk && kk <= srem.len()
                && p.serialization.view() == parser::lowered_prefix(srem.subrange(0, kk), kk)
                && urllib::is_ascii_alpha(srem.index(0))
                && (forall|j: int| 1 <= j < kk ==> urllib::is_scheme_char(srem.index(j)))
                && ((kk < srem.len() && srem.index(kk) == 0x3Au8) || kk == srem.len());
            wn_shape(srem, k0);
            wn_shape_unique(srem, k0, kw);
            assert(p.serialization.view() == parser::lowered_prefix(srem.subrange(0, kw), kw));
        }
        assert(parser::lowered_prefix(input@.subrange(0, kw), kw)
            == input@.subrange(0, kw)) by {
            let lp = parser::lowered_prefix(input@.subrange(0, kw), kw);
            assert((lp.len() as int) == kw);
            assert forall|i: int| 0 <= i < kw
                implies lp.index(i) == input@.index(i) by {
                assert(parser::lower_byte(input@.index(i)) == input@.index(i));
            }
        }
        assert((se as int) == kw);
    }
    let se32: u32 = se as u32;
    proof {
        assert((se as int) <= 0xFFFF_FFFF);
    }
    let ghost pre_colon = p.serialization.view();
    p.serialization.push(0x3Au8);
    let ghost pre_slashes = p.serialization.view();
    p.serialization.push(0x2Fu8);
    p.serialization.push(0x2Fu8);
    proof {
        let colon = seq![0x3Au8];
        let slashes = seq![0x2Fu8, 0x2Fu8];
        assert(parser::machine_domain(colon));
        assert(parser::machine_domain(slashes));
        parser::machine_domain_add(pre_colon, colon);
        parser::machine_domain_add(pre_slashes, slashes);
        assert(p.serialization.view() == input@.subrange(0, (se as int) + 3));
        let tail = input@.subrange((se + 3) as int, (input@.len() as int));
        parser::machine_domain_subrange(input@, (se + 3) as int, (input@.len() as int));
        assert(((se + 3) as int) + 3 * (tail.len() as int) + 3 <= 0xFFFF_FFFF);
    }
    let inp2 = parser::Input { bytes: input, pos: se + 3 };
    proof {
        let tail = input@.subrange((se + 3) as int, (input@.len() as int));
        assert(parser::input_rem(&inp2) == tail) by {
            parser::rem_shift(input, 0, (se + 3) as int);
        }
        assert(parser::input_ok(&inp2));
        assert(parser::machine_domain(parser::input_rem(&inp2)));
        assert((parser::input_rem(&inp2).len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_wf(&inp2));
    }
    let schv = bytes_slice(&p.serialization, 0, se32);
    proof {
        assert(schv.view() == input@.subrange(0, (se as int)));
    }
    let st = parser::scheme_type_from(&schv);
    proof {
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        assert((se as int) == kw);
        assert(st == parser::scheme_type_of(input@.subrange(0, kw)));
        assert(parser::is_special(st) == special);
        assert(st != parser::SchemeType::File);
    }
    let ui = p.parse_userinfo(inp2, st);
    if ui.is_err() {
        return;
    }
    let (ue32, rest_u) = ui.unwrap();
    proof {
        let tail = input@.subrange((se + 3) as int, (input@.len() as int));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < (tail.len() as int)
            implies tail.index(j) != 0x40u8 by {
            assert((se + 3) + j < (input@.len() as int));
        }
        assert(p.serialization.view() == input@.subrange(0, (se + 3) as int));
        assert((ue32 as int) == ((se + 3) as int));
        assert(((se + 3) as int) + (tail.len() as int) + 40 <= 0xFFFF_FFFF);
    }
    let scan = parser::host_scan_walls(inp2, special);
    proof {
        let tail = input@.subrange((se + 3) as int, (input@.len() as int));
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        assert((se as int) == kw);
        assert(tail == input@.subrange(kw + 3, (input@.len() as int)));
        assert(parser::host_split_form(tail, hh, special));
        let hs = scan.0 as int;
        assert(hs <= (tail.len() as int));
        if hs < hh {
            assert(parser::host_term_byte(tail.index(hs), special));
            assert(false);
        }
        if hs > hh {
            if hh < (tail.len() as int) {
                assert(parser::host_term_byte(tail.index(hh), special));
                assert(false);
            } else {
                assert(false);
            }
        }
        assert(hs == hh);
    }
    let a_us: usize = se + 3;
    let b_us: usize = se + 3 + scan.0;
    let after = parser::Input { bytes: input, pos: b_us };
    proof {
        let run = input@.subrange((se + 3) as int, (b_us as int));
        assert((a_us as int) <= (b_us as int));
        assert((b_us as int) <= (input@.len() as int));
        parser::machine_domain_subrange(input@, (se + 3) as int, (b_us as int));
        assert(parser::machine_domain(run));
        let (kw, hh) = choose|kk: int, hh: int| wn_auth_split(input@, kk, hh, special);
        assert((b_us as int) == (kw + 3 + hh));
        assert(run == input@.subrange(kw + 3, kw + 3 + hh));
        let tail = input@.subrange(kw + 3, (input@.len() as int));
        assert(parser::host_split_form(tail, hh, special));
        assert(run == tail.subrange(0, hh));
        assert(parser::host_run_class(run));
        assert(parser::input_rem(&after)
            == input@.subrange((b_us as int), (input@.len() as int))) by {
            parser::rem_shift(input, 0, (se + 3) as int);
        }
        parser::machine_domain_subrange(input@, (b_us as int),
            (input@.len() as int));
        assert(parser::machine_domain(parser::input_rem(&after)));
        assert(parser::input_ok(&after));
        assert(parser::input_wf(&after));
        assert(parser::machine_domain(p.serialization.view()));
        assert((p.serialization.view().len() as int) + (run.len() as int) + 8
            <= 0xFFFF_FFFF);
    }
    let hw = parser::host_write_arm(&mut p.serialization, input, a_us, b_us,
        special, after);
    if hw.is_err() {
        proof {
            assert(hw == Result::Err(parser::ParseError::EmptyHost));
            assert((b_us as int) == (a_us as int));
            assert(((input@.len() as int) - ((se + 3) as int)) >= 1);
            assert(false);
        }
    }
    let (he32, htag) = hw.unwrap();
    proof {
        let run = input@.subrange((se + 3) as int, (b_us as int));
        assert(p.serialization.view() == input@.subrange(0, (se + 3) as int) + run);
        assert(htag == HostInternal::Domain);
        assert((he32 as int) == (p.serialization.view().len() as int));
    }
    // the path stage and the wrap-up (the parser's own record
    // construction) over the post-host tail
    let rest_c = parser::Input { bytes: input, pos: b_us };
    proof {
        let o = p.serialization.view();
        let n0 = (o.len() as int);
        assert(o == input@.subrange(0, (se + 3) as int)
            + input@.subrange((se + 3) as int, (b_us as int)));
        assert(n0 == (b_us as int));
        assert(parser::input_ok(&rest_c));
        parser::machine_domain_subrange(input@, (b_us as int), (input@.len() as int));
        assert(parser::machine_domain(parser::input_rem(&rest_c)));
        assert((parser::input_rem(&rest_c).len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_wf(&rest_c));
        assert(parser::machine_domain(o));
        assert((he32 as int) == n0);
        assert(n0 + 5 * (parser::input_rem(&rest_c).len() as int) + 38
            <= 20 * (input@.len() as int) + 400);
        assert(n0 + 5 * (parser::input_rem(&rest_c).len() as int) + 38
            <= 0xFFFF_FFFF);
        assert(n0 + 11 * (parser::input_rem(&rest_c).len() as int) + 26
            <= 20 * (input@.len() as int) + 400);
        assert(n0 + 11 * (parser::input_rem(&rest_c).len() as int) + 26
            <= 0xFFFF_FFFF);
        assert(((se32 as int)) + 3 <= n0);
        assert(urllib::is_ascii_alpha(o.index(0)));
        assert(o.index(se32 as int) == 0x3Au8);
        assert(o.index((se32 as int) + 1) == 0x2Fu8);
        assert(o.index((se32 as int) + 2) == 0x2Fu8);
        assert((ue32 as int) == ((se32 as int) + 3));
        assert((ue32 as int) <= n0);
        // the wrap-up's route disjunction: route D (the byte at the
        // username boundary is the host's first letter, neither ':' nor '@')
        assert(o.index(ue32 as int) != 0x3Au8);
        assert(o.index(ue32 as int) != 0x40u8);
        vstd::seq::lemma_seq_subrange_len(o, 0, se32 as int);
        assert(o.subrange(0, se32 as int) == input@.subrange(0, (se as int)));
        assert(st == parser::scheme_type_of(o.subrange(0, se32 as int)));
        if parser::is_special(st) {
            // the last written byte is the host run's letter tail
            assert(n0 >= 1);
            assert(o.index(n0 - 1) != 0x2Fu8);
        }
        assert(((he32 as int)) <= n0);
        assert(((he32 as int)) >= ((se + 3) as int));
    }
    let w = p.ads_authority_path_wq(rest_c, st, se32, ue32, (se + 3) as u32,
        he32, htag, Option::None, he32);
    if w.is_ok() {
        proof {
            assert(url_invariant(&w.unwrap()));
        }
    }
}
/* ------------------------------------------------------------
 * The samples
 * ------------------------------------------------------------ */

/// urltestdata.json record: http://example.com/foo/bar/../ton
#[verifier::rlimit(600)]
proof fn wsa14_cls()
    ensures wn_auth_class(seq![0x68u8, 0x74u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x74u8, 0x6Fu8, 0x6Eu8], true)
{
    let s = seq![0x68u8, 0x74u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x74u8, 0x6Fu8, 0x6Eu8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 4, 11, true)) by {
        let tail = s.subrange(7, (s.len() as int));
        assert((tail.len() as int) == 26);
        let runlit = seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8];
        assert(parser::host_split_form(tail, 11, true)) by {
        assert(tail.subrange(0, 11) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 11)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 11 implies !parser::host_term_byte(tail.index(j), true) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(11) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(11), true));
        }
        assert forall|i: int| #![trigger s.index(i)]
            7 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x68u8, 0x74u8, 0x74u8, 0x70u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        assert(s.index(5) == 0x2Fu8);
        assert(s.index(6) == 0x2Fu8);
        assert(wn_auth_split(s, 4, 11, true));
    }
}

/// http://example.com/foo/bar/../ton: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa14()
{
    let v: Vec<u8> = vec![0x68u8, 0x74u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x74u8, 0x6Fu8, 0x6Eu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x68u8, 0x74u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x74u8, 0x6Fu8, 0x6Eu8]);
        wsa14_cls();
        wn_auth_certificate(sl@, true);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, true);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 4, 11, true);
        assert((inst.1 as int) == 4);
        assert((inst.2 as int) == 11);
        assert(inst.0.view() == sl@.subrange(0, 18));
        assert(sl@.subrange(0, 18) == seq![0x68u8, 0x74u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]);
        }
    }
    let dr = wn_authority_drive(sl, true);
    wn_full_chain(sl, true);
}

/// urltestdata.json record: wss://foo:81/
#[verifier::rlimit(600)]
proof fn wsa15_cls()
    ensures wn_auth_class(seq![0x77u8, 0x73u8, 0x73u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x38u8, 0x31u8, 0x2Fu8], true)
{
    let s = seq![0x77u8, 0x73u8, 0x73u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x38u8, 0x31u8, 0x2Fu8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 3, 3, true)) by {
        let tail = s.subrange(6, (s.len() as int));
        assert((tail.len() as int) == 7);
        let runlit = seq![0x66u8, 0x6Fu8, 0x6Fu8];
        assert(parser::host_split_form(tail, 3, true)) by {
        assert(tail.subrange(0, 3) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 3)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 3 implies !parser::host_term_byte(tail.index(j), true) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(3) == 0x3Au8);
                assert(parser::host_term_byte(tail.index(3), true));
        }
        assert forall|i: int| #![trigger s.index(i)]
            6 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 3 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 3), 3);
        assert(lp == seq![0x77u8, 0x73u8, 0x73u8]) by {
            assert((lp.len() as int) == 3);
            assert forall|i: int| 0 <= i < 3 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(3) == 0x3Au8);
        assert(s.index(4) == 0x2Fu8);
        assert(s.index(5) == 0x2Fu8);
        assert(wn_auth_split(s, 3, 3, true));
    }
}

/// wss://foo:81/: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa15()
{
    let v: Vec<u8> = vec![0x77u8, 0x73u8, 0x73u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x38u8, 0x31u8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x77u8, 0x73u8, 0x73u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x38u8, 0x31u8, 0x2Fu8]);
        wsa15_cls();
        wn_auth_certificate(sl@, true);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, true);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 3, 3, true);
        assert((inst.1 as int) == 3);
        assert((inst.2 as int) == 3);
        assert(inst.0.view() == sl@.subrange(0, 9));
        assert(sl@.subrange(0, 9) == seq![0x77u8, 0x73u8, 0x73u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8]);
        }
    }
    let dr = wn_authority_drive(sl, true);
}

/// urltestdata.json record: ftp://foo:80/
#[verifier::rlimit(600)]
proof fn wsa16_cls()
    ensures wn_auth_class(seq![0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x38u8, 0x30u8, 0x2Fu8], true)
{
    let s = seq![0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x38u8, 0x30u8, 0x2Fu8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 3, 3, true)) by {
        let tail = s.subrange(6, (s.len() as int));
        assert((tail.len() as int) == 7);
        let runlit = seq![0x66u8, 0x6Fu8, 0x6Fu8];
        assert(parser::host_split_form(tail, 3, true)) by {
        assert(tail.subrange(0, 3) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 3)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 3 implies !parser::host_term_byte(tail.index(j), true) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(3) == 0x3Au8);
                assert(parser::host_term_byte(tail.index(3), true));
        }
        assert forall|i: int| #![trigger s.index(i)]
            6 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 3 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 3), 3);
        assert(lp == seq![0x66u8, 0x74u8, 0x70u8]) by {
            assert((lp.len() as int) == 3);
            assert forall|i: int| 0 <= i < 3 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(3) == 0x3Au8);
        assert(s.index(4) == 0x2Fu8);
        assert(s.index(5) == 0x2Fu8);
        assert(wn_auth_split(s, 3, 3, true));
    }
}

/// ftp://foo:80/: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa16()
{
    let v: Vec<u8> = vec![0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x38u8, 0x30u8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x38u8, 0x30u8, 0x2Fu8]);
        wsa16_cls();
        wn_auth_certificate(sl@, true);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, true);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 3, 3, true);
        assert((inst.1 as int) == 3);
        assert((inst.2 as int) == 3);
        assert(inst.0.view() == sl@.subrange(0, 9));
        assert(sl@.subrange(0, 9) == seq![0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8]);
        }
    }
    let dr = wn_authority_drive(sl, true);
}

/// urltestdata.json record: ssh://example.com/foo/bar.git
#[verifier::rlimit(600)]
proof fn wsa17_cls()
    ensures wn_auth_class(seq![0x73u8, 0x73u8, 0x68u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x67u8, 0x69u8, 0x74u8], false)
{
    let s = seq![0x73u8, 0x73u8, 0x68u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x67u8, 0x69u8, 0x74u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 3, 11, false)) by {
        let tail = s.subrange(6, (s.len() as int));
        assert((tail.len() as int) == 23);
        let runlit = seq![0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8];
        assert(parser::host_split_form(tail, 11, false)) by {
        assert(tail.subrange(0, 11) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 11)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 11 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(11) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(11), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            6 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 3 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 3), 3);
        assert(lp == seq![0x73u8, 0x73u8, 0x68u8]) by {
            assert((lp.len() as int) == 3);
            assert forall|i: int| 0 <= i < 3 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(3) == 0x3Au8);
        assert(s.index(4) == 0x2Fu8);
        assert(s.index(5) == 0x2Fu8);
        assert(wn_auth_split(s, 3, 11, false));
    }
}

/// ssh://example.com/foo/bar.git: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa17()
{
    let v: Vec<u8> = vec![0x73u8, 0x73u8, 0x68u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x67u8, 0x69u8, 0x74u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x73u8, 0x73u8, 0x68u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x67u8, 0x69u8, 0x74u8]);
        wsa17_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 3, 11, false);
        assert((inst.1 as int) == 3);
        assert((inst.2 as int) == 11);
        assert(inst.0.view() == sl@.subrange(0, 17));
        assert(sl@.subrange(0, 17) == seq![0x73u8, 0x73u8, 0x68u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]);
        }
    }
    let dr = wn_authority_drive(sl, false);
    wn_full_chain(sl, false);
}

/// urltestdata.json record: git://github.com/foo/bar.git
#[verifier::rlimit(600)]
proof fn wsa18_cls()
    ensures wn_auth_class(seq![0x67u8, 0x69u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x67u8, 0x69u8, 0x74u8, 0x68u8, 0x75u8, 0x62u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x67u8, 0x69u8, 0x74u8], false)
{
    let s = seq![0x67u8, 0x69u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x67u8, 0x69u8, 0x74u8, 0x68u8, 0x75u8, 0x62u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x67u8, 0x69u8, 0x74u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 3, 10, false)) by {
        let tail = s.subrange(6, (s.len() as int));
        assert((tail.len() as int) == 22);
        let runlit = seq![0x67u8, 0x69u8, 0x74u8, 0x68u8, 0x75u8, 0x62u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8];
        assert(parser::host_split_form(tail, 10, false)) by {
        assert(tail.subrange(0, 10) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 10)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 10 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(10) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(10), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            6 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 3 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 3), 3);
        assert(lp == seq![0x67u8, 0x69u8, 0x74u8]) by {
            assert((lp.len() as int) == 3);
            assert forall|i: int| 0 <= i < 3 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(3) == 0x3Au8);
        assert(s.index(4) == 0x2Fu8);
        assert(s.index(5) == 0x2Fu8);
        assert(wn_auth_split(s, 3, 10, false));
    }
}

/// git://github.com/foo/bar.git: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa18()
{
    let v: Vec<u8> = vec![0x67u8, 0x69u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x67u8, 0x69u8, 0x74u8, 0x68u8, 0x75u8, 0x62u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x67u8, 0x69u8, 0x74u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x67u8, 0x69u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x67u8, 0x69u8, 0x74u8, 0x68u8, 0x75u8, 0x62u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x67u8, 0x69u8, 0x74u8]);
        wsa18_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 3, 10, false);
        assert((inst.1 as int) == 3);
        assert((inst.2 as int) == 10);
        assert(inst.0.view() == sl@.subrange(0, 16));
        assert(sl@.subrange(0, 16) == seq![0x67u8, 0x69u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x67u8, 0x69u8, 0x74u8, 0x68u8, 0x75u8, 0x62u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]);
        }
    }
    let dr = wn_authority_drive(sl, false);
    wn_full_chain(sl, false);
}

/// urltestdata.json record: tftp://foobar.com/someconfig;mode=netascii
#[verifier::rlimit(600)]
proof fn wsa19_cls()
    ensures wn_auth_class(seq![0x74u8, 0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x73u8, 0x6Fu8, 0x6Du8, 0x65u8, 0x63u8, 0x6Fu8, 0x6Eu8, 0x66u8, 0x69u8, 0x67u8, 0x3Bu8, 0x6Du8, 0x6Fu8, 0x64u8, 0x65u8, 0x3Du8, 0x6Eu8, 0x65u8, 0x74u8, 0x61u8, 0x73u8, 0x63u8, 0x69u8, 0x69u8], false)
{
    let s = seq![0x74u8, 0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x73u8, 0x6Fu8, 0x6Du8, 0x65u8, 0x63u8, 0x6Fu8, 0x6Eu8, 0x66u8, 0x69u8, 0x67u8, 0x3Bu8, 0x6Du8, 0x6Fu8, 0x64u8, 0x65u8, 0x3Du8, 0x6Eu8, 0x65u8, 0x74u8, 0x61u8, 0x73u8, 0x63u8, 0x69u8, 0x69u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 4, 10, false)) by {
        let tail = s.subrange(7, (s.len() as int));
        assert((tail.len() as int) == 35);
        let runlit = seq![0x66u8, 0x6Fu8, 0x6Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8];
        assert(parser::host_split_form(tail, 10, false)) by {
        assert(tail.subrange(0, 10) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 10)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 10 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(10) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(10), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            7 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x74u8, 0x66u8, 0x74u8, 0x70u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        assert(s.index(5) == 0x2Fu8);
        assert(s.index(6) == 0x2Fu8);
        assert(wn_auth_split(s, 4, 10, false));
    }
}

/// tftp://foobar.com/someconfig;mode=netascii: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa19()
{
    let v: Vec<u8> = vec![0x74u8, 0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x73u8, 0x6Fu8, 0x6Du8, 0x65u8, 0x63u8, 0x6Fu8, 0x6Eu8, 0x66u8, 0x69u8, 0x67u8, 0x3Bu8, 0x6Du8, 0x6Fu8, 0x64u8, 0x65u8, 0x3Du8, 0x6Eu8, 0x65u8, 0x74u8, 0x61u8, 0x73u8, 0x63u8, 0x69u8, 0x69u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x74u8, 0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8, 0x73u8, 0x6Fu8, 0x6Du8, 0x65u8, 0x63u8, 0x6Fu8, 0x6Eu8, 0x66u8, 0x69u8, 0x67u8, 0x3Bu8, 0x6Du8, 0x6Fu8, 0x64u8, 0x65u8, 0x3Du8, 0x6Eu8, 0x65u8, 0x74u8, 0x61u8, 0x73u8, 0x63u8, 0x69u8, 0x69u8]);
        wsa19_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 4, 10, false);
        assert((inst.1 as int) == 4);
        assert((inst.2 as int) == 10);
        assert(inst.0.view() == sl@.subrange(0, 17));
        assert(sl@.subrange(0, 17) == seq![0x74u8, 0x66u8, 0x74u8, 0x70u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8]);
        }
    }
    let dr = wn_authority_drive(sl, false);
    wn_full_chain(sl, false);
}

/// urltestdata.json record: data://test/a/../b
#[verifier::rlimit(600)]
proof fn wsa20_cls()
    ensures wn_auth_class(seq![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8], false)
{
    let s = seq![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 4, 4, false)) by {
        let tail = s.subrange(7, (s.len() as int));
        assert((tail.len() as int) == 11);
        let runlit = seq![0x74u8, 0x65u8, 0x73u8, 0x74u8];
        assert(parser::host_split_form(tail, 4, false)) by {
        assert(tail.subrange(0, 4) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 4)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 4 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(4) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(4), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            7 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x64u8, 0x61u8, 0x74u8, 0x61u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        assert(s.index(5) == 0x2Fu8);
        assert(s.index(6) == 0x2Fu8);
        assert(wn_auth_split(s, 4, 4, false));
    }
}

/// data://test/a/../b: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa20()
{
    let v: Vec<u8> = vec![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8]);
        wsa20_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 4, 4, false);
        assert((inst.1 as int) == 4);
        assert((inst.2 as int) == 4);
        assert(inst.0.view() == sl@.subrange(0, 11));
        assert(sl@.subrange(0, 11) == seq![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8]);
        }
    }
    let dr = wn_authority_drive(sl, false);
    wn_full_chain(sl, false);
}

/// urltestdata.json record: javascript://test/a/../b
#[verifier::rlimit(600)]
proof fn wsa21_cls()
    ensures wn_auth_class(seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8], false)
{
    let s = seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 10, 4, false)) by {
        let tail = s.subrange(13, (s.len() as int));
        assert((tail.len() as int) == 11);
        let runlit = seq![0x74u8, 0x65u8, 0x73u8, 0x74u8];
        assert(parser::host_split_form(tail, 4, false)) by {
        assert(tail.subrange(0, 4) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 4)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 4 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(4) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(4), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            13 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 10 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 10), 10);
        assert(lp == seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8]) by {
            assert((lp.len() as int) == 10);
            assert forall|i: int| 0 <= i < 10 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(10) == 0x3Au8);
        assert(s.index(11) == 0x2Fu8);
        assert(s.index(12) == 0x2Fu8);
        assert(wn_auth_split(s, 10, 4, false));
    }
}

/// javascript://test/a/../b: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa21()
{
    let v: Vec<u8> = vec![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8]);
        wsa21_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 10, 4, false);
        assert((inst.1 as int) == 10);
        assert((inst.2 as int) == 4);
        assert(inst.0.view() == sl@.subrange(0, 17));
        assert(sl@.subrange(0, 17) == seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8]);
        }
    }
    let dr = wn_authority_drive(sl, false);
    wn_full_chain(sl, false);
}

/// urltestdata.json record: mailto://test/a/../b
#[verifier::rlimit(600)]
proof fn wsa22_cls()
    ensures wn_auth_class(seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8], false)
{
    let s = seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 6, 4, false)) by {
        let tail = s.subrange(9, (s.len() as int));
        assert((tail.len() as int) == 11);
        let runlit = seq![0x74u8, 0x65u8, 0x73u8, 0x74u8];
        assert(parser::host_split_form(tail, 4, false)) by {
        assert(tail.subrange(0, 4) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 4)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 4 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(4) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(4), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            9 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 6 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 6), 6);
        assert(lp == seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8]) by {
            assert((lp.len() as int) == 6);
            assert forall|i: int| 0 <= i < 6 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(6) == 0x3Au8);
        assert(s.index(7) == 0x2Fu8);
        assert(s.index(8) == 0x2Fu8);
        assert(wn_auth_split(s, 6, 4, false));
    }
}

/// mailto://test/a/../b: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa22()
{
    let v: Vec<u8> = vec![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8]);
        wsa22_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 6, 4, false);
        assert((inst.1 as int) == 6);
        assert((inst.2 as int) == 4);
        assert(inst.0.view() == sl@.subrange(0, 13));
        assert(sl@.subrange(0, 13) == seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8]);
        }
    }
    let dr = wn_authority_drive(sl, false);
    wn_full_chain(sl, false);
}

/// urltestdata.json record: intent://test/a/../b
#[verifier::rlimit(600)]
proof fn wsa23_cls()
    ensures wn_auth_class(seq![0x69u8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8], false)
{
    let s = seq![0x69u8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 6, 4, false)) by {
        let tail = s.subrange(9, (s.len() as int));
        assert((tail.len() as int) == 11);
        let runlit = seq![0x74u8, 0x65u8, 0x73u8, 0x74u8];
        assert(parser::host_split_form(tail, 4, false)) by {
        assert(tail.subrange(0, 4) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 4)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 4 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(4) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(4), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            9 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 6 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 6), 6);
        assert(lp == seq![0x69u8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x74u8]) by {
            assert((lp.len() as int) == 6);
            assert forall|i: int| 0 <= i < 6 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(6) == 0x3Au8);
        assert(s.index(7) == 0x2Fu8);
        assert(s.index(8) == 0x2Fu8);
        assert(wn_auth_split(s, 6, 4, false));
    }
}

/// intent://test/a/../b: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa23()
{
    let v: Vec<u8> = vec![0x69u8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x69u8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8]);
        wsa23_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 6, 4, false);
        assert((inst.1 as int) == 6);
        assert((inst.2 as int) == 4);
        assert(inst.0.view() == sl@.subrange(0, 13));
        assert(sl@.subrange(0, 13) == seq![0x69u8, 0x6Eu8, 0x74u8, 0x65u8, 0x6Eu8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8]);
        }
    }
    let dr = wn_authority_drive(sl, false);
    wn_full_chain(sl, false);
}

/// urltestdata.json record: urn://test/a/../b
#[verifier::rlimit(600)]
proof fn wsa24_cls()
    ensures wn_auth_class(seq![0x75u8, 0x72u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8], false)
{
    let s = seq![0x75u8, 0x72u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 3, 4, false)) by {
        let tail = s.subrange(6, (s.len() as int));
        assert((tail.len() as int) == 11);
        let runlit = seq![0x74u8, 0x65u8, 0x73u8, 0x74u8];
        assert(parser::host_split_form(tail, 4, false)) by {
        assert(tail.subrange(0, 4) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 4)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 4 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(4) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(4), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            6 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 3 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 3), 3);
        assert(lp == seq![0x75u8, 0x72u8, 0x6Eu8]) by {
            assert((lp.len() as int) == 3);
            assert forall|i: int| 0 <= i < 3 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(3) == 0x3Au8);
        assert(s.index(4) == 0x2Fu8);
        assert(s.index(5) == 0x2Fu8);
        assert(wn_auth_split(s, 3, 4, false));
    }
}

/// urn://test/a/../b: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa24()
{
    let v: Vec<u8> = vec![0x75u8, 0x72u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x75u8, 0x72u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8]);
        wsa24_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    // serialization face skipped for this sample
    // full-chain face skipped for this sample
}

/// urltestdata.json record: stun://test/a/../b
#[verifier::rlimit(600)]
proof fn wsa25_cls()
    ensures wn_auth_class(seq![0x73u8, 0x74u8, 0x75u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8], false)
{
    let s = seq![0x73u8, 0x74u8, 0x75u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    assert(parser::machine_domain(s)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < s.len() implies parser::machine_domain_byte(s.index(i)) by {}
    }
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_auth_split(s, 4, 4, false)) by {
        let tail = s.subrange(7, (s.len() as int));
        assert((tail.len() as int) == 11);
        let runlit = seq![0x74u8, 0x65u8, 0x73u8, 0x74u8];
        assert(parser::host_split_form(tail, 4, false)) by {
        assert(tail.subrange(0, 4) == runlit);
        assert(parser::host_run_class(tail.subrange(0, 4)));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < 4 implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(runlit.index(j)));
        }
        assert(tail.index(4) == 0x2Fu8);
                assert(parser::host_term_byte(tail.index(4), false));
        }
        assert forall|i: int| #![trigger s.index(i)]
            7 <= i < (s.len() as int) implies s.index(i) != 0x40u8 by {}
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x73u8, 0x74u8, 0x75u8, 0x6Eu8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        assert(s.index(5) == 0x2Fu8);
        assert(s.index(6) == 0x2Fu8);
        assert(wn_auth_split(s, 4, 4, false));
    }
}

/// stun://test/a/../b: entry-face certificate, the parse Ok-branch invariant,
/// the authority-region serialization, and (without an explicit
/// port) the full-chain wrap-up invariant face
#[verifier::rlimit(600)]
exec fn wsa25()
{
    let v: Vec<u8> = vec![0x73u8, 0x74u8, 0x75u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x73u8, 0x74u8, 0x75u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x2Fu8, 0x61u8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8, 0x62u8]);
        wsa25_cls();
        wn_auth_certificate(sl@, false);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    let dr = wn_authority_drive(sl, false);
    if let Option::Some(inst) = dr {
        proof {
        wn_auth_split_unique(sl@, inst.1 as int, inst.2 as int, 4, 4, false);
        assert((inst.1 as int) == 4);
        assert((inst.2 as int) == 4);
        assert(inst.0.view() == sl@.subrange(0, 11));
        assert(sl@.subrange(0, 11) == seq![0x73u8, 0x74u8, 0x75u8, 0x6Eu8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8]);
        }
    }
    let dr = wn_authority_drive(sl, false);
    wn_full_chain(sl, false);
}

/// urltestdata.json record: javascript:example.com/
#[verifier::rlimit(600)]
proof fn wsn01_cls()
    ensures wn_anar_class(seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8])
{
    let s = seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8];
    assert(wn_anar_class(s)) by {
        assert(parser::machine_domain(s));
        assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
        let rem2 = s.subrange(11, (s.len() as int));
        assert((rem2.len() as int) == 12);
        assert(rem2.index(0) != 0x2Fu8);
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 10 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 10), 10);
        assert(lp == seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8]) by {
            assert((lp.len() as int) == 10);
            assert forall|i: int| 0 <= i < 10 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(10) == 0x3Au8);
        assert(wn_anar_split(s, 10));
    }
}

/// javascript:example.com/: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsn01()
{
    let v: Vec<u8> = vec![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x6Au8, 0x61u8, 0x76u8, 0x61u8, 0x73u8, 0x63u8, 0x72u8, 0x69u8, 0x70u8, 0x74u8, 0x3Au8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8]);
        wsn01_cls();
        wn_anar_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: mailto:example.com/
#[verifier::rlimit(600)]
proof fn wsn02_cls()
    ensures wn_anar_class(seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8])
{
    let s = seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8];
    assert(wn_anar_class(s)) by {
        assert(parser::machine_domain(s));
        assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
        let rem2 = s.subrange(7, (s.len() as int));
        assert((rem2.len() as int) == 12);
        assert(rem2.index(0) != 0x2Fu8);
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 6 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 6), 6);
        assert(lp == seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8]) by {
            assert((lp.len() as int) == 6);
            assert forall|i: int| 0 <= i < 6 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(6) == 0x3Au8);
        assert(wn_anar_split(s, 6));
    }
}

/// mailto:example.com/: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsn02()
{
    let v: Vec<u8> = vec![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x6Du8, 0x61u8, 0x69u8, 0x6Cu8, 0x74u8, 0x6Fu8, 0x3Au8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8]);
        wsn02_cls();
        wn_anar_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: data:text/html,test#test
#[verifier::rlimit(600)]
proof fn wsn03_cls()
    ensures wn_anar_class(seq![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x74u8, 0x65u8, 0x78u8, 0x74u8, 0x2Fu8, 0x68u8, 0x74u8, 0x6Du8, 0x6Cu8, 0x2Cu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x23u8, 0x74u8, 0x65u8, 0x73u8, 0x74u8])
{
    let s = seq![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x74u8, 0x65u8, 0x78u8, 0x74u8, 0x2Fu8, 0x68u8, 0x74u8, 0x6Du8, 0x6Cu8, 0x2Cu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x23u8, 0x74u8, 0x65u8, 0x73u8, 0x74u8];
    assert(wn_anar_class(s)) by {
        assert(parser::machine_domain(s));
        assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
        let rem2 = s.subrange(5, (s.len() as int));
        assert((rem2.len() as int) == 19);
        assert(rem2.index(0) != 0x2Fu8);
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x64u8, 0x61u8, 0x74u8, 0x61u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        assert(wn_anar_split(s, 4));
    }
}

/// data:text/html,test#test: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsn03()
{
    let v: Vec<u8> = vec![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x74u8, 0x65u8, 0x78u8, 0x74u8, 0x2Fu8, 0x68u8, 0x74u8, 0x6Du8, 0x6Cu8, 0x2Cu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x23u8, 0x74u8, 0x65u8, 0x73u8, 0x74u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x64u8, 0x61u8, 0x74u8, 0x61u8, 0x3Au8, 0x74u8, 0x65u8, 0x78u8, 0x74u8, 0x2Fu8, 0x68u8, 0x74u8, 0x6Du8, 0x6Cu8, 0x2Cu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8, 0x23u8, 0x74u8, 0x65u8, 0x73u8, 0x74u8]);
        wsn03_cls();
        wn_anar_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: foo:/
#[verifier::rlimit(600)]
proof fn wsn04_cls()
    ensures wn_anar_class(seq![0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x2Fu8])
{
    let s = seq![0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x2Fu8];
    assert(wn_anar_class(s)) by {
        assert(parser::machine_domain(s));
        assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
        let rem2 = s.subrange(4, (s.len() as int));
        assert((rem2.len() as int) == 1);
        assert((rem2.len() as int) < 2);
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 3 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 3), 3);
        assert(lp == seq![0x66u8, 0x6Fu8, 0x6Fu8]) by {
            assert((lp.len() as int) == 3);
            assert forall|i: int| 0 <= i < 3 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(3) == 0x3Au8);
        assert(wn_anar_split(s, 3));
    }
}

/// foo:/: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsn04()
{
    let v: Vec<u8> = vec![0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x66u8, 0x6Fu8, 0x6Fu8, 0x3Au8, 0x2Fu8]);
        wsn04_cls();
        wn_anar_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: about:/../
#[verifier::rlimit(600)]
proof fn wsn05_cls()
    ensures wn_anar_class(seq![0x61u8, 0x62u8, 0x6Fu8, 0x75u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8])
{
    let s = seq![0x61u8, 0x62u8, 0x6Fu8, 0x75u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8];
    assert(wn_anar_class(s)) by {
        assert(parser::machine_domain(s));
        assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
        let rem2 = s.subrange(6, (s.len() as int));
        assert((rem2.len() as int) == 4);
        assert(rem2.index(1) != 0x2Fu8);
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 5 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 5), 5);
        assert(lp == seq![0x61u8, 0x62u8, 0x6Fu8, 0x75u8, 0x74u8]) by {
            assert((lp.len() as int) == 5);
            assert forall|i: int| 0 <= i < 5 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(5) == 0x3Au8);
        assert(wn_anar_split(s, 5));
    }
}

/// about:/../: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsn05()
{
    let v: Vec<u8> = vec![0x61u8, 0x62u8, 0x6Fu8, 0x75u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x61u8, 0x62u8, 0x6Fu8, 0x75u8, 0x74u8, 0x3Au8, 0x2Fu8, 0x2Eu8, 0x2Eu8, 0x2Fu8]);
        wsn05_cls();
        wn_anar_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: file://test
#[verifier::rlimit(600)]
proof fn wsf01_cls()
    ensures wn_file_class(seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8])
{
    let s = seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8];
    assert(parser::machine_domain(s));
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_file_split(s, 4)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        let rem2 = s.subrange(5, (s.len() as int));
        assert(parser::file_state_entry_face(rem2)) by {
            // face 1: the head is the '/' the face demands
            assert(rem2.index(0) == 0x2Fu8);
            assert(rem2.index(1) == 0x2Fu8);
            // face 2: the wall-split class over "test" (no wall byte in
            // the run, so the only (wall-free, wall-at-or-end) split is
            // the whole run)
            let t = rem2.subrange(2, (rem2.len() as int));
            assert((t.len() as int) == 4);
            assert forall|kk: int| #![trigger parser::file_wall_free(t, kk)]
                (0 <= kk && kk <= (t.len() as int)
                    && parser::file_wall_free(t, kk)
                    && (kk == (t.len() as int)
                        || parser::file_wall_byte(t.index(kk))))
                implies parser::host_run_class(t.subrange(0, kk)) by {
                if kk == 4 {
                    assert(t.subrange(0, 4) == t);
                    assert(parser::host_run_class(t));
                } else {
                    assert(kk < 4);
                    assert(t.index(kk) != 0x2Fu8 && t.index(kk) != 0x5Cu8
                        && t.index(kk) != 0x3Fu8 && t.index(kk) != 0x23u8);
                    assert(false);
                }
            }
            assert(parser::file_host_entry_class(t));
        }
        assert(0x61 <= s.index(0) <= 0x7A);
        assert(s.index(4) == 0x3Au8);
    }
}

/// file://test: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsf01()
{
    let v: Vec<u8> = vec![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8]);
        wsf01_cls();
        wn_file_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: file://localhost/test
#[verifier::rlimit(600)]
proof fn wsf02_cls()
    ensures wn_file_class(seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x6Cu8, 0x6Fu8, 0x63u8, 0x61u8, 0x6Cu8, 0x68u8, 0x6Fu8, 0x73u8, 0x74u8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8])
{
    let s = seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x6Cu8, 0x6Fu8, 0x63u8, 0x61u8, 0x6Cu8, 0x68u8, 0x6Fu8, 0x73u8, 0x74u8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8];
    assert(parser::machine_domain(s));
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_file_split(s, 4)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        let rem2 = s.subrange(5, (s.len() as int));
        assert(parser::file_state_entry_face(rem2)) by {
            assert(rem2.index(0) == 0x2Fu8);
            assert(rem2.index(1) == 0x2Fu8);
            // face 2: the wall-split class over "localhost/test" (the
            // '/' at 9 is the only wall before the tail end)
            let t = rem2.subrange(2, (rem2.len() as int));
            assert((t.len() as int) == 14);
            assert forall|kk: int| #![trigger parser::file_wall_free(t, kk)]
                (0 <= kk && kk <= (t.len() as int)
                    && parser::file_wall_free(t, kk)
                    && (kk == (t.len() as int)
                        || parser::file_wall_byte(t.index(kk))))
                implies parser::host_run_class(t.subrange(0, kk)) by {
                parser::file_wall_free_iff(t, kk);
                if kk == 9 {
                    assert(t.index(9) == 0x2Fu8);
                    assert(parser::host_run_class(t.subrange(0, 9)));
                } else {
                    assert(kk != 9);
                    if kk < 9 {
                        assert(t.index(kk) != 0x2Fu8 && t.index(kk) != 0x5Cu8
                            && t.index(kk) != 0x3Fu8 && t.index(kk) != 0x23u8);
                        assert(false);
                    } else {
                        assert(kk > 9);
                        assert(t.index(9) == 0x2Fu8);
                        assert(!parser::file_wall_free(t, kk));
                        assert(false);
                    }
                }
            }
            assert(parser::file_host_entry_class(t));
        }
        assert(0x61 <= s.index(0) <= 0x7A);
        assert(s.index(4) == 0x3Au8);
    }
}

/// file://localhost/test: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsf02()
{
    let v: Vec<u8> = vec![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x6Cu8, 0x6Fu8, 0x63u8, 0x61u8, 0x6Cu8, 0x68u8, 0x6Fu8, 0x73u8, 0x74u8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x6Cu8, 0x6Fu8, 0x63u8, 0x61u8, 0x6Cu8, 0x68u8, 0x6Fu8, 0x73u8, 0x74u8, 0x2Fu8, 0x74u8, 0x65u8, 0x73u8, 0x74u8]);
        wsf02_cls();
        wn_file_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: file:///foo/bar.txt
#[verifier::rlimit(600)]
proof fn wsf03_cls()
    ensures wn_file_class(seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x74u8, 0x78u8, 0x74u8])
{
    let s = seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x74u8, 0x78u8, 0x74u8];
    assert(parser::machine_domain(s));
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_file_split(s, 4)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        let rem2 = s.subrange(5, (s.len() as int));
        assert(parser::file_state_entry_face(rem2)) by {
            assert(rem2.index(0) == 0x2Fu8);
            assert(rem2.index(1) == 0x2Fu8);
            // face 2: the wall-split class over "/foo/bar.txt" (the
            // head '/' is a wall, so the only wall-free split is empty)
            let t = rem2.subrange(2, (rem2.len() as int));
            assert((t.len() as int) == 12);
            assert forall|kk: int| #![trigger parser::file_wall_free(t, kk)]
                (0 <= kk && kk <= (t.len() as int)
                    && parser::file_wall_free(t, kk)
                    && (kk == (t.len() as int)
                        || parser::file_wall_byte(t.index(kk))))
                implies parser::host_run_class(t.subrange(0, kk)) by {
                parser::file_wall_free_iff(t, kk);
                if kk == 0 {
                    assert(parser::host_run_class(t.subrange(0, 0)));
                } else {
                    assert(kk >= 1);
                    assert(t.index(0) == 0x2Fu8);
                    assert(!parser::file_wall_free(t, kk));
                    assert(false);
                }
            }
            assert(parser::file_host_entry_class(t));
        }
        assert(0x61 <= s.index(0) <= 0x7A);
        assert(s.index(4) == 0x3Au8);
    }
}

/// file:///foo/bar.txt: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsf03()
{
    let v: Vec<u8> = vec![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x74u8, 0x78u8, 0x74u8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x2Fu8, 0x66u8, 0x6Fu8, 0x6Fu8, 0x2Fu8, 0x62u8, 0x61u8, 0x72u8, 0x2Eu8, 0x74u8, 0x78u8, 0x74u8]);
        wsf03_cls();
        wn_file_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: file://spider///
#[verifier::rlimit(600)]
proof fn wsf04_cls()
    ensures wn_file_class(seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x73u8, 0x70u8, 0x69u8, 0x64u8, 0x65u8, 0x72u8, 0x2Fu8, 0x2Fu8, 0x2Fu8])
{
    let s = seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x73u8, 0x70u8, 0x69u8, 0x64u8, 0x65u8, 0x72u8, 0x2Fu8, 0x2Fu8, 0x2Fu8];
    assert(parser::machine_domain(s));
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_file_split(s, 4)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        let rem2 = s.subrange(5, (s.len() as int));
        assert(parser::file_state_entry_face(rem2)) by {
            assert(rem2.index(0) == 0x2Fu8);
            assert(rem2.index(1) == 0x2Fu8);
            // face 2: the wall-split class over "spider///" (the '/'
            // at 6 is the first wall)
            let t = rem2.subrange(2, (rem2.len() as int));
            assert((t.len() as int) == 9);
            assert forall|kk: int| #![trigger parser::file_wall_free(t, kk)]
                (0 <= kk && kk <= (t.len() as int)
                    && parser::file_wall_free(t, kk)
                    && (kk == (t.len() as int)
                        || parser::file_wall_byte(t.index(kk))))
                implies parser::host_run_class(t.subrange(0, kk)) by {
                parser::file_wall_free_iff(t, kk);
                if kk == 6 {
                    assert(t.index(6) == 0x2Fu8);
                    assert(parser::host_run_class(t.subrange(0, 6)));
                } else {
                    assert(kk != 6);
                    if kk < 6 {
                        assert(t.index(kk) != 0x2Fu8 && t.index(kk) != 0x5Cu8
                            && t.index(kk) != 0x3Fu8 && t.index(kk) != 0x23u8);
                        assert(false);
                    } else {
                        assert(kk > 6);
                        assert(t.index(6) == 0x2Fu8);
                        assert(!parser::file_wall_free(t, kk));
                        assert(false);
                    }
                }
            }
            assert(parser::file_host_entry_class(t));
        }
        assert(0x61 <= s.index(0) <= 0x7A);
        assert(s.index(4) == 0x3Au8);
    }
}

/// file://spider///: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsf04()
{
    let v: Vec<u8> = vec![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x73u8, 0x70u8, 0x69u8, 0x64u8, 0x65u8, 0x72u8, 0x2Fu8, 0x2Fu8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x2Fu8, 0x73u8, 0x70u8, 0x69u8, 0x64u8, 0x65u8, 0x72u8, 0x2Fu8, 0x2Fu8, 0x2Fu8]);
        wsf04_cls();
        wn_file_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: file:/example.com/
#[verifier::rlimit(600)]
proof fn wsf05_cls()
    ensures wn_file_class(seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8])
{
    let s = seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8];
    assert(parser::machine_domain(s));
    assert(20 * (s.len() as int) + 400 <= 0xFFFF_FFFF);
    assert(wn_file_split(s, 4)) by {
        assert forall|i: int| #![trigger s.index(i)]
            0 <= i < 4 implies 0x61 <= s.index(i) <= 0x7A by {}
        let lp = parser::lowered_prefix(s.subrange(0, 4), 4);
        assert(lp == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8]) by {
            assert((lp.len() as int) == 4);
            assert forall|i: int| 0 <= i < 4 implies lp.index(i) == s.index(i) by {
                assert(parser::lower_byte(s.index(i)) == s.index(i));
            }
        }
        assert(s.index(4) == 0x3Au8);
        let rem2 = s.subrange(5, (s.len() as int));
        assert(parser::file_state_entry_face(rem2)) by {
            assert(rem2.index(0) == 0x2Fu8);
            assert(rem2.index(1) == 0x65u8);
            assert(rem2.index(1) != 0x2Fu8 && rem2.index(1) != 0x5Cu8);
        }
        assert(0x61 <= s.index(0) <= 0x7A);
        assert(s.index(4) == 0x3Au8);
    }
}

/// file:/example.com/: entry-face certificate and the parse Ok-branch invariant
#[verifier::rlimit(100)]
exec fn wsf05()
{
    let v: Vec<u8> = vec![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x66u8, 0x69u8, 0x6Cu8, 0x65u8, 0x3Au8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8]);
        wsf05_cls();
        wn_file_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
}

/// urltestdata.json record: //
#[verifier::rlimit(600)]
proof fn wsb01_cls()
    ensures wn_bare_class(seq![0x2Fu8, 0x2Fu8])
{
}

/// //: the entry face holds (the scheme-grammar antecedent is
/// false on the non-alpha head); the parse error face is the
/// exported four-error disjunction
#[verifier::rlimit(100)]
exec fn wsb01()
{
    let v: Vec<u8> = vec![0x2Fu8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x2Fu8, 0x2Fu8]);
        wsb01_cls();
        wn_bare_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    if r.is_err() {
        proof {
            assert(r == Err(parser::ParseError::EmptyHost)
                || r == Err(parser::ParseError::InvalidPort)
                || r == Err(parser::ParseError::Overflow)
                || r == Err(parser::ParseError::RelativeUrlWithoutBase));
        }
    }
}

/// urltestdata.json record: //example.com/
#[verifier::rlimit(600)]
proof fn wsb02_cls()
    ensures wn_bare_class(seq![0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8])
{
}

/// //example.com/: the entry face holds (the scheme-grammar antecedent is
/// false on the non-alpha head); the parse error face is the
/// exported four-error disjunction
#[verifier::rlimit(100)]
exec fn wsb02()
{
    let v: Vec<u8> = vec![0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8];
    let sl: &[u8] = &v[..];
    proof {
        assert(sl@ == seq![0x2Fu8, 0x2Fu8, 0x65u8, 0x78u8, 0x61u8, 0x6Du8, 0x70u8, 0x6Cu8, 0x65u8, 0x2Eu8, 0x63u8, 0x6Fu8, 0x6Du8, 0x2Fu8]);
        wsb02_cls();
        wn_bare_certificate(sl@);
    }
    let r = Url::parse(sl);
    if r.is_ok() {
        proof {
            assert(url_invariant(&r.unwrap()));
        }
    }
    if r.is_err() {
        proof {
            assert(r == Err(parser::ParseError::EmptyHost)
                || r == Err(parser::ParseError::InvalidPort)
                || r == Err(parser::ParseError::Overflow)
                || r == Err(parser::ParseError::RelativeUrlWithoutBase));
        }
    }
}

}
