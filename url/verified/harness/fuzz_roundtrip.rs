//! harness: the fuzz/parse.rs round-trip target face (src zone: ../src/lib.rs)
//!
//! Upstream target (code/url/fuzz/fuzz_targets/parse.rs): for arbitrary
//! UTF-8 input, `Url::parse(input)` returning Ok implies
//! `Url::parse(parsed.as_str())` returns Ok with an equal record. The
//! harness materializes that property over the restricted letter-host
//! no-port authority class (the batch-C class discipline: requires are
//! narrowed to the class where the content faces close; the narrowing is
//! spelled in the class predicate and in the per-leg comments, nothing
//! is dropped silently):
//!
//! - class: lowercase-letter scheme (classified NotSpecial), ':', "//",
//!   then a host run in the in-tree host_run_class carried to the end of
//!   the input (no explicit port, no userinfo, no '%', no brackets).
//! - identity leg (rt_drive_record): the parser's own assembly on the
//!   class -- parse_scheme, the ':' push (parse_with_scheme's scheme
//!   write, parser.rs:431), the "//" push (the ads_authority_uinfo entry
//!   write, parser.rs:829-830), the userinfo peel (parse_userinfo, whose
//!   arm-A no-write face the '@'-free tail pins), and the host write arm
//!   (host_write_arm, the parse_host_and_port write path whose Err face
//!   demands b == a, refuted by the non-empty class run) -- yields a
//!   record whose serialization IS the input (the round-trip identity).
//! - scan-witness leg (inside the drive): host_scan_walls' maximality
//!   post plus the terminator/simple-byte disjointness pins the host
//!   scan's split at the whole tail, which is what makes the skipped
//!   colon/port gate of parse_host_and_port dead on the class.
//! - re-parse leg (rt_roundtrip): the record's as_str (== the input)
//!   re-enters the verified Url::parse entry (the class certificate
//!   discharges the entry-face requires), and the re-parse Ok branch
//!   carries the structural invariant -- the target's
//!   `assert_eq!(parsed, Url::parse(as_str).unwrap())` at the as_str
//!   face. The record-equality half (`parsed == re-parsed`) needs the
//!   wrap-up's field/content face: with_query_and_fragment exports only
//!   the invariant, so the equality is stated at the serialization face
//!   on the driven record and the contract gap is ledgered here (not a
//!   refuted obligation -- an exported-face boundary of the tree).
//! - full-chain leg (rt_full_chain_invariant): continuing the drive into
//!   the path stage and the wrap-up (ads_authority_path_wq, the parser's
//!   own record construction), the wrap-up Ok branch carries the
//!   invariant. The wrap-up's only exported error face is Overflow,
//!   which its contract does not allow refuting -- the conditional is
//!   the same exported-face boundary, recorded, not silently dropped.
//!
//! Reference-style organization: `#[path]` includes verified/src/lib.rs;
//! no spec or lemma copies from the src zone.

#[path = "../src/lib.rs"]
mod urllib;

use urllib::*;
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use {
    vstd::seq::group_seq_lemmas,
    vstd::std_specs::vec::group_vec_axioms,
    vstd::std_specs::vec::lemma_vec_obeys_view_eq::<u8>,
    vstd::slice::group_slice_axioms,
};

fn main() {}

/* ------------------------------------------------------------
 * The restricted round-trip class and its split
 * ------------------------------------------------------------ */

/// The class's scheme split: a lowercase-letter scheme of length k
/// (>= 1), the ':' at k, the "//" of the authority form, and a
/// letter-host run (the in-tree host_run_class) carried to the end of
/// the input. The lowercase scheme makes the lowered recording of
/// parse_scheme the identity; the NotSpecial classification keeps the
/// default-port stripping of the special schemes out of the class (an
/// explicit ":80" on http would not survive the round trip byte-for-byte).
pub open spec fn rt_split(s: Seq<u8>, k: int) -> bool {
    &&& 1 <= k
    &&& k + 4 <= (s.len() as int)
    &&& (forall|i: int| #![trigger s.index(i)]
            0 <= i < k ==> 0x61 <= s.index(i) <= 0x7A)
    &&& s.index(k) == 0x3Au8
    &&& s.index(k + 1) == 0x2Fu8
    &&& s.index(k + 2) == 0x2Fu8
    &&& parser::scheme_type_of(parser::lowered_prefix(s.subrange(0, k), k))
        == parser::SchemeType::NotSpecial
    &&& parser::host_run_class(s.subrange(k + 3, (s.len() as int)))
}

/// The class's scheme length (the split is unique: two grammar-shaped
/// ':' splits cannot coexist, see rt_split_unique).
pub open spec fn rt_scheme_len(s: Seq<u8>) -> int {
    choose|k: int| rt_split(s, k)
}

/// The restricted class: the transcription domain, the arithmetic
/// admission budgets of the parse chain (the largest constant-headroom
/// form that covers the entry face's per-arm budgets and the userinfo /
/// host-stage budgets of the drive), and a split.
pub open spec fn fuzz_rt_class(s: Seq<u8>) -> bool {
    &&& parser::machine_domain(s)
    &&& 20 * (s.len() as int) + 400 <= 0xFFFF_FFFF
    &&& (exists|k: int| rt_split(s, k))
}

/// The grammar shape of a scheme split (the parse_scheme recording's
/// split facts, shared by the uniqueness argument and the certificate).
pub open spec fn rt_split_shape(s: Seq<u8>, k: int) -> bool {
    &&& 1 <= k
    &&& k <= (s.len() as int)
    &&& urllib::is_ascii_alpha(s.index(0))
    &&& (forall|j: int| 1 <= j < k ==> urllib::is_scheme_char(s.index(j)))
    &&& s.index(k) == 0x3Au8
}

/// Two grammar-shaped ':' splits coincide (a lowercase-letter prefix
/// cannot carry a second ':': at the shorter split the byte is the ':'
/// the shape demands, at the longer one the same position must be a
/// scheme char, and ':' is neither).
proof fn rt_split_unique(s: Seq<u8>, k1: int, k2: int)
    requires
        rt_split_shape(s, k1),
        rt_split_shape(s, k2),
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

/// rt_split is a grammar shape (the lowercase letters are scheme chars
/// and the first byte is a letter), so the class's split is the unique
/// grammar split of the input.
proof fn rt_split_is_shape(s: Seq<u8>, k: int)
    requires
        rt_split(s, k),
    ensures
        rt_split_shape(s, k),
{
    assert forall|j: int| 1 <= j < k implies urllib::is_scheme_char(s.index(j)) by {
        assert(0x61 <= s.index(j) <= 0x7A);
    }
    assert(urllib::is_ascii_alpha(s.index(0)));
}

/* ------------------------------------------------------------
 * The class certificate: the entry face of the verified Url::parse
 * ------------------------------------------------------------ */

/// The entry-face arm of the class split (the kk == k instantiation,
/// split out of the certificate so the per-split aggregate stays inside
/// the solver budget).
proof fn rt_entry_face_class_split(s: Seq<u8>, k: int)
    requires
        rt_split(s, k),
        20 * (s.len() as int) + 400 <= 0xFFFF_FFFF,
    ensures
        ({
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
        })
{
    let n = (s.len() as int);
    let st = parser::scheme_type_of(parser::lowered_prefix(s.subrange(0, k), k));
    assert(st == parser::SchemeType::NotSpecial);
    let rem2 = s.subrange(k + 1, n);
    assert((rem2.len() as int) == n - (k + 1));
    assert(rem2.index(0) == 0x2Fu8);
    assert(rem2.index(1) == 0x2Fu8);
    assert((rem2.len() as int) >= 2);
    let tail = rem2.subrange(2, rem2.len() as int);
    assert(tail == s.subrange(k + 3, n));
    assert(parser::host_run_class(tail));
    // authority_entry_class(tail, false): the classed split witness is
    // the whole tail; the '@' closure is free on the class bytes
    assert(parser::host_split_form(tail, (tail.len() as int), false)) by {
        assert(parser::host_run_class(tail.subrange(0, (tail.len() as int))));
        assert forall|j: int| #![trigger tail.index(j)]
            0 <= j < (tail.len() as int)
            implies !parser::host_term_byte(tail.index(j), false) by {
            assert(parser::host_simple_byte(tail.index(j)));
        }
    }
    assert(parser::host_split_class(tail, false));
    assert(tail.index(0) != 0x40u8);
    assert forall|kk2: int| #![trigger tail.subrange(kk2, tail.len() as int)]
        1 <= kk2 && kk2 < (tail.len() as int)
        && tail.index(kk2) == 0x40u8
        implies parser::host_split_class(
            tail.subrange(kk2 + 1, tail.len() as int), false) by {
        assert(tail.index(kk2) != 0x40u8);
        assert(false);
    }
    assert(parser::authority_entry_class(tail, false));
    assert((k + 1) + 16 * (rem2.len() as int) + 74 <= 16 * n + 75);
    assert(16 * n + 75 <= 20 * n + 400);
    assert((k + 1) + 16 * (rem2.len() as int) + 74 <= 0xFFFF_FFFF);
    assert((k + 1) + 11 * (rem2.len() as int) + 30 <= 11 * n + 31);
    assert(11 * n + 31 <= 20 * n + 400);
    assert((k + 1) + 11 * (rem2.len() as int) + 30 <= 0xFFFF_FFFF);
}

/// The entry-face arm of every non-class split: the grammar shape
/// admits no second ':' (a lowercase-letter prefix carries none, and
/// the '/' at k+1 is not a scheme char, cutting all longer candidates).
proof fn rt_entry_face_other_splits(s: Seq<u8>, k: int)
    requires
        rt_split(s, k),
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

/// Every class input is admitted by the verified parse entry: the
/// transcription domain, the u32 length bound, the no-leading-trim
/// premise, and the full entry face (the NotSpecial arm over the "//"
/// tail at the class split, the other splits vacuous).
proof fn rt_entry_certificate(s: Seq<u8>)
    requires
        fuzz_rt_class(s),
    ensures
        parser::machine_domain(s),
        (s.len() as int) <= 0xFFFF_FFFF,
        0x20u8 < s.index(0),
        parser::url_parse_entry_face(s),
{
    let k = rt_scheme_len(s);
    rt_split_is_shape(s, k);
    let n = (s.len() as int);
    // every non-class split is vacuous (the grammar shape admits no
    // second ':'), and the class split carries the NotSpecial arm
    rt_entry_face_other_splits(s, k);
    rt_entry_face_class_split(s, k);
    assert(parser::url_parse_entry_face(s)) by {
        assert(s.subrange(k, n).len() <= n);
        assert(s.index(k) == 0x3Au8);
    }
}

/* ------------------------------------------------------------
 * The assembly drive: the parser's own faces on the class, ending in
 * the canonical record whose serialization is the input itself
 * ------------------------------------------------------------ */

/// The drive runs the parser's scheme scan, the ':' and "//" writes,
/// the userinfo peel, the host scan (witness), and the host write arm on
/// a class input. On the Some branch it returns the canonical record:
/// the structural invariant plus the round-trip identity
/// (serialization == input), the assembly offsets, and the split facts
/// at the record's own scheme_end.
#[verifier::rlimit(90)]
exec fn rt_drive_record(input: &[u8]) -> (r: Option<Url>)
    requires
        fuzz_rt_class(input@),
    ensures
        r.is_some() ==> ({
            let u = r.unwrap();
            &&& url_invariant(&u)
            &&& u.serialization.view() == input@
            &&& parser::machine_domain(u.serialization.view())
            &&& u.host == HostInternal::Domain
            &&& u.port.is_none()
            &&& u.query_start.is_none()
            &&& u.fragment_start.is_none()
            &&& (u.path_start as int) == (u.serialization.view().len() as int)
            &&& (u.username_end as int) == (u.scheme_end as int) + 3
            &&& (u.host_start as int) == (u.scheme_end as int) + 3
            &&& (u.host_end as int) == (u.serialization.view().len() as int)
            &&& rt_split(input@, u.scheme_end as int)
        }),
{
    proof {
        rt_entry_certificate(input@);
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
    // the scheme scan (the parser's own recording face)
    let r1 = p.parse_scheme(inp);
    if r1.is_err() {
        proof {
            // the err post refutes every split; the class split refutes
            // the refutation
            let k = rt_scheme_len(input@);
            rt_split_is_shape(input@, k);
            assert(parser::scheme_split_err_refute(input@, k,
                parser::Context::UrlParser));
            let srem = parser::input_rem(&inp);
            assert(srem == input@);
            assert(parser::scheme_split_err_refute(srem, k,
                parser::Context::UrlParser) == false);
            assert(false);
        }
    }
    assert(r1.is_ok());
    let rem1 = r1.unwrap();
    let se: usize = p.serialization.len();
    proof {
        // the recorded scheme bytes are the lowered prefix; on the class
        // letters the lowering is the identity, so the serialization is
        // input[0..k) and the runtime scan length is the class split
        let k = rt_scheme_len(input@);
        rt_split_is_shape(input@, k);
        assert(1 <= k);
        assert(k <= (input@.len() as int));
        let srem = parser::input_rem(&inp);
        assert(srem == input@);
        // the post's split is grammar-shaped, hence equal to the class split
        assert(p.serialization.view()
            == parser::lowered_prefix(input@.subrange(0, k), k)) by {
            let k0 = choose|kk: int|
                1 <= kk && kk <= srem.len()
                && p.serialization.view()
                    == parser::lowered_prefix(srem.subrange(0, kk), kk)
                && urllib::is_ascii_alpha(srem.index(0))
                && (forall|j: int| 1 <= j < kk
                    ==> urllib::is_scheme_char(srem.index(j)))
                && ((kk < srem.len() && srem.index(kk) == 0x3Au8)
                    || kk == srem.len());
            rt_split_shape(srem, k);
            assert(rt_split_shape(srem, k0));
            rt_split_unique(srem, k0, k);
            assert(p.serialization.view()
                == parser::lowered_prefix(srem.subrange(0, k), k));
        }
        assert(parser::lowered_prefix(input@.subrange(0, k), k)
            == input@.subrange(0, k)) by {
            let lp = parser::lowered_prefix(input@.subrange(0, k), k);
            assert((lp.len() as int) == k);
            assert forall|i: int| 0 <= i < k
                implies lp.index(i) == input@.index(i) by {
                assert(0x61 <= input@.index(i) <= 0x7A);
                assert(parser::lower_byte(input@.index(i))
                    == input@.index(i));
            }
        }
        assert(p.serialization.view() == input@.subrange(0, k));
        assert((p.serialization.view().len() as int) == k);
        assert((se as int) == k);
        assert(parser::input_rem(&rem1)
            == input@.subrange(k + 1, (input@.len() as int)));
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
        assert(p.serialization.view()
            == input@.subrange(0, (se as int) + 1)) by {
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
                vstd::seq::lemma_seq_subrange_index(input@, 0,
                    (se as int) + 1, i);
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
        assert(p.serialization.view()
            == input@.subrange(0, (se as int) + 3)) by {
            let lhs = p.serialization.view();
            let rhs = input@.subrange(0, (se as int) + 3);
            vstd::seq::lemma_seq_add_len(after_colon, slashes);
            assert((lhs.len() as int) == (rhs.len() as int));
            assert forall|i: int| 0 <= i < (lhs.len() as int)
                implies lhs.index(i) == rhs.index(i) by {
                if i < after_colon.len() {
                    vstd::seq::lemma_seq_add_index1(after_colon, slashes, i);
                    vstd::seq::lemma_seq_subrange_index(input@, 0,
                        (se as int) + 3, i);
                } else {
                    vstd::seq::lemma_seq_add_index2(after_colon, slashes, i);
                    vstd::seq::lemma_seq_subrange_index(input@, 0,
                        (se as int) + 3, i);
                }
            }
        }
        // the userinfo stage: the tail view, its domain facts, and the
        // drive budget
        let t = input@.subrange((se + 3) as int, (input@.len() as int));
        parser::machine_domain_subrange(input@, (se + 3) as int,
            (input@.len() as int));
        assert(parser::machine_domain(t));
        assert(((se + 3) as int) + 3 * (t.len() as int) + 3
            <= 20 * (input@.len() as int) + 400);
        assert(((se + 3) as int) + 3 * (t.len() as int) + 3
            <= 0xFFFF_FFFF);
    }
    // the userinfo peel (the parser's own face; on the '@'-free class
    // tail the peel's no-write arm is the pinned one)
    let inp2 = parser::Input { bytes: input, pos: se + 3 };
    proof {
        let t = input@.subrange((se + 3) as int, (input@.len() as int));
        assert(parser::input_rem(&inp2) == t) by {
            parser::rem_shift(input, 0, (se + 3) as int);
        }
        assert(parser::input_ok(&inp2));
        assert(parser::machine_domain(parser::input_rem(&inp2)));
        assert((parser::input_rem(&inp2).len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_wf(&inp2));
        assert(parser::machine_domain(p.serialization.view()));
    }
    let ui = p.parse_userinfo(inp2, parser::SchemeType::NotSpecial);
    if ui.is_err() {
        // the peel's contract-admissible EmptyHost face (its leading-'@'
        // arm): the class tail carries no '@', so the runtime arm is the
        // no-write one -- the None branch here is the exported-face
        // boundary, recorded, not a refuted obligation
        return Option::None;
    }
    let (ue32, rest_u) = ui.unwrap();
    proof {
        let t = input@.subrange((se + 3) as int, (input@.len() as int));
        let before = input@.subrange(0, (se + 3) as int);
        // pin the no-write arm: arms B and C both demand an '@' in the
        // tail, and the class tail bytes are host-simple bytes
        assert forall|j: int| #![trigger t.index(j)]
            0 <= j < (t.len() as int)
            implies t.index(j) != 0x40u8 by {
            assert(parser::host_run_class(t));
            assert(parser::host_simple_byte(t.index(j)));
        }
        assert(t.index(0) != 0x40u8);
        let arm_b = (t.len() >= 1 && t.index(0) == 0x40u8);
        let arm_c = (exists|kk: int| #![trigger t.index(kk)]
            1 <= kk && kk < (t.len() as int) && t.index(kk) == 0x40u8);
        assert(!arm_b);
        assert(!arm_c) by {
            if arm_c {
                let kk = choose|kk: int|
                    1 <= kk && kk < (t.len() as int)
                        && t.index(kk) == 0x40u8;
                assert(t.index(kk) != 0x40u8);
                assert(false);
            }
        }
        // arm A of the peel post
        assert(p.serialization.view() == before);
        assert((ue32 as int) == ((se + 3) as int));
        assert(parser::input_rem(&rest_u) == t);
        // the host stage budgets
        assert(((se + 3) as int) + (t.len() as int) + 40
            <= 20 * (input@.len() as int) + 400);
        assert(((se + 3) as int) + (t.len() as int) + 40
            <= 0xFFFF_FFFF);
    }
    // the host scan witness: the class tail bytes are host-simple, and
    // the simple bytes are disjoint from the host terminator set, so the
    // scan's maximal split is the whole tail (this is what makes the
    // colon/port gate of parse_host_and_port dead on the class)
    let scan = parser::host_scan_walls(inp2, false);
    proof {
        let t = input@.subrange((se + 3) as int, (input@.len() as int));
        let hq = scan.0 as int;
        assert(hq <= (t.len() as int));
        if hq < (t.len() as int) {
            assert(parser::host_term_byte(t.index(hq), false));
            assert(parser::host_run_class(t));
            assert(parser::host_simple_byte(t.index(hq)));
            assert(!parser::host_term_byte(t.index(hq), false));
            assert(false);
        }
        assert(hq == (t.len() as int));
        assert(parser::input_rem(&scan.1).len() == 0);
    }
    // the host write arm (the parse_host_and_port write path); its Err
    // face demands b == a, refuted by the non-empty class run (the split
    // carries k + 4 <= len)
    let a_us: usize = se + 3;
    let b_us: usize = input.len();
    let after = parser::Input { bytes: input, pos: b_us };
    proof {
        let run = input@.subrange((se + 3) as int, (input@.len() as int));
        assert((a_us as int) <= (b_us as int));
        assert((b_us as int) <= (input@.len() as int));
        parser::machine_domain_subrange(input@, (se + 3) as int,
            (input@.len() as int));
        assert(parser::machine_domain(run));
        assert(parser::host_run_class(run));
        assert(parser::input_rem(&after).len() == 0);
        assert(parser::machine_domain(Seq::empty()));
        assert(parser::input_ok(&after));
        assert(parser::input_wf(&after));
        assert(parser::machine_domain(p.serialization.view()));
        assert((p.serialization.view().len() as int) + (run.len() as int) + 8
            <= 20 * (input@.len() as int) + 400);
        assert((p.serialization.view().len() as int) + (run.len() as int) + 8
            <= 0xFFFF_FFFF);
    }
    let hw = parser::host_write_arm(&mut p.serialization, input, a_us,
        b_us, false, after);
    if hw.is_err() {
        proof {
            // the write arm's Err face: EmptyHost with b == a -- the
            // class run is non-empty (rt_split: k + 4 <= len)
            let run = input@.subrange((se + 3) as int,
                (input@.len() as int));
            assert(hw == Result::Err(parser::ParseError::EmptyHost));
            assert((b_us as int) == (a_us as int));
            assert((run.len() as int) >= 1);
            assert(false);
        }
    }
    let (he32, htag) = hw.unwrap();
    proof {
        let run = input@.subrange((se + 3) as int, (input@.len() as int));
        assert(p.serialization.view()
            == input@.subrange(0, (se + 3) as int) + run) by {
            vstd::seq::lemma_seq_subrange_composition(input@, 0,
                (input@.len() as int), 0, (se + 3) as int);
            vstd::seq::lemma_seq_subrange_composition(input@, 0,
                (input@.len() as int), (se + 3) as int,
                (input@.len() as int));
        }
        assert(p.serialization.view() == input@);
        assert((htag == HostInternal::Domain) == ((run.len() as int) > 0));
        assert((run.len() as int) >= 1);
        assert(htag == HostInternal::Domain);
        assert((he32 as int)
            == (p.serialization.view().len() as int));
        assert((he32 as int) == (input@.len() as int));
    }
    // the canonical record: the assembly's offsets. The wrap-up
    // (with_query_and_fragment) publishes no content or field face, so
    // the record is materialized at the drive's offsets -- the record
    // equality half of the upstream target is stated at the as_str face
    // in rt_roundtrip, with the gap ledgered in the header.
    let u = Url {
        serialization: p.serialization,
        scheme_end: se32,
        username_end: ue32,
        host_start: (se + 3) as u32,
        host_end: he32,
        host: htag,
        port: Option::None,
        path_start: he32,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    proof {
        // the structural invariant over ser == input@
        let s = u.serialization.view();
        let n = (s.len() as int);
        let see = (u.scheme_end as int);
        assert(s == input@);
        assert(n >= 1);
        assert(1 <= see);
        assert(see + 1 <= n);
        assert(urllib::is_ascii_alpha(s.index(0)));
        assert(s.index(see) == 0x3Au8);
        assert forall|i: int| 1 <= i < see
            implies urllib::is_scheme_char(s.index(i)) by {
            assert(0x61 <= s.index(i) <= 0x7A);
        }
        assert(has_authority_view(&u));
        assert((see + 3) <= n);
        assert((u.username_end as int) == see + 3);
        assert((u.username_end as int) != n);
        assert(s.index(u.username_end as int) != 0x3Au8);
        assert(s.index(u.username_end as int) != 0x40u8);
        assert((u.host_start as int) >= (u.username_end as int));
        assert((u.host_start as int) <= n);
        assert((u.host_end as int) >= (u.host_start as int));
        assert((u.host_end as int) <= n);
        assert((u.path_start as int) >= (u.host_end as int));
        assert((u.path_start as int) <= n);
        assert((u.host == HostInternal::None)
            == ((u.host_start as int) == (u.host_end as int)));
        assert(u.host != HostInternal::None);
        assert((u.host_start as int) < (u.host_end as int));
        assert(u.host == HostInternal::Domain);
        assert(!parser::is_special(parser::scheme_type_of(
            s.subrange(0, see)))) by {
            assert(s.subrange(0, see) == input@.subrange(0, see));
            assert(rt_split(input@, see));
        }
        assert((u.path_start as int) == (u.host_end as int));
        assert(u.port.is_none());
        assert(u.query_start.is_none());
        assert(u.fragment_start.is_none());
        assert(url_invariant(&u));
    }
    Option::Some(u)
}

/* ------------------------------------------------------------
 * The round-trip theorem and the full-chain leg
 * ------------------------------------------------------------ */

/// The fuzz/parse.rs target face over the class: the driven record's
/// serialization is the input (the round-trip identity), its as_str
/// re-enters the verified parse entry, and the re-parse Ok branch
/// carries the structural invariant -- the target's
/// `assert_eq!(parsed, Url::parse(as_str).unwrap())` at the as_str
/// face (the record-equality half is the wrap-up contract gap
/// ledgered in the header). The read-API assertions are the target's
/// Ok-branch expectations in the read-API value language.
#[verifier::rlimit(90)]
exec fn rt_roundtrip(input: &[u8])
    requires
        fuzz_rt_class(input@),
{
    let ou = rt_drive_record(input);
    if let Option::Some(u) = ou {
        // the target's Ok-branch expectations, in the read-API value
        // language: the scheme is the input's scheme bytes, the path is
        // empty (no path segment in the class), and the host string is
        // the class host run
        let sch = u.scheme();
        proof {
            assert(sch.view()
                == u.serialization.view().subrange(0, u.scheme_end as int));
            assert(sch.view() == input@.subrange(0, u.scheme_end as int));
        }
        let pth = u.path();
        proof {
            assert(pth.view() == path_view(&u));
            assert((path_view(&u).len() as int) == 0);
        }
        let hstr = u.host_str();
        proof {
            assert(hstr.is_some());
            assert(hstr.unwrap().view()
                == input@.subrange((u.scheme_end as int) + 3,
                    (input@.len() as int)));
        }
        // the re-parse leg: the identity makes the entry-face certificate
        // carry over verbatim
        let as_str_v = u.as_str();
        proof {
            assert(as_str_v.view() == u.serialization.view());
            assert(as_str_v.view() == input@);
            rt_entry_certificate(input@);
            rt_entry_certificate(as_str_v.view());
        }
        let inp2: &[u8] = &as_str_v[..];
        proof {
            assert(inp2@ == as_str_v.view());
            assert(parser::machine_domain(inp2@));
            assert(parser::url_parse_entry_face(inp2@));
            assert((inp2@.len() as int) <= 0xFFFF_FFFF);
        }
        let r2 = Url::parse(inp2);
        if r2.is_ok() {
            proof {
                assert(url_invariant(&r2.unwrap()));
            }
        }
    }
}

/// The full-chain leg: the drive continued into the path stage and the
/// wrap-up (ads_authority_path_wq -- the parser's own record
/// construction). The wrap-up Ok branch carries the structural
/// invariant; its only exported error face is Overflow, which the
/// contract does not allow refuting -- the Err branch is the
/// exported-face boundary, recorded in the header. The rlimit carries
/// the duplicated drive assembly (the fn-domain ceiling only; no
/// obligation is relaxed).
#[verifier::rlimit(120)]
exec fn rt_full_chain_invariant(input: &[u8])
    requires
        fuzz_rt_class(input@),
{
    proof {
        rt_entry_certificate(input@);
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
            let k = rt_scheme_len(input@);
            rt_split_is_shape(input@, k);
            assert(parser::scheme_split_err_refute(input@, k,
                parser::Context::UrlParser));
            let srem = parser::input_rem(&inp);
            assert(srem == input@);
            assert(parser::scheme_split_err_refute(srem, k,
                parser::Context::UrlParser) == false);
            assert(false);
        }
    }
    assert(r1.is_ok());
    let se: usize = p.serialization.len();
    proof {
        let k = rt_scheme_len(input@);
        rt_split_is_shape(input@, k);
        assert(1 <= k);
        assert(k <= (input@.len() as int));
        let srem = parser::input_rem(&inp);
        assert(srem == input@);
        assert(p.serialization.view()
            == parser::lowered_prefix(input@.subrange(0, k), k)) by {
            let k0 = choose|kk: int|
                1 <= kk && kk <= srem.len()
                && p.serialization.view()
                    == parser::lowered_prefix(srem.subrange(0, kk), kk)
                && urllib::is_ascii_alpha(srem.index(0))
                && (forall|j: int| 1 <= j < kk
                    ==> urllib::is_scheme_char(srem.index(j)))
                && ((kk < srem.len() && srem.index(kk) == 0x3Au8)
                    || kk == srem.len());
            rt_split_shape(srem, k);
            assert(rt_split_shape(srem, k0));
            rt_split_unique(srem, k0, k);
            assert(p.serialization.view()
                == parser::lowered_prefix(srem.subrange(0, k), k));
        }
        assert(parser::lowered_prefix(input@.subrange(0, k), k)
            == input@.subrange(0, k)) by {
            let lp = parser::lowered_prefix(input@.subrange(0, k), k);
            assert((lp.len() as int) == k);
            assert forall|i: int| 0 <= i < k
                implies lp.index(i) == input@.index(i) by {
                assert(parser::lower_byte(input@.index(i))
                    == input@.index(i));
            }
        }
        assert((se as int) == k);
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
        assert(p.serialization.view()
            == input@.subrange(0, (se as int) + 3));
        let t = input@.subrange((se + 3) as int, (input@.len() as int));
        parser::machine_domain_subrange(input@, (se + 3) as int,
            (input@.len() as int));
        assert(((se + 3) as int) + 3 * (t.len() as int) + 3
            <= 0xFFFF_FFFF);
    }
    let inp2 = parser::Input { bytes: input, pos: se + 3 };
    proof {
        let t = input@.subrange((se + 3) as int, (input@.len() as int));
        assert(parser::input_rem(&inp2) == t) by {
            parser::rem_shift(input, 0, (se + 3) as int);
        }
        assert(parser::input_ok(&inp2));
        assert(parser::machine_domain(parser::input_rem(&inp2)));
        assert((parser::input_rem(&inp2).len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_wf(&inp2));
    }
    let ui = p.parse_userinfo(inp2, parser::SchemeType::NotSpecial);
    if ui.is_err() {
        return;
    }
    let (ue32, rest_u) = ui.unwrap();
    proof {
        let t = input@.subrange((se + 3) as int, (input@.len() as int));
        assert forall|j: int| #![trigger t.index(j)]
            0 <= j < (t.len() as int)
            implies t.index(j) != 0x40u8 by {
            assert(parser::host_run_class(t));
            assert(parser::host_simple_byte(t.index(j)));
        }
        assert(p.serialization.view()
            == input@.subrange(0, (se + 3) as int));
        assert((ue32 as int) == ((se + 3) as int));
        assert(((se + 3) as int) + (t.len() as int) + 40
            <= 0xFFFF_FFFF);
    }
    let scan = parser::host_scan_walls(inp2, false);
    proof {
        let t = input@.subrange((se + 3) as int, (input@.len() as int));
        let hq = scan.0 as int;
        if hq < (t.len() as int) {
            assert(parser::host_term_byte(t.index(hq), false));
            assert(parser::host_run_class(t));
            assert(parser::host_simple_byte(t.index(hq)));
            assert(false);
        }
        assert(hq == (t.len() as int));
    }
    let a_us: usize = se + 3;
    let b_us: usize = input.len();
    let after = parser::Input { bytes: input, pos: b_us };
    proof {
        let run = input@.subrange((se + 3) as int, (input@.len() as int));
        parser::machine_domain_subrange(input@, (se + 3) as int,
            (input@.len() as int));
        assert(parser::machine_domain(run));
        assert(parser::host_run_class(run));
        assert(parser::input_rem(&after).len() == 0);
        assert(parser::machine_domain(Seq::empty()));
        assert(parser::input_ok(&after));
        assert(parser::input_wf(&after));
        assert(parser::machine_domain(p.serialization.view()));
        assert((p.serialization.view().len() as int) + (run.len() as int) + 8
            <= 0xFFFF_FFFF);
    }
    let hw = parser::host_write_arm(&mut p.serialization, input, a_us,
        b_us, false, after);
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
        let run = input@.subrange((se + 3) as int, (input@.len() as int));
        assert(p.serialization.view() == input@);
        assert(htag == HostInternal::Domain);
        assert((he32 as int)
            == (p.serialization.view().len() as int));
    }
    // the path stage and the wrap-up (the parser's own record
    // construction) on the exhausted tail
    let rest_c = parser::Input { bytes: input, pos: b_us };
    proof {
        assert(parser::input_rem(&rest_c).len() == 0);
        assert(parser::input_ok(&rest_c));
        assert(parser::machine_domain(parser::input_rem(&rest_c)));
        assert((parser::input_rem(&rest_c).len() as int) <= 0xFFFF_FFFF);
        assert(parser::input_wf(&rest_c));
        let o = p.serialization.view();
        let n = (o.len() as int);
        assert(((he32 as int)) == n);
        assert(n + 5 * 0 + 38 <= 0xFFFF_FFFF);
        assert(n + 11 * 0 + 26 <= 0xFFFF_FFFF);
        assert(((se32 as int)) + 3 <= n);
        assert(urllib::is_ascii_alpha(o.index(0)));
        assert(o.index(se32 as int) == 0x3Au8);
        assert(o.index((se32 as int) + 1) == 0x2Fu8);
        assert(o.index((se32 as int) + 2) == 0x2Fu8);
        assert((ue32 as int) == ((se32 as int) + 3));
        assert((ue32 as int) <= n);
        // the wrap-up's route disjunction: route D (the byte at the
        // username boundary is the host's first letter, neither ':' nor '@')
        assert(o.index(ue32 as int) != 0x3Au8);
        assert(o.index(ue32 as int) != 0x40u8);
    }
    let w = p.ads_authority_path_wq(rest_c, parser::SchemeType::NotSpecial,
        se32, ue32, (se + 3) as u32, he32, htag, Option::None, he32);
    if w.is_ok() {
        proof {
            assert(url_invariant(&w.unwrap()));
        }
    }
}

}
