//! harness: parse-machine staged witnesses (src zone: ../src/lib.rs)
//!
//! Stage-driver for the parser state-machine materialization batch: the
//! machine faces under verification are the byte-model Input, the scheme
//! scan (parse_scheme), the port scan/writer, the percent-encoding model,
//! and later segments as they land. Reference-style organization:
//! `#[path]` includes verified/src/lib.rs, no spec copies.

#[path = "../src/lib.rs"]
mod urllib;

use urllib::*;
use vstd::seq::seq;
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use {
    vstd::seq::group_seq_lemmas,
    vstd::std_specs::vec::group_vec_axioms,
    vstd::std_specs::vec::lemma_vec_obeys_view_eq::<u8>,
    vstd::slice::group_slice_axioms,
};

/* ------------------------------------------------------------
 * Stage exemplars: deterministic concrete drives of the landed
 * scheme scan (the parse-urltestdata scheme face). The carries use
 * Vec-backed views (literal byte-slice views do not resolve their
 * elements for the solver). Deterministic drives of the Porter and
 * the query/fragment placement take the Err-side refutation
 * machinery registered for the scanner-completion batch.
 * ------------------------------------------------------------ */

/// scheme exemplar: "https://" scans "https", remaining starts after ':'
/// (the parse_with_scheme dispatcher consumes it).
exec fn ex_scheme_https()
{
    let v: Vec<u8> = vec![
        0x68u8, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x78,
    ];
    let inp_slice: &[u8] = &v[..];
    let input = parser::Input { bytes: inp_slice, pos: 0 };
    proof {
        assert(parser::machine_domain(inp_slice@));
        assert((inp_slice@.len() as int) <= 0xFFFF_FFFF);
        assert(inp_slice@.len() == 9);
        assert(parser::input_rem(&input).index(0) == 0x68u8);
        assert(parser::input_rem(&input).index(1) == 0x74u8);
        assert(parser::input_rem(&input).index(2) == 0x74u8);
        assert(parser::input_rem(&input).index(3) == 0x70u8);
        assert(parser::input_rem(&input).index(4) == 0x73u8);
        assert(parser::input_rem(&input).index(5) == 0x3au8);
        assert(urllib::is_ascii_alpha(parser::input_rem(&input).index(0)));
        assert(urllib::is_scheme_char(0x74u8));
        assert(parser::scheme_split_err_refute(parser::input_rem(&input), 5,
            parser::Context::UrlParser) == true);
    }
    let mut p = parser::Parser {
        serialization: Vec::new(),
        base_url: None,
        context: parser::Context::UrlParser,
    };
    let r = p.parse_scheme(input);
    if r.is_err() {
        proof {
            assert(false);
        }
    }
    assert(r.is_ok());
    assert(parser::input_rem(&r.unwrap()) == seq![0x2Fu8, 0x2F, 0x78]);
    assert(p.serialization.view() == seq![0x68u8, 0x74, 0x74, 0x70, 0x73]);
}

/// scheme exemplar: "HTTP://x" lowercases the scheme bytes (parser.rs:408).
exec fn ex_scheme_uppercase()
{
    let v: Vec<u8> = vec![0x48u8, 0x54, 0x54, 0x50, 0x3a, 0x2f, 0x2f, 0x78];
    let inp_slice: &[u8] = &v[..];
    let input = parser::Input { bytes: inp_slice, pos: 0 };
    proof {
        assert(parser::machine_domain(inp_slice@));
        assert((inp_slice@.len() as int) <= 0xFFFF_FFFF);
        assert(inp_slice@.len() == 8);
        assert(parser::input_rem(&input).index(0) == 0x48u8);
        assert(parser::input_rem(&input).index(1) == 0x54u8);
        assert(parser::input_rem(&input).index(2) == 0x54u8);
        assert(parser::input_rem(&input).index(3) == 0x50u8);
        assert(parser::input_rem(&input).index(4) == 0x3au8);
        assert(urllib::is_ascii_alpha(parser::input_rem(&input).index(0)));
        assert(parser::scheme_split_err_refute(parser::input_rem(&input), 4,
            parser::Context::UrlParser) == true);
    }
    let mut p = parser::Parser {
        serialization: Vec::new(),
        base_url: None,
        context: parser::Context::UrlParser,
    };
    let r = p.parse_scheme(input);
    if r.is_err() {
        proof {
            assert(false);
        }
    }
    assert(r.is_ok());
    assert(p.serialization.view() == seq![0x68u8, 0x74, 0x74, 0x70]);
}

/// Url::parse entry exemplar (the non-special authority drive):
/// "custom://host/path" -- the ":://" arm reaches the FACE-1 authority
/// chain (after_double_slash) through parse_non_special. The drive
/// instantiates the whole entry stack: machine domain, no-leading-trim,
/// and url_parse_entry_face at the unique scheme split k=6 (the
/// NotSpecial class face over "//host/path" with the host-split
/// witness h=4, the run "host" followed by the '/' terminator).
exec fn ex_url_custom_authority_entry()
{
    let v: Vec<u8> = vec![
        0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
        0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68,
    ];
    let inp_slice: &[u8] = &v[..];
    proof {
        assert(inp_slice@ == seq![
            0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
            0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
            0x2f, 0x70, 0x61, 0x74, 0x68,
        ]);
        assert(parser::machine_domain(inp_slice@));
        assert((inp_slice@.len() as int) == 18);
        assert(0x20u8 < inp_slice@.index(0));
        assert(urllib::is_ascii_alpha(inp_slice@.index(0)));
        assert(inp_slice@.index(6) == 0x3au8);
        ex_entry_face_custom();
        assert(parser::url_parse_entry_face(inp_slice@));
    }
    let r = urllib::Url::parse(inp_slice);
    // the postcondition instantiation: any Ok value carries the full
    // structural url_invariant (the concrete Ok-ness itself is a
    // runtime fact here; the drive's verification content is the
    // non-vacuity of the whole entry stack above)
    assert(r.is_ok() ==> urllib::url_invariant(&r.unwrap()));
}

/// The exemplar's entry-face certificate (the split case analysis for
/// the unique ':' at index 6 of "custom://host/path", the NotSpecial
/// class face over the "//" tail with the host-split witness h=4 over
/// "host"): a separate proof fn so the drive's aggregate body check
/// stays inside the solver budget.
proof fn ex_entry_face_custom()
    ensures ({
        let ex = seq![
            0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
            0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
            0x2f, 0x70, 0x61, 0x74, 0x68,
        ];
        parser::url_parse_entry_face(ex)
    })
    decreases 0int,
{
    let s = seq![
        0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
        0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68,
    ];
    assert(s.len() == 18);
    assert(parser::machine_domain(s));
    assert(parser::url_parse_entry_face(s)) by {
            assert forall|k: int|
                #![trigger s.subrange(k,
                    s.len() as int)]
                (0 <= k)
                    && (k + 1 <= (s.len() as int))
                    && (s.subrange(k,
                            s.len() as int).len() as int)
                        <= (s.len() as int)
                    && urllib::is_ascii_alpha(s.index(0))
                    && (forall|j: int| 1 <= j && j < k
                        ==> urllib::is_scheme_char(
                            s.index(j)))
                    && s.index(k) == 0x3au8
                implies ({
                    let st = parser::scheme_type_of(
                        parser::lowered_prefix(
                            s.subrange(0, k), k));
                    let rem2 = s.subrange(
                        k + 1, s.len() as int);
                    (st == parser::SchemeType::File
                        ==> (parser::file_state_entry_face(rem2)
                            && (k + 1)
                                + 20 * (rem2.len() as int) + 176
                                <= 0xFFFF_FFFF))
                    && (st == parser::SchemeType::SpecialNotFile
                        ==> (forall|c: int|
                                #![trigger rem2.subrange(c,
                                    rem2.len() as int)]
                                (0 <= c
                                    && c <= (rem2.len() as int)
                                    && (rem2.subrange(c,
                                            rem2.len() as int).len()
                                        as int)
                                        <= (rem2.len() as int)
                                    && parser::slash_run_prefix(rem2, c)
                                    && ((c == rem2.len() as int)
                                        || (rem2.index(c) != 0x2fu8
                                            && rem2.index(c) != 0x5cu8)))
                                ==> (parser::authority_entry_class(
                                        rem2.subrange(c,
                                            rem2.len() as int), true)
                                    && (k + 1)
                                        + 16 * ((rem2.len() as int) - c)
                                        + 74
                                        <= 0xFFFF_FFFF)))
                        && (st == parser::SchemeType::NotSpecial ==> (
                            (((rem2.len() as int) >= 2
                                && rem2.index(0) == 0x2fu8
                                && rem2.index(1) == 0x2fu8)
                                ==> parser::authority_entry_class(
                                    rem2.subrange(2,
                                        rem2.len() as int), false))
                            && (k + 1) + 16 * (rem2.len() as int) + 74
                                <= 0xFFFF_FFFF
                            && (k + 1) + 11 * (rem2.len() as int) + 30
                                <= 0xFFFF_FFFF))
                })
            by {
                // the only ':' sits at index 6; for k > 6 the
                // scheme-char span would include it; k < 6 has no ':'
                if k > 6 {
                    assert(!urllib::is_scheme_char(0x3au8));
                    assert(false);
                } else if k < 6 {
                    assert(s.index(k) != 0x3au8);
                    assert(false);
                } else {
                    assert(k == 6);
                    ex_entry_face_case6();
                }
            }
        }
}

/// The k == 6 slice of the exemplar's entry face (the NotSpecial
/// classification of the "custom" scheme bytes and the post-scheme
/// faces over the "//host/path" remainder): a separate proof fn so
/// the face certificate's aggregate stays inside the solver budget.
proof fn ex_case6_scheme()
    ensures ({
        let s = seq![
            0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
            0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
            0x2f, 0x70, 0x61, 0x74, 0x68,
        ];
        parser::scheme_type_of(parser::lowered_prefix(
            s.subrange(0, 6), 6))
            == parser::SchemeType::NotSpecial
    })
    decreases 0int
{
    let s = seq![
        0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
        0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68,
    ];
    let lp = parser::lowered_prefix(s.subrange(0, 6), 6);
    assert(lp == seq![
        0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d]);
}

/// The "//"-conditional class face of the exemplar's k == 6 slice
/// (over "host/path", the host-split witness h=4).
/// The class certificate of the exemplar's host tail (the
/// host-split witness h=4 over "host" with the '/' terminator, the
/// @-free closure).
/// The host-split certificate of the exemplar's tail (the run
/// "host" with the '/' terminator).
proof fn ex_case6_hostsplit()
    ensures ({
        let s = seq![
            0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
            0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
            0x2f, 0x70, 0x61, 0x74, 0x68,
        ];
        let rem2 = s.subrange(7, 18);
        let tail = rem2.subrange(2, rem2.len() as int);
        parser::host_split_form(tail, 4, false)
    })
    decreases 0int
{
    let s = seq![
        0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
        0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68,
    ];
    let rem2 = s.subrange(7, 18);
    let tail = rem2.subrange(2, 11);
    assert(tail == seq![
        0x68u8, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68]);
    let hostpart = tail.subrange(0, 4);
    assert(hostpart == seq![0x68u8, 0x6f, 0x73, 0x74]);
    assert(parser::host_run_class(hostpart));
    assert((forall|j: int| 0 <= j && j < 4
        ==> !parser::host_term_byte(
            tail.index(j), false)));
    assert(parser::host_term_byte(tail.index(4), false));
}

/// The class certificate of the exemplar's host tail (the @-free
/// closure over the host-split form).
proof fn ex_case6_authority_class()
    ensures ({
        let s = seq![
            0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
            0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
            0x2f, 0x70, 0x61, 0x74, 0x68,
        ];
        let rem2 = s.subrange(7, 18);
        parser::authority_entry_class(
            rem2.subrange(2, rem2.len() as int), false)
    })
    decreases 0int
{
    let s = seq![
        0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
        0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68,
    ];
    let rem2 = s.subrange(7, 18);
    let tail = rem2.subrange(2, 11);
    // The host-split certificate of the helper carries the split
    // forms; the class closure (the split class and the @-free
    // conjuncts) evaluates over the ground tail literals without
    // hand-guidance -- hand-holding intermediate facts made the
    // whole-fn aggregate exceed the solver budget.
    ex_case6_hostsplit();
}

/// The k == 6 slice of the exemplar's entry face (the NotSpecial
/// classification of the "custom" scheme bytes and the post-scheme
/// faces over the "//host/path" remainder): a separate proof fn so
/// the face certificate's aggregate stays inside the solver budget.
/// The "//"-conditional class face of the exemplar's k == 6 slice
/// (over "host/path", the host-split witness h=4).
proof fn ex_case6_classface()
    ensures ({
        let s = seq![
            0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
            0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
            0x2f, 0x70, 0x61, 0x74, 0x68,
        ];
        let rem2 = s.subrange(7, 18);
        (((rem2.len() as int) >= 2
            && rem2.index(0) == 0x2fu8
            && rem2.index(1) == 0x2fu8)
            ==> parser::authority_entry_class(
                rem2.subrange(2, rem2.len() as int), false))
    })
    decreases 0int
{
    let s = seq![
        0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
        0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68,
    ];
    let rem2 = s.subrange(7, 18);
    assert(rem2 == seq![
        0x2fu8, 0x2f, 0x68, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68]);
    ex_case6_authority_class();
    assert((rem2.len() as int) >= 2
        && rem2.index(0) == 0x2fu8
        && rem2.index(1) == 0x2fu8);
}

/// The k == 6 slice of the exemplar's entry face, assembled from the
/// per-conjunct certificates (the aggregate stays inside the solver
/// budget).
proof fn ex_entry_face_case6()
    ensures ({
        let s = seq![
            0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
            0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
            0x2f, 0x70, 0x61, 0x74, 0x68,
        ];
        let st = parser::scheme_type_of(parser::lowered_prefix(
            s.subrange(0, 6), 6));
        let rem2 = s.subrange(7, 18);
        st == parser::SchemeType::NotSpecial
        && (((rem2.len() as int) >= 2
                && rem2.index(0) == 0x2fu8
                && rem2.index(1) == 0x2fu8)
            ==> parser::authority_entry_class(
                rem2.subrange(2, rem2.len() as int), false))
        && (6 + 1) + 16 * (rem2.len() as int) + 74
            <= 0xFFFF_FFFF
        && (6 + 1) + 11 * (rem2.len() as int) + 30
            <= 0xFFFF_FFFF
    })
    decreases 0int
{
    let s = seq![
        0x63u8, 0x75, 0x73, 0x74, 0x6f, 0x6d, 0x3a,
        0x2f, 0x2f, 0x68, 0x6f, 0x73, 0x74,
        0x2f, 0x70, 0x61, 0x74, 0x68,
    ];
    ex_case6_scheme();
    ex_case6_classface();
    let rem2 = s.subrange(7, 18);
    assert((rem2.len() as int) >= 2
        && rem2.index(0) == 0x2fu8
        && rem2.index(1) == 0x2fu8);
    assert((6 + 1) + 16 * (rem2.len() as int) + 74
        <= 0xFFFF_FFFF);
    assert((6 + 1) + 11 * (rem2.len() as int) + 30
        <= 0xFFFF_FFFF);
}

fn main() {}
}
