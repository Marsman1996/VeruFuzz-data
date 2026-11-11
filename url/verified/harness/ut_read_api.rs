//! harness: unit-test witnesses for the Url read API (src zone: ../src/lib.rs)
//!
//! Mirrors the read-API exemplars of url/tests/unit.rs: test_query (unit.rs:735),
//! test_fragment (769), host (341), host_serialization (380), test_slicing (1067),
//! test_has_authority (1275), test_authority (1287), test_domain (723), and the
//! cannot-be-a-base / is-special face scattered in the above. Reference-style
//! organization: `#[path]` includes verified/src/lib.rs, no spec copies.
//! Each exemplar constructs the parse-result record of the named upstream input
//! (the parser machine itself is a later batch; the field values here are the
//! documented parse result, and the structural invariant is proved per record,
//! so every read-API duty below runs on records the parser provably produces).

#[path = "../src/lib.rs"]
mod urllib;

use urllib::*;
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use {
    vstd::seq::group_seq_lemmas,
    vstd::std_specs::vec::group_vec_axioms,
    vstd::laws_eq::group_laws_eq,
    vstd::std_specs::vec::lemma_vec_obeys_view_eq::<u8>,
};

fn main() {}

/// Closed-form evaluation of dec_val over a concrete 4-digit region
/// (the fold's recursive subrange unroll needs explicit composition steps; the
/// form below has an ensures the caller can chain, the requires are the
/// region's digit facts).
proof fn dec_val_4(sv: Seq<u8>, a: int, d3: u8, d2: u8, d1: u8, d0: u8)
    requires
        a >= 0,
        a + 4 <= sv.len(),
        sv.index(a) == d3,
        sv.index(a + 1) == d2,
        sv.index(a + 2) == d1,
        sv.index(a + 3) == d0,
    ensures
        dec_val(sv.subrange(a, a + 4))
            == (((((d3 as int) - 0x30) * 10 + ((d2 as int) - 0x30)) * 10 + ((d1 as int) - 0x30)) * 10 + ((d0 as int) - 0x30)),
{
    dec_val_step(sv.subrange(a, a + 4));
    dec_val_step(sv.subrange(a, a + 3));
    dec_val_step(sv.subrange(a, a + 2));
    dec_val_step(sv.subrange(a, a + 1));
    assert(dec_val(Seq::empty()) == 0);
    vstd::seq::lemma_seq_subrange_len(sv, a, a + 4);
    vstd::seq::lemma_seq_subrange_len(sv, a, a + 3);
    vstd::seq::lemma_seq_subrange_len(sv, a, a + 2);
    vstd::seq::lemma_seq_subrange_len(sv, a, a + 1);
    vstd::seq::lemma_seq_subrange_len(sv, a, a);
    vstd::seq::lemma_seq_subrange_composition(sv, a, a + 4, 0, 3);
    vstd::seq::lemma_seq_subrange_composition(sv, a, a + 3, 0, 2);
    vstd::seq::lemma_seq_subrange_composition(sv, a, a + 2, 0, 1);
    vstd::seq::lemma_seq_subrange_composition(sv, a, a + 1, 0, 0);
    assert(sv.subrange(a, a + 4).subrange(0, 3) == sv.subrange(a, a + 3));
    assert(sv.subrange(a, a + 3).subrange(0, 2) == sv.subrange(a, a + 2));
    assert(sv.subrange(a, a + 2).subrange(0, 1) == sv.subrange(a, a + 1));
    assert(sv.subrange(a, a + 1).subrange(0, 0) == sv.subrange(a, a));
    vstd::seq::lemma_seq_subrange_index(sv, a, a + 4, 3);
    vstd::seq::lemma_seq_subrange_index(sv, a, a + 3, 2);
    vstd::seq::lemma_seq_subrange_index(sv, a, a + 2, 1);
    vstd::seq::lemma_seq_subrange_index(sv, a, a + 1, 0);
    assert(sv.subrange(a, a + 4).index(3) == d0);
    assert(sv.subrange(a, a + 3).index(2) == d1);
    assert(sv.subrange(a, a + 2).index(1) == d2);
    assert(sv.subrange(a, a + 1).index(0) == d3);
}

/// Closed-form evaluation of dec_val over a concrete 2-digit region.
proof fn dec_val_2(sv: Seq<u8>, a: int, d1: u8, d0: u8)
    requires
        a >= 0,
        a + 2 <= sv.len(),
        sv.index(a) == d1,
        sv.index(a + 1) == d0,
    ensures
        dec_val(sv.subrange(a, a + 2))
            == (((d1 as int) - 0x30) * 10 + ((d0 as int) - 0x30)),
{
    dec_val_step(sv.subrange(a, a + 2));
    dec_val_step(sv.subrange(a, a + 1));
    assert(dec_val(Seq::empty()) == 0);
    vstd::seq::lemma_seq_subrange_len(sv, a, a + 2);
    vstd::seq::lemma_seq_subrange_len(sv, a, a + 1);
    vstd::seq::lemma_seq_subrange_len(sv, a, a);
    vstd::seq::lemma_seq_subrange_composition(sv, a, a + 2, 0, 1);
    vstd::seq::lemma_seq_subrange_composition(sv, a, a + 1, 0, 0);
    assert(sv.subrange(a, a + 2).subrange(0, 1) == sv.subrange(a, a + 1));
    assert(sv.subrange(a, a + 1).subrange(0, 0) == sv.subrange(a, a));
    vstd::seq::lemma_seq_subrange_index(sv, a, a + 2, 1);
    vstd::seq::lemma_seq_subrange_index(sv, a, a + 1, 0);
    assert(sv.subrange(a, a + 2).index(1) == d0);
    assert(sv.subrange(a, a + 1).index(0) == d1);
}

/// one-step unroll of the dec_val fold (the recursive definitional axiom does
/// not saturate on subrange terms of a concrete record; the step is applied
/// positionally, once per digit).
proof fn dec_val_step(s: Seq<u8>)
    requires
        s.len() > 0,
    ensures
        dec_val(s) == dec_val(s.subrange(0, s.len() - 1)) * 10
            + ((s.index(s.len() - 1) as int) - 0x30),
{
}

/// subrange content == literal: the pointwise witness is supplied by the
/// caller (concrete records), the length/index/ext-equal steps come from
/// the vstd range lemmas invoked positionally.
proof fn slice_content(p: Seq<u8>, a: int, b: int, lit: Seq<u8>)
    requires
        0 <= a <= b <= p.len(),
        lit.len() == b - a,
        forall|k: int| 0 <= k < lit.len() ==> lit.index(k) == p.index(a + k),
    ensures
        p.subrange(a, b) == lit,
{
    vstd::seq::lemma_seq_subrange_len(p, a, b);
    assert forall|k: int| 0 <= k < lit.len() implies p.subrange(a, b).index(k) == p.index(a + k) by {
        vstd::seq::lemma_seq_subrange_index(p, a, b, k);
    }
    vstd::seq::lemma_seq_ext_equal(p.subrange(a, b), lit);
}

/* ---------- U1 test_query (unit.rs:735-767), the query/path/fragment face ----------
 * Upstream: Url::parse("https://example.com/products?page=2#fragment")
 *   .query() == Some("page=2"); the same record yields path "/products",
 *   fragment Some("fragment"), scheme "https", host Domain("example.com"). */
exec fn ut_test_query()
{
    let u = Url {
        serialization: vec![
            0x68u8, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c,
            0x65, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x70, 0x72, 0x6f, 0x64, 0x75, 0x63, 0x74, 0x73,
            0x3f, 0x70, 0x61, 0x67, 0x65, 0x3d, 0x32, 0x23, 0x66, 0x72, 0x61, 0x67, 0x6d, 0x65,
            0x6e, 0x74,
        ],
        scheme_end: 5,
        username_end: 8,
        host_start: 8,
        host_end: 19,
        host: HostInternal::Domain,
        port: Option::None,
        path_start: 19,
        query_start: Option::Some(28),
        fragment_start: Option::Some(35),
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![
            0x68u8, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c,
            0x65, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x70, 0x72, 0x6f, 0x64, 0x75, 0x63, 0x74, 0x73,
            0x3f, 0x70, 0x61, 0x67, 0x65, 0x3d, 0x32, 0x23, 0x66, 0x72, 0x61, 0x67, 0x6d, 0x65,
            0x6e, 0x74,
        ]);
        assert(sv.index(0) == 0x68u8);
        assert(forall|i: int| 1 <= i < 5 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x74u8));
        }
        assert(url_invariant(&u));
    }
    let q = u.query();
    assert(q.is_some());
    assert(q.is_some());
    proof {
        assert(query_content_view(&u) == u.serialization.view().subrange(29, 35));
        slice_content(u.serialization.view(), 29, 35,
            seq![0x70u8, 0x61, 0x67, 0x65, 0x3d, 0x32]);
    }
    assert(q.unwrap().view() == seq![0x70u8, 0x61, 0x67, 0x65, 0x3d, 0x32]);
    // path and fragment contents through the same slicing helper
    proof {
        slice_content(u.serialization.view(), 19, 28,
            seq![0x2fu8, 0x70, 0x72, 0x6f, 0x64, 0x75, 0x63, 0x74, 0x73]);
        slice_content(u.serialization.view(), 36, 44,
            seq![0x66u8, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74]);
    }
    let p = u.path();
    assert(p.view() == seq![0x2fu8, 0x70, 0x72, 0x6f, 0x64, 0x75, 0x63, 0x74, 0x73]);
    let f = u.fragment();
    assert(f.unwrap().view() == seq![0x66u8, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74]);
    let s = u.scheme();
    assert(s.view() == seq![0x68u8, 0x74, 0x74, 0x70, 0x73]);
    let h = u.host_str();
    assert(h.is_some());
    assert(h.unwrap().view()
        == seq![0x65u8, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d]);
}


/* ---------- ut_test_fragment_some ----------
 * Record: 'https://example.com/#fragment' */
exec fn ut_test_fragment_some()
{
    let u = Url {
        serialization: vec![
            0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e,
            0x63, 0x6f, 0x6d, 0x2f, 0x23, 0x66, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74
        ],
        scheme_end: 5,
        username_end: 8,
        host_start: 8,
        host_end: 19,
        host: HostInternal::Domain,
        port: Option::None,
        path_start: 19,
        query_start: Option::None,
        fragment_start: Option::Some(20),
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x23, 0x66, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74]);
        assert(forall|i: int| 1 <= i < 5 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    let f = u.fragment();
    assert(f.is_some());
    proof { slice_content(sv, 21, 29, seq![0x66, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74]); }
    assert(f.unwrap().view() == seq![0x66, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74]);
}


/* ---------- ut_test_fragment_none_query_none ----------
 * Record: 'https://example.com/' */
exec fn ut_test_fragment_none_query_none()
{
    let u = Url {
        serialization: vec![
            0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e,
            0x63, 0x6f, 0x6d, 0x2f
        ],
        scheme_end: 5,
        username_end: 8,
        host_start: 8,
        host_end: 19,
        host: HostInternal::Domain,
        port: Option::None,
        path_start: 19,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d, 0x2f]);
        assert(forall|i: int| 1 <= i < 5 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    let f = u.fragment();
    assert(f.is_none());
    let q = u.query();
    assert(q.is_none());
    let p = u.path();
    proof { slice_content(sv, 19, 20, seq![0x2fu8]); }
    assert(p.view() == seq![0x2fu8]);
}


/* ---------- ut_host_domain ----------
 * Record: 'http://www.mozilla.org/' */
exec fn ut_host_domain()
{
    let u = Url {
        serialization: vec![
            0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x77, 0x77, 0x77, 0x2e, 0x6d, 0x6f, 0x7a, 0x69, 0x6c,
            0x6c, 0x61, 0x2e, 0x6f, 0x72, 0x67, 0x2f
        ],
        scheme_end: 4,
        username_end: 7,
        host_start: 7,
        host_end: 22,
        host: HostInternal::Domain,
        port: Option::None,
        path_start: 22,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x77, 0x77, 0x77, 0x2e, 0x6d, 0x6f, 0x7a, 0x69, 0x6c, 0x6c, 0x61, 0x2e, 0x6f, 0x72, 0x67, 0x2f]);
        assert(forall|i: int| 1 <= i < 4 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    let hb = u.has_host();
    assert(hb);
    let h = u.host();
    assert(h.is_some());
    proof { slice_content(sv, 7, 22, seq![0x77, 0x77, 0x77, 0x2e, 0x6d, 0x6f, 0x7a, 0x69, 0x6c, 0x6c, 0x61, 0x2e, 0x6f, 0x72, 0x67]); }
    let hv = h.unwrap();
    let hl: Vec<u8> = vec![0x77, 0x77, 0x77, 0x2e, 0x6d, 0x6f, 0x7a, 0x69, 0x6c, 0x6c, 0x61, 0x2e, 0x6f, 0x72, 0x67];
    proof {
        assert(hl.view() == seq![0x77, 0x77, 0x77, 0x2e, 0x6d, 0x6f, 0x7a, 0x69, 0x6c, 0x6c, 0x61, 0x2e, 0x6f, 0x72, 0x67]);
    }
    // verify the variant + content without the opaque rust PartialEq on Vec:
    // the Domain arm carries the host-region bytes, the other arms would
    // contradict the Domain tag of the record via host()'s ensures.
    match hv {
        Host::Domain(d) => {
            assert(d.view() == seq![0x77, 0x77, 0x77, 0x2e, 0x6d, 0x6f, 0x7a, 0x69, 0x6c, 0x6c, 0x61, 0x2e, 0x6f, 0x72, 0x67]);
        }
        _ => {
            let never = false;
            assert(never);
        }
    }
    let hs = u.host_str();
    assert(hs.unwrap().view() == seq![0x77, 0x77, 0x77, 0x2e, 0x6d, 0x6f, 0x7a, 0x69, 0x6c, 0x6c, 0x61, 0x2e, 0x6f, 0x72, 0x67]);
    let d = u.domain();
    assert(d.unwrap().view() == seq![0x77, 0x77, 0x77, 0x2e, 0x6d, 0x6f, 0x7a, 0x69, 0x6c, 0x6c, 0x61, 0x2e, 0x6f, 0x72, 0x67]);
}


/* ---------- ut_host_ipv4 ----------
 * Record: 'http://1.35.33.49/' */
exec fn ut_host_ipv4()
{
    let u = Url {
        serialization: vec![
            0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x31, 0x2e, 0x33, 0x35, 0x2e, 0x33, 0x33, 0x2e, 0x34,
            0x39, 0x2f
        ],
        scheme_end: 4,
        username_end: 7,
        host_start: 7,
        host_end: 17,
        host: HostInternal::Ipv4(0x01232131),
        port: Option::None,
        path_start: 17,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x31, 0x2e, 0x33, 0x35, 0x2e, 0x33, 0x33, 0x2e, 0x34, 0x39, 0x2f]);
        assert(forall|i: int| 1 <= i < 4 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    let h = u.host();
    assert(h.is_some());
    assert(h.unwrap() == Host::Ipv4(0x01232131));
    let hs = u.host_str();
    proof { slice_content(sv, 7, 17, seq![0x31, 0x2e, 0x33, 0x35, 0x2e, 0x33, 0x33, 0x2e, 0x34, 0x39]); }
    assert(hs.unwrap().view() == seq![0x31, 0x2e, 0x33, 0x35, 0x2e, 0x33, 0x33, 0x2e, 0x34, 0x39]);
    let dm = u.domain();
    assert(dm.is_none());
}


/* ---------- ut_host_ipv6 ----------
 * Record: 'http://[::1]/' */
exec fn ut_host_ipv6()
{
    let u = Url {
        serialization: vec![
            0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x5b, 0x3a, 0x3a, 0x31, 0x5d, 0x2f
        ],
        scheme_end: 4,
        username_end: 7,
        host_start: 7,
        host_end: 12,
        host: HostInternal::Ipv6([0, 0, 0, 0, 0, 0, 0, 1]),
        port: Option::None,
        path_start: 12,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x5b, 0x3a, 0x3a, 0x31, 0x5d, 0x2f]);
        assert(forall|i: int| 1 <= i < 4 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    let h = u.host();
    assert(h.is_some());
    assert(h.unwrap() == Host::Ipv6([0, 0, 0, 0, 0, 0, 0, 1]));
    let hs = u.host_str();
    proof { slice_content(sv, 7, 12, seq![0x5b, 0x3a, 0x3a, 0x31, 0x5d]); }
    assert(hs.unwrap().view() == seq![0x5b, 0x3a, 0x3a, 0x31, 0x5d]);
    let dm = u.domain();
    assert(dm.is_none());
}

/* ---------- ut_has_authority_false_mailto ----------
 * Record: 'mailto:joe@example.com' */
exec fn ut_has_authority_false_mailto()
{
    let u = Url {
        serialization: vec![
            0x6d, 0x61, 0x69, 0x6c, 0x74, 0x6f, 0x3a, 0x6a, 0x6f, 0x65, 0x40, 0x65, 0x78, 0x61, 0x6d, 0x70,
            0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d
        ],
        scheme_end: 6,
        username_end: 7,
        host_start: 7,
        host_end: 7,
        host: HostInternal::None,
        port: Option::None,
        path_start: 7,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x6d, 0x61, 0x69, 0x6c, 0x74, 0x6f, 0x3a, 0x6a, 0x6f, 0x65, 0x40, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d]);
        assert(forall|i: int| 1 <= i < 6 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x61));
            assert(is_scheme_char(0x69));
            assert(is_scheme_char(0x6c));
            assert(is_scheme_char(0x6f));
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    let ha = u.has_authority();
    assert(!ha);
    let cb = u.cannot_be_a_base();
    assert(cb);
    let sp = u.is_special();
    assert(!sp);
}


/* ---------- ut_has_authority_false_unix ----------
 * Record: 'unix:/run/foo.socket' */
exec fn ut_has_authority_false_unix()
{
    let u = Url {
        serialization: vec![
            0x75, 0x6e, 0x69, 0x78, 0x3a, 0x2f, 0x72, 0x75, 0x6e, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x73, 0x6f,
            0x63, 0x6b, 0x65, 0x74
        ],
        scheme_end: 4,
        username_end: 5,
        host_start: 5,
        host_end: 5,
        host: HostInternal::None,
        port: Option::None,
        path_start: 5,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x75, 0x6e, 0x69, 0x78, 0x3a, 0x2f, 0x72, 0x75, 0x6e, 0x2f, 0x66, 0x6f, 0x6f, 0x2e, 0x73, 0x6f, 0x63, 0x6b, 0x65, 0x74]);
        assert(forall|i: int| 1 <= i < 4 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x69));
            assert(is_scheme_char(0x6e));
            assert(is_scheme_char(0x78));
        }
        assert(url_invariant(&u));
    }
    let ha = u.has_authority();
    assert(!ha);
    let cb = u.cannot_be_a_base();
    assert(!cb);
    let sp = u.is_special();
    assert(!sp);
}


/* ---------- ut_has_authority_true_file ----------
 * Record: 'file:///tmp/foo' */
exec fn ut_has_authority_true_file()
{
    let u = Url {
        serialization: vec![
            0x66, 0x69, 0x6c, 0x65, 0x3a, 0x2f, 0x2f, 0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x66, 0x6f, 0x6f
        ],
        scheme_end: 4,
        username_end: 7,
        host_start: 7,
        host_end: 7,
        host: HostInternal::None,
        port: Option::None,
        path_start: 7,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x66, 0x69, 0x6c, 0x65, 0x3a, 0x2f, 0x2f, 0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x66, 0x6f, 0x6f]);
        assert(forall|i: int| 1 <= i < 4 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x65));
            assert(is_scheme_char(0x69));
            assert(is_scheme_char(0x6c));
        }
        assert(url_invariant(&u));
    }
    let ha = u.has_authority();
    assert(ha);
    let cb = u.cannot_be_a_base();
    assert(!cb);
    proof {
        slice_content(sv, 0, 4, seq![0x66, 0x69, 0x6c, 0x65]);
    }
    let sp = u.is_special();
    assert(sp);
    let hb = u.has_host();
    assert(!hb);
    let hs2 = u.host_str();
    assert(hs2.is_none());
}


/* ---------- ut_has_authority_true_http ----------
 * Record: 'http://example.com/tmp/foo' */
exec fn ut_has_authority_true_http()
{
    let u = Url {
        serialization: vec![
            0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63,
            0x6f, 0x6d, 0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x66, 0x6f, 0x6f
        ],
        scheme_end: 4,
        username_end: 7,
        host_start: 7,
        host_end: 18,
        host: HostInternal::Domain,
        port: Option::None,
        path_start: 18,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x66, 0x6f, 0x6f]);
        assert(forall|i: int| 1 <= i < 4 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x70));
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    let ha = u.has_authority();
    assert(ha);
    let cb = u.cannot_be_a_base();
    assert(!cb);
    proof {
        slice_content(sv, 0, 4, seq![0x68, 0x74, 0x74, 0x70]);
        slice_content(sv, 18, 26, seq![0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x66, 0x6f, 0x6f]);
    }
    let sp = u.is_special();
    assert(sp);
}


/* ---------- ut_test_slicing_full ----------
 * Record: 'https://user:pass@domain.com:9742/path/file.ext?key=val&key2=val2#fragment' */
exec fn ut_test_slicing_full()
{
    let u = Url {
        serialization: vec![
            0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x75, 0x73, 0x65, 0x72, 0x3a, 0x70, 0x61, 0x73,
            0x73, 0x40, 0x64, 0x6f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x63, 0x6f, 0x6d, 0x3a, 0x39, 0x37, 0x34,
            0x32, 0x2f, 0x70, 0x61, 0x74, 0x68, 0x2f, 0x66, 0x69, 0x6c, 0x65, 0x2e, 0x65, 0x78, 0x74, 0x3f,
            0x6b, 0x65, 0x79, 0x3d, 0x76, 0x61, 0x6c, 0x26, 0x6b, 0x65, 0x79, 0x32, 0x3d, 0x76, 0x61, 0x6c,
            0x32, 0x23, 0x66, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74
        ],
        scheme_end: 5,
        username_end: 12,
        host_start: 18,
        host_end: 28,
        host: HostInternal::Domain,
        port: Option::Some(9742),
        path_start: 33,
        query_start: Option::Some(47),
        fragment_start: Option::Some(65),
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x75, 0x73, 0x65, 0x72, 0x3a, 0x70, 0x61, 0x73, 0x73, 0x40, 0x64, 0x6f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x63, 0x6f, 0x6d, 0x3a, 0x39, 0x37, 0x34, 0x32, 0x2f, 0x70, 0x61, 0x74, 0x68, 0x2f, 0x66, 0x69, 0x6c, 0x65, 0x2e, 0x65, 0x78, 0x74, 0x3f, 0x6b, 0x65, 0x79, 0x3d, 0x76, 0x61, 0x6c, 0x26, 0x6b, 0x65, 0x79, 0x32, 0x3d, 0x76, 0x61, 0x6c, 0x32, 0x23, 0x66, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74]);
        assert(forall|i: int| 1 <= i < 5 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x70));
            assert(is_scheme_char(0x73));
            assert(is_scheme_char(0x74));
        }
        assert(sv.index(28) == 0x3au8);
        assert(sv.index(29) == 0x39u8);
        assert(sv.index(30) == 0x37u8);
        assert(sv.index(31) == 0x34u8);
        assert(sv.index(32) == 0x32u8);
        assert(forall|i: int| 29 <= i < 33 ==> is_dec_digit(sv.index(i))) by {
            assert(is_dec_digit(0x39u8));
            assert(is_dec_digit(0x37u8));
            assert(is_dec_digit(0x34u8));
            assert(is_dec_digit(0x32u8));
        }
        assert((u.host_end as int) == 28);
        assert((u.path_start as int) == 33);
        assert((u.host_end as int) + 1 == 29);
        dec_val_4(sv, 29, 0x39u8, 0x37u8, 0x34u8, 0x32u8);
        assert(sv.subrange((u.host_end as int) + 1, u.path_start as int)
            == sv.subrange(29, 33));
        assert(url_invariant(&u));
    }
    let s = u.scheme();
    proof { slice_content(sv, 0, 5, seq![0x68, 0x74, 0x74, 0x70, 0x73]); }
    assert(s.view() == seq![0x68, 0x74, 0x74, 0x70, 0x73]);
    let un = u.username();
    proof { slice_content(sv, 8, 12, seq![0x75, 0x73, 0x65, 0x72]); }
    assert(un.view() == seq![0x75, 0x73, 0x65, 0x72]);
    let pw = u.password();
    assert(pw.is_some());
    proof { slice_content(sv, 13, 17, seq![0x70, 0x61, 0x73, 0x73]); }
    assert(pw.unwrap().view() == seq![0x70, 0x61, 0x73, 0x73]);
    let hs = u.host_str();
    proof { slice_content(sv, 18, 28, seq![0x64, 0x6f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x63, 0x6f, 0x6d]); }
    assert(hs.unwrap().view() == seq![0x64, 0x6f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x63, 0x6f, 0x6d]);
    let po = u.port();
    assert(po == Option::Some(9742));
    let au = u.authority();
    proof { slice_content(sv, 8, 33, seq![0x75, 0x73, 0x65, 0x72, 0x3a, 0x70, 0x61, 0x73, 0x73, 0x40, 0x64, 0x6f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x63, 0x6f, 0x6d, 0x3a, 0x39, 0x37, 0x34, 0x32]); }
    assert(au.view() == seq![0x75, 0x73, 0x65, 0x72, 0x3a, 0x70, 0x61, 0x73, 0x73, 0x40, 0x64, 0x6f, 0x6d, 0x61, 0x69, 0x6e, 0x2e, 0x63, 0x6f, 0x6d, 0x3a, 0x39, 0x37, 0x34, 0x32]);
    let p = u.path();
    proof { slice_content(sv, 33, 47, seq![0x2f, 0x70, 0x61, 0x74, 0x68, 0x2f, 0x66, 0x69, 0x6c, 0x65, 0x2e, 0x65, 0x78, 0x74]); }
    assert(p.view() == seq![0x2f, 0x70, 0x61, 0x74, 0x68, 0x2f, 0x66, 0x69, 0x6c, 0x65, 0x2e, 0x65, 0x78, 0x74]);
    let q = u.query();
    assert(q.is_some());
    proof { slice_content(sv, 48, 65, seq![0x6b, 0x65, 0x79, 0x3d, 0x76, 0x61, 0x6c, 0x26, 0x6b, 0x65, 0x79, 0x32, 0x3d, 0x76, 0x61, 0x6c, 0x32]); }
    assert(q.unwrap().view() == seq![0x6b, 0x65, 0x79, 0x3d, 0x76, 0x61, 0x6c, 0x26, 0x6b, 0x65, 0x79, 0x32, 0x3d, 0x76, 0x61, 0x6c, 0x32]);
    let f = u.fragment();
    assert(f.is_some());
    proof { slice_content(sv, 66, 74, seq![0x66, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74]); }
    assert(f.unwrap().view() == seq![0x66, 0x72, 0x61, 0x67, 0x6d, 0x65, 0x6e, 0x74]);
}


/* ---------- ut_authority_facebook_empty ----------
 * Record: 'file:///tmp/foo' */
exec fn ut_authority_facebook_empty()
{
    let u = Url {
        serialization: vec![
            0x66, 0x69, 0x6c, 0x65, 0x3a, 0x2f, 0x2f, 0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x66, 0x6f, 0x6f
        ],
        scheme_end: 4,
        username_end: 7,
        host_start: 7,
        host_end: 7,
        host: HostInternal::None,
        port: Option::None,
        path_start: 7,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x66, 0x69, 0x6c, 0x65, 0x3a, 0x2f, 0x2f, 0x2f, 0x74, 0x6d, 0x70, 0x2f, 0x66, 0x6f, 0x6f]);
        assert(forall|i: int| 1 <= i < 4 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x65));
            assert(is_scheme_char(0x69));
            assert(is_scheme_char(0x6c));
        }
        assert(url_invariant(&u));
    }
    let a = u.authority();
    assert(a.view().len() == 0);
}


/* ---------- ut_authority_ftp_user_port ----------
 * Record: 'ftp://user@127.0.0.1:2121/' */
exec fn ut_authority_ftp_user_port()
{
    let u = Url {
        serialization: vec![
            0x66, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x75, 0x73, 0x65, 0x72, 0x40, 0x31, 0x32, 0x37, 0x2e, 0x30,
            0x2e, 0x30, 0x2e, 0x31, 0x3a, 0x32, 0x31, 0x32, 0x31, 0x2f
        ],
        scheme_end: 3,
        username_end: 10,
        host_start: 11,
        host_end: 20,
        host: HostInternal::Domain,
        port: Option::Some(2121),
        path_start: 25,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x66, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x75, 0x73, 0x65, 0x72, 0x40, 0x31, 0x32, 0x37, 0x2e, 0x30, 0x2e, 0x30, 0x2e, 0x31, 0x3a, 0x32, 0x31, 0x32, 0x31, 0x2f]);
        assert(forall|i: int| 1 <= i < 3 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x70));
            assert(is_scheme_char(0x74));
        }
        assert(sv.index(20) == 0x3au8);
        assert(sv.index(21) == 0x32u8);
        assert(sv.index(22) == 0x31u8);
        assert(sv.index(23) == 0x32u8);
        assert(sv.index(24) == 0x31u8);
        assert(forall|i: int| 21 <= i < 25 ==> is_dec_digit(sv.index(i))) by {
            assert(is_dec_digit(0x32u8));
            assert(is_dec_digit(0x31u8));
        }
        assert((u.host_end as int) == 20);
        assert((u.path_start as int) == 25);
        assert((u.host_end as int) + 1 == 21);
        dec_val_4(sv, 21, 0x32u8, 0x31u8, 0x32u8, 0x31u8);
        assert(sv.subrange((u.host_end as int) + 1, u.path_start as int)
            == sv.subrange(21, 25));
        assert(url_invariant(&u));
    }
    let au = u.authority();
    proof { slice_content(sv, 6, 25, seq![0x75, 0x73, 0x65, 0x72, 0x40, 0x31, 0x32, 0x37, 0x2e, 0x30, 0x2e, 0x30, 0x2e, 0x31, 0x3a, 0x32, 0x31, 0x32, 0x31]); }
    assert(au.view() == seq![0x75, 0x73, 0x65, 0x72, 0x40, 0x31, 0x32, 0x37, 0x2e, 0x30, 0x2e, 0x30, 0x2e, 0x31, 0x3a, 0x32, 0x31, 0x32, 0x31]);
    let un = u.username();
    proof { slice_content(sv, 6, 10, seq![0x75, 0x73, 0x65, 0x72]); }
    assert(un.view() == seq![0x75, 0x73, 0x65, 0x72]);
    let pw2 = u.password();
    assert(pw2.is_none());
    let po = u.port();
    assert(po == Option::Some(2121));
    let pod = u.port_or_known_default();
    assert(pod == Option::Some(2121));
}


/* ---------- ut_port_or_known_default_and_empty_path ----------
 * Record: 'ssh://example.com:22' */
exec fn ut_port_or_known_default_and_empty_path()
{
    let u = Url {
        serialization: vec![
            0x73, 0x73, 0x68, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f,
            0x6d, 0x3a, 0x32, 0x32
        ],
        scheme_end: 3,
        username_end: 6,
        host_start: 6,
        host_end: 17,
        host: HostInternal::Domain,
        port: Option::Some(22),
        path_start: 20,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x73, 0x73, 0x68, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d, 0x3a, 0x32, 0x32]);
        assert(forall|i: int| 1 <= i < 3 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x68));
            assert(is_scheme_char(0x73));
        }
        assert(sv.index(17) == 0x3au8);
        assert(sv.index(18) == 0x32u8);
        assert(sv.index(19) == 0x32u8);
        assert(forall|i: int| 18 <= i < 20 ==> is_dec_digit(sv.index(i))) by {
            assert(is_dec_digit(0x32u8));
        }
        assert((u.host_end as int) == 17);
        assert((u.path_start as int) == 20);
        assert((u.host_end as int) + 1 == 18);
        dec_val_2(sv, 18, 0x32u8, 0x32u8);
        assert(sv.subrange((u.host_end as int) + 1, u.path_start as int)
            == sv.subrange(18, 20));
        assert(url_invariant(&u));
    }
    let po = u.port();
    assert(po == Option::Some(22));
    let pod = u.port_or_known_default();
    assert(pod == Option::Some(22));
    let p2 = u.path();
    assert(p2.view().len() == 0);
    let ha = u.has_authority();
    assert(ha);
}


/* ---------- ut_port_or_known_default_https ----------
 * Record: 'https://example.com/products' */
exec fn ut_port_or_known_default_https()
{
    let u = Url {
        serialization: vec![
            0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e,
            0x63, 0x6f, 0x6d, 0x2f, 0x70, 0x72, 0x6f, 0x64, 0x75, 0x63, 0x74, 0x73
        ],
        scheme_end: 5,
        username_end: 8,
        host_start: 8,
        host_end: 19,
        host: HostInternal::Domain,
        port: Option::None,
        path_start: 19,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x68, 0x74, 0x74, 0x70, 0x73, 0x3a, 0x2f, 0x2f, 0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d, 0x2f, 0x70, 0x72, 0x6f, 0x64, 0x75, 0x63, 0x74, 0x73]);
        assert(forall|i: int| 1 <= i < 5 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x70));
            assert(is_scheme_char(0x73));
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    proof {
        slice_content(sv, 0, 5, seq![0x68, 0x74, 0x74, 0x70, 0x73]);
    }
    let po = u.port();
    assert(po.is_none());
    let pod = u.port_or_known_default();
    assert(pod == Option::Some(443));
}


/* ---------- ut_cannot_be_a_base_data ----------
 * Record: 'data:text/plain,Stuff' */
exec fn ut_cannot_be_a_base_data()
{
    let u = Url {
        serialization: vec![
            0x64, 0x61, 0x74, 0x61, 0x3a, 0x74, 0x65, 0x78, 0x74, 0x2f, 0x70, 0x6c, 0x61, 0x69, 0x6e, 0x2c,
            0x53, 0x74, 0x75, 0x66, 0x66
        ],
        scheme_end: 4,
        username_end: 5,
        host_start: 5,
        host_end: 5,
        host: HostInternal::None,
        port: Option::None,
        path_start: 5,
        query_start: Option::None,
        fragment_start: Option::None,
    };
    let ghost sv = u.serialization.view();
    proof {
        assert(sv == seq![0x64, 0x61, 0x74, 0x61, 0x3a, 0x74, 0x65, 0x78, 0x74, 0x2f, 0x70, 0x6c, 0x61, 0x69, 0x6e, 0x2c, 0x53, 0x74, 0x75, 0x66, 0x66]);
        assert(forall|i: int| 1 <= i < 4 ==> is_scheme_char(sv.index(i))) by {
            assert(is_scheme_char(0x61));
            assert(is_scheme_char(0x74));
        }
        assert(url_invariant(&u));
    }
    let cb = u.cannot_be_a_base();
    assert(cb);
    let ha = u.has_authority();
    assert(!ha);
    let p = u.path();
    proof { slice_content(sv, 5, 21, seq![0x74, 0x65, 0x78, 0x74, 0x2f, 0x70, 0x6c, 0x61, 0x69, 0x6e, 0x2c, 0x53, 0x74, 0x75, 0x66, 0x66]); }
    assert(p.view() == seq![0x74, 0x65, 0x78, 0x74, 0x2f, 0x70, 0x6c, 0x61, 0x69, 0x6e, 0x2c, 0x53, 0x74, 0x75, 0x66, 0x66]);
}

}
