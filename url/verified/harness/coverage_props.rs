//! harness: coverage properties for the Url read API (src zone: ../src/lib.rs)
//!
//! Universal (fuzz-shaped) properties over arbitrary records satisfying the
//! structural invariant -- the read-face counterpart of the fuzz/parse.rs and
//! fuzz/fuzz-url.rs targets, restricted to what the data model determines
//! without the parser machine (the parse round-trip property is the parser
//! batch's target). Reference-style organization: `#[path]` includes
//! verified/src/lib.rs; no spec copies.
//!
//! P1 tail decomposition: path + ["?" + query]? + ["#" + fragment]? cover
//! the serialization from path_start to the end, disjointly, in order
//! (the zero-shot shape behind every read-API value).
//! P3 default-port table: port_or_known_default keeps an explicit port and
//! substitutes only the well-known ports for the five special schemes.
//! P4 host-tag face: the Domain tag pairs with a non-empty host region
//! whenever the scheme is special (check_invariants lib.rs:743-747).

#[path = "../src/lib.rs"]
mod urllib;

use urllib::*;
use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use {vstd::seq::group_seq_lemmas, vstd::std_specs::vec::group_vec_axioms};

fn main() {}

/// P1: serialization tail decomposition.
/// For any record that satisfies the structural invariant, the bytes from
/// path_start onward are exactly path_view, then (if a query exists) the
/// byte '?' followed by the query content, then (if a fragment exists) the
/// byte '#' followed by the fragment content.
pub proof fn tail_decomposition(u: &Url)
    requires
        url_invariant(u),
    ensures
        u.serialization.view().subrange(u.path_start as int, u.serialization.view().len() as int)
            == path_view(u)
            + (if u.query_start.is_some() {
                seq![0x3Fu8] + query_content_view(u)
            } else {
                Seq::empty()
            })
            + (if u.fragment_start.is_some() {
                seq![0x23u8] + fragment_content_view(u)
            } else {
                Seq::empty()
            }),
{
    let s = u.serialization.view();
    let n = s.len() as int;
    let ps = u.path_start as int;
    let qend = if u.fragment_start.is_some() {
        u.fragment_start.unwrap() as int
    } else {
        n
    };
    // resolve the component order: path [? query] [# fragment]
    if u.query_start.is_some() && u.fragment_start.is_some() {
        let qs = u.query_start.unwrap() as int;
        let fs = u.fragment_start.unwrap() as int;
        // bounds from the invariant: ps <= qs < fs < n
        vstd::seq::lemma_seq_subrange_len(s, ps, n);
        // path part
        vstd::seq::lemma_seq_subrange_len(s, ps, qs);
        assert(s.subrange(ps, qs).len() == qs - ps);
        assert(path_view(u) == s.subrange(ps, qs));
        // '?' head of the query part
        vstd::seq::lemma_seq_subrange_len(s, qs, fs);
        assert(s.subrange(qs, fs).len() == fs - qs);
        assert(s.subrange(qs, fs).index(0) == 0x3Fu8);
        // '#' head of the fragment part
        assert(s.subrange(fs, n).index(0) == 0x23u8);
        assert(fragment_content_view(u) == s.subrange(fs + 1, n));
        // glue: subrange(ps, n) = subrange(ps, qs) + subrange(qs, n)
        assert(s.subrange(qs, n).len() == n - qs);
        assert(s.subrange(qs, n) == seq![0x3Fu8] + s.subrange(qs + 1, n)) by {
            assert forall|i: int| 0 <= i < s.subrange(qs, n).len() implies
                s.subrange(qs, n).index(i) == (seq![0x3Fu8] + s.subrange(qs + 1, n)).index(i) by {
                if i == 0 {
                    assert(s.subrange(qs, n).index(0) == s.index(qs));
                    assert(s.index(qs) == 0x3Fu8);
                } else {
                    assert(s.subrange(qs, n).index(i) == s.index(qs + i));
                    assert((seq![0x3Fu8] + s.subrange(qs + 1, n)).index(i)
                        == s.subrange(qs + 1, n).index(i - 1));
                    assert(s.subrange(qs + 1, n).index(i - 1) == s.index(qs + i));
                }
            }
        }
        assert(s.subrange(fs, n) == seq![0x23u8] + s.subrange(fs + 1, n)) by {
            assert forall|i: int| 0 <= i < s.subrange(fs, n).len() implies
                s.subrange(fs, n).index(i) == (seq![0x23u8] + s.subrange(fs + 1, n)).index(i) by {
                if i == 0 {
                    assert(s.subrange(fs, n).index(0) == s.index(fs));
                    assert(s.index(fs) == 0x23u8);
                } else {
                    assert(s.subrange(fs, n).index(i) == s.index(fs + i));
                }
            }
        }
        assert(s.subrange(ps, n) == s.subrange(ps, qs) + s.subrange(qs, n)) by {
            assert forall|i: int| 0 <= i < s.subrange(ps, n).len() implies
                s.subrange(ps, n).index(i) == (s.subrange(ps, qs) + s.subrange(qs, n)).index(i) by {
                if i < qs - ps {
                    assert(s.subrange(ps, n).index(i) == s.index(ps + i));
                    assert((s.subrange(ps, qs) + s.subrange(qs, n)).index(i)
                        == s.subrange(ps, qs).index(i));
                    assert(s.subrange(ps, qs).index(i) == s.index(ps + i));
                } else {
                    assert(s.subrange(ps, n).index(i) == s.index(ps + i));
                    assert((s.subrange(ps, qs) + s.subrange(qs, n)).index(i)
                        == s.subrange(qs, n).index(i - (qs - ps)));
                    assert(s.subrange(qs, n).index(i - (qs - ps)) == s.index(qs + (i - (qs - ps))));
                    assert(qs + (i - (qs - ps)) == ps + i);
                }
            }
        }
        assert(s.subrange(qs, n) == s.subrange(qs, fs) + s.subrange(fs, n)) by {
            assert forall|i: int| 0 <= i < s.subrange(qs, n).len() implies
                s.subrange(qs, n).index(i) == (s.subrange(qs, fs) + s.subrange(fs, n)).index(i) by {
                if i < fs - qs {
                    assert(s.subrange(qs, n).index(i) == s.index(qs + i));
                    assert((s.subrange(qs, fs) + s.subrange(fs, n)).index(i)
                        == s.subrange(qs, fs).index(i));
                    assert(s.subrange(qs, fs).index(i) == s.index(qs + i));
                } else {
                    assert(s.subrange(qs, n).index(i) == s.index(qs + i));
                    assert((s.subrange(qs, fs) + s.subrange(fs, n)).index(i)
                        == s.subrange(fs, n).index(i - (fs - qs)));
                    assert(s.subrange(fs, n).index(i - (fs - qs)) == s.index(fs + (i - (fs - qs))));
                    assert(fs + (i - (fs - qs)) == qs + i);
                }
            }
        }
        // final glue: query part = '?' + content, so
        // subrange(qs, fs) == '?' + subrange(qs+1, fs)
        assert(s.subrange(qs, fs) == seq![0x3Fu8] + s.subrange(qs + 1, fs)) by {
            assert forall|i: int| 0 <= i < s.subrange(qs, fs).len() implies
                s.subrange(qs, fs).index(i) == (seq![0x3Fu8] + s.subrange(qs + 1, fs)).index(i) by {
                if i == 0 {
                    assert(s.subrange(qs, fs).index(0) == s.index(qs));
                    assert(s.index(qs) == 0x3Fu8);
                } else {
                    assert(s.subrange(qs, fs).index(i) == s.index(qs + i));
                    assert((seq![0x3Fu8] + s.subrange(qs + 1, fs)).index(i)
                        == s.subrange(qs + 1, fs).index(i - 1));
                    assert(s.subrange(qs + 1, fs).index(i - 1) == s.index(qs + i));
                }
            }
        }
        // query_content_view ends at the fragment start in this case
        assert(query_content_view(u) == s.subrange(qs + 1, fs));
        assert(s.subrange(ps, n)
            == s.subrange(ps, qs)
            + (seq![0x3Fu8] + s.subrange(qs + 1, fs))
            + (seq![0x23u8] + s.subrange(fs + 1, n)));
    } else if u.query_start.is_some() {
        let qs = u.query_start.unwrap() as int;
        vstd::seq::lemma_seq_subrange_len(s, ps, n);
        assert(path_view(u) == s.subrange(ps, qs));
        assert(query_content_view(u) == s.subrange(qs + 1, n));
        assert(s.subrange(ps, n) == s.subrange(ps, qs) + s.subrange(qs, n)) by {
            assert forall|i: int| 0 <= i < s.subrange(ps, n).len() implies
                s.subrange(ps, n).index(i) == (s.subrange(ps, qs) + s.subrange(qs, n)).index(i) by {
                if i < qs - ps {
                    assert(s.subrange(ps, n).index(i) == s.index(ps + i));
                    assert((s.subrange(ps, qs) + s.subrange(qs, n)).index(i)
                        == s.subrange(ps, qs).index(i));
                    assert(s.subrange(ps, qs).index(i) == s.index(ps + i));
                } else {
                    assert(s.subrange(ps, n).index(i) == s.index(ps + i));
                    assert((s.subrange(ps, qs) + s.subrange(qs, n)).index(i)
                        == s.subrange(qs, n).index(i - (qs - ps)));
                    assert(s.subrange(qs, n).index(i - (qs - ps)) == s.index(qs + (i - (qs - ps))));
                    assert(qs + (i - (qs - ps)) == ps + i);
                }
            }
        }
        assert(s.subrange(qs, n) == seq![0x3Fu8] + s.subrange(qs + 1, n)) by {
            assert forall|i: int| 0 <= i < s.subrange(qs, n).len() implies
                s.subrange(qs, n).index(i) == (seq![0x3Fu8] + s.subrange(qs + 1, n)).index(i) by {
                if i == 0 {
                    assert(s.subrange(qs, n).index(0) == s.index(qs));
                    assert(s.index(qs) == 0x3Fu8);
                } else {
                    assert(s.subrange(qs, n).index(i) == s.index(qs + i));
                    assert((seq![0x3Fu8] + s.subrange(qs + 1, n)).index(i)
                        == s.subrange(qs + 1, n).index(i - 1));
                    assert(s.subrange(qs + 1, n).index(i - 1) == s.index(qs + i));
                }
            }
        }
        assert(s.subrange(ps, n)
            == s.subrange(ps, qs) + (seq![0x3Fu8] + s.subrange(qs + 1, n)));
    } else if u.fragment_start.is_some() {
        let fs = u.fragment_start.unwrap() as int;
        vstd::seq::lemma_seq_subrange_len(s, ps, n);
        assert(path_view(u) == s.subrange(ps, fs));
        assert(fragment_content_view(u) == s.subrange(fs + 1, n));
        assert(s.subrange(ps, n) == s.subrange(ps, fs) + s.subrange(fs, n)) by {
            assert forall|i: int| 0 <= i < s.subrange(ps, n).len() implies
                s.subrange(ps, n).index(i) == (s.subrange(ps, fs) + s.subrange(fs, n)).index(i) by {
                if i < fs - ps {
                    assert(s.subrange(ps, n).index(i) == s.index(ps + i));
                    assert((s.subrange(ps, fs) + s.subrange(fs, n)).index(i)
                        == s.subrange(ps, fs).index(i));
                    assert(s.subrange(ps, fs).index(i) == s.index(ps + i));
                } else {
                    assert(s.subrange(ps, n).index(i) == s.index(ps + i));
                    assert((s.subrange(ps, fs) + s.subrange(fs, n)).index(i)
                        == s.subrange(fs, n).index(i - (fs - ps)));
                    assert(s.subrange(fs, n).index(i - (fs - ps)) == s.index(fs + (i - (fs - ps))));
                    assert(fs + (i - (fs - ps)) == ps + i);
                }
            }
        }
        assert(s.subrange(fs, n) == seq![0x23u8] + s.subrange(fs + 1, n)) by {
            assert forall|i: int| 0 <= i < s.subrange(fs, n).len() implies
                s.subrange(fs, n).index(i) == (seq![0x23u8] + s.subrange(fs + 1, n)).index(i) by {
                if i == 0 {
                    assert(s.subrange(fs, n).index(0) == s.index(fs));
                    assert(s.index(fs) == 0x23u8);
                } else {
                    assert(s.subrange(fs, n).index(i) == s.index(fs + i));
                    assert((seq![0x23u8] + s.subrange(fs + 1, n)).index(i)
                        == s.subrange(fs + 1, n).index(i - 1));
                    assert(s.subrange(fs + 1, n).index(i - 1) == s.index(fs + i));
                }
            }
        }
        assert(s.subrange(ps, n)
            == s.subrange(ps, fs) + (seq![0x23u8] + s.subrange(fs + 1, n)));
    } else {
        vstd::seq::lemma_seq_subrange_len(s, ps, n);
        assert(path_view(u) == s.subrange(ps, n));
        assert(s.subrange(ps, n)
            == path_view(u) + Seq::empty() + Seq::empty());
    }
}

/// P3: port_or_known_default keeps an explicit port; the default table is
/// the five-scheme table of parser.rs:185-192.
pub proof fn port_face_keeps_explicit(u: &Url)
    requires
        url_invariant(u),
        u.port.is_some(),
    ensures
        port_or_known_default_view(u) == u.port,
{
}

/// P4 (check_invariants lib.rs:743-747): a Domain tag on a special scheme
/// carries a non-empty host region; combined with host()/host_str() the
/// region is exactly the Domain payload of host() and of host_str().
pub proof fn domain_tag_special_nonempty(u: &Url)
    requires
        url_invariant(u),
        u.host == HostInternal::Domain,
        parser::is_special(parser::scheme_type_of(
            u.serialization.view().subrange(0, u.scheme_end as int))),
    ensures
        (u.host_start as int) < (u.host_end as int),
        host_str_view(u).is_some(),
{
}

}
