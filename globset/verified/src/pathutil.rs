//! globset `src/pathutil.rs` mirror (upstream 141 lines incl. test mod;
//! the 13 tests are pinned in verified/harness/ut_pathutil.rs).
//!
//! Upstream pin: crates/globset/src/pathutil.rs @
//! 178cc027e283fd965cb72d0a7395b219eada170c.
//!
//! Transcription decisions for this file:
//!  - `&Cow<'a, [u8]>` / `Cow<'a, [u8]>` ride the crate-root twin
//!    `CowBytes<'a>` (see src/lib.rs base-mapping table).
//!  - `bstr::ByteSlice::rfind_byte` is re-erected here as a fully
//!    verified twin `rfind_byte` (descending probe over the slice,
//!    the url parser.rs rfind precedent) whose contract equals the
//!    bstr semantics -- rightmost occurrence -- described in the
//!    value model `rfind_pref`. This closes the bstr trust face at
//!    its only pathutil consumption; nothing here calls into bstr.
//!  - `std::path::is_separator` is erected as the platform oracle
//!    face with the two pinned axiom sets (the batch-plan D2
//!    ruling): unix = exactly `/`, windows = `/` and `\` (byte
//!    level: the non-unix arm calls `is_separator(char::from(byte))`
//!    and `char::from(u8)` lands in Latin-1, where both platforms
//!    name no separator outside ASCII).
//!  - `normalize_path` (the cfg(unix) arm) is the host-live primary
//!    obligation; the cfg(not(unix)) rewrite loop is the twin
//!    `normalize_path_rewrite`, parameterized by the platform oracle
//!    and proved against both axiom sets. Both platform test arms
//!    (upstream normal3/normal4) are pinned under BOTH axiom sets in
//!    the harness; no interactive windows verification is opened.
//!
//! Upstream doc lines are quoted verbatim per function below
//! (pathutil.rs:5-8, 24-39, 56-57, 64-65).

use vstd::prelude::*;
use vstd::seq::Seq;

use crate::CowBytes;

verus! {

// ===========================================================================
// Value model: rightmost occurrence (the rfind_byte semantics).
// rfind_pref(s, b, n): the index of the rightmost occurrence of `b` in
// s[0..n), or -1 if there is none.
// ===========================================================================

pub open spec fn rfind_pref(s: Seq<u8>, b: u8, n: int) -> int
    decreases n,
{
    if n <= 0 {
        -1
    } else if s.index(n - 1) == b {
        n - 1
    } else {
        rfind_pref(s, b, n - 1)
    }
}

proof fn rfind_pref_none(s: Seq<u8>, b: u8, n: int)
    ensures
        rfind_pref(s, b, n) == -1 <==> forall|k: int|
            0 <= k < n ==> s.index(k) != b,
    decreases n,
{
    if n > 0 {
        rfind_pref_none(s, b, n - 1);
    }
}

/// If `j` carries `b` and nothing after `j` (up to `n`) does, then `j` IS
/// the rightmost occurrence (the probe-result bridge).
proof fn rfind_pref_hit_at(s: Seq<u8>, b: u8, n: int, j: int)
    requires
        0 <= j < n,
        s.index(j) == b,
        forall|k: int| j < k < n ==> s.index(k) != b,
    ensures
        rfind_pref(s, b, n) == j,
    decreases n,
{
    if n - 1 > j {
        assert(s.index(n - 1) != b);
        rfind_pref_hit_at(s, b, n - 1, j);
    } else {
        // n - 1 == j: the definition unfolds to j directly
        assert(s.index(n - 1) == b);
    }
}

// ===========================================================================
// rfind_byte -- the bstr `ByteSlice::rfind_byte` face, re-erected
// here as a verified twin (descending probe; the url parser.rs
// rightmost-slash probe shape).
// Origin Rust (pathutil.rs:13/46, the two consumption sites):
//     path.rfind_byte(b'/').map(|i| i + 1).unwrap_or(0)
//     name.rfind_byte(b'.')
// ===========================================================================

pub fn rfind_byte(bs: &[u8], b: u8) -> (r: Option<usize>)
    ensures
        r is Some ==> {
            &&& 0 <= (r.get_Some_0() as int) < bs@.len() as int
            &&& bs@.index(r.get_Some_0() as int) == b
            &&& rfind_pref(bs@, b, bs@.len() as int) == r.get_Some_0() as int
            &&& forall|k: int|
                (r.get_Some_0() as int) < k < bs@.len() as int ==> bs@.index(k) != b
        },
        r matches None ==> {
            &&& forall|k: int| 0 <= k < bs@.len() as int ==> bs@.index(k) != b
            &&& rfind_pref(bs@, b, bs@.len() as int) == -1
        },
{
    // descending probe from the right end (first match scanning
    // downward is the rightmost occurrence)
    let mut i: usize = bs.len();
    let mut found: bool = false;
    let mut k: usize = 0;
    while !found && i > 0
        invariant
            i <= bs.len(),
            k <= bs.len(),
            bs@.len() == bs.len(),
            forall|q: int| i <= q < bs@.len() ==> bs@.index(q) != b,
            found ==> (k == i - 1 && bs@.index(k as int) == b),
        decreases (if found { 0int } else { 1int }), i,
    {
        if bs[i - 1] == b {
            found = true;
            k = i - 1;
        } else {
            proof {
                assert(bs@.index((i - 1) as int) != b);
                assert(i >= 1);
            }
            i -= 1;
        }
    }
    proof {
        if found {
            assert((k as int) < bs@.len() as int);
            assert(bs@.index(k as int) == b);
            assert forall|q: int| (k as int) < q < bs@.len() as int implies
                bs@.index(q) != b by {
                assert((k as int) == (i as int) - 1);
            }
            rfind_pref_hit_at(bs@, b, bs.len() as int, k as int);
        } else {
            assert(i == 0) by {
                assert(i <= 0);
                assert(i >= 0);
            }
            rfind_pref_none(bs@, b, bs.len() as int);
        }
    }
    if found {
        Some(k)
    } else {
        None
    }
}

// ===========================================================================
// file_name (pathutil.rs:9-22).
// ===========================================================================

/// The two-byte sequence `..` (the pathutil.rs:18 rejection target;
/// `b".."` respelled as hex bytes).
pub open spec fn spec_dotdot() -> Seq<u8> {
    seq![0x2e, 0x2e]
}

/// The final component of `p`: everything after the rightmost `/`
/// (the whole `p` when it has none).
pub open spec fn spec_final_component(p: Seq<u8>) -> Seq<u8> {
    let last = rfind_pref(p, 0x2f, p.len() as int);
    p.subrange(if last >= 0 { last + 1 } else { 0 }, p.len() as int)
}

/// The final component of the path, if it is a normal file.
///
/// If the path terminates in `..`, or consists solely of a root of prefix,
/// file_name will return `None`.
///
/// (Upstream body pathutil.rs:9-22: empty check, rightmost-`/` scan,
/// Cow-slice of the tail, `..` rejection. Spec additions beyond the doc:
/// the mode-preservation face -- Borrowed in stays Borrowed, Owned in
/// stays Owned -- which upstream carries in its match arms.)
pub fn file_name<'a>(path: &CowBytes<'a>) -> (r: Option<CowBytes<'a>>)
    ensures
        r matches None <==> path.view().len() == 0
            || spec_final_component(path.view()) == spec_dotdot(),
        r is Some ==> {
            &&& path.view().len() > 0
            &&& spec_final_component(path.view()) != spec_dotdot()
            &&& r.get_Some_0().view() == spec_final_component(path.view())
            &&& (r.get_Some_0().is_borrowed_mode() <==> path.is_borrowed_mode())
        },
{
    let bs: &[u8] = path.as_slice();
    if bs.len() == 0 {
        proof {
            assert(path.view().len() == 0);
        }
        return None;
    }
    // Origin Rust (pathutil.rs:13):
    //     let last_slash = path.rfind_byte(b'/').map(|i| i + 1).unwrap_or(0);
    let found = rfind_byte(bs, 0x2f);
    let last: usize = match found {
        Some(j) => {
            proof {
                assert(((j as int) + 1) <= bs@.len() as int);
            }
            j + 1
        }
        None => 0,
    };
    // Origin Rust (pathutil.rs:14-20): the got == ".." check over the
    // tail; spelled here as the guarded 2-byte read.
    let tail: &[u8] = vstd::slice::slice_subrange(bs, last, bs.len());
    proof {
        // the tail slice rfind position matches the spec model
        if found is Some {
            assert(rfind_pref(bs@, 0x2f, bs@.len() as int) == (found.get_Some_0() as int));
            assert(spec_final_component(bs@)
                == bs@.subrange((found.get_Some_0() as int) + 1, bs@.len() as int));
        } else {
            assert(rfind_pref(bs@, 0x2f, bs@.len() as int) == -1);
            assert(spec_final_component(bs@) == bs@.subrange(0, bs@.len() as int));
        }
        assert(tail@ == spec_final_component(bs@));
    }
    if tail.len() == 2 && tail[0] == 0x2e && tail[1] == 0x2e {
        proof {
            assert(tail@ == seq![0x2e, 0x2e]);
            assert(tail@ == spec_dotdot());
            assert(bs@ == path.view());
        }
        return None;
    }
    // Origin Rust (pathutil.rs:14-17):
    //     let got = match *path {
    //         Cow::Borrowed(path) => Cow::Borrowed(&path[last_slash..]),
    //         Cow::Owned(ref path) => Cow::Owned(path[last_slash..].to_vec()),
    //     };
    Some(match path {
        CowBytes::Borrowed(inner) => CowBytes::Borrowed(vstd::slice::slice_subrange(
            *inner,
            last,
            inner.len(),
        )),
        CowBytes::Owned(v) => CowBytes::Owned(vstd::slice::slice_to_vec(
            vstd::slice::slice_subrange(v.as_slice(), last, v.len()),
        )),
    })
}

// ===========================================================================
// file_name_ext (pathutil.rs:40-54).
// ===========================================================================

/// The extension of a file name `p`: everything from the rightmost `.` on
/// (the whole name when the dot leads it -- "liberal" matching).
pub open spec fn spec_final_ext(p: Seq<u8>) -> Seq<u8> {
    let last = rfind_pref(p, 0x2e, p.len() as int);
    p.subrange(if last >= 0 { last } else { 0 }, p.len() as int)
}

/// Return a file extension given a path's file name.
///
/// Note that this does NOT match the semantics of std::path::Path::extension.
/// Namely, the extension includes the `.` and matching is otherwise more
/// liberal. Specifically, the extension is:
///
/// * None, if the file name given is empty;
/// * None, if there is no embedded `.`;
/// * Otherwise, the portion of the file name starting with the final `.`.
///
/// e.g., A file name of `.rs` has an extension `.rs`.
pub fn file_name_ext<'a>(name: &CowBytes<'a>) -> (r: Option<CowBytes<'a>>)
    ensures
        r matches None <==> name.view().len() == 0
            || rfind_pref(name.view(), 0x2e, name.view().len() as int) < 0,
        r is Some ==> {
            &&& name.view().len() > 0
            &&& rfind_pref(name.view(), 0x2e, name.view().len() as int) >= 0
            &&& r.get_Some_0().view() == spec_final_ext(name.view())
            // the doc's "the extension includes the `.`" face: the
            // leading byte of the extension is the dot itself (a `.rs`
            // name yields the `.rs` extension)
            &&& r.get_Some_0().view().len() > 0
            &&& r.get_Some_0().view().index(0) == 0x2e
            &&& (r.get_Some_0().is_borrowed_mode() <==> name.is_borrowed_mode())
        },
{
    let bs: &[u8] = name.as_slice();
    if bs.len() == 0 {
        proof {
            assert(name.view().len() == 0);
        }
        return None;
    }
    // Origin Rust (pathutil.rs:46-49):
    //     let last_dot_at = match name.rfind_byte(b'.') {
    //         None => return None,
    //         Some(i) => i,
    //     };
    let found = rfind_byte(bs, 0x2e);
    let last: usize = match found {
        Some(j) => {
            proof {
                assert(((j as int)) < bs@.len() as int);
            }
            j
        }
        None => {
            proof {
                rfind_pref_none(bs@, 0x2e, bs.len() as int);
            }
            return None;
        }
    };
    // Origin Rust (pathutil.rs:50-53):
    //     Some(match *name {
    //         Cow::Borrowed(name) => Cow::Borrowed(&name[last_dot_at..]),
    //         Cow::Owned(ref name) => Cow::Owned(name[last_dot_at..].to_vec()),
    //     })
    proof {
        assert(bs@.index(last as int) == 0x2e);
        assert(rfind_pref(bs@, 0x2e, bs@.len() as int) == last as int);
        assert(spec_final_ext(bs@) == bs@.subrange(last as int, bs@.len() as int));
        assert(bs@ == name.view());
    }
    Some(match name {
        CowBytes::Borrowed(inner) => CowBytes::Borrowed(vstd::slice::slice_subrange(
            *inner,
            last,
            inner.len(),
        )),
        CowBytes::Owned(v) => CowBytes::Owned(vstd::slice::slice_to_vec(
            vstd::slice::slice_subrange(v.as_slice(), last, v.len()),
        )),
    })
}

// ===========================================================================
// normalize_path -- the unix cfg arm is the host-live primary (a
// plain forward); the not-unix rewrite loop is parameterized over the
// platform oracle below.
//
// Upstream doc (pathutil.rs:56-57, both arms):
//   Normalizes a path to use `/` as a separator everywhere, even on
//   platforms that recognize other characters as separators.
// ===========================================================================

/// Platform oracle (the std::path::is_separator face, pinned closed:
/// unix names exactly `/`, windows names `/` and `\` -- the D2 axiom
/// sets; `char::from(u8)` stays in Latin-1 where no other separator
/// exists on either platform).
pub open spec fn spec_is_separator(b: u8, windows: bool) -> bool {
    if windows {
        b == 0x2f || b == 0x5c
    } else {
        b == 0x2f
    }
}

/// Exec twin of the oracle predicate (same closed body).
pub fn is_separator_exec(b: u8, windows: bool) -> (r: bool)
    ensures
        r == spec_is_separator(b, windows),
{
    if windows {
        b == 0x2f || b == 0x5c
    } else {
        b == 0x2f
    }
}

/// The normalize semantics: every non-`/` byte the oracle calls a
/// separator becomes `/`; everything else passes through in place.
pub open spec fn spec_normalized(s: Seq<u8>, windows: bool) -> Seq<u8> {
    Seq::new(
        s.len(),
        |i: int| {
            let b = s.index(i);
            if b != 0x2f && spec_is_separator(b, windows) {
                0x2f
            } else {
                b
            }
        },
    )
}

/// Whether `s` carries any byte the oracle rewrite would touch.
pub open spec fn spec_has_rewrite(s: Seq<u8>, windows: bool) -> bool {
    exists|i: int|
        0 <= i < s.len() && s.index(i) != 0x2f && spec_is_separator(s.index(i), windows)
}

/// Normalizes a path to use `/` as a separator everywhere, even on
/// platforms that recognize other characters as separators.
///
/// Origin Rust (pathutil.rs:58-62, the cfg(unix) arm -- the live code
/// on every unix host, with upstream's body comment):
///     #[cfg(unix)]
///     pub(crate) fn normalize_path(path: Cow<'_, [u8]>) -> Cow<'_, [u8]> {
///         // UNIX only uses /, so we're good.
///         path
///     }
pub fn normalize_path(path: CowBytes) -> (r: CowBytes)
    ensures
        r.view() == path.view(),
        r.is_borrowed_mode() <==> path.is_borrowed_mode(),
{
    // UNIX only uses /, so we're good.
    path
}

/// The not-unix arm, parameterized over the platform oracle (which
/// axiom set instantiates it). Value+mode semantics identical to
/// upstream's lazy to_mut loop:
///  - no rewrite-needed byte: returns the value unchanged (upstream
///    never reaches the to_mut call, so mode is kept; under the unix
///    oracle set no byte ever matches, so the loop arm and the
///    identity arm coincide -- the coherence claim D2 pins);
///  - some rewrite-needed byte: returns an Owned copy with the
///    rewrites applied (upstream's single to_mut conversion).
///
/// Origin Rust (pathutil.rs:66-77, cfg(not(unix))):
///     pub(crate) fn normalize_path(mut path: Cow<[u8]>) -> Cow<[u8]> {
///         use std::path::is_separator;
///         for i in 0..path.len() {
///             if path[i] == b'/' || !is_separator(char::from(path[i])) {
///                 continue;
///             }
///             path.to_mut()[i] = b'/';
///         }
///         path
///     }
/// (exec restructure note: the lazy per-iteration to_mut is spelled
/// scan-then-build -- a first-occurrence scan, then a single owned
/// copy construction -- because that is exactly the observable
/// value/mode split; the value and mode products are identical.)
pub fn normalize_path_rewrite(path: CowBytes, windows: bool) -> (r: CowBytes)
    ensures
        r.view() == spec_normalized(path.view(), windows),
        r.is_borrowed_mode() <==> (path.is_borrowed_mode()
            && !spec_has_rewrite(path.view(), windows)),
{
    let bs: &[u8] = path.as_slice();
    // phase 1: the first-occurrence scan (any byte the oracle would
    // rewrite?)
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut wpos: usize = 0;
    while !found && i < bs.len()
        invariant
            i <= bs.len(),
            wpos <= bs.len(),
            bs@.len() == bs.len(),
            found ==> (wpos == i && wpos < bs.len()
                && bs@.index(wpos as int) != 0x2f
                && spec_is_separator(bs@.index(wpos as int), windows)),
            !found ==> forall|k: int| 0 <= k < i ==> !(bs@.index(k) != 0x2f
                && spec_is_separator(bs@.index(k), windows)),
        decreases (if found { 0int } else { 1int }), bs.len() - i,
    {
        let c = bs[i];
        if c != 0x2f && is_separator_exec(c, windows) {
            proof {
                assert(bs@.index(i as int) != 0x2f);
                assert(spec_is_separator(bs@.index(i as int), windows));
            }
            found = true;
            wpos = i;
        } else {
            proof {
                assert(!(bs@.index(i as int) != 0x2f
                    && spec_is_separator(bs@.index(i as int), windows)));
            }
            i += 1;
        }
    }
    if !found {
        proof {
            assert(forall|k: int| 0 <= k < bs@.len() as int ==> !(bs@.index(k) != 0x2f
                && spec_is_separator(bs@.index(k), windows)));
            assert(!spec_has_rewrite(bs@, windows));
            assert(bs@ == path.view());
            spec_normalized_noop(path.view(), windows);
        }
        return path;
    }
    proof {
        assert(bs@ == path.view());
        assert(spec_has_rewrite(path.view(), windows)) by {
            let w = wpos as int;
            assert(0 <= w < bs@.len() as int);
            assert(bs@.index(w) != 0x2f && spec_is_separator(bs@.index(w), windows));
        }
    }
    // phase 2: at least one rewrite exists -- an owned copy with all
    // oracle-matched rewrites applied (upstream's to_mut once, then
    // the same condition per position)
    let mut out: Vec<u8> = Vec::new();
    let mut j: usize = 0;
    while j < bs.len()
        invariant
            j <= bs.len(),
            out@.len() == j,
            forall|k: int| 0 <= k < j ==> out@.index(k)
                == spec_normalized(bs@, windows).index(k),
        decreases bs.len() - j,
    {
        let c = bs[j];
        if c != 0x2f && is_separator_exec(c, windows) {
            proof {
                assert(bs@.index(j as int) != 0x2f);
                assert(spec_is_separator(bs@.index(j as int), windows));
                assert(spec_normalized(bs@, windows).index(j as int) == 0x2f);
            }
            out.push(0x2f);
        } else {
            proof {
                assert(c == 0x2f || !spec_is_separator(bs@.index(j as int), windows));
                assert(spec_normalized(bs@, windows).index(j as int) == bs@.index(j as int));
            }
            out.push(c);
        }
        j += 1;
    }
    proof {
        assert(out@.len() == bs@.len() as int);
        assert forall|k: int| 0 <= k < out@.len() implies
            out@.index(k) == spec_normalized(bs@, windows).index(k) by {
        }
        ext_equal(out@, spec_normalized(bs@, windows));
        assert(out@ == spec_normalized(bs@, windows));
    }
    CowBytes::Owned(out)
}

/// When the oracle matches nothing, normalize is the identity (the
/// cross-arm coherence step: under the unix axiom set this always
/// holds, so upstream's identity arm equals the rewrite arm).
proof fn spec_normalized_noop(s: Seq<u8>, windows: bool)
    requires
        !spec_has_rewrite(s, windows),
    ensures
        spec_normalized(s, windows) == s,
{
    assert forall|k: int| 0 <= k < s.len() implies
        spec_normalized(s, windows).index(k) == s.index(k) by {
        assert(!(s.index(k) != 0x2f && spec_is_separator(s.index(k), windows)));
    }
    ext_equal(spec_normalized(s, windows), s);
}

} // verus!

/// Single-file driver anchor (KVerus convention; consumers reference
/// this file via #[path]).
fn main() {}
