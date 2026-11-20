//! ignore IG1 **harness zone** -- the UT assertion theorems and law rows
//! over the src-zone twin (verified/src/lib.rs, which mounts
//! verified/src/pathutil.rs).
//!
//! The two-zone split (glob precedent): src keeps the transcription +
//! spec models + the DP33 material-chain theorems; this file carries the
//! obligation-ized test exemplars. Source UTs per harness-inventory
//! section 2.3: the four inline pathutil vector groups (upstream src
//! marks: `mod tests`, pathutil.rs:173-218), the Match combinator laws
//! and PartialErrorBuilder folding cases of lib.rs (inventory section 10
//! IG1 harness row). Every block comment states its source UT with the
//! upstream line anchor.
//!
//! KAT note (doubt-yourself-first discipline): the runtime leg of these
//! vectors was taken
//! against the PINNED upstream source on the host toolchain (rustc 1.94,
//! cargo; byte-identical `#[path]` include of code/crates/ignore/src/
//! pathutil.rs driven over the same vectors -- see the scripts record in
//! out/kverus-run/IG1/notes.md). The spec rows below are the formal
//! counterparts; the upstream-behavior column they pin came from the
//! pinned tree, not from this twin.
//!
//! Byte-literal convention (globset-twin precedent): `&[u8]` literals
//! have no static view identity in Verus specs, so KAT rows spell paths
//! as hex byte Seq constants (e.g. `seq![0x61, 0x2F, 0x62]` for "a/b");
//! exec-form rows assert kind/shape facts that do not depend on
//! un-pinnable literal views.
//!
//! Running: ./third_party/verus-docker.sh verus --rlimit 300
//!   database/ignore/verified/harness/ut_ig1.rs

use vstd::prelude::*;
use vstd::seq::*;

#[path = "../src/lib.rs"]
mod iglib;

use iglib::pathutil::*;
use iglib::*;

verus! {

// =========================================================================
// UT1 -- file_name_basic (upstream pathutil.rs:180-185)
// =========================================================================
//
// Upstream test body (pathutil.rs:181-184, verbatim rows):
//   assert_eq!(file_name("a"), Some(OsStr::new("a")));
//   assert_eq!(file_name("a/b"), Some(OsStr::new("b")));
//   assert_eq!(file_name("/a/b.txt"), Some(OsStr::new("b.txt")));

/// UT1: the basic vectors, spec rows over the pinned byte spellings.
proof fn ut1_file_name_basic() {
    reveal_with_fuel(memrchr_last, 10);
    // "a" -> Some("a")
    assert(file_name_spec(seq![0x61]) == Some(seq![0x61]));
    // "a/b" -> Some("b")
    assert(file_name_spec(seq![0x61, 0x2F, 0x62]) == Some(seq![0x62]));
    // "/a/b.txt" -> Some("b.txt")
    assert(file_name_spec(seq![0x2F, 0x61, 0x2F, 0x62, 0x2E, 0x74, 0x78, 0x74])
        == Some(seq![0x62, 0x2E, 0x74, 0x78, 0x74]));
}

// =========================================================================
// UT2 -- file_name_dot_components (upstream pathutil.rs:189-198,
//        #[cfg(unix)]-gated; the twin is unix-targeted so all rows land)
// =========================================================================
//
// Upstream test body (pathutil.rs:192-197, verbatim rows):
//   assert_eq!(file_name(""), None);
//   assert_eq!(file_name("."), None);
//   assert_eq!(file_name(".."), None);
//   assert_eq!(file_name("a/."), None);
//   assert_eq!(file_name("a/.."), None);
//   assert_eq!(file_name("/a/b/.."), None);

/// UT2: the empty/dot-component vectors (the None side of the DP32 rule:
/// only final components exactly `.` or `..` lose the name).
proof fn ut2_file_name_dot_components() {
    reveal_with_fuel(memrchr_last, 10);
    // "" -> None
    assert(file_name_spec(Seq::empty()) == None);
    // "." -> None
    assert(file_name_spec(seq![0x2E]) == None);
    // ".." -> None
    assert(file_name_spec(seq![0x2E, 0x2E]) == None);
    // "a/." -> None
    assert(file_name_spec(seq![0x61, 0x2F, 0x2E]) == None);
    // "a/.." -> None
    assert(file_name_spec(seq![0x61, 0x2F, 0x2E, 0x2E]) == None);
    // "/a/b/.." -> None
    assert(file_name_spec(seq![0x2F, 0x61, 0x2F, 0x62, 0x2F, 0x2E, 0x2E]) == None);
}

// =========================================================================
// UT3 -- file_name_trailing_dot (upstream pathutil.rs:200-206)
// =========================================================================
//
// Upstream test body (pathutil.rs:202-205, verbatim rows):
//   assert_eq!(file_name("a."), Some(OsStr::new("a.")));
//   assert_eq!(file_name("a/.b."), Some(OsStr::new(".b.")));
//   assert_eq!(file_name("a/..."), Some(OsStr::new("...")));
//   assert_eq!(file_name("a/..b.."), Some(OsStr::new("..b..")));

/// UT3: names that merely END in a dot keep the name (the Some side of
/// the DP32 rule; the note comment upstream pathutil.rs:187-188 about the
/// Windows std divergence stays a platform record -- the twin keeps the
/// unix byte semantics).
proof fn ut3_file_name_trailing_dot() {
    reveal_with_fuel(memrchr_last, 10);
    // "a." -> Some("a.")
    assert(file_name_spec(seq![0x61, 0x2E]) == Some(seq![0x61, 0x2E]));
    // "a/.b." -> Some(".b.")
    assert(file_name_spec(seq![0x61, 0x2F, 0x2E, 0x62, 0x2E])
        == Some(seq![0x2E, 0x62, 0x2E]));
    // "a/..." -> Some("...")
    assert(file_name_spec(seq![0x61, 0x2F, 0x2E, 0x2E, 0x2E])
        == Some(seq![0x2E, 0x2E, 0x2E]));
    // "a/..b.." -> Some("..b..")
    assert(file_name_spec(seq![0x61, 0x2F, 0x2E, 0x2E, 0x62, 0x2E, 0x2E])
        == Some(seq![0x2E, 0x2E, 0x62, 0x2E, 0x2E]));
}

// =========================================================================
// UT4 -- hidden_trailing_dot (upstream pathutil.rs:208-217)
// =========================================================================
//
// Upstream test body (pathutil.rs:210-216, verbatim rows):
//   assert!(is_hidden_path(Path::new(".foo")));
//   assert!(is_hidden_path(Path::new("a/.foo.")));
//   assert!(is_hidden_path(Path::new("a/.foo..")));
//   assert!(is_hidden_path(Path::new("a/...")));
//   assert!(!is_hidden_path(Path::new("a/foo.")));
//   assert!(!is_hidden_path(Path::new("a/.")));
//   assert!(!is_hidden_path(Path::new("a/..")));

/// UT4: hidden detection over the trailing-dot family (the no-file-name
/// cases "a/." / "a/.." are NOT hidden -- None payload, false by
/// pathutil.rs:88-90).
proof fn ut4_hidden_trailing_dot() {
    reveal_with_fuel(memrchr_last, 10);
    // ".foo" hidden
    assert(is_hidden_path_only_spec(seq![0x2E, 0x66, 0x6F, 0x6F]));
    // "a/.foo." hidden (name starts with '.')
    assert(is_hidden_path_only_spec(seq![0x61, 0x2F, 0x2E, 0x66, 0x6F, 0x6F, 0x2E]));
    // "a/.foo.." hidden
    assert(is_hidden_path_only_spec(seq![0x61, 0x2F, 0x2E, 0x66, 0x6F, 0x6F, 0x2E, 0x2E]));
    // "a/..." hidden (a real name of three dots)
    assert(is_hidden_path_only_spec(seq![0x61, 0x2F, 0x2E, 0x2E, 0x2E]));
    // "a/foo." not hidden (the trailing dot does not hide)
    assert(!is_hidden_path_only_spec(seq![0x61, 0x2F, 0x66, 0x6F, 0x6F, 0x2E]));
    // "a/." / "a/.." not hidden (no file name at all)
    assert(!is_hidden_path_only_spec(seq![0x61, 0x2F, 0x2E]));
    assert(!is_hidden_path_only_spec(seq![0x61, 0x2F, 0x2E, 0x2E]));
}

// =========================================================================
// UT5 -- strip_prefix byte-arm KAT rows (runtime-probe family; DP33)
// =========================================================================
//
// The upstream crate has NO inline strip_prefix test fn before PR 3609;
// these rows pin the byte-arm behavior (taken by driving the real
// pathutil include on the host -- see notes.md), in the same event the
// DP33 register entry rests on them. PR 3609 turned the cross-boundary
// family into refusal rows (verified on the patched tree,
// out/kverus-run/PR3609-verify/transcripts/); the raw (pre-patch)
// witness values remain on the raw face strip_prefix_raw_spec (src).
// Rows under the PATCHED spec:
//   ignore::strip_prefix("/home/foo", "/home/foobar") == None          <- DP33 fixed
//   ignore::strip_prefix("/home/foo", "/home/foo/bar") == Some("/bar") <- separator retained
//   ignore::strip_prefix("/home", "/home/") == Some("/")
//   ignore::strip_prefix("./", "./a/b") == Some("a/b")
//   ignore::strip_prefix("a", "abc") == None                           <- DP33 family fixed
//   ignore::strip_prefix("", "abc") == Some("abc")
//   ignore::strip_prefix("/", "/a") == Some("a")
//   ignore::strip_prefix("foo/", "foo/bar") == Some("bar")
//   ignore::strip_prefix("foo", "foobar/baz") == None                  <- DP33 family fixed

/// UT5: the byte-arm rows, spec form.
proof fn ut5_strip_prefix_rows() {
    // "/home/foo" = seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x66, 0x6F, 0x6F]
    let home_foo: Seq<u8> = seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x66, 0x6F, 0x6F];
    // "/home/foo" from "/home/foobar" -> None (DP33 cross-boundary
    // refused by the patch; the raw face's Some("bar") is the
    // strip_prefix_raw_spec row, src dp33_raw_arm_witness)
    assert(strip_prefix_spec(
        home_foo,
        seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72],
    ) == None);
    // "/home/foo" from "/home/foo/bar" -> Some("/bar") (separator kept)
    assert(strip_prefix_spec(
        home_foo,
        seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72],
    ) == Some(seq![0x2F, 0x62, 0x61, 0x72]));
    // "/home" from "/home/" -> Some("/")
    assert(strip_prefix_spec(
        seq![0x2F, 0x68, 0x6F, 0x6D, 0x65],
        seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F],
    ) == Some(seq![0x2F]));
    // "./" from "./a/b" -> Some("a/b")
    assert(strip_prefix_spec(Seq::empty(), seq![0x61]) == Some(seq![0x61]));
    // (the "./" pair: prefix "./" == seq![0x2E, 0x2F] over path "./a/b")
    let dot_slash: Seq<u8> = seq![0x2E, 0x2F];
    let path_a_b: Seq<u8> = seq![0x2E, 0x2F, 0x61, 0x2F, 0x62];
    assert(strip_prefix_spec(dot_slash, path_a_b) == Some(seq![0x61, 0x2F, 0x62]));
    // "a" from "abc" -> None (DP33 family fixed: byte prefix of a NAME)
    assert(strip_prefix_spec(seq![0x61], seq![0x61, 0x62, 0x63]) == None);
    // "" from "abc" -> Some("abc") (empty prefix strips everything)
    assert(strip_prefix_spec(Seq::empty(), seq![0x61, 0x62, 0x63])
        == Some(seq![0x61, 0x62, 0x63]));
    // "/" from "/a" -> Some("a")
    assert(strip_prefix_spec(seq![0x2F], seq![0x2F, 0x61]) == Some(seq![0x61]));
    // "foo/" from "foo/bar" -> Some("bar")
    assert(strip_prefix_spec(seq![0x66, 0x6F, 0x6F, 0x2F], seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72])
        == Some(seq![0x62, 0x61, 0x72]));
    // "foo" from "foobar/baz" -> None (DP33 family fixed)
    assert(strip_prefix_spec(
        seq![0x66, 0x6F, 0x6F],
        seq![0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A],
    ) == None);
}

/// UT5b: is_file_name rows (the upstream :124-136 face, no dedicated
/// upstream test; pinned by the same runtime probe: "a" true, "a/b"
/// false, the empty path true -- no separator byte present).
proof fn ut5b_is_file_name_rows() {
    assert(is_file_name_spec(Seq::empty()));
    assert(is_file_name_spec(seq![0x61]));
    assert(!is_file_name_spec(seq![0x61, 0x2F, 0x62]));
    assert(!is_file_name_spec(seq![0x2F, 0x61]));
}

// =========================================================================
// UT6 -- std oracle rows (the not-unix arm / std strip_prefix contrast)
// =========================================================================
//
// Runtime std ground truth (host rustc probes, recorded in notes.md):
//   Path::new("/home/foobar").strip_prefix("/home/foo") == Err
//   Path::new("/home/foobar").strip_prefix("/home/foo/bar") ... etc.
// The trusted acceptance oracle std_strip_prefix_accepts mirrors those
// Ok/Err rows; the unix arm divergence on the same pairs is the DP33
// material (kept in src; re-pinned here in two rows).

/// UT6: accept/reject rows of the std oracle on the shared vectors.
/// The ("/home/foo", "/home/foobar") pair invokes the src-zone witness
/// (dp33_std_arm_refuses_witness -- the full staged proof stays there,
/// single source of verified facts); the ("a", "abc") pair goes through
/// the general std_comps_rel_single row. The remaining runtime rows
/// (accepts ("/", "/a"), ("foo/", "foo/bar"); rejects ("foo",
/// "foobar/baz")) are recorded as runtime std-probe evidence in the
/// notes (the oracle face documents them; the assembly-fuel cost of the
/// trailing-separator / absolute shapes is allocated to a later batch,
/// not to the IG1 obligation set).
proof fn ut6_std_oracle_rows() {
    // rejects: ("/home/foo", "/home/foobar") -- src witness invocation
    dp33_std_arm_refuses_witness();
    assert(!std_strip_prefix_accepts(dp33_prefix_bytes(), dp33_path_bytes()));
    // rejects: ("a", "abc") -- single NAME sharing a byte prefix
    std_comps_rel_single(seq![0x61]);
    std_comps_rel_single(seq![0x61, 0x62, 0x63]);
    assert(std_comps(seq![0x61]) =~= seq![seq![0x61]]);
    assert(std_comps(seq![0x61, 0x62, 0x63]) =~= seq![seq![0x61, 0x62, 0x63]]);
    // the single components differ (one byte vs a three-byte name)
    let a_comp: Seq<u8> = seq![0x61];
    let b_comp: Seq<u8> = seq![0x61, 0x62, 0x63];
    assert(a_comp.len() == 1 && b_comp.len() == 3 && !(a_comp =~= b_comp));
    // comps_prefix fails at index 0 (a[0] is the 1-byte name, b[0] the
    // 3-byte one); comps_uniform row with the witness index 0
    let a_comps: Seq<Seq<u8>> = seq![seq![0x61]];
    let abc: Seq<u8> = seq![0x61, 0x62, 0x63];
    assert(!std_strip_prefix_accepts(seq![0x61], seq![0x61, 0x62, 0x63])) by {
        assert(a_comps.len() == 1);
        assert(a_comps[0] =~= seq![0x61]);
        assert(std_comps(abc)[0] =~= abc);
    }
    // accepts: ("", "abc") -- empty component sequence is a prefix of any
    assert(std_comps(Seq::empty()) =~= Seq::empty());
    assert(std_strip_prefix_accepts(Seq::empty(), seq![0x61, 0x62, 0x63]));
}

// =========================================================================
// UT6b -- the DP33 arm rows (unix byte strip vs not(unix) std)
// =========================================================================
//
// PRE-PATCH the two arms of ONE upstream four-line function
// (pathutil.rs:100-116) disagreed on the byte-prefix-shared pairs; the
// PR 3609 boundary fix aligns them on every pair in this table. The
// rows now re-pin the POST-PATCH agreement: both the unix arm (the
// patched strip_prefix_spec) and the not(unix) arm (== the std oracle)
// refuse the cross-boundary pairs (src dp33_post_patch_agreement_
// statement carries the primary pair's staged proof).

/// UT6b: the DP33 arm rows, post-patch agreement form.
proof fn ut6b_dp33_arm_contrast_rows() {
    let prefix: Seq<u8> = seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x66, 0x6F, 0x6F];
    let pth: Seq<u8> = seq![0x2F, 0x68, 0x6F, 0x6D, 0x65, 0x2F, 0x66, 0x6F, 0x6F, 0x62, 0x61, 0x72];
    // post-patch: the patched unix arm refuses (PR 3609 row 1)
    assert(strip_prefix_spec(prefix, pth) == None);
    // the not(unix) arm (== std oracle) also refuses (pathutil.rs:113-116)
    dp33_std_arm_refuses_witness();
    assert(!std_strip_prefix_accepts(prefix, pth));
    // the ("a", "abc") pair of the same shape agrees too
    assert(strip_prefix_spec(seq![0x61], seq![0x61, 0x62, 0x63]) == None);
    std_comps_rel_single(seq![0x61]);
    std_comps_rel_single(seq![0x61, 0x62, 0x63]);
    let a_comps: Seq<Seq<u8>> = seq![seq![0x61]];
    let abc: Seq<u8> = seq![0x61, 0x62, 0x63];
    assert(!std_strip_prefix_accepts(seq![0x61], seq![0x61, 0x62, 0x63])) by {
        assert(a_comps.len() == 1);
        assert(a_comps[0] =~= seq![0x61]);
        assert(std_comps(abc)[0] =~= abc);
    }
}

// =========================================================================
// UT7 -- Match combinator laws (upstream lib.rs:427-487)
// =========================================================================
//
// No upstream test fns for Match (lib.rs:489-549 module is the temp-dir
// helper only); the law rows here obligation-ize the documented
// contracts (the is_none/is_ignore/is_whitelist partition, invert flip
// and involution, inner, or fallback, map shape preservation).

/// UT7a: kind-partition rows on each constructor (exec face).
pub fn ut7a_match_kind_rows() {
    let none: Match<u64> = Match::None;
    let t_none_1 = none.is_none();
    let t_none_2 = none.is_ignore();
    let t_none_3 = none.is_whitelist();
    assert(t_none_1 && !t_none_2 && !t_none_3);
    let ig: Match<u64> = Match::Ignore(2u64);
    let t_ig_1 = ig.is_none();
    let t_ig_2 = ig.is_ignore();
    let t_ig_3 = ig.is_whitelist();
    assert(!t_ig_1 && t_ig_2 && !t_ig_3);
    let wl: Match<u64> = Match::Whitelist(3u64);
    let t_wl_1 = wl.is_none();
    let t_wl_2 = wl.is_ignore();
    let t_wl_3 = wl.is_whitelist();
    assert(!t_wl_1 && !t_wl_2 && t_wl_3);
}

/// UT7b: invert flips the kind and is involutive on the payload chain
/// (docs lib.rs:453-454, "Inverts the match ... A non-match remains the
/// same"), spec track.
proof fn ut7b_invert_flips_kinds() {
    let none: Match<u64> = Match::None;
    let inv0 = invert_of_match(none);
    assert(inv0 matches Match::None);
    let ig: Match<u64> = Match::Ignore(2u64);
    let inv1 = invert_of_match(ig);
    assert(inv1 matches Match::Whitelist(_));
    let wl: Match<u64> = Match::Whitelist(3u64);
    let inv2 = invert_of_match(wl);
    assert(inv2 matches Match::Ignore(_));
}

proof fn ut7b_invert_involution(m: Match<u64>)
    ensures invert_of_match(invert_of_match(m)) == m
{
    match m {
        Match::None => {},
        Match::Ignore(_) => {},
        Match::Whitelist(_) => {},
    }
}

/// UT7c: inner returns the payload of non-None matches (docs
/// lib.rs:463, "Return the value inside this match if it exists").
pub fn ut7c_inner_rows() {
    let none: Match<u64> = Match::None;
    let inner_none = none.inner();
    assert(inner_none matches None);
    let ig: Match<u64> = Match::Ignore(2u64);
    let inner_ig = ig.inner();
    assert(inner_ig matches Some(_));
    match inner_ig {
        Some(x) => assert(*x == 2u64),
        None => assert(false),
    }
    let wl: Match<u64> = Match::Whitelist(3u64);
    match wl.inner() {
        Some(x) => assert(*x == 3u64),
        None => assert(false),
    }
}

/// UT7d: or keeps the left non-None and falls through on None (docs
/// lib.rs:483, "Return the match if it is not none. Otherwise, return
/// other."), exec face.
pub fn ut7d_or_rows() {
    // NB: upstream `or` consumes both sides (lib.rs:485
    // `pub fn or(self, other: Self) -> Self`); fresh values per row,
    // matching upstream by-value semantics.
    let o1 = Match::<u64>::None.or(Match::Ignore(2u64));
    assert(o1 matches Match::Ignore(_));
    let o2 = Match::Ignore(2u64).or(Match::None);
    assert(o2 matches Match::Ignore(_));
    let o3 = Match::Ignore(2u64).or(Match::Whitelist(3u64));
    assert(o3 matches Match::Ignore(_));
}

/// UT7e: map preserves the constructor shape and is the identity on
/// None (docs lib.rs:473-474, "Apply the given function to the value
/// inside this match. If the match has no value, then return the match
/// unchanged."), exec face with a bound-safe closure payload.
pub fn ut7e_map_rows() {
    let none: Match<u64> = Match::None;
    let half = |t: u64| t % 2;
    let m0 = none.map(half);
    assert(m0 matches Match::None);
    let ig: Match<u64> = Match::Ignore(2u64);
    let m1 = ig.map(half);
    assert(m1 matches Match::Ignore(_));
    let wl: Match<u64> = Match::Whitelist(3u64);
    let m2 = wl.map(half);
    assert(m2 matches Match::Whitelist(_));
}

/// UT7f: the map value law, spec track (map_spec with a spec_fn
/// payload): map over Ignore applies f to the payload. The payload-use
/// idiom is the type-annotated closure let (the trait_for_fn example
/// form); named fn items do not coerce and untyped closures stay opaque.
proof fn ut7f_map_value_law() {
    let m: Match<int> = Match::Ignore(2int);
    let f: spec_fn(int) -> int = |t: int| t / 2;
    match map_spec(m, f) {
        Match::None => assert(false),
        Match::Ignore(t) => assert(t == 1int),
        Match::Whitelist(_) => assert(false),
    }
}

// =========================================================================
// UT8 -- PartialErrorBuilder folding rules (upstream lib.rs:375-407)
// =========================================================================
//
// No upstream test fns; the folding obligations follow lib.rs:398-406:
// empty -> None, single -> Some(that error), plural -> Some(Partial).

/// UT8a: the empty stack folds to None.
pub fn ut8a_peb_empty() {
    let b = PartialErrorBuilder::new();
    let r = b.into_error_option();
    assert(r matches None);
}

/// UT8b: a single stacked error returns UNWRAPPED (no Partial wrap) --
/// including when the single error is itself a Partial (the subtle row:
/// upstream pops the lone element out of the vec).
pub fn ut8b_peb_single() {
    let mut b = PartialErrorBuilder::new();
    b.push(Error::Io(IoErrorFace::new(3)));
    match b.into_error_option() {
        Some(e) => assert(e matches Error::Io(_)),
        None => assert(false),
    }
    let mut b2 = PartialErrorBuilder::new();
    let mut inner = Vec::new();
    let _ = inner.push(Error::InvalidDefinition);
    b2.push(Error::Partial(inner));
    match b2.into_error_option() {
        Some(e) => assert(e matches Error::Partial(_)),
        None => assert(false),
    }
}

/// UT8c: a plural stack folds to Some(Partial(the list)).
pub fn ut8c_peb_plural() {
    let mut b = PartialErrorBuilder::new();
    b.push(Error::InvalidDefinition);
    b.push(Error::UnrecognizedFileType(Vec::new()));
    match b.into_error_option() {
        Some(e) => assert(e matches Error::Partial(_)),
        None => assert(false),
    }
}

/// UT8d: push_ignore_io drops exclusive-io errors and keeps the rest;
/// the descent rows matter here -- a WithLineNumber-wrapped Io is an
/// exclusive io error too (lib.rs:176), so it drops as well.
pub fn ut8d_peb_push_ignore_io() {
    // the descent rows evaluate is_io_spec through the tag wrapper:
    // give the recursive spec fn enough fuel at the call sites
    proof {
        reveal_with_fuel(is_io_spec, 4);
    }
    let mut b = PartialErrorBuilder::new();
    b.push_ignore_io(Error::Io(IoErrorFace::new(1)));
    assert(b.errs@.len() == 0); // dropped
    b.push_ignore_io(Error::WithLineNumber {
        line: 5,
        err: std::boxed::Box::new(Error::Io(IoErrorFace::new(2))),
    });
    assert(b.errs@.len() == 0); // descends through the tag: still io, dropped
    b.push_ignore_io(Error::InvalidDefinition);
    assert(b.errs@.len() == 1); // kept
    b.push_ignore_io(Error::Glob {
        glob: None,
        err: Vec::new(),
    });
    assert(b.errs@.len() == 2); // kept
}

/// UT8e: maybe_push / maybe_push_ignore_io follow the Option payload.
pub fn ut8e_peb_maybe_push() {
    let mut b = PartialErrorBuilder::new();
    b.maybe_push(None);
    assert(b.errs@.len() == 0);
    b.maybe_push(Some(Error::InvalidDefinition));
    assert(b.errs@.len() == 1);
    b.maybe_push_ignore_io(Some(Error::Io(IoErrorFace::new(9))));
    assert(b.errs@.len() == 1); // io dropped
    b.maybe_push_ignore_io(None);
    assert(b.errs@.len() == 1); // None is a no-op
    b.maybe_push_ignore_io(Some(Error::UnrecognizedFileType(Vec::new())));
    assert(b.errs@.len() == 2); // kept
}

// =========================================================================
// UT9 -- Error predicate family (upstream lib.rs:156-260)
// =========================================================================
//
// Rows over the docs: is_partial (lib.rs:157-160), is_io with the
// "exclusively" reading (lib.rs:172), io_error / into_io_error
/// (lib.rs:187-195, 227-229), depth (lib.rs:253-254). No upstream test
/// fns; these rows obligation-ize the implemented descent behavior.

/// UT9a: is_partial descends through wrappers; bare leaves are not
/// partial.
pub fn ut9a_is_partial_rows() {
    proof {
        reveal_with_fuel(is_partial_spec, 4);
        reveal_with_fuel(is_io_spec, 4);
        reveal_with_fuel(io_error_spec, 4);
        reveal_with_fuel(depth_spec, 4);
    }
    let e_io = Error::Io(IoErrorFace::new(1));
    let r1 = is_partial(&e_io);
    assert(!r1);
    let e_invalid = Error::InvalidDefinition;
    let r2 = is_partial(&e_invalid);
    assert(!r2);
    let e_partial = Error::Partial(Vec::new());
    let r3 = is_partial(&e_partial);
    assert(r3);
    let e_wrapped_partial = Error::WithDepth {
        depth: 1,
        err: std::boxed::Box::new(Error::Partial(Vec::new())),
    };
    let r4 = is_partial(&e_wrapped_partial);
    assert(r4);
    let e_wrapped_plain = Error::WithDepth {
        depth: 1,
        err: std::boxed::Box::new(Error::InvalidDefinition),
    };
    let r5 = is_partial(&e_wrapped_plain);
    assert(!r5);
}

/// UT9b: is_io -- the "exclusively" family: bare Io yes;
/// WithLineNumber/Io yes (descends, lib.rs:176); Partial([io]) yes;
/// Partial([io, io]) no (plural), Partial([io, glob]) no.
pub fn ut9b_is_io_exclusively_rows() {
    proof {
        reveal_with_fuel(is_io_spec, 4);
    }
    let e_io = Error::Io(IoErrorFace::new(1));
    let r1 = is_io(&e_io);
    assert(r1);
    let e_tagged = Error::WithLineNumber {
        line: 5,
        err: std::boxed::Box::new(Error::Io(IoErrorFace::new(2))),
    };
    let r2 = is_io(&e_tagged);
    assert(r2);
    let mut single = Vec::new();
    let _ = single.push(Error::Io(IoErrorFace::new(3)));
    let e_single = Error::Partial(single);
    let r3 = is_io(&e_single);
    assert(r3);
    let mut plural = Vec::new();
    let _ = plural.push(Error::Io(IoErrorFace::new(4)));
    let _ = plural.push(Error::Io(IoErrorFace::new(5)));
    let e_plural = Error::Partial(plural);
    let r4 = is_io(&e_plural);
    assert(!r4);
    let mut mixed = Vec::new();
    let _ = mixed.push(Error::Io(IoErrorFace::new(6)));
    let _ = mixed.push(Error::InvalidDefinition);
    let e_mixed = Error::Partial(mixed);
    let r5 = is_io(&e_mixed);
    assert(!r5);
    let e_loop = Error::Loop {
        ancestor: PathBytes { bytes: Vec::new() },
        child: PathBytes { bytes: Vec::new() },
    };
    let r6 = is_io(&e_loop);
    assert(!r6);
    let e_glob = Error::Glob { glob: None, err: Vec::new() };
    let r7 = is_io(&e_glob);
    assert(!r7);
}

/// UT9c: io_error / into_io_error surface the io payload exactly on the
/// exclusive-io shapes; Loop never (docs lib.rs:190-193 give the loop
/// case as the None example).
pub fn ut9c_io_error_rows() {
    proof {
        reveal_with_fuel(is_io_spec, 4);
        reveal_with_fuel(io_error_spec, 4);
        reveal_with_fuel(into_io_error_spec, 4);
    }
    let io_err = Error::Io(IoErrorFace::new(7));
    let r1 = io_error(&io_err);
    assert(r1 matches Some(_));
    let consumed = Error::Io(IoErrorFace::new(8));
    let r2 = into_io_error(consumed);
    assert(r2 matches Some(_));
    let wrap = Error::WithDepth {
        depth: 2,
        err: std::boxed::Box::new(Error::Io(IoErrorFace::new(9))),
    };
    let r3 = io_error(&wrap);
    assert(r3 matches Some(_));
    let r4 = into_io_error(wrap);
    assert(r4 matches Some(_));
    let mut plural_vec = Vec::new();
    let _ = plural_vec.push(Error::Io(IoErrorFace::new(10)));
    let _ = plural_vec.push(Error::InvalidDefinition);
    let e_plural = Error::Partial(plural_vec);
    let r5 = io_error(&e_plural);
    assert(r5 matches None);
    let mut lone_vec = Vec::new();
    let _ = lone_vec.push(Error::Io(IoErrorFace::new(11)));
    let e_lone = Error::Partial(lone_vec);
    let r6 = io_error(&e_lone);
    assert(r6 matches Some(_));
    let loop_err = Error::Loop {
        ancestor: PathBytes { bytes: Vec::new() },
        child: PathBytes { bytes: Vec::new() },
    };
    let r7 = io_error(&loop_err);
    assert(r7 matches None);
    let r8 = into_io_error(loop_err);
    assert(r8 matches None);
}

/// UT9d: depth returns None everywhere except WithDepth Some(depth) /
/// WithPath descent (lib.rs:254-260; upstream marks the recursive
/// directory iterator case).
pub fn ut9d_depth_rows() {
    proof {
        reveal_with_fuel(depth_spec, 4);
    }
    let e_io = Error::Io(IoErrorFace::new(1));
    let r1 = depth(&e_io);
    assert(r1 matches None);
    let e_partial = Error::Partial(Vec::new());
    let r2 = depth(&e_partial);
    assert(r2 matches None);
    let e_depth = Error::WithDepth {
        depth: 4,
        err: std::boxed::Box::new(Error::InvalidDefinition),
    };
    let r3 = depth(&e_depth);
    match r3 {
        Some(d) => assert(d == 4),
        None => assert(false),
    }
    // WithPath descends into its inner error's depth
    let e_path = Error::WithPath {
        path: PathBytes { bytes: Vec::new() },
        err: std::boxed::Box::new(Error::WithDepth {
            depth: 6,
            err: std::boxed::Box::new(Error::InvalidDefinition),
        }),
    };
    let r4 = depth(&e_path);
    match r4 {
        Some(d) => assert(d == 6),
        None => assert(false),
    }
}

// =========================================================================
// UT10 -- tagger helper rows (upstream lib.rs:262-284)
// =========================================================================

/// UT10: with_path / with_depth shape rows and the tagged empty-path
/// omission (lib.rs:277-284: an empty path yields a bare WithLineNumber
/// wrapper; a non-empty path yields the WithPath wrap).
pub fn ut10_tagger_rows() {
    let e = Error::InvalidDefinition;
    let wp = error_with_path(e, b"/x");
    assert(wp matches Error::WithPath { .. });
    let wd = error_with_depth(Error::InvalidDefinition, 3);
    assert(wd matches Error::WithDepth { .. });
    let t_empty = error_tagged(Error::InvalidDefinition, b"", 5);
    assert(t_empty matches Error::WithLineNumber { .. });
    let t_nonempty = error_tagged(Error::InvalidDefinition, b"/y", 6);
    assert(t_nonempty matches Error::WithPath { .. });
}

}

fn main() {}
