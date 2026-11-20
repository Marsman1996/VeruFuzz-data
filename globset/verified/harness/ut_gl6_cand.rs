//! GL6 harness -- the Candidate family: from_bytes/from_cow/new
//! triples (basename/ext columns, mode preservation), the window
//! slicers (path_prefix/path_suffix; lib.rs:651-671 -- NOT the
//! glob.rs:1086-1096 cfg(test) helpers), and basename_for_regex
//! (lib.rs:655-663, GM14's carrier).
//!
//! Upstream anchors: the two length-filter regressions lib.rs:1361-1423
//! exercise the Candidate side via GlobSet (GL7's column); the rows here
//! pin the Candidate columns verbatim on the strategy-resizable vectors,
//! plus the GL1 pathutil fixtures they ride on, plus the GM9 doc corners
//! (.rs owns ext .rs; ..rs owns .rs; empty; no-dot).
//! The ".."-skip family (lib.rs:1419-1422's `**/..` x "parent/..") lands
//! as the basename-empty rows: basename "" and basename_for_regex ".."
//! (the GL7 BasenameLiteral guard !basename.is_empty() consumes these).
//!
//! Grounding shape (GL1 ut_vectors precedent): value rows build the
//! input as an exec `vec!` (its spec view pins directly, per the GL1
//! probe evidence) and feed Candidate::from_cow in the Owned mode;
//! recursive-model folding rides `by (compute_only)` on LITERAL
//! arguments only (the compute engine does not simplify place views
//! -- that wall is real and recorded in the GL6 notes); Borrowed-mode
//! rows keep the b"..." slice inputs and assert the mode clauses only,
//! which fold straight off the constructors' postconditions.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

#[path = "../src/lib.rs"]
mod lib;

#[allow(unused_imports)]
use lib::CowBytes;
#[allow(unused_imports)]
use lib::pathutil;
#[allow(unused_imports)]
use lib::glob;

use lib::{Candidate, spec_cand_basename, spec_cand_base_for_regex_arm, spec_cand_ext, spec_window};

verus! {

// -------------------------------------------------------------------------
// Row family 1: "foo/bar" (GL1 name1 carried end-to-end through the
// Candidate triple): basename "bar", ext "".
// -------------------------------------------------------------------------

fn cand_foo_bar() {
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72])
            == seq![0x62, 0x61, 0x72]) by (compute_only);
        assert(spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72])
            == Seq::empty()) by (compute_only);
    }
    assert(c.basename.view() == seq![0x62, 0x61, 0x72]);           // "bar"
    assert(c.ext.view() == Seq::empty());
}

fn cand_foo_bar_rs() {
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72, 0x2e, 0x72, 0x73];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72, 0x2e, 0x72, 0x73],
        ) == seq![0x62, 0x61, 0x72, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(spec_cand_ext(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72, 0x2e, 0x72, 0x73],
        ) == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.basename.view() == seq![0x62, 0x61, 0x72, 0x2e, 0x72, 0x73]);
    assert(c.ext.view() == seq![0x2e, 0x72, 0x73]);               // ".rs"
}

// GM9 corner rows: ".rs" owns extension ".rs"; "..rs" owns ".rs";
// "foo" owns none.

fn cand_dot_rs() {
    let v: Vec<u8> = vec![0x2e, 0x72, 0x73];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(seq![0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
        assert(spec_cand_ext(seq![0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.basename.view() == seq![0x2e, 0x72, 0x73]);
    // the extension includes the leading dot (GM9)
    assert(c.ext.view() == seq![0x2e, 0x72, 0x73]);
}

fn cand_dotdot_rs() {
    let v: Vec<u8> = vec![0x2e, 0x2e, 0x72, 0x73];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(seq![0x2e, 0x2e, 0x72, 0x73])
            == seq![0x2e, 0x2e, 0x72, 0x73]) by (compute_only);
        assert(spec_cand_ext(seq![0x2e, 0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(c.basename.view() == seq![0x2e, 0x2e, 0x72, 0x73]);
    assert(c.ext.view() == seq![0x2e, 0x72, 0x73]);
}

fn cand_foo_no_ext() {
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(seq![0x66, 0x6f, 0x6f])
            == seq![0x66, 0x6f, 0x6f]) by (compute_only);
        assert(spec_cand_ext(seq![0x66, 0x6f, 0x6f]) == Seq::empty()) by (compute_only);
    }
    assert(c.basename.view() == seq![0x66, 0x6f, 0x6f]);
    assert(c.ext.view() == Seq::empty());
}

// GL1 fixtures' None corners: empty path and `..`-tail collapse to the
// empty basename/ext (the unwrap_or columns).

fn cand_empty() {
    let v: Vec<u8> = vec![];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(Seq::empty()) == Seq::empty()) by (compute_only);
        assert(spec_cand_ext(Seq::empty()) == Seq::empty()) by (compute_only);
    }
    assert(c.basename.view() == Seq::empty());
    assert(c.ext.view() == Seq::empty());
}

fn cand_dotdot_tail() {
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e])
            == Seq::empty()) by (compute_only);
        assert(spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e])
            == Seq::empty()) by (compute_only);
        assert(spec_cand_base_for_regex_arm(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e],
        )) by (compute_only);
    }
    assert(c.basename.view() == Seq::empty());
    assert(c.ext.view() == Seq::empty());
    // basename_for_regex: the basename is empty and the RAW path ends
    // with ".." -- the regex arm's virtual base (GM14's carrier)
    let bfr: Vec<u8> = c.basename_for_regex();
    assert(bfr@ == seq![0x2e, 0x2e]);
}

fn cand_parent_dotdot() {
    // the lib.rs:1420-1422 row: set does not remember `parent/..` --
    // here the Candidate columns the BasenameLiteral guard reads
    let v: Vec<u8> = vec![0x70, 0x61, 0x72, 0x65, 0x6e, 0x74, 0x2f, 0x2e, 0x2e];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(
            seq![0x70, 0x61, 0x72, 0x65, 0x6e, 0x74, 0x2f, 0x2e, 0x2e],
        ) == Seq::empty()) by (compute_only);
        assert(spec_cand_base_for_regex_arm(
            seq![0x70, 0x61, 0x72, 0x65, 0x6e, 0x74, 0x2f, 0x2e, 0x2e],
        )) by (compute_only);
    }
    assert(c.basename.view() == Seq::empty());
    assert(c.ext.view() == Seq::empty());
    let bfr: Vec<u8> = c.basename_for_regex();
    assert(bfr@ == seq![0x2e, 0x2e]);
}

fn cand_root_slash() {
    // GL1 SUSPECT-1's "/"-row behavior: file_name is Some(empty) -- the
    // basename column is empty and NOT the dotdot arm (path lacks a
    // trailing "..")
    let v: Vec<u8> = vec![0x2f];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_cand_basename(seq![0x2f]) == Seq::empty()) by (compute_only);
        assert(!spec_cand_base_for_regex_arm(seq![0x2f])) by (compute_only);
    }
    assert(c.basename.view() == Seq::empty());
    let bfr: Vec<u8> = c.basename_for_regex();
    assert(bfr@ == Seq::empty());
}

// -------------------------------------------------------------------------
// Row family 2: the window slicers (lib.rs:651-671).
// -------------------------------------------------------------------------

fn windows_prefix() {
    let v: Vec<u8> = vec![0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_window(
            seq![0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68],
            3int,
            false,
        ) == seq![0x61, 0x62, 0x63]) by (compute_only);
        assert(spec_window(
            seq![0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68],
            8int,
            false,
        ) == seq![0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68]) by (compute_only);
    }
    let pre3: &[u8] = c.path_prefix(3);
    assert(pre3@ == seq![0x61, 0x62, 0x63]);
    let whole: &[u8] = c.path_prefix(8);
    assert(whole@ == c.path.view());
    let wide: &[u8] = c.path_prefix(20);
    assert(wide@ == c.path.view());
}

fn windows_suffix() {
    let v: Vec<u8> = vec![0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        assert(spec_window(
            seq![0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68],
            3int,
            true,
        ) == seq![0x66, 0x67, 0x68]) by (compute_only);
    }
    let suf3: &[u8] = c.path_suffix(3);
    assert(suf3@ == seq![0x66, 0x67, 0x68]);
    let whole: &[u8] = c.path_suffix(8);
    assert(whole@ == c.path.view());
}

// -------------------------------------------------------------------------
// Row family 3: Borrowed-mode preservation rows (from_bytes/new slice
// input stays Borrowed through all three Cow columns -- the Cow ghost
// model's Borrowed lane; plus the unix from_path_lossy identity noted
// on `new`).
// -------------------------------------------------------------------------

fn cand_borrowed_modes() {
    let p: &[u8] = b"foo/bar.rs";
    let c: Candidate = Candidate::from_bytes(p);
    assert(c.path.is_borrowed_mode());
    assert(c.basename.is_borrowed_mode());
    assert(c.ext.is_borrowed_mode());
}

fn cand_new_modes() {
    let p: &[u8] = b"foo/bar.rs";
    let c1: Candidate = Candidate::new(p);
    let c2: Candidate = Candidate::from_bytes(p);
    assert(c1.path.is_borrowed_mode());
    assert(c2.path.is_borrowed_mode());
    // new == from_bytes on unix (the bstr unix identity), view-level
    assert(c1.path.view() == c2.path.view());
    assert(c1.basename.view() == c2.basename.view());
    assert(c1.ext.view() == c2.ext.view());
}

fn cand_new_invalid_utf8_unix() {
    // the from_path_lossy unix arm is the byte identity: a \xFF path
    // reaches the columns raw (no U+FFFD transcoding on unix; the
    // runtime oracle pins this row below -- oracle spot)
    let p: &[u8] = b"foo/\xffbar";
    let c: Candidate = Candidate::new(p);
    assert(c.path.view() == p@);
    assert(c.path.is_borrowed_mode());
    assert(c.basename.is_borrowed_mode());
    assert(c.ext.is_borrowed_mode());
}

// Owned-mode columns: the Cow ghost model's Owned lane (GL1's tests
// are Owned-input shaped; here the full triple must be Owned).

fn cand_owned_columns() {
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72, 0x2e, 0x72, 0x73];
    let c: Candidate = Candidate::from_cow(CowBytes::Owned(v));
    proof {
        // the name column is Some, so every mode follows the Owned path
        assert(lib::spec_cand_name_opt(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72, 0x2e, 0x72, 0x73],
        ) is Some) by (compute_only);
        assert(spec_cand_ext(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72, 0x2e, 0x72, 0x73],
        ).len() > 0) by (compute_only);
    }
    assert(!c.path.is_borrowed_mode());
    assert(!c.basename.is_borrowed_mode());
    assert(!c.ext.is_borrowed_mode());
}

// -------------------------------------------------------------------------
// Spec-model spot pins (the spec_cand_* value columns on the same
// vectors, asserted directly against the recursive models; pure proof
// rows, literal args only).
// -------------------------------------------------------------------------

proof fn model_pins() {
    assert(spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72])
        == seq![0x62, 0x61, 0x72]) by (compute_only);
    assert(spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72])
        == Seq::empty()) by (compute_only);
    assert(spec_cand_ext(seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73])
        == seq![0x2e, 0x72, 0x73]) by (compute_only);
    assert(spec_cand_basename(seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e])
        == Seq::empty()) by (compute_only);
    assert(spec_cand_base_for_regex_arm(seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e]))
        by (compute_only);
    assert(!spec_cand_base_for_regex_arm(seq![0x2f])) by (compute_only);
    assert(spec_window(seq![1, 2, 3, 4, 5], 3int, false) == seq![1, 2, 3]) by (compute_only);
    assert(spec_window(seq![1, 2, 3, 4, 5], 3int, true) == seq![3, 4, 5]) by (compute_only);
    assert(spec_window(seq![1, 2, 3], 9int, false) == seq![1, 2, 3]) by (compute_only);
}

} // verus!

fn main() {}
