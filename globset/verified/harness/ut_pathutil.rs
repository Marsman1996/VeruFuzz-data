//! GL1 harness -- the 13 pathutil unit tests, re-erected as assertion
//! theorems over the verified src tree.
//!
//! Upstream rows (pathutil.rs:98-140, the name!/ext!/normalize! macro
//! fixtures; values verbatim):
//!   name1 "foo/bar" -> Some("bar");  name2 "foo" -> Some("foo");
//!   name3 "foo/.." -> None;          name4 "" -> None;
//!   ext1 "foo.rs" -> Some(".rs");    ext2 ".rs" -> Some(".rs");
//!   ext3 "..rs" -> Some(".rs");      ext4 "" -> None;
//!   ext5 "foo" -> None;
//!   normal1 b"foo" -> b"foo";        normal2 b"foo/bar" -> b"foo/bar";
//!   normal3 b"foo\\bar" -> unix: b"foo\\bar" / windows: b"foo/bar";
//!   normal4 b"foo\\bar/baz" -> unix: b"foo\\bar/baz" / windows: b"foo/bar/baz".
//! The upstream tests feed Cow::Owned inputs; the borrowed-mode column
//! of the contracts is additionally pinned on representative rows
//! (upstream's tests never exercise a Borrowed input; those extra
//! rows are contract coverage, recorded as GL1-added).
//!
//! Grounding shape (the siphasher ut_vectors precedent): per row, the
//! spec chain is folded on the ground input sequence by the compute
//! engine inside a proof block, then the exec call's postcondition
//! bridges to the concrete expected value.

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod lib;
#[allow(unused_imports)]
use lib::pathutil;

use lib::pathutil::{
    file_name, file_name_ext, normalize_path, normalize_path_rewrite, rfind_byte,
    spec_dotdot, spec_final_component, spec_final_ext, spec_normalized,
    rfind_pref,
};
use lib::CowBytes;

verus! {

// ===========================================================================
// name! rows (4) -- Cow::Owned inputs, exact value pins.
// ===========================================================================

fn ut_name1() {
    // name!(name1, "foo/bar", Some("bar"))
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72];
    let c = CowBytes::Owned(v);
    let got = file_name(&c);
    proof {
        assert(spec_final_component(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72])
            == seq![0x62, 0x61, 0x72]) by (compute_only);
    }
    assert(got is Some);
    assert(got.get_Some_0().view() == seq![0x62, 0x61, 0x72]); // "bar"
    assert(got.get_Some_0().is_owned_mode());
}

fn ut_name2() {
    // name!(name2, "foo", Some("foo"))
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f];
    let c = CowBytes::Owned(v);
    let got = file_name(&c);
    proof {
        assert(spec_final_component(seq![0x66, 0x6f, 0x6f])
            == seq![0x66, 0x6f, 0x6f]) by (compute_only);
    }
    assert(got is Some);
    assert(got.get_Some_0().view() == seq![0x66, 0x6f, 0x6f]); // "foo"
}

fn ut_name3() {
    // name!(name3, "foo/..", None)
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e];
    let c = CowBytes::Owned(v);
    let got = file_name(&c);
    proof {
        assert(spec_final_component(seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e])
            == spec_dotdot()) by (compute_only);
    }
    assert(got matches None);
}

fn ut_name4() {
    // name!(name4, "", None)
    let v: Vec<u8> = Vec::new();
    let c = CowBytes::Owned(v);
    let got = file_name(&c);
    proof {
        assert(c.view().len() == 0);
    }
    assert(got matches None);
}

// ===========================================================================
// ext! rows (5).
// ===========================================================================

fn ut_ext1() {
    // ext!(ext1, "foo.rs", Some(".rs"))
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73];
    let c = CowBytes::Owned(v);
    let got = file_name_ext(&c);
    proof {
        assert(rfind_pref(seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73], 0x2e, 6) == 3) by (compute_only);
        assert(spec_final_ext(seq![0x66, 0x6f, 0x6f, 0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(got is Some);
    assert(got.get_Some_0().view() == seq![0x2e, 0x72, 0x73]); // ".rs"
    assert(got.get_Some_0().is_owned_mode());
}

fn ut_ext2() {
    // ext!(ext2, ".rs", Some(".rs")) -- the dotfile leads its own ext
    // family (GM9's worked example)
    let v: Vec<u8> = vec![0x2e, 0x72, 0x73];
    let c = CowBytes::Owned(v);
    let got = file_name_ext(&c);
    proof {
        assert(rfind_pref(seq![0x2e, 0x72, 0x73], 0x2e, 3) == 0) by (compute_only);
        assert(spec_final_ext(seq![0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(got is Some);
    assert(got.get_Some_0().view() == seq![0x2e, 0x72, 0x73]); // ".rs"
}

fn ut_ext3() {
    // ext!(ext3, "..rs", Some(".rs")) -- the RIGHTMOST dot wins
    let v: Vec<u8> = vec![0x2e, 0x2e, 0x72, 0x73];
    let c = CowBytes::Owned(v);
    let got = file_name_ext(&c);
    proof {
        assert(rfind_pref(seq![0x2e, 0x2e, 0x72, 0x73], 0x2e, 4) == 1) by (compute_only);
        assert(spec_final_ext(seq![0x2e, 0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(got is Some);
    assert(got.get_Some_0().view() == seq![0x2e, 0x72, 0x73]); // ".rs"
}

fn ut_ext4() {
    // ext!(ext4, "", None)
    let v: Vec<u8> = Vec::new();
    let c = CowBytes::Owned(v);
    let got = file_name_ext(&c);
    proof {
        assert(c.view().len() == 0);
    }
    assert(got matches None);
}

fn ut_ext5() {
    // ext!(ext5, "foo", None) -- no embedded dot
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f];
    let c = CowBytes::Owned(v);
    let got = file_name_ext(&c);
    proof {
        assert(rfind_pref(seq![0x66, 0x6f, 0x6f], 0x2e, 3) == -1) by (compute_only);
    }
    assert(got matches None);
}

// ===========================================================================
// normalize! rows (4, both cfg arms). normal1/2 carry no
// platform-sensitive byte (identical under both axiom sets);
// normal3/4 are the split rows, each pinned under BOTH the unix and
// the windows oracle (upstream compiles one arm per platform; the
// parameterized twin proves both).
// ===========================================================================

fn ut_normal1() {
    // normalize!(normal1, b"foo", b"foo")
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f];
    let c = CowBytes::Owned(v);
    let got = normalize_path(c);
    assert(got.view() == seq![0x66, 0x6f, 0x6f]);
    // the rewrite arm agrees (no separator byte at all)
    proof {
        assert(spec_normalized(seq![0x66, 0x6f, 0x6f], true)
            == seq![0x66, 0x6f, 0x6f]) by (compute_only);
        assert(spec_normalized(seq![0x66, 0x6f, 0x6f], false)
            == seq![0x66, 0x6f, 0x6f]) by (compute_only);
    }
    let c2 = CowBytes::Owned(vec![0x66, 0x6f, 0x6f]);
    let got2 = normalize_path_rewrite(c2, true);
    assert(got2.view() == seq![0x66, 0x6f, 0x6f]);
    assert(got2.is_owned_mode());
    let c3 = CowBytes::Owned(vec![0x66, 0x6f, 0x6f]);
    let got3 = normalize_path_rewrite(c3, false);
    assert(got3.view() == seq![0x66, 0x6f, 0x6f]);
}

fn ut_normal2() {
    // normalize!(normal2, b"foo/bar", b"foo/bar") -- '/' is a
    // separator on every platform and already normalized
    let v: Vec<u8> = vec![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72];
    let c = CowBytes::Owned(v);
    let got = normalize_path(c);
    assert(got.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]);
    proof {
        assert(spec_normalized(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72], true)
            == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]) by (compute_only);
        assert(spec_normalized(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72], false)
            == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]) by (compute_only);
    }
    let c2 = CowBytes::Owned(vec![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]);
    let got2 = normalize_path_rewrite(c2, true);
    assert(got2.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]);
    let c3 = CowBytes::Owned(vec![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]);
    let got3 = normalize_path_rewrite(c3, false);
    assert(got3.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]);
}

fn ut_normal3() {
    // normalize!(normal3, b"foo\\bar", ...)
    //   unix arm:    b"foo\\bar"  (backslash is not a separator)
    //   windows arm: b"foo/bar"   (backslash rewritten)
    let unix_in = CowBytes::Owned(vec![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72]);
    let got_unix = normalize_path(unix_in);
    assert(got_unix.view() == seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72]);
    // windows oracle: backslash rewritten, mode goes Owned
    proof {
        assert(spec_normalized(seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72], true)
            == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]) by (compute_only);
        assert(spec_normalized(seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72], false)
            == seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72]) by (compute_only);
    }
    let win_in = CowBytes::Owned(vec![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72]);
    let got_win = normalize_path_rewrite(win_in, true);
    assert(got_win.view() == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]);
    assert(got_win.is_owned_mode());
    // unix oracle on the rewrite arm: identity (no rewrite byte)
    let ux_in = CowBytes::Owned(vec![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72]);
    let got_ux = normalize_path_rewrite(ux_in, false);
    assert(got_ux.view() == seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72]);
    assert(got_ux.is_owned_mode()); // Owned input without rewrite: kept
}

fn ut_normal4() {
    // normalize!(normal4, b"foo\\bar/baz", ...)
    //   unix arm:    b"foo\\bar/baz"
    //   windows arm: b"foo/bar/baz"
    let unix_in = CowBytes::Owned(vec![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a]);
    let got_unix = normalize_path(unix_in);
    assert(got_unix.view()
        == seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a]);
    proof {
        assert(spec_normalized(
            seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a],
            true,
        ) == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a]) by (compute_only);
        assert(spec_normalized(
            seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a],
            false,
        ) == seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a]) by (compute_only);
    }
    let win_in = CowBytes::Owned(vec![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a]);
    let got_win = normalize_path_rewrite(win_in, true);
    assert(got_win.view()
        == seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a]);
    let ux_in = CowBytes::Owned(vec![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a]);
    let got_ux = normalize_path_rewrite(ux_in, false);
    assert(got_ux.view()
        == seq![0x66, 0x6f, 0x6f, 0x5c, 0x62, 0x61, 0x72, 0x2f, 0x62, 0x61, 0x7a]);
}

// ===========================================================================
// GL1-added rows (contract coverage beyond upstream's fixtures; the
// borrowed-mode and dotdot-in-middle columns). Slice groundings are
// stated per index + ext_equal (whole-sequence array-view equations
// are a known solver hang shape on this host).
// ===========================================================================

fn ut_gl1_borrowed_name() {
    // Borrowed input keeps the Borrowed mode (the Cow discipline)
    let underlying: [u8; 7] = [0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72];
    let bs: &[u8] = &underlying;
    let c = CowBytes::Borrowed(bs);
    let got = file_name(&c);
    proof {
        assert(bs@.len() == 7);
        assert(bs@.index(0) == 0x66);
        assert(bs@.index(1) == 0x6f);
        assert(bs@.index(2) == 0x6f);
        assert(bs@.index(3) == 0x2f);
        assert(bs@.index(4) == 0x62);
        assert(bs@.index(5) == 0x61);
        assert(bs@.index(6) == 0x72);
        ext_equal(bs@, seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72]);
        assert(spec_final_component(seq![0x66, 0x6f, 0x6f, 0x2f, 0x62, 0x61, 0x72])
            == seq![0x62, 0x61, 0x72]) by (compute_only);
    }
    assert(got is Some);
    assert(got.get_Some_0().view() == seq![0x62, 0x61, 0x72]);
    assert(got.get_Some_0().is_borrowed_mode());
}

fn ut_gl1_borrowed_ext() {
    let underlying: [u8; 3] = [0x2e, 0x72, 0x73];
    let bs: &[u8] = &underlying;
    let c = CowBytes::Borrowed(bs);
    let got = file_name_ext(&c);
    proof {
        assert(bs@.len() == 3);
        assert(bs@.index(0) == 0x2e);
        assert(bs@.index(1) == 0x72);
        assert(bs@.index(2) == 0x73);
        ext_equal(bs@, seq![0x2e, 0x72, 0x73]);
        assert(rfind_pref(seq![0x2e, 0x72, 0x73], 0x2e, 3) == 0) by (compute_only);
        assert(spec_final_ext(seq![0x2e, 0x72, 0x73])
            == seq![0x2e, 0x72, 0x73]) by (compute_only);
    }
    assert(got is Some);
    assert(got.get_Some_0().view() == seq![0x2e, 0x72, 0x73]);
    assert(got.get_Some_0().is_borrowed_mode());
}

fn ut_gl1_dotdot_middle() {
    // "foo/../bar": final component is "bar" (only a TRAILING .. is
    // rejected; the doc's "path terminates in `..`" face)
    let v: Vec<u8> = vec![
        0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e, 0x2f, 0x62, 0x61, 0x72,
    ];
    let c = CowBytes::Owned(v);
    let got = file_name(&c);
    proof {
        assert(spec_final_component(
            seq![0x66, 0x6f, 0x6f, 0x2f, 0x2e, 0x2e, 0x2f, 0x62, 0x61, 0x72],
        ) == seq![0x62, 0x61, 0x72]) by (compute_only);
    }
    assert(got is Some);
    assert(got.get_Some_0().view() == seq![0x62, 0x61, 0x72]);
}

fn ut_gl1_dotdot_borrowed_trailing() {
    // borrowed "a/..": trailing dotdot rejects, mode face intact
    let underlying: [u8; 4] = [0x61, 0x2f, 0x2e, 0x2e];
    let bs: &[u8] = &underlying;
    let c = CowBytes::Borrowed(bs);
    let got = file_name(&c);
    proof {
        assert(bs@.len() == 4);
        assert(bs@.index(0) == 0x61);
        assert(bs@.index(1) == 0x2f);
        assert(bs@.index(2) == 0x2e);
        assert(bs@.index(3) == 0x2e);
        ext_equal(bs@, seq![0x61, 0x2f, 0x2e, 0x2e]);
        assert(spec_final_component(seq![0x61, 0x2f, 0x2e, 0x2e])
            == spec_dotdot()) by (compute_only);
    }
    assert(got matches None);
}

// ===========================================================================
// rfind_byte spot pins (the bstr face twin; ground rows).
// ===========================================================================

fn ut_gl1_rfind() {
    let hay: [u8; 5] = [0x61, 0x2f, 0x62, 0x2f, 0x63];
    let r1 = rfind_byte(&hay, 0x2f);
    let r2 = rfind_byte(&hay, 0x61);
    let r3 = rfind_byte(&hay, 0x7a);
    let empty: [u8; 0] = [];
    let r4 = rfind_byte(&empty, 0x2f);
    proof {
        let hsv: Seq<u8> = seq![0x61, 0x2f, 0x62, 0x2f, 0x63];
        assert((&hay)@.len() == 5);
        assert((&hay)@.index(0) == 0x61);
        assert((&hay)@.index(1) == 0x2f);
        assert((&hay)@.index(2) == 0x62);
        assert((&hay)@.index(3) == 0x2f);
        assert((&hay)@.index(4) == 0x63);
        ext_equal((&hay)@, hsv);
        assert(hsv.index(4) == 0x63);
        assert(hsv.index(3) == 0x2f);
        assert(rfind_pref(hsv, 0x2f, 5) == 3);
        assert(hsv.index(1) == 0x2f);
        assert(hsv.index(2) == 0x62);
        assert(hsv.index(0) == 0x61);
        assert(rfind_pref(hsv, 0x61, 5) == 0);
        assert(hsv.index(4) == 0x63);
        assert(hsv.index(3) == 0x2f);
        assert(hsv.index(2) == 0x62);
        assert(hsv.index(1) == 0x2f);
        assert(hsv.index(0) == 0x61);
        assert(rfind_pref(hsv, 0x7a, 5) == -1);
    }
    assert(r1 is Some && r1.get_Some_0() == 3); // rightmost, not 1
    assert(r2 is Some && r2.get_Some_0() == 0);
    assert(r3 matches None);
    assert(r4 matches None);
}

} // verus!

fn main() {}
