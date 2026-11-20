//! GL1 harness -- the `escape` test body (lib.rs:1317-1327, 7 rows) and
//! the escape doc examples (lib.rs:1126-1131, 6 rows), re-erected as
//! assertion theorems over the verified src tree. Inputs ride the
//! chars base mapping (&[char], see src/lib.rs); expected values are
//! the upstream strings verbatim.
//!
//! Grounding shape (the siphasher ut_vectors precedent): per row, the
//! spec chain is folded on the ground char sequence by the compute
//! engine inside a proof block, then the exec call's postcondition
//! bridges to the concrete expected value. Slice groundings are stated
//! per index + ext_equal (whole-sequence array-view equations are a
//! known solver hang shape on this host).

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod lib;
#[allow(unused_imports)]
use lib::pathutil;

use lib::{escape, spec_escape};
use lib::CowBytes; // root-binding mount fix (pathutil's crate:: ref)

verus! {

/// fz = "foo" (the upstream escape-test first row: escape("foo") == "foo")
fn ut_doc_plain() {
    let cs: &[char] = &['f', 'o', 'o'];
    let got = escape(cs);
    proof {
        assert(cs@.len() == 3);
        assert(cs@.index(0) == 'f');
        assert(cs@.index(1) == 'o');
        assert(cs@.index(2) == 'o');
        ext_equal(cs@, seq!['f', 'o', 'o']);
        assert(spec_escape(seq!['f', 'o', 'o']) == seq!['f', 'o', 'o']) by (compute_only);
    }
    assert(got@ == seq!['f', 'o', 'o']);
    // the upstream row: assert_eq!("foo", escape("foo"));
}

/// Doc examples (lib.rs:1126-1131), first: escape("foo*bar") == "foo[*]bar"
fn ut_doc_star_mid() {
    let cs: &[char] = &['f', 'o', 'o', '*', 'b', 'a', 'r'];
    let got = escape(cs);
    proof {
        assert(cs@.len() == 7);
        assert(cs@.index(0) == 'f');
        assert(cs@.index(1) == 'o');
        assert(cs@.index(2) == 'o');
        assert(cs@.index(3) == '*');
        assert(cs@.index(4) == 'b');
        assert(cs@.index(5) == 'a');
        assert(cs@.index(6) == 'r');
        ext_equal(cs@, seq!['f', 'o', 'o', '*', 'b', 'a', 'r']);
        assert(spec_escape(seq!['f', 'o', 'o', '*', 'b', 'a', 'r'])
            == seq!['f', 'o', 'o', '[', '*', ']', 'b', 'a', 'r']) by (compute_only);
    }
    assert(got@ == seq!['f', 'o', 'o', '[', '*', ']', 'b', 'a', 'r']);
}

/// escape("foo?bar") == "foo[?]bar"
fn ut_doc_question() {
    let cs: &[char] = &['f', 'o', 'o', '?', 'b', 'a', 'r'];
    let got = escape(cs);
    proof {
        assert(cs@.len() == 7);
        assert(cs@.index(3) == '?');
        ext_equal(cs@, seq!['f', 'o', 'o', '?', 'b', 'a', 'r']);
        assert(spec_escape(seq!['f', 'o', 'o', '?', 'b', 'a', 'r'])
            == seq!['f', 'o', 'o', '[', '?', ']', 'b', 'a', 'r']) by (compute_only);
    }
    assert(got@ == seq!['f', 'o', 'o', '[', '?', ']', 'b', 'a', 'r']);
}

/// escape("foo[bar") == "foo[[]bar"
fn ut_doc_openbracket() {
    let cs: &[char] = &['f', 'o', 'o', '[', 'b', 'a', 'r'];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq!['f', 'o', 'o', '[', 'b', 'a', 'r']);
        assert(spec_escape(seq!['f', 'o', 'o', '[', 'b', 'a', 'r'])
            == seq!['f', 'o', 'o', '[', '[', ']', 'b', 'a', 'r']) by (compute_only);
    }
    assert(got@ == seq!['f', 'o', 'o', '[', '[', ']', 'b', 'a', 'r']);
}

/// escape("foo]bar") == "foo[]]bar"
fn ut_doc_closebracket() {
    let cs: &[char] = &['f', 'o', 'o', ']', 'b', 'a', 'r'];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq!['f', 'o', 'o', ']', 'b', 'a', 'r']);
        assert(spec_escape(seq!['f', 'o', 'o', ']', 'b', 'a', 'r'])
            == seq!['f', 'o', 'o', '[', ']', ']', 'b', 'a', 'r']) by (compute_only);
    }
    assert(got@ == seq!['f', 'o', 'o', '[', ']', ']', 'b', 'a', 'r']);
}

/// escape("foo{bar") == "foo[{]bar"
fn ut_doc_openbrace() {
    let cs: &[char] = &['f', 'o', 'o', '{', 'b', 'a', 'r'];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq!['f', 'o', 'o', '{', 'b', 'a', 'r']);
        assert(spec_escape(seq!['f', 'o', 'o', '{', 'b', 'a', 'r'])
            == seq!['f', 'o', 'o', '[', '{', ']', 'b', 'a', 'r']) by (compute_only);
    }
    assert(got@ == seq!['f', 'o', 'o', '[', '{', ']', 'b', 'a', 'r']);
}

/// escape("foo}bar") == "foo[}]bar"
fn ut_doc_closebrace() {
    let cs: &[char] = &['f', 'o', 'o', '}', 'b', 'a', 'r'];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq!['f', 'o', 'o', '}', 'b', 'a', 'r']);
        assert(spec_escape(seq!['f', 'o', 'o', '}', 'b', 'a', 'r'])
            == seq!['f', 'o', 'o', '[', '}', ']', 'b', 'a', 'r']) by (compute_only);
    }
    assert(got@ == seq!['f', 'o', 'o', '[', '}', ']', 'b', 'a', 'r']);
}

// ===========================================================================
// test-body rows (lib.rs:1318-1327).
// ===========================================================================

/// assert_eq!("foo[*]", escape("foo*"));
fn ut_body_star_suffix() {
    let cs: &[char] = &['f', 'o', 'o', '*'];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq!['f', 'o', 'o', '*']);
        assert(spec_escape(seq!['f', 'o', 'o', '*'])
            == seq!['f', 'o', 'o', '[', '*', ']']) by (compute_only);
    }
    assert(got@ == seq!['f', 'o', 'o', '[', '*', ']']);
}

/// assert_eq!("[[][]]", escape("[]"));
fn ut_body_brackets_only() {
    let cs: &[char] = &['[', ']'];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq!['[', ']']);
        assert(spec_escape(seq!['[', ']'])
            == seq!['[', '[', ']', '[', ']', ']']) by (compute_only);
    }
    assert(got@ == seq!['[', '[', ']', '[', ']', ']']);
}

/// assert_eq!("[*][?]", escape("*?"));
fn ut_body_star_question() {
    let cs: &[char] = &['*', '?'];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq!['*', '?']);
        assert(spec_escape(seq!['*', '?'])
            == seq!['[', '*', ']', '[', '?', ']']) by (compute_only);
    }
    assert(got@ == seq!['[', '*', ']', '[', '?', ']']);
}

/// assert_eq!("src/[*][*]/[*].rs", escape("src/**/*.rs"));
fn ut_body_source_row() {
    let cs: &[char] = &[
        's', 'r', 'c', '/', '*', '*', '/', '*', '.', 'r', 's',
    ];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq![
            's', 'r', 'c', '/', '*', '*', '/', '*', '.', 'r', 's'
        ]);
        assert(spec_escape(seq![
                's', 'r', 'c', '/', '*', '*', '/', '*', '.', 'r', 's'
            ])
            == seq![
                's', 'r', 'c', '/', '[', '*', ']', '[', '*', ']', '/', '[', '*', ']',
                '.', 'r', 's',
            ]) by (compute_only);
    }
    assert(got@
        == seq![
            's', 'r', 'c', '/', '[', '*', ']', '[', '*', ']', '/', '[', '*', ']',
            '.', 'r', 's',
        ]);
}

/// assert_eq!("bar[[]ab[]]baz", escape("bar[ab]baz"));
fn ut_body_class_mid() {
    let cs: &[char] = &[
        'b', 'a', 'r', '[', 'a', 'b', ']', 'b', 'a', 'z',
    ];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq![
            'b', 'a', 'r', '[', 'a', 'b', ']', 'b', 'a', 'z'
        ]);
        assert(spec_escape(seq![
                'b', 'a', 'r', '[', 'a', 'b', ']', 'b', 'a', 'z'
            ])
            == seq![
                'b', 'a', 'r', '[', '[', ']', 'a', 'b', '[', ']', ']', 'b', 'a', 'z',
            ]) by (compute_only);
    }
    assert(got@
        == seq![
            'b', 'a', 'r', '[', '[', ']', 'a', 'b', '[', ']', ']', 'b', 'a', 'z',
        ]);
}

/// assert_eq!("bar[[]!![]]!baz", escape("bar[!!]!baz")); -- the `!`
/// needs-no-escape note of the upstream match arm (lib.rs:1137-1139)
fn ut_body_bang_class() {
    let cs: &[char] = &[
        'b', 'a', 'r', '[', '!', '!', ']', '!', 'b', 'a', 'z',
    ];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq![
            'b', 'a', 'r', '[', '!', '!', ']', '!', 'b', 'a', 'z'
        ]);
        assert(spec_escape(seq![
                'b', 'a', 'r', '[', '!', '!', ']', '!', 'b', 'a', 'z'
            ])
            == seq![
                'b', 'a', 'r', '[', '[', ']', '!', '!', '[', ']', ']', '!', 'b', 'a', 'z',
            ]) by (compute_only);
    }
    assert(got@
        == seq![
            'b', 'a', 'r', '[', '[', ']', '!', '!', '[', ']', ']', '!', 'b', 'a', 'z',
        ]);
}

// ===========================================================================
// GL1-added derived row (not upstream-pinned): a non-ASCII char passes
// through untouched (the chars base is arbitrary scalar values; only
// the six metas wrap).
// ===========================================================================

fn ut_gl1_nonascii_passthrough() {
    // "a\u{2603}b" -- the snowman as the non-ASCII pass-through witness
    let cs: &[char] = &['a', '\u{2603}', 'b'];
    let got = escape(cs);
    proof {
        ext_equal(cs@, seq!['a', '\u{2603}', 'b']);
        assert(spec_escape(seq!['a', '\u{2603}', 'b'])
            == seq!['a', '\u{2603}', 'b']) by (compute_only);
    }
    assert(got@ == seq!['a', '\u{2603}', 'b']);
}

} // verus!

fn main() {}
