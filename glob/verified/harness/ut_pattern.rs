//! glob **harness zone** -- the UT assertion theorems (the A2/A3/A1/A4
//! error-position exemplars, the B3/B5/B6/B7/B8 matching-property exemplars,
//! the C1 escape assertions).
//! The two-zone split (out of verified/src/lib.rs PART VII): UT assertion
//! theorems and property exemplars belong to the harness zone (src keeps
//! only the F1-family theorems).
//!
//! Reference-style structure: `#[path = "../src/lib.rs"] mod globlib;` -- it
//! directly references the already-verified spec-track models of the src side
//! (the error-position semantics compile_err/star_run/compile_err_scan/
//! pos_close_abs, the matching leaves in_model/parse_model/chars_eq_model,
//! the deterministic subset m_det/matches_with_model, escape_model, and the
//! tok/TOK_*_I/M_* constants); **the fact source is never duplicated** (the
//! referenced names resolve via `use globlib::*`; the upstream line-number
//! comments are kept). A property theorem that is at the same time a forall
//! theorem of the library specs is assigned to this harness file by its
//! primary use (the obligation-ized UT exemplars); each block comment states
//! its source UT.
//!
//! Running: VERUS_Z3_PATH=<z3> <verus>
//! database/glob/verified/harness/ut_pattern.rs
//! Reading: aside from the F1 expected error carried in by the integral
//! re-verification of the globlib module (the unwrap anchor of upstream
//! lib.rs:964, now at src/lib.rs:141 -- the same obligation at the same site
//! as in a standalone src run),
//! everything else is verified (the UT assertions are the same obligation
//! group as in the pre-split aggregate file).

use vstd::prelude::*;
use vstd::seq::*;

#[path = "../src/lib.rs"]
mod globlib;

use globlib::*;

verus! {


/// A2: test_wildcard_errors (lib.rs:1122-1129) -- five groups of
/// error-position assertions.
proof fn check_wildcard_error_positions() {
    reveal_with_fuel(compile_err, 9);
    reveal_with_fuel(star_run, 6);
    // assert!(Pattern::new("a/**b").unwrap_err().pos == 4);
    let s1: Seq<char> = seq!['a', '/', '*', '*', 'b'];
    assert(s1.len() == 5 && s1[1] == '/' && s1[2] == '*' && s1[3] == '*' && s1[4] == 'b');
    assert(star_run(s1, 2) == 2);
    assert(compile_err(s1, 0) == compile_err(s1, 1));
    assert(compile_err(s1, 1) == compile_err(s1, 2));
    assert(compile_err(s1, 2) == Some(4)); // **b: ends in a non-separator => pos 4
    assert(compile_err(s1, 0) == Some(4));

    // assert!(Pattern::new("a/bc**").unwrap_err().pos == 3);
    let s2: Seq<char> = seq!['a', '/', 'b', 'c', '*', '*'];
    assert(s2.len() == 6 && s2[3] == 'c' && s2[4] == '*' && s2[5] == '*');
    assert(star_run(s2, 4) == 2);
    assert(compile_err(s2, 0) == compile_err(s2, 4));
    assert(compile_err(s2, 4) == Some(3)); // bc**: the preceding char is not a separator => pos 3
    assert(compile_err(s2, 0) == Some(3));

    // assert!(Pattern::new("a/*****").unwrap_err().pos == 4);
    let s3: Seq<char> = seq!['a', '/', '*', '*', '*', '*', '*'];
    assert(s3.len() == 7 && s3[2] == '*' && s3[3] == '*' && s3[4] == '*');
    assert(star_run(s3, 2) == 5);
    assert(compile_err(s3, 0) == compile_err(s3, 2));
    assert(compile_err(s3, 2) == Some(4)); // five consecutive `*`s => ERROR_WILDCARDS, pos = old+2
    assert(compile_err(s3, 0) == Some(4));

    // assert!(Pattern::new("a/b**c**d").unwrap_err().pos == 2);
    let s4: Seq<char> = seq!['a', '/', 'b', '*', '*', 'c', '*', '*', 'd'];
    assert(s4.len() == 9 && s4[2] == 'b' && s4[3] == '*' && s4[4] == '*');
    assert(star_run(s4, 3) == 2);
    assert(compile_err(s4, 0) == compile_err(s4, 3));
    assert(compile_err(s4, 3) == Some(2)); // b**: the preceding char is not a separator => pos 2
    assert(compile_err(s4, 0) == Some(2));

    // assert!(Pattern::new("a**b").unwrap_err().pos == 0);
    let s5: Seq<char> = seq!['a', '*', '*', 'b'];
    assert(s5.len() == 4 && s5[0] == 'a' && s5[1] == '*' && s5[2] == '*' && s5[3] == 'b');
    assert(star_run(s5, 1) == 2);
    assert(compile_err(s5, 0) == compile_err(s5, 1));
    assert(compile_err(s5, 1) == Some(0)); // a**: the preceding char is not a separator => pos 0
    assert(compile_err(s5, 0) == Some(0));
}

/// A3: test_unclosed_bracket_errors (lib.rs:1131-1141) -- all eight groups
/// report ERROR_INVALID_RANGE at the `[` (pos == 3).
proof fn check_unclosed_bracket_error_positions() {
    reveal_with_fuel(compile_err, 8);
    // assert!(Pattern::new("abc[def").unwrap_err().pos == 3);
    let t1: Seq<char> = seq!['a', 'b', 'c', '[', 'd', 'e', 'f'];
    assert(t1.len() == 7 && t1[4] == 'd' && t1[5] == 'e' && t1[6] == 'f');
    assert(compile_err_scan(t1, 3, 7) == Some(3)); // no ']' => Some(i)
    assert(compile_err_scan(t1, 3, 6) == compile_err_scan(t1, 3, 7));
    assert(compile_err_scan(t1, 3, 5) == compile_err_scan(t1, 3, 6));
    assert(compile_err(t1, 3) == compile_err_scan(t1, 3, 6));
    assert(compile_err(t1, 0) == compile_err(t1, 3));
    assert(compile_err(t1, 0) == Some(3));

    // assert!(Pattern::new("abc[!def").unwrap_err().pos == 3);
    let t2: Seq<char> = seq!['a', 'b', 'c', '[', '!', 'd', 'e', 'f'];
    assert(t2.len() == 8 && t2[4] == '!' && t2[7] == 'f');
    assert(compile_err_scan(t2, 3, 8) == Some(3));
    assert(compile_err_scan(t2, 3, 7) == compile_err_scan(t2, 3, 8));
    assert(compile_err(t2, 3) == compile_err_scan(t2, 3, 6));
    assert(compile_err(t2, 0) == compile_err(t2, 3));
    assert(compile_err(t2, 0) == Some(3));

    // assert!(Pattern::new("abc[").unwrap_err().pos == 3);
    let t3: Seq<char> = seq!['a', 'b', 'c', '['];
    assert(t3.len() == 4);
    assert(compile_err(t3, 0) == Some(3)); // i+4/i+3 both out of bounds

    // assert!(Pattern::new("abc[!").unwrap_err().pos == 3);
    let t4: Seq<char> = seq!['a', 'b', 'c', '[', '!'];
    assert(t4.len() == 5 && t4[4] == '!');
    assert(compile_err(t4, 0) == Some(3)); // i+4 > len and i+3 > len

    // assert!(Pattern::new("abc[d").unwrap_err().pos == 3);
    let t5: Seq<char> = seq!['a', 'b', 'c', '[', 'd'];
    assert(t5.len() == 5 && t5[4] == 'd');
    assert(compile_err_scan(t5, 3, 5) == Some(3)); // no ']' => Some(3)
    assert(compile_err(t5, 3) == compile_err_scan(t5, 3, 5));
    assert(compile_err(t5, 0) == compile_err(t5, 3));
    assert(compile_err(t5, 0) == Some(3));

    // assert!(Pattern::new("abc[!d").unwrap_err().pos == 3);
    let t6: Seq<char> = seq!['a', 'b', 'c', '[', '!', 'd'];
    assert(t6.len() == 6 && t6[4] == '!' && t6[5] == 'd');
    assert(compile_err_scan(t6, 3, 6) == Some(3));
    assert(compile_err(t6, 3) == compile_err_scan(t6, 3, 6));
    assert(compile_err(t6, 0) == compile_err(t6, 3));
    assert(compile_err(t6, 0) == Some(3));

    // assert!(Pattern::new("abc[]").unwrap_err().pos == 3);
    let t7: Seq<char> = seq!['a', 'b', 'c', '[', ']'];
    assert(t7.len() == 5 && t7[4] == ']');
    // i+4 = 7 > len => the first branch is not taken; the second branch requires chars[i+1] != ']',
    // chars[4] == ']' => not taken either => Err(3)
    assert(compile_err(t7, 3) == Some(3));
    assert(compile_err(t7, 0) == compile_err(t7, 3));
    assert(compile_err(t7, 0) == Some(3));

    // assert!(Pattern::new("abc[!]").unwrap_err().pos == 3);
    let t8: Seq<char> = seq!['a', 'b', 'c', '[', '!', ']'];
    assert(t8.len() == 6 && t8[4] == '!' && t8[5] == ']');
    // i+4 = 7 > len => the first branch is not taken; the second branch requires chars[i+1] != '!',
    // chars[4] == '!' => neither taken => Err(3)
    assert(compile_err(t8, 3) == Some(3));
    assert(compile_err(t8, 0) == compile_err(t8, 3));
    assert(compile_err(t8, 0) == Some(3));
}

/// A1: the compile half of test_pattern_from_str (lib.rs:1117-1120) --
/// `"a*b".parse::<Pattern>().unwrap()` succeeds (compile_err == None),
/// `"a/**b".parse::<Pattern>().unwrap_err().pos == 4` (FromStr delegates to new).
proof fn check_from_str_compile() {
    reveal_with_fuel(compile_err, 6);
    reveal_with_fuel(star_run, 4);
    let ok_pat: Seq<char> = seq!['a', '*', 'b'];
    assert(ok_pat.len() == 3 && ok_pat[1] == '*');
    assert(star_run(ok_pat, 1) == 1);
    assert(compile_err(ok_pat, 0) == compile_err(ok_pat, 1));
    assert(compile_err(ok_pat, 1) == compile_err(ok_pat, 2));
    assert(compile_err(ok_pat, 2) == None);
    assert(compile_err(ok_pat, 0) == None); // the parse().unwrap() obligation is satisfiable

    let bad_pat: Seq<char> = seq!['a', '/', '*', '*', 'b'];
    assert(star_run(bad_pat, 2) == 2);
    // FromStr (lib.rs:572-578) delegates to new: the error positions agree
    assert(compile_err(bad_pat, 0) == Some(4));
}

/// A4: test_glob_errors (lib.rs:1143-1147) -- the error positions of glob
/// fully agree with Pattern::new (the precheck forwards `Pattern::new(pattern)?` verbatim).
proof fn check_glob_error_positions() {
    reveal_with_fuel(compile_err, 8);
    reveal_with_fuel(star_run, 6);
    assert(glob_pattern_err(seq!['a', '/', '*', '*', 'b']) == Some(4));
    assert(compile_err(seq!['a', '/', '*', '*', 'b'], 0)
        == glob_pattern_err(seq!['a', '/', '*', '*', 'b']));
    assert(glob_pattern_err(seq!['a', 'b', 'c', '[', 'd', 'e', 'f']) == Some(3));
    assert(compile_err(seq!['a', 'b', 'c', '[', 'd', 'e', 'f'], 0)
        == glob_pattern_err(seq!['a', 'b', 'c', '[', 'd', 'e', 'f']));
}

/// The B3/B5/B6 subset: the matching-leaf obligations of the
/// test_range_pattern / case-insensitive series (lib.rs:1279-1327, 1354-1392).
proof fn check_range_pattern_leaf_semantics() {
    reveal_with_fuel(parse_model, 6);
    reveal_with_fuel(in_model, 6);
    // ---- [0-9]: CharRange ----
    let d09: Seq<char> = seq!['0', '-', '9'];
    assert(d09.len() == 3 && d09[1] == '-');
    let specs09 = parse_model(d09, 0);
    assert(specs09.len() == 1);
    assert(specs09[0] == (true, '0', '9'));
    // for i in 0..10: pat.matches(&format!("a{i}b")) -- at the leaf level:
    assert(in_model(specs09, '5', true));   // '5' is in [0-9]
    assert(in_model(specs09, '9', true));
    assert(!in_model(specs09, 'a', true));  // !matches("a_b") (lib.rs:1285)

    // ---- [a-z] case-insensitive (lib.rs:1293-1309) ----
    let az: Seq<char> = seq!['a', '-', 'z'];
    let specs_az = parse_model(az, 0);
    assert(specs_az.len() == 1 && specs_az[0] == (true, 'a', 'z'));
    assert(in_model(specs_az, 'q', true));
    // case_sensitive: false => 'A'-'Z' all fall into [a-z] (lib.rs:1299-1305)
    assert(in_model(specs_az, 'A', false));
    assert(in_model(specs_az, 'Z', false));
    assert(!in_model(specs_az, '1', false)); // '1' not in [a-z] (insensitive reading included)

    // ---- [abc-]: the trailing '-' literalized (lib.rs:1311-1319) ----
    let abc_dash: Seq<char> = seq!['a', 'b', 'c', '-'];
    let specs_abcd = parse_model(abc_dash, 0);
    assert(specs_abcd.len() == 4);
    assert(specs_abcd[0] == (false, 'a', 'a'));
    assert(specs_abcd[1] == (false, 'b', 'b'));
    assert(specs_abcd[2] == (false, 'c', 'c'));
    assert(specs_abcd[3] == (false, '-', '-'));
    assert(in_model(specs_abcd, '-', true));  // pat.matches("-")
    assert(in_model(specs_abcd, 'b', true));
    assert(!in_model(specs_abcd, 'd', true)); // !pat.matches("d")

    // ---- [2-1]: the empty range matches nothing (lib.rs:1321-1323) ----
    let empty_r: Seq<char> = seq!['2', '-', '1'];
    let specs_21 = parse_model(empty_r, 0);
    assert(specs_21.len() == 1 && specs_21[0] == (true, '2', '1'));
    assert(!in_model(specs_21, '1', true));  // !matches("1")
    assert(!in_model(specs_21, '2', true));  // !matches("2")

    // ---- [-] and [!-] (lib.rs:1325-1326) ----
    let dash: Seq<char> = seq!['-'];
    let specs_dash = parse_model(dash, 0);
    assert(specs_dash.len() == 1 && specs_dash[0] == (false, '-', '-'));
    assert(in_model(specs_dash, '-', true));   // [-] matches '-'
    // [!-] => !in_model: lib.rs:1326 !matches("-")
    assert(!!in_model(specs_dash, '-', true));

    // ---- B6: the [a]/[!a] case-sensitivity switch (lib.rs:1370-1392) ----
    let single_a: Seq<char> = seq!['a'];
    let specs_a = parse_model(single_a, 0);
    assert(specs_a.len() == 1 && specs_a[0] == (false, 'a', 'a'));
    assert(in_model(specs_a, 'a', false));  // insensitive: matches `a`
    assert(in_model(specs_a, 'A', false));  // insensitive: matches `A`
    assert(!in_model(specs_a, 'A', true));  // sensitive: does not match `A` (lib.rs:1387)
    // [!a] => negation (the AnyExcept token layer; see the m_det theorems)
}

/// The B7/doc subset: the matches_with obligations on deterministic token sequences.
proof fn check_matches_with_det_subset() {
    reveal_with_fuel(m_det, 12);
    reveal_with_fuel(in_model, 4);
    // assert!(Pattern::new("c?t").unwrap().matches("cat")); (lib.rs:766 doc)
    let toks_cqt: Seq<(int, char, Seq<(bool, char, char)>)> = seq![
        tok(TOK_CHAR_I, 'c'),
        tok(TOK_ANY_CHAR_I, '?'),
        tok(TOK_CHAR_I, 't'),
    ];
    let cat: Seq<char> = seq!['c', 'a', 't'];
    assert(cat.len() == 3 && cat[0] == 'c' && cat[1] == 'a' && cat[2] == 't');
    assert(matches_with_model(toks_cqt, cat, true, false, false));

    // assert!(Pattern::new("k[!e]tteh").unwrap().matches("kitteh")); (lib.rs:767 doc)
    let specs_e: Seq<(bool, char, char)> = seq![(false, 'e', 'e')];
    let toks_kitteh: Seq<(int, char, Seq<(bool, char, char)>)> = seq![
        tok(TOK_CHAR_I, 'k'),
        tok_set(TOK_ANY_EXCEPT_I, specs_e),
        tok(TOK_CHAR_I, 't'),
        tok(TOK_CHAR_I, 't'),
        tok(TOK_CHAR_I, 'e'),
        tok(TOK_CHAR_I, 'h'),
    ];
    let kitteh: Seq<char> = seq!['k', 'i', 't', 't', 'e', 'h'];
    assert(kitteh.len() == 6 && kitteh[1] == 'i');
    assert(matches_with_model(toks_kitteh, kitteh, true, false, false));

    // assert!(!Pattern::new("abc?def").unwrap().matches_with("abc/def",
    //        options_require_literal)); (lib.rs:1410-1412)
    let toks_abcqdef: Seq<(int, char, Seq<(bool, char, char)>)> = seq![
        tok(TOK_CHAR_I, 'a'),
        tok(TOK_CHAR_I, 'b'),
        tok(TOK_CHAR_I, 'c'),
        tok(TOK_ANY_CHAR_I, '?'),
        tok(TOK_CHAR_I, 'd'),
        tok(TOK_CHAR_I, 'e'),
        tok(TOK_CHAR_I, 'f'),
    ];
    let abcdef: Seq<char> = seq!['a', 'b', 'c', '/', 'd', 'e', 'f'];
    assert(abcdef.len() == 7 && abcdef[3] == '/');
    assert(!matches_with_model(toks_abcqdef, abcdef, true, true, false));
    // assert!(...matches_with("abc/def", options_not_require_literal))
    // (lib.rs:1423-1425): require_literal_separator == false => it matches
    assert(matches_with_model(toks_abcqdef, abcdef, true, false, false));

    // The B8 subset: assert!(!Pattern::new("aaa/?bbb")....matches_with(
    //        "aaa/.bbb", options_require_literal_leading_dot))
    // (lib.rs:1487-1493)
    let toks_qdot: Seq<(int, char, Seq<(bool, char, char)>)> = seq![
        tok(TOK_CHAR_I, 'a'),
        tok(TOK_CHAR_I, 'a'),
        tok(TOK_CHAR_I, 'a'),
        tok(TOK_CHAR_I, '/'),
        tok(TOK_ANY_CHAR_I, '?'),
        tok(TOK_CHAR_I, 'b'),
        tok(TOK_CHAR_I, 'b'),
        tok(TOK_CHAR_I, 'b'),
    ];
    let dotfile: Seq<char> = seq!['a', 'a', 'a', '/', '.', 'b', 'b', 'b'];
    assert(dotfile.len() == 8 && dotfile[3] == '/' && dotfile[4] == '.');
    assert(!matches_with_model(toks_qdot, dotfile, true, false, true));
    // (lib.rs:1492): under the insensitive reading, `?` matches '.'
    assert(matches_with_model(toks_qdot, dotfile, true, false, false));

    // B5: case-insensitive (lib.rs:1354-1367): all aBcDeFg variants
    let toks_case: Seq<(int, char, Seq<(bool, char, char)>)> = seq![
        tok(TOK_CHAR_I, 'a'),
        tok(TOK_CHAR_I, 'B'),
        tok(TOK_CHAR_I, 'c'),
    ];
    let abc: Seq<char> = seq!['a', 'b', 'c'];
    let ABC: Seq<char> = seq!['A', 'B', 'C'];
    assert(abc.len() == 3 && abc[0] == 'a' && abc[1] == 'b' && abc[2] == 'c');
    assert(ABC.len() == 3 && ABC[0] == 'A' && ABC[2] == 'C');
    assert(matches_with_model(toks_case, abc, false, false, false)); // "abcdefg"
    assert(matches_with_model(toks_case, ABC, false, false, false)); // "ABCDEFG"
    // Case-sensitive reading: the two literals do not match
    assert(!matches_with_model(toks_case, abc, true, false, false));
}

/// C1: test_pattern_escape (lib.rs:1347-1352) --
/// (1) the expected escape output (lib.rs:1350);
/// (2) the escape product compiles (the compile half of the roundtrip; the
///     full roundtrip proof is not carried out here).
proof fn check_pattern_escape() {
    reveal_with_fuel(escape_model, 12);
    reveal_with_fuel(compile_err, 16);
    reveal_with_fuel(compile_err_scan, 12);
    reveal_with_fuel(pos_close_abs, 8);
    // let s = "_[_]_?_*_!_";
    let s: Seq<char> = seq!['_', '[', '_', ']', '_', '?', '_', '*', '_', '!', '_'];
    assert(s.len() == 11);
    // assert_eq!(Pattern::escape(s), "_[[]_[]]_[?]_[*]_!_".to_string());
    let expect: Seq<char> = seq![
        '_', '[', '[', ']', '_', '[', ']', ']', '_', '[', '?', ']', '_', '[',
        '*', ']', '_', '!', '_',
    ];
    assert(escape_model(s, 0) == expect);
    // assert!(Pattern::new(&Pattern::escape(s)).unwrap().matches(s));
    // -- the compile half: the escape product contains no unclosed brackets /
    //    illegal stars => compile_ok
    assert(compile_err(expect, 0) == None);
}

}

fn main() {}
