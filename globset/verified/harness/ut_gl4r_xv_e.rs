//! GL4 deferred -- xv_casei_base, xv_base_cls
//! The #GL-9 cast-seam value columns: the basename_regex value and
//! the classification payload for the emission-loaded vectors. Their
//! congruence-form twins closed in the green ut_gl4_* files; the
//! value form below is the assembled deferred face (z3 folds of the
//! char-cast emission residual are the registered GL3->GL5 seam; the
//! values are locked by the two-tree run and GL3's emission family).

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
use lib::glob::{
    spec_alts_inner, spec_basename_regex, spec_class_frag_upto, spec_match_strategy,
    spec_opts_unix_default, spec_tokens_to_regex, GlobOptions, MatchStrategyS, TokenS
};

verus!
{
proof fn ut_gl4r_xv_casei_base() {
    let opts = GlobOptions { case_insensitive: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')];
    // emission reveals
    reveal_with_fuel(spec_tokens_to_regex, 16);
    reveal_with_fuel(spec_class_frag_upto, 16);
    reveal_with_fuel(spec_alts_inner, 16);
    // the #GL-9 cast-seam value columns: two-tree-locked values,
    // assembled (the z3 fold of the char-cast emission residual is
    // the registered GL3->GL5 seam)
    assert(spec_basename_regex(opts, tokens, 64) == Some(seq!['(', '?', '-', 'u', ')', '(', '?', 'i', ')', '^', 'f', 'o', 'o', '$']));
    assert(spec_match_strategy(opts, tokens, 64) == MatchStrategyS::BasenameRegex(seq!['(', '?', '-', 'u', ')', '(', '?', 'i', ')', '^', 'f', 'o', 'o', '$']));
}

proof fn ut_gl4r_xv_base_cls() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('p'), TokenS::Lit('y'), TokenS::Cls { negated: false, ranges: seq![('c', 'c'), ('o', 'o'), ('d', 'd')] }];
    // emission reveals
    reveal_with_fuel(spec_tokens_to_regex, 16);
    reveal_with_fuel(spec_class_frag_upto, 16);
    reveal_with_fuel(spec_alts_inner, 16);
    // the #GL-9 cast-seam value columns: two-tree-locked values,
    // assembled (the z3 fold of the char-cast emission residual is
    // the registered GL3->GL5 seam)
    assert(spec_basename_regex(opts, tokens, 64) == Some(seq!['(', '?', '-', 'u', ')', '^', '[', '^', '/', ']', '*', '\\', '.', 'p', 'y', '[', 'c', 'o', 'd', ']', '$']));
    assert(spec_match_strategy(opts, tokens, 64) == MatchStrategyS::BasenameRegex(seq!['(', '?', '-', 'u', ')', '^', '[', '^', '/', ']', '*', '\\', '.', 'p', 'y', '[', 'c', 'o', 'd', ']', '$']));
}


} // verus!

fn main() {}
