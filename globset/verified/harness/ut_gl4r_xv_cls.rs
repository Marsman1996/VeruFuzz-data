//! GL4 deferred -- xv_cls_a_z, xv_cls_neg_dot0
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
proof fn ut_gl4r_xv_cls_a_z() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Cls { negated: false, ranges: seq![('a', 'z')] }];
    // emission reveals
    reveal_with_fuel(spec_tokens_to_regex, 16);
    reveal_with_fuel(spec_class_frag_upto, 16);
    reveal_with_fuel(spec_alts_inner, 16);
    // the #GL-9 cast-seam value columns: two-tree-locked values,
    // assembled (the z3 fold of the char-cast emission residual is
    // the registered GL3->GL5 seam)
    assert(spec_basename_regex(opts, tokens, 64) == Some(seq!['(', '?', '-', 'u', ')', '^', '[', 'a', '-', 'z', ']', '$']));
    assert(spec_match_strategy(opts, tokens, 64) == MatchStrategyS::BasenameRegex(seq!['(', '?', '-', 'u', ')', '^', '[', 'a', '-', 'z', ']', '$']));
}

proof fn ut_gl4r_xv_cls_neg_dot0() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Cls { negated: true, ranges: seq![('.', '0')] }];
    // emission reveals
    reveal_with_fuel(spec_tokens_to_regex, 16);
    reveal_with_fuel(spec_class_frag_upto, 16);
    reveal_with_fuel(spec_alts_inner, 16);
    // the #GL-9 cast-seam value columns: two-tree-locked values,
    // assembled (the z3 fold of the char-cast emission residual is
    // the registered GL3->GL5 seam)
    assert(spec_basename_regex(opts, tokens, 64) == Some(seq!['(', '?', '-', 'u', ')', '^', '[', '^', '\\', '.', '-', '0', ']', '$']));
    assert(spec_match_strategy(opts, tokens, 64) == MatchStrategyS::BasenameRegex(seq!['(', '?', '-', 'u', ')', '^', '[', '^', '\\', '.', '-', '0', ']', '$']));
}


} // verus!

fn main() {}
