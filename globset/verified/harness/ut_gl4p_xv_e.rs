//! GL4 parse-binding (deferred column) -- XV: the CASEI BasenameRegex witness + the basename class row (SLASHLIT)
//! Generated from the locked two-tree truth table (out/kverus-run/
//! GL4/mirror-run.txt == oracle-run.txt == the upstream RE columns):
//! every asserted ground value is the oracle==mirror entry. The
//! assertion lane is reveal_with_fuel + plain z3 (#GL-10: by(compute)
//! panics the engine on walker lanes); fuel 16 sits above every
//! fixture's token depth. The parse-binding column rides GL2's
//! machine on the same reveal lane.

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
    spec_alts_inner, spec_basename_gate_scan, spec_basename_literal, spec_basename_literal_walk, spec_basename_regex,
    spec_basename_tokens, spec_class_frag_upto, spec_ext, spec_ext_walk, spec_lit_walk,
    spec_literal, spec_match_strategy, spec_opts_unix_default, spec_parse_glob, spec_parse_loop,
    spec_prefix, spec_prefix_walk, spec_ranges_slash_upto, spec_req_ext_walk, spec_required_ext,
    spec_suffix, spec_suffix_walk, spec_tokens_to_regex, GlobOptions, MatchStrategyS, TokenS
};

verus!
{
proof fn ut_gl4p_xv_casei_base() {
    let opts = GlobOptions { case_insensitive: true, ..spec_opts_unix_default() };
    reveal_with_fuel(spec_parse_loop, 28);
    assert(spec_parse_glob(seq!['*', '*', '/', 'f', 'o', 'o'], opts, false) == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]));
}

proof fn ut_gl4p_xv_base_cls() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    reveal_with_fuel(spec_parse_loop, 40);
    assert(spec_parse_glob(seq!['*', '*', '/', '*', '.', 'p', 'y', '[', 'c', 'o', 'd', ']'], opts, false) == Ok(seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('p'), TokenS::Lit('y'), TokenS::Cls { negated: false, ranges: seq![('c', 'c'), ('o', 'o'), ('d', 'd')] }]));
}


} // verus!

fn main() {}
