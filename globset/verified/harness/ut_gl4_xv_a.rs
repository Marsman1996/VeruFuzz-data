//! GL4 extractor KAT -- XV: empty, lone **, mid-RecZ, alternates
//! Generated from the locked two-tree truth table (out/kverus-run/
//! GL4/mirror-run.txt == oracle-run.txt == the upstream RE columns):
//! every asserted ground value is the oracle==mirror entry. The
//! assertion lane is reveal_with_fuel + plain z3 (#GL-10: by(compute)
//! panics the engine on walker lanes); fuel 16 sits above every
//! fixture's token depth. Emission-loaded vectors assert the
//! basename_regex/classification rows in congruence form here; their
//! value-form columns ride ut_gl4r_* (the #GL-9 cast-seam rows,
//! two-tree-locked) plus the ut_gl4p_* parse-binding deferrals.

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
    spec_basename_gate_scan, spec_basename_literal, spec_basename_literal_walk,
    spec_basename_regex, spec_basename_tokens, spec_ext, spec_ext_walk, spec_lit_walk,
    spec_literal, spec_match_strategy, spec_opts_unix_default, spec_prefix, spec_prefix_walk,
    spec_ranges_slash_upto, spec_req_ext_walk, spec_required_ext, spec_suffix, spec_suffix_walk,
    spec_to_regex_with, GlobOptions, MatchStrategyS, TokenS
};

verus!
{
proof fn ut_gl4_xv_empty() {
    let opts = spec_opts_unix_default();
    let tokens = seq![];
    // walker reveals (fuel 16 sits above every fixture's token depth)
    reveal_with_fuel(spec_lit_walk, 16);
    reveal_with_fuel(spec_ext_walk, 16);
    reveal_with_fuel(spec_req_ext_walk, 16);
    reveal_with_fuel(spec_prefix_walk, 16);
    reveal_with_fuel(spec_suffix_walk, 16);
    reveal_with_fuel(spec_basename_literal_walk, 16);
    reveal_with_fuel(spec_basename_gate_scan, 16);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    // all eight family columns (the full decision table; the
    // classification assert reuses these derived values)
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_basename_regex(opts, tokens, 64) == None);
    assert(spec_match_strategy(opts, tokens, 64) == MatchStrategyS::Regex);
}

proof fn ut_gl4_xv_recponly() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP];
    // walker reveals (fuel 16 sits above every fixture's token depth)
    reveal_with_fuel(spec_lit_walk, 16);
    reveal_with_fuel(spec_ext_walk, 16);
    reveal_with_fuel(spec_req_ext_walk, 16);
    reveal_with_fuel(spec_prefix_walk, 16);
    reveal_with_fuel(spec_suffix_walk, 16);
    reveal_with_fuel(spec_basename_literal_walk, 16);
    reveal_with_fuel(spec_basename_gate_scan, 16);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    // all eight family columns (the full decision table; the
    // classification assert reuses these derived values)
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_basename_regex(opts, tokens, 64) == None);
    assert(spec_match_strategy(opts, tokens, 64) == MatchStrategyS::Regex);
}

proof fn ut_gl4_xv_mid_recz() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('a'), TokenS::RecZ, TokenS::Lit('b')];
    // walker reveals (fuel 16 sits above every fixture's token depth)
    reveal_with_fuel(spec_lit_walk, 16);
    reveal_with_fuel(spec_ext_walk, 16);
    reveal_with_fuel(spec_req_ext_walk, 16);
    reveal_with_fuel(spec_prefix_walk, 16);
    reveal_with_fuel(spec_suffix_walk, 16);
    reveal_with_fuel(spec_basename_literal_walk, 16);
    reveal_with_fuel(spec_basename_gate_scan, 16);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    // all eight family columns (the full decision table; the
    // classification assert reuses these derived values)
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_basename_regex(opts, tokens, 64) == None);
    assert(spec_match_strategy(opts, tokens, 64) == MatchStrategyS::Regex);
}

proof fn ut_gl4_xv_alts() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Alts(seq![seq![TokenS::Lit('a')], seq![TokenS::Lit('b')]])];
    // walker reveals (fuel 16 sits above every fixture's token depth)
    reveal_with_fuel(spec_lit_walk, 16);
    reveal_with_fuel(spec_ext_walk, 16);
    reveal_with_fuel(spec_req_ext_walk, 16);
    reveal_with_fuel(spec_prefix_walk, 16);
    reveal_with_fuel(spec_suffix_walk, 16);
    reveal_with_fuel(spec_basename_literal_walk, 16);
    reveal_with_fuel(spec_basename_gate_scan, 16);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    // all eight family columns (the full decision table; the
    // classification assert reuses these derived values)
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_basename_regex(opts, tokens, 64) == None);
    assert(spec_match_strategy(opts, tokens, 64) == MatchStrategyS::Regex);
}


} // verus!

fn main() {}
