//! GL5 weld corpus -- the 4 vectors of rec31
//! Generated from the locked two-tree run (GL5/gen_harness.py + mirror-run.txt): tokens,
//! classification, fuel, and expectations all come from the
//! mirror==oracle==upstream-polarity lock; the assertion lane is
//! reveal_with_fuel + plain z3 per #GL-10.

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
    spec_cls_member_upto, spec_tok_emits, spec_tok_seq_emits, spec_seq_emits_upto,
    spec_pats_kept_scan, spec_alts_branch_kept,
    spec_literal, spec_ext, spec_required_ext, spec_prefix, spec_suffix,
    spec_basename_tokens, spec_basename_literal,
    spec_c_ext, spec_c_basename, spec_c_base_for_regex,
    spec_c_starts_with, spec_c_ends_with,
    spec_tm_at, spec_tm_recp_star, spec_tm_dot_star, spec_tm_recz_tail, spec_tm_all_chars,
    spec_tm_alts_try, spec_tm_mid_try,
    spec_last_slash_upto, spec_last_dot_upto,
    spec_lit_walk, spec_ext_walk, spec_req_ext_walk, spec_prefix_walk, spec_suffix_walk,
    spec_basename_literal_walk, spec_basename_gate_scan, spec_ranges_slash_upto,
    spec_match_strategy, spec_opts_unix_default, spec_strat_check, spec_tokens_match,
    GlobOptions, MatchStrategyS, TokenS,
};

verus!
{
// matchrec31  (pat='some/*/needle.txt' path='some/one/two/needle.txt' opts=SLASHLIT expected=false fuel=2)
proof fn ut_gl5_matchrec31() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('n'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('d'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'o', 'n', 'e', '/', 't', 'w', 'o', '/', 'n', 'e', 'e', 'd', 'l', 'e', '.', 't', 'x', 't'];
    let fuel: nat = 2 as nat;
    let crev: nat = 25 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 25);
    reveal_with_fuel(spec_tm_recp_star, 25);
    reveal_with_fuel(spec_tm_dot_star, 25);
    reveal_with_fuel(spec_tm_recz_tail, 25);
    reveal_with_fuel(spec_tm_all_chars, 25);
    reveal_with_fuel(spec_tm_alts_try, 25);
    reveal_with_fuel(spec_tm_mid_try, 75);
    reveal_with_fuel(spec_tok_emits, 25);
    reveal_with_fuel(spec_tok_seq_emits, 25);
    reveal_with_fuel(spec_seq_emits_upto, 25);
    reveal_with_fuel(spec_pats_kept_scan, 25);
    reveal_with_fuel(spec_cls_member_upto, 25);
    reveal_with_fuel(spec_last_slash_upto, 25);
    reveal_with_fuel(spec_last_dot_upto, 25);
    reveal_with_fuel(spec_lit_walk, 24);
    reveal_with_fuel(spec_ext_walk, 24);
    reveal_with_fuel(spec_req_ext_walk, 24);
    reveal_with_fuel(spec_prefix_walk, 24);
    reveal_with_fuel(spec_suffix_walk, 24);
    reveal_with_fuel(spec_basename_literal_walk, 24);
    reveal_with_fuel(spec_basename_gate_scan, 24);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 't', 'x', 't']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_ext(path) == seq!['.', 't', 'x', 't']);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::RequiredExtension(seq!['.', 't', 'x', 't']));
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 't', 'x', 't']), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 't', 'x', 't']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec32  (pat='some/*/needle.txt' path='some/one/two/three/needle.txt' opts=SLASHLIT expected=false fuel=2)
proof fn ut_gl5_matchrec32() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('n'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('d'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'o', 'n', 'e', '/', 't', 'w', 'o', '/', 't', 'h', 'r', 'e', 'e', '/', 'n', 'e', 'e', 'd', 'l', 'e', '.', 't', 'x', 't'];
    let fuel: nat = 2 as nat;
    let crev: nat = 31 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 31);
    reveal_with_fuel(spec_tm_recp_star, 31);
    reveal_with_fuel(spec_tm_dot_star, 31);
    reveal_with_fuel(spec_tm_recz_tail, 31);
    reveal_with_fuel(spec_tm_all_chars, 31);
    reveal_with_fuel(spec_tm_alts_try, 31);
    reveal_with_fuel(spec_tm_mid_try, 93);
    reveal_with_fuel(spec_tok_emits, 31);
    reveal_with_fuel(spec_tok_seq_emits, 31);
    reveal_with_fuel(spec_seq_emits_upto, 31);
    reveal_with_fuel(spec_pats_kept_scan, 31);
    reveal_with_fuel(spec_cls_member_upto, 31);
    reveal_with_fuel(spec_last_slash_upto, 31);
    reveal_with_fuel(spec_last_dot_upto, 31);
    reveal_with_fuel(spec_lit_walk, 24);
    reveal_with_fuel(spec_ext_walk, 24);
    reveal_with_fuel(spec_req_ext_walk, 24);
    reveal_with_fuel(spec_prefix_walk, 24);
    reveal_with_fuel(spec_suffix_walk, 24);
    reveal_with_fuel(spec_basename_literal_walk, 24);
    reveal_with_fuel(spec_basename_gate_scan, 24);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 't', 'x', 't']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_ext(path) == seq!['.', 't', 'x', 't']);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::RequiredExtension(seq!['.', 't', 'x', 't']));
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 't', 'x', 't']), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 't', 'x', 't']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec33  (pat='.*/**' path='.abc' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchrec33() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('.'), TokenS::Zom, TokenS::RecS];
    let path = seq!['.', 'a', 'b', 'c'];
    let fuel: nat = 2 as nat;
    let crev: nat = 24 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 24);
    reveal_with_fuel(spec_tm_recp_star, 24);
    reveal_with_fuel(spec_tm_dot_star, 24);
    reveal_with_fuel(spec_tm_recz_tail, 24);
    reveal_with_fuel(spec_tm_all_chars, 24);
    reveal_with_fuel(spec_tm_alts_try, 24);
    reveal_with_fuel(spec_tm_mid_try, 72);
    reveal_with_fuel(spec_tok_emits, 24);
    reveal_with_fuel(spec_tok_seq_emits, 24);
    reveal_with_fuel(spec_seq_emits_upto, 24);
    reveal_with_fuel(spec_pats_kept_scan, 24);
    reveal_with_fuel(spec_cls_member_upto, 24);
    reveal_with_fuel(spec_last_slash_upto, 24);
    reveal_with_fuel(spec_last_dot_upto, 24);
    reveal_with_fuel(spec_lit_walk, 24);
    reveal_with_fuel(spec_ext_walk, 24);
    reveal_with_fuel(spec_req_ext_walk, 24);
    reveal_with_fuel(spec_prefix_walk, 24);
    reveal_with_fuel(spec_suffix_walk, 24);
    reveal_with_fuel(spec_basename_literal_walk, 24);
    reveal_with_fuel(spec_basename_gate_scan, 24);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Regex);
    assert(spec_strat_check(opts, MatchStrategyS::Regex, tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Regex, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec34  (pat='foo/**' path='foo' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchrec34() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::RecS];
    let path = seq!['f', 'o', 'o'];
    let fuel: nat = 2 as nat;
    let crev: nat = 24 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 24);
    reveal_with_fuel(spec_tm_recp_star, 24);
    reveal_with_fuel(spec_tm_dot_star, 24);
    reveal_with_fuel(spec_tm_recz_tail, 24);
    reveal_with_fuel(spec_tm_all_chars, 24);
    reveal_with_fuel(spec_tm_alts_try, 24);
    reveal_with_fuel(spec_tm_mid_try, 72);
    reveal_with_fuel(spec_tok_emits, 24);
    reveal_with_fuel(spec_tok_seq_emits, 24);
    reveal_with_fuel(spec_seq_emits_upto, 24);
    reveal_with_fuel(spec_pats_kept_scan, 24);
    reveal_with_fuel(spec_cls_member_upto, 24);
    reveal_with_fuel(spec_last_slash_upto, 24);
    reveal_with_fuel(spec_last_dot_upto, 24);
    reveal_with_fuel(spec_lit_walk, 24);
    reveal_with_fuel(spec_ext_walk, 24);
    reveal_with_fuel(spec_req_ext_walk, 24);
    reveal_with_fuel(spec_prefix_walk, 24);
    reveal_with_fuel(spec_suffix_walk, 24);
    reveal_with_fuel(spec_basename_literal_walk, 24);
    reveal_with_fuel(spec_basename_gate_scan, 24);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == Some(seq!['f', 'o', 'o', '/']));
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 3);
    assert(seq!['f', 'o', 'o', '/'].len() == 4);
    assert(path.index(0) == 'f');
    assert(path.index(1) == 'o');
    assert(path.index(2) == 'o');
    assert(seq!['f', 'o', 'o', '/'].index(0) == 'f');
    assert(seq!['f', 'o', 'o', '/'].index(1) == 'o');
    assert(seq!['f', 'o', 'o', '/'].index(2) == 'o');
    assert(seq!['f', 'o', 'o', '/'].index(3) == '/');
    assert(path.len() == 3);
    assert(seq!['f', 'o', 'o', '/'].len() == 4);
    assert(spec_c_starts_with(seq!['f', 'o', 'o', '/'], path) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Prefix(seq!['f', 'o', 'o', '/']));
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['f', 'o', 'o', '/']), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['f', 'o', 'o', '/']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}

} // verus!

fn main() {}
