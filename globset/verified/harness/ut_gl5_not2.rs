//! GL5 weld corpus -- the 10 vectors of not2
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
// matchnot11  (pat='.*/**' path='abc/a.bc' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot11() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('.'), TokenS::Zom, TokenS::RecS];
    let path = seq!['a', 'b', 'c', '/', 'a', '.', 'b', 'c'];
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
// matchnot12  (pat='a[0-9]b' path='a_b' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot12() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('a'), TokenS::Cls { negated: false, ranges: seq![('0', '9')] }, TokenS::Lit('b')];
    let path = seq!['a', '_', 'b'];
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
// matchnot13  (pat='a[!0-9]b' path='a0b' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot13() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('a'), TokenS::Cls { negated: true, ranges: seq![('0', '9')] }, TokenS::Lit('b')];
    let path = seq!['a', '0', 'b'];
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
// matchnot14  (pat='a[!0-9]b' path='a9b' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot14() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('a'), TokenS::Cls { negated: true, ranges: seq![('0', '9')] }, TokenS::Lit('b')];
    let path = seq!['a', '9', 'b'];
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
// matchnot15  (pat='[!-]' path='-' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot15() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Cls { negated: true, ranges: seq![('-', '-')] }];
    let path = seq!['-'];
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
// matchnot16  (pat='*hello.txt' path='hello.txt-and-then-some' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot16() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't', '-', 'a', 'n', 'd', '-', 't', 'h', 'e', 'n', '-', 's', 'o', 'm', 'e'];
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
    assert(tokens.len() == 10);
    assert(tokens.subrange(1, 10).len() == 9);
    assert(tokens.subrange(1, 10).index(0) == TokenS::Lit('h'));
    assert(spec_suffix_walk(tokens.subrange(10, 10), seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], 0) == Some(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 10), Seq::empty(), 11) == Some(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 't', 'x', 't']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 23);
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 9);
    assert(path.index(14) == 't');
    assert(path.index(15) == 'h');
    assert(path.index(16) == 'e');
    assert(path.index(17) == 'n');
    assert(path.index(18) == '-');
    assert(path.index(19) == 's');
    assert(path.index(20) == 'o');
    assert(path.index(21) == 'm');
    assert(path.index(22) == 'e');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'e');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == 'o');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == '.');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 'x');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 't');
    assert(path.index(14) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(spec_c_ends_with(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == false);
    let wsubc = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 9 as int);
    assert(wsubc.len() == 8 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot17  (pat='*hello.txt' path='goodbye.txt' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot17() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['g', 'o', 'o', 'd', 'b', 'y', 'e', '.', 't', 'x', 't'];
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
    assert(tokens.len() == 10);
    assert(tokens.subrange(1, 10).len() == 9);
    assert(tokens.subrange(1, 10).index(0) == TokenS::Lit('h'));
    assert(spec_suffix_walk(tokens.subrange(10, 10), seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], 0) == Some(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 10), Seq::empty(), 11) == Some(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 't', 'x', 't']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 11);
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 9);
    assert(path.index(2) == 'o');
    assert(path.index(3) == 'd');
    assert(path.index(4) == 'b');
    assert(path.index(5) == 'y');
    assert(path.index(6) == 'e');
    assert(path.index(7) == '.');
    assert(path.index(8) == 't');
    assert(path.index(9) == 'x');
    assert(path.index(10) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'e');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == 'o');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == '.');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 'x');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 't');
    assert(path.index(2) == 'o');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(spec_c_ends_with(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == false);
    let wsubc = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 9 as int);
    assert(wsubc.len() == 8 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot18  (pat='*some/path/to/hello.txt' path='some/path/to/hello.txt-and-then-some' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot18() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::Lit('/'), TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('/'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't', '-', 'a', 'n', 'd', '-', 't', 'h', 'e', 'n', '-', 's', 'o', 'm', 'e'];
    let fuel: nat = 2 as nat;
    let crev: nat = 38 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 38);
    reveal_with_fuel(spec_tm_recp_star, 38);
    reveal_with_fuel(spec_tm_dot_star, 38);
    reveal_with_fuel(spec_tm_recz_tail, 38);
    reveal_with_fuel(spec_tm_all_chars, 38);
    reveal_with_fuel(spec_tm_alts_try, 38);
    reveal_with_fuel(spec_tm_mid_try, 114);
    reveal_with_fuel(spec_tok_emits, 38);
    reveal_with_fuel(spec_tok_seq_emits, 38);
    reveal_with_fuel(spec_seq_emits_upto, 38);
    reveal_with_fuel(spec_pats_kept_scan, 38);
    reveal_with_fuel(spec_cls_member_upto, 38);
    reveal_with_fuel(spec_last_slash_upto, 38);
    reveal_with_fuel(spec_last_dot_upto, 38);
    reveal_with_fuel(spec_lit_walk, 24);
    reveal_with_fuel(spec_ext_walk, 24);
    reveal_with_fuel(spec_req_ext_walk, 24);
    reveal_with_fuel(spec_prefix_walk, 24);
    reveal_with_fuel(spec_suffix_walk, 24);
    reveal_with_fuel(spec_basename_literal_walk, 24);
    reveal_with_fuel(spec_basename_gate_scan, 24);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    assert(tokens.len() == 23);
    assert(tokens.subrange(1, 23).len() == 22);
    assert(tokens.subrange(1, 23).index(0) == TokenS::Lit('s'));
    assert(spec_suffix_walk(tokens.subrange(23, 23), seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], 0) == Some(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 23), Seq::empty(), 24) == Some(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 't', 'x', 't']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 36);
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 22);
    assert(path.index(14) == 'e');
    assert(path.index(15) == 'l');
    assert(path.index(16) == 'l');
    assert(path.index(17) == 'o');
    assert(path.index(18) == '.');
    assert(path.index(19) == 't');
    assert(path.index(20) == 'x');
    assert(path.index(21) == 't');
    assert(path.index(22) == '-');
    assert(path.index(23) == 'a');
    assert(path.index(24) == 'n');
    assert(path.index(25) == 'd');
    assert(path.index(26) == '-');
    assert(path.index(27) == 't');
    assert(path.index(28) == 'h');
    assert(path.index(29) == 'e');
    assert(path.index(30) == 'n');
    assert(path.index(31) == '-');
    assert(path.index(32) == 's');
    assert(path.index(33) == 'o');
    assert(path.index(34) == 'm');
    assert(path.index(35) == 'e');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 's');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'o');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'm');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'e');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == '/');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == 'p');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 'a');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 't');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 'h');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(9) == '/');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(10) == 't');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(11) == 'o');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(12) == '/');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(13) == 'h');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(14) == 'e');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(15) == 'l');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(16) == 'l');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(17) == 'o');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(18) == '.');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(19) == 't');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(20) == 'x');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(21) == 't');
    assert(path.index(14) == 'e');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 's');
    assert(spec_c_ends_with(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == false);
    let wsubc = seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 22 as int);
    assert(wsubc.len() == 21 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot19  (pat='*some/path/to/hello.txt' path='some/other/path/to/hello.txt' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot19() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::Lit('/'), TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('/'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'o', 't', 'h', 'e', 'r', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'];
    let fuel: nat = 2 as nat;
    let crev: nat = 30 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 30);
    reveal_with_fuel(spec_tm_recp_star, 30);
    reveal_with_fuel(spec_tm_dot_star, 30);
    reveal_with_fuel(spec_tm_recz_tail, 30);
    reveal_with_fuel(spec_tm_all_chars, 30);
    reveal_with_fuel(spec_tm_alts_try, 30);
    reveal_with_fuel(spec_tm_mid_try, 90);
    reveal_with_fuel(spec_tok_emits, 30);
    reveal_with_fuel(spec_tok_seq_emits, 30);
    reveal_with_fuel(spec_seq_emits_upto, 30);
    reveal_with_fuel(spec_pats_kept_scan, 30);
    reveal_with_fuel(spec_cls_member_upto, 30);
    reveal_with_fuel(spec_last_slash_upto, 30);
    reveal_with_fuel(spec_last_dot_upto, 30);
    reveal_with_fuel(spec_lit_walk, 24);
    reveal_with_fuel(spec_ext_walk, 24);
    reveal_with_fuel(spec_req_ext_walk, 24);
    reveal_with_fuel(spec_prefix_walk, 24);
    reveal_with_fuel(spec_suffix_walk, 24);
    reveal_with_fuel(spec_basename_literal_walk, 24);
    reveal_with_fuel(spec_basename_gate_scan, 24);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    assert(tokens.len() == 23);
    assert(tokens.subrange(1, 23).len() == 22);
    assert(tokens.subrange(1, 23).index(0) == TokenS::Lit('s'));
    assert(spec_suffix_walk(tokens.subrange(23, 23), seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], 0) == Some(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 23), Seq::empty(), 24) == Some(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 't', 'x', 't']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 28);
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 22);
    assert(path.index(6) == 't');
    assert(path.index(7) == 'h');
    assert(path.index(8) == 'e');
    assert(path.index(9) == 'r');
    assert(path.index(10) == '/');
    assert(path.index(11) == 'p');
    assert(path.index(12) == 'a');
    assert(path.index(13) == 't');
    assert(path.index(14) == 'h');
    assert(path.index(15) == '/');
    assert(path.index(16) == 't');
    assert(path.index(17) == 'o');
    assert(path.index(18) == '/');
    assert(path.index(19) == 'h');
    assert(path.index(20) == 'e');
    assert(path.index(21) == 'l');
    assert(path.index(22) == 'l');
    assert(path.index(23) == 'o');
    assert(path.index(24) == '.');
    assert(path.index(25) == 't');
    assert(path.index(26) == 'x');
    assert(path.index(27) == 't');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 's');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'o');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'm');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'e');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == '/');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == 'p');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 'a');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 't');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 'h');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(9) == '/');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(10) == 't');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(11) == 'o');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(12) == '/');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(13) == 'h');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(14) == 'e');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(15) == 'l');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(16) == 'l');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(17) == 'o');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(18) == '.');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(19) == 't');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(20) == 'x');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(21) == 't');
    assert(path.index(6) == 't');
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 's');
    assert(spec_c_ends_with(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == false);
    let wsubc = seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 22 as int);
    assert(wsubc.len() == 21 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot20  (pat='a' path='foo/a' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot20() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('a')];
    let path = seq!['f', 'o', 'o', '/', 'a'];
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
    assert(tokens.len() == 1);
    assert(tokens.subrange(0, 1).len() == 1);
    assert(tokens.subrange(0, 1).index(0) == TokenS::Lit('a'));
    assert(spec_suffix_walk(tokens.subrange(1, 1), seq!['a'], 0) == Some(seq!['a'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(0, 1), Seq::empty(), 2) == Some(seq!['a']));
    assert(spec_literal(opts, tokens) == Some(seq!['a']));
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == Some(seq!['a']));
    assert(spec_suffix(opts, tokens) == Some((seq!['a'], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Literal(seq!['a']));
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['a']), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['a']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}

} // verus!

fn main() {}
