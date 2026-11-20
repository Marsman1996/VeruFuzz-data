//! GL5 weld corpus -- the 10 vectors of not1
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
// matchnot1  (pat='a*b*c' path='abcd' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot1() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('a'), TokenS::Zom, TokenS::Lit('b'), TokenS::Zom, TokenS::Lit('c')];
    let path = seq!['a', 'b', 'c', 'd'];
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
// matchnot2  (pat='abc*abc*abc' path='abcabcabcabcabcabcabca' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot2() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c'), TokenS::Zom, TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c'), TokenS::Zom, TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c')];
    let path = seq!['a', 'b', 'c', 'a', 'b', 'c', 'a', 'b', 'c', 'a', 'b', 'c', 'a', 'b', 'c', 'a', 'b', 'c', 'a', 'b', 'c', 'a'];
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
// matchnot3  (pat='some/**/needle.txt' path='some/other/notthis.txt' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot3() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::RecZ, TokenS::Lit('n'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('d'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'o', 't', 'h', 'e', 'r', '/', 'n', 'o', 't', 't', 'h', 'i', 's', '.', 't', 'x', 't'];
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
// matchnot4  (pat='some/**/**/needle.txt' path='some/other/notthis.txt' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot4() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::RecZ, TokenS::Lit('n'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('d'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'o', 't', 'h', 'e', 'r', '/', 'n', 'o', 't', 't', 'h', 'i', 's', '.', 't', 'x', 't'];
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
// matchnot5  (pat='/**/test' path='test' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot5() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecZ, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['t', 'e', 's', 't'];
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
// matchnot6  (pat='/**/test' path='/one/notthis' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot6() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecZ, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['/', 'o', 'n', 'e', '/', 'n', 'o', 't', 't', 'h', 'i', 's'];
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
// matchnot7  (pat='/**/test' path='/notthis' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot7() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecZ, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['/', 'n', 'o', 't', 't', 'h', 'i', 's'];
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
// matchnot8  (pat='**/.*' path='ab.c' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot8() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('.'), TokenS::Zom];
    let path = seq!['a', 'b', '.', 'c'];
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
// matchnot9  (pat='**/.*' path='abc/ab.c' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot9() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('.'), TokenS::Zom];
    let path = seq!['a', 'b', 'c', '/', 'a', 'b', '.', 'c'];
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
// matchnot10  (pat='.*/**' path='a.bc' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot10() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('.'), TokenS::Zom, TokenS::RecS];
    let path = seq!['a', '.', 'b', 'c'];
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

} // verus!

fn main() {}
