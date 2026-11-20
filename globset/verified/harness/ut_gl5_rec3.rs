//! GL5 weld corpus -- the 8 vectors of rec3
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
// matchrec19  (pat='**/.*' path='.abc' opts=DEF expected=true fuel=10)
proof fn ut_gl5_matchrec19() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('.'), TokenS::Zom];
    let path = seq!['.', 'a', 'b', 'c'];
    let fuel: nat = 10 as nat;
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
    assert(spec_strat_check(opts, MatchStrategyS::Regex, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Regex, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec20  (pat='**/.*' path='abc/.abc' opts=DEF expected=true fuel=14)
proof fn ut_gl5_matchrec20() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('.'), TokenS::Zom];
    let path = seq!['a', 'b', 'c', '/', '.', 'a', 'b', 'c'];
    let fuel: nat = 14 as nat;
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
    assert(spec_strat_check(opts, MatchStrategyS::Regex, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Regex, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec21  (pat='**/foo/bar' path='foo/bar' opts=DEF expected=true fuel=12)
proof fn ut_gl5_matchrec21() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')];
    let path = seq!['f', 'o', 'o', '/', 'b', 'a', 'r'];
    let fuel: nat = 12 as nat;
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
    assert(tokens.len() == 8);
    assert(tokens.subrange(1, 8).len() == 7);
    assert(tokens.subrange(1, 8).index(0) == TokenS::Lit('f'));
    assert(spec_suffix_walk(tokens.subrange(8, 8), seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], 0) == Some(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 8), seq!['/'], 9) == Some(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], true)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 7);
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].len() == 8);
    assert(path.index(0) == 'f');
    assert(path.index(1) == 'o');
    assert(path.index(2) == 'o');
    assert(path.index(3) == '/');
    assert(path.index(4) == 'b');
    assert(path.index(5) == 'a');
    assert(path.index(6) == 'r');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(0) == '/');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(1) == 'f');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(2) == 'o');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(3) == 'o');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(4) == '/');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(5) == 'b');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(6) == 'a');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(7) == 'r');
    assert(spec_c_ends_with(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], path) == false);
    let wsubc = seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].subrange(1, 8 as int);
    assert(wsubc.len() == 7 as int);
    assert(path.index(0) == 'f');
    assert(path.index(1) == 'o');
    assert(path.index(2) == 'o');
    assert(path.index(3) == '/');
    assert(path.index(4) == 'b');
    assert(path.index(5) == 'a');
    assert(path.index(6) == 'r');
    assert forall|i: int| 0 <= i <= 6 implies path.index(i) == seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(1 + i) by {
    }
    assert(path == wsubc);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], component: true });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], component: true }, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], component: true }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec22  (pat='.*/**' path='.abc/abc' opts=DEF expected=true fuel=14)
proof fn ut_gl5_matchrec22() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('.'), TokenS::Zom, TokenS::RecS];
    let path = seq!['.', 'a', 'b', 'c', '/', 'a', 'b', 'c'];
    let fuel: nat = 14 as nat;
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
    assert(spec_strat_check(opts, MatchStrategyS::Regex, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Regex, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec23  (pat='test/**' path='test/' opts=DEF expected=true fuel=10)
proof fn ut_gl5_matchrec23() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t'), TokenS::RecS];
    let path = seq!['t', 'e', 's', 't', '/'];
    let fuel: nat = 10 as nat;
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
    assert(spec_prefix(opts, tokens) == Some(seq!['t', 'e', 's', 't', '/']));
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 5);
    assert(seq!['t', 'e', 's', 't', '/'].len() == 5);
    assert(path.index(0) == 't');
    assert(path.index(1) == 'e');
    assert(path.index(2) == 's');
    assert(path.index(3) == 't');
    assert(path.index(4) == '/');
    assert(seq!['t', 'e', 's', 't', '/'].index(0) == 't');
    assert(seq!['t', 'e', 's', 't', '/'].index(1) == 'e');
    assert(seq!['t', 'e', 's', 't', '/'].index(2) == 's');
    assert(seq!['t', 'e', 's', 't', '/'].index(3) == 't');
    assert(seq!['t', 'e', 's', 't', '/'].index(4) == '/');
    let psub = path.subrange(0, 5);
    let sure = seq!['t', 'e', 's', 't', '/'];
    assert(psub.len() == 5);
    assert forall|i: int| 0 <= i <= 4 implies path.index(i) == sure.index(i) by {
    }
    assert(psub == sure);
    assert(spec_c_starts_with(seq!['t', 'e', 's', 't', '/'], path) == true);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']));
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec24  (pat='test/**' path='test/one' opts=DEF expected=true fuel=13)
proof fn ut_gl5_matchrec24() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t'), TokenS::RecS];
    let path = seq!['t', 'e', 's', 't', '/', 'o', 'n', 'e'];
    let fuel: nat = 13 as nat;
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
    assert(spec_prefix(opts, tokens) == Some(seq!['t', 'e', 's', 't', '/']));
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 8);
    assert(seq!['t', 'e', 's', 't', '/'].len() == 5);
    assert(path.index(0) == 't');
    assert(path.index(1) == 'e');
    assert(path.index(2) == 's');
    assert(path.index(3) == 't');
    assert(path.index(4) == '/');
    assert(seq!['t', 'e', 's', 't', '/'].index(0) == 't');
    assert(seq!['t', 'e', 's', 't', '/'].index(1) == 'e');
    assert(seq!['t', 'e', 's', 't', '/'].index(2) == 's');
    assert(seq!['t', 'e', 's', 't', '/'].index(3) == 't');
    assert(seq!['t', 'e', 's', 't', '/'].index(4) == '/');
    let psub = path.subrange(0, 5);
    let sure = seq!['t', 'e', 's', 't', '/'];
    assert(psub.len() == 5);
    assert forall|i: int| 0 <= i <= 4 implies path.index(i) == sure.index(i) by {
    }
    assert(psub == sure);
    assert(spec_c_starts_with(seq!['t', 'e', 's', 't', '/'], path) == true);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']));
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec25  (pat='test/**' path='test/one/two' opts=DEF expected=true fuel=17)
proof fn ut_gl5_matchrec25() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t'), TokenS::RecS];
    let path = seq!['t', 'e', 's', 't', '/', 'o', 'n', 'e', '/', 't', 'w', 'o'];
    let fuel: nat = 17 as nat;
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
    assert(spec_prefix(opts, tokens) == Some(seq!['t', 'e', 's', 't', '/']));
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 12);
    assert(seq!['t', 'e', 's', 't', '/'].len() == 5);
    assert(path.index(0) == 't');
    assert(path.index(1) == 'e');
    assert(path.index(2) == 's');
    assert(path.index(3) == 't');
    assert(path.index(4) == '/');
    assert(seq!['t', 'e', 's', 't', '/'].index(0) == 't');
    assert(seq!['t', 'e', 's', 't', '/'].index(1) == 'e');
    assert(seq!['t', 'e', 's', 't', '/'].index(2) == 's');
    assert(seq!['t', 'e', 's', 't', '/'].index(3) == 't');
    assert(seq!['t', 'e', 's', 't', '/'].index(4) == '/');
    let psub = path.subrange(0, 5);
    let sure = seq!['t', 'e', 's', 't', '/'];
    assert(psub.len() == 5);
    assert forall|i: int| 0 <= i <= 4 implies path.index(i) == sure.index(i) by {
    }
    assert(psub == sure);
    assert(spec_c_starts_with(seq!['t', 'e', 's', 't', '/'], path) == true);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']));
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['t', 'e', 's', 't', '/']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec26  (pat='some/*/needle.txt' path='some/one/needle.txt' opts=DEF expected=true fuel=24)
proof fn ut_gl5_matchrec26() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('n'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('d'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'o', 'n', 'e', '/', 'n', 'e', 'e', 'd', 'l', 'e', '.', 't', 'x', 't'];
    let fuel: nat = 24 as nat;
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
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 't', 'x', 't']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 't', 'x', 't']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}

} // verus!

fn main() {}
