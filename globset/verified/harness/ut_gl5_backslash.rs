//! GL5 weld corpus -- the 7 vectors of backslash
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
// matchbackslash1  (pat='\\[' path='[' opts=BSESC expected=true fuel=5)
proof fn ut_gl5_matchbackslash1() {
    let opts = spec_opts_unix_default(); // backslash_escape is the unix default
    let tokens = seq![TokenS::Lit('[')];
    let path = seq!['['];
    let fuel: nat = 5 as nat;
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
    assert(tokens.subrange(0, 1).index(0) == TokenS::Lit('['));
    assert(spec_suffix_walk(tokens.subrange(1, 1), seq!['['], 0) == Some(seq!['['])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(0, 1), Seq::empty(), 2) == Some(seq!['[']));
    assert(spec_literal(opts, tokens) == Some(seq!['[']));
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == Some(seq!['[']));
    assert(spec_suffix(opts, tokens) == Some((seq!['['], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Literal(seq!['[']));
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['[']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['[']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchbackslash2  (pat='\\?' path='?' opts=BSESC expected=true fuel=5)
proof fn ut_gl5_matchbackslash2() {
    let opts = spec_opts_unix_default(); // backslash_escape is the unix default
    let tokens = seq![TokenS::Lit('?')];
    let path = seq!['?'];
    let fuel: nat = 5 as nat;
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
    assert(tokens.subrange(0, 1).index(0) == TokenS::Lit('?'));
    assert(spec_suffix_walk(tokens.subrange(1, 1), seq!['?'], 0) == Some(seq!['?'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(0, 1), Seq::empty(), 2) == Some(seq!['?']));
    assert(spec_literal(opts, tokens) == Some(seq!['?']));
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == Some(seq!['?']));
    assert(spec_suffix(opts, tokens) == Some((seq!['?'], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Literal(seq!['?']));
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['?']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['?']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchbackslash3  (pat='\\*' path='*' opts=BSESC expected=true fuel=5)
proof fn ut_gl5_matchbackslash3() {
    let opts = spec_opts_unix_default(); // backslash_escape is the unix default
    let tokens = seq![TokenS::Lit('*')];
    let path = seq!['*'];
    let fuel: nat = 5 as nat;
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
    assert(tokens.subrange(0, 1).index(0) == TokenS::Lit('*'));
    assert(spec_suffix_walk(tokens.subrange(1, 1), seq!['*'], 0) == Some(seq!['*'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(0, 1), Seq::empty(), 2) == Some(seq!['*']));
    assert(spec_literal(opts, tokens) == Some(seq!['*']));
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == Some(seq!['*']));
    assert(spec_suffix(opts, tokens) == Some((seq!['*'], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Literal(seq!['*']));
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['*']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['*']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchbackslash4  (pat='\\[a-z]' path='\\a' opts=NOBSESC expected=true fuel=6)
proof fn ut_gl5_matchbackslash4() {
    let opts = GlobOptions { backslash_escape: false, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::Lit('\\'), TokenS::Cls { negated: false, ranges: seq![('a', 'z')] }];
    let path = seq!['\\', 'a'];
    let fuel: nat = 6 as nat;
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
// matchbackslash5  (pat='\\?' path='\\a' opts=NOBSESC expected=true fuel=6)
proof fn ut_gl5_matchbackslash5() {
    let opts = GlobOptions { backslash_escape: false, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::Lit('\\'), TokenS::Any];
    let path = seq!['\\', 'a'];
    let fuel: nat = 6 as nat;
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
// matchbackslash6  (pat='\\*' path='\\\\' opts=NOBSESC expected=true fuel=7)
proof fn ut_gl5_matchbackslash6() {
    let opts = GlobOptions { backslash_escape: false, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::Lit('\\'), TokenS::Zom];
    let path = seq!['\\', '\\'];
    let fuel: nat = 7 as nat;
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
    assert(spec_prefix(opts, tokens) == Some(seq!['\\']));
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 2);
    assert(seq!['\\'].len() == 1);
    assert(path.index(0) == '\\');
    assert(seq!['\\'].index(0) == '\\');
    let psub = path.subrange(0, 1);
    let sure = seq!['\\'];
    assert(psub.len() == 1);
    assert forall|i: int| 0 <= i <= 0 implies path.index(i) == sure.index(i) by {
    }
    assert(psub == sure);
    assert(spec_c_starts_with(seq!['\\'], path) == true);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Prefix(seq!['\\']));
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['\\']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Prefix(seq!['\\']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchbackslash7  (pat='\\a' path='a' opts=DEF expected=true fuel=5)
proof fn ut_gl5_matchbackslash7() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('a')];
    let path = seq!['a'];
    let fuel: nat = 5 as nat;
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
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['a']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['a']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}

} // verus!

fn main() {}
