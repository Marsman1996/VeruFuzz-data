//! GL5 weld corpus -- the 6 vectors of rec2
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
// matchrec13  (pat='**/test' path='one/two/test' opts=DEF expected=true fuel=17)
proof fn ut_gl5_matchrec13() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['o', 'n', 'e', '/', 't', 'w', 'o', '/', 't', 'e', 's', 't'];
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
    assert(tokens.len() == 5);
    assert(tokens.subrange(1, 5).len() == 4);
    assert(tokens.subrange(1, 5).index(0) == TokenS::Lit('t'));
    assert(spec_suffix_walk(tokens.subrange(5, 5), seq!['/', 't', 'e', 's', 't'], 0) == Some(seq!['/', 't', 'e', 's', 't'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 5), seq!['/'], 6) == Some(seq!['/', 't', 'e', 's', 't']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['/', 't', 'e', 's', 't'], true)));
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')]));
    assert(spec_basename_literal(opts, tokens) == Some(seq!['t', 'e', 's', 't']));
    assert(spec_c_basename(path) == seq!['t', 'e', 's', 't']);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']));
    assert(spec_strat_check(opts, MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec14  (pat='**/test' path='one/test' opts=DEF expected=true fuel=13)
proof fn ut_gl5_matchrec14() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['o', 'n', 'e', '/', 't', 'e', 's', 't'];
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
    assert(tokens.len() == 5);
    assert(tokens.subrange(1, 5).len() == 4);
    assert(tokens.subrange(1, 5).index(0) == TokenS::Lit('t'));
    assert(spec_suffix_walk(tokens.subrange(5, 5), seq!['/', 't', 'e', 's', 't'], 0) == Some(seq!['/', 't', 'e', 's', 't'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 5), seq!['/'], 6) == Some(seq!['/', 't', 'e', 's', 't']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['/', 't', 'e', 's', 't'], true)));
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')]));
    assert(spec_basename_literal(opts, tokens) == Some(seq!['t', 'e', 's', 't']));
    assert(spec_c_basename(path) == seq!['t', 'e', 's', 't']);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']));
    assert(spec_strat_check(opts, MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec15  (pat='**/test' path='test' opts=DEF expected=true fuel=9)
proof fn ut_gl5_matchrec15() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['t', 'e', 's', 't'];
    let fuel: nat = 9 as nat;
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
    assert(tokens.len() == 5);
    assert(tokens.subrange(1, 5).len() == 4);
    assert(tokens.subrange(1, 5).index(0) == TokenS::Lit('t'));
    assert(spec_suffix_walk(tokens.subrange(5, 5), seq!['/', 't', 'e', 's', 't'], 0) == Some(seq!['/', 't', 'e', 's', 't'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 5), seq!['/'], 6) == Some(seq!['/', 't', 'e', 's', 't']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['/', 't', 'e', 's', 't'], true)));
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')]));
    assert(spec_basename_literal(opts, tokens) == Some(seq!['t', 'e', 's', 't']));
    assert(spec_c_basename(path) == seq!['t', 'e', 's', 't']);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']));
    assert(spec_strat_check(opts, MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameLiteral(seq!['t', 'e', 's', 't']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchrec16  (pat='/**/test' path='/one/two/test' opts=DEF expected=true fuel=17)
proof fn ut_gl5_matchrec16() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecZ, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['/', 'o', 'n', 'e', '/', 't', 'w', 'o', '/', 't', 'e', 's', 't'];
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
// matchrec17  (pat='/**/test' path='/one/test' opts=DEF expected=true fuel=13)
proof fn ut_gl5_matchrec17() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecZ, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['/', 'o', 'n', 'e', '/', 't', 'e', 's', 't'];
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
// matchrec18  (pat='/**/test' path='/test' opts=DEF expected=true fuel=9)
proof fn ut_gl5_matchrec18() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecZ, TokenS::Lit('t'), TokenS::Lit('e'), TokenS::Lit('s'), TokenS::Lit('t')];
    let path = seq!['/', 't', 'e', 's', 't'];
    let fuel: nat = 9 as nat;
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

} // verus!

fn main() {}
