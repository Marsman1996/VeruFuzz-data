//! GL5 weld corpus -- the 8 vectors of basename
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
// basename_empty  (pat='**/*' path='' opts=SLASHLIT expected=true fuel=6)
proof fn ut_gl5_basename_empty() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Zom];
    let path = seq![];
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
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Zom]));
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_base_for_regex(path) == seq![]);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// basename_trailing_separator  (pat='**/*' path='foo/' opts=SLASHLIT expected=true fuel=10)
proof fn ut_gl5_basename_trailing_separator() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Zom];
    let path = seq!['f', 'o', 'o', '/'];
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
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Zom]));
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_base_for_regex(path) == seq![]);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// basename_parent_component  (pat='**/.*' path='foo/..' opts=SLASHLIT expected=true fuel=12)
proof fn ut_gl5_basename_parent_component() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Lit('.'), TokenS::Zom];
    let path = seq!['f', 'o', 'o', '/', '.', '.'];
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
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Lit('.'), TokenS::Zom]));
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_base_for_regex(path) == seq!['.', '.']);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// basename_class  (pat='**/*.py[cod]' path='src/module.pyc' opts=SLASHLIT expected=true fuel=20)
proof fn ut_gl5_basename_class() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('p'), TokenS::Lit('y'), TokenS::Cls { negated: false, ranges: seq![('c', 'c'), ('o', 'o'), ('d', 'd')] }];
    let path = seq!['s', 'r', 'c', '/', 'm', 'o', 'd', 'u', 'l', 'e', '.', 'p', 'y', 'c'];
    let fuel: nat = 20 as nat;
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
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('p'), TokenS::Lit('y'), TokenS::Cls { negated: false, ranges: seq![('c', 'c'), ('o', 'o'), ('d', 'd')] }]));
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_base_for_regex(path) == seq!['m', 'o', 'd', 'u', 'l', 'e', '.', 'p', 'y', 'c']);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// basename_negated_class  (pat='**/[!/]' path='foo/a' opts=SLASHLIT expected=true fuel=10)
proof fn ut_gl5_basename_negated_class() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Cls { negated: true, ranges: seq![('/', '/')] }];
    let path = seq!['f', 'o', 'o', '/', 'a'];
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
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Cls { negated: true, ranges: seq![('/', '/')] }]));
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_base_for_regex(path) == seq!['a']);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// class_includes_separator  (pat='**/[!a]' path='/' opts=SLASHLIT expected=true fuel=6)
proof fn ut_gl5_class_includes_separator() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Cls { negated: true, ranges: seq![('a', 'a')] }];
    let path = seq!['/'];
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
// class_separator_range  (pat='**/[.-0]' path='/' opts=SLASHLIT expected=true fuel=6)
proof fn ut_gl5_class_separator_range() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Cls { negated: false, ranges: seq![('.', '0')] }];
    let path = seq!['/'];
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
// basename_class_miss  (pat='**/*.py[cod]' path='src/module.pyi' opts=SLASHLIT expected=false fuel=2)
proof fn ut_gl5_basename_class_miss() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('p'), TokenS::Lit('y'), TokenS::Cls { negated: false, ranges: seq![('c', 'c'), ('o', 'o'), ('d', 'd')] }];
    let path = seq!['s', 'r', 'c', '/', 'm', 'o', 'd', 'u', 'l', 'e', '.', 'p', 'y', 'i'];
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
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('p'), TokenS::Lit('y'), TokenS::Cls { negated: false, ranges: seq![('c', 'c'), ('o', 'o'), ('d', 'd')] }]));
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_base_for_regex(path) == seq!['m', 'o', 'd', 'u', 'l', 'e', '.', 'p', 'y', 'i']);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameRegex(Seq::empty()), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}

} // verus!

fn main() {}
