//! GL5 weld corpus -- the 8 vectors of pat
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
// matchpat1  (pat='*hello.txt' path='hello.txt' opts=DEF expected=true fuel=14)
proof fn ut_gl5_matchpat1() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'];
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
    assert(path.len() == 9);
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 9);
    assert(path.index(0) == 'h');
    assert(path.index(1) == 'e');
    assert(path.index(2) == 'l');
    assert(path.index(3) == 'l');
    assert(path.index(4) == 'o');
    assert(path.index(5) == '.');
    assert(path.index(6) == 't');
    assert(path.index(7) == 'x');
    assert(path.index(8) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'e');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == 'o');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == '.');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 'x');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 't');
    assert forall|i: int| 0 <= i <= 8 implies path.index(0 + i) == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(i) by {
    }
    let wsub = path.subrange(0, 9);
    assert(wsub.len() == 9);
    assert(wsub == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']);
    assert(spec_c_ends_with(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == true);
    let wsubc = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 9 as int);
    assert(wsubc.len() == 8 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchpat2  (pat='*hello.txt' path='gareth_says_hello.txt' opts=DEF expected=true fuel=26)
proof fn ut_gl5_matchpat2() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['g', 'a', 'r', 'e', 't', 'h', '_', 's', 'a', 'y', 's', '_', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'];
    let fuel: nat = 26 as nat;
    let crev: nat = 26 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 26);
    reveal_with_fuel(spec_tm_recp_star, 26);
    reveal_with_fuel(spec_tm_dot_star, 26);
    reveal_with_fuel(spec_tm_recz_tail, 26);
    reveal_with_fuel(spec_tm_all_chars, 26);
    reveal_with_fuel(spec_tm_alts_try, 26);
    reveal_with_fuel(spec_tm_mid_try, 78);
    reveal_with_fuel(spec_tok_emits, 26);
    reveal_with_fuel(spec_tok_seq_emits, 26);
    reveal_with_fuel(spec_seq_emits_upto, 26);
    reveal_with_fuel(spec_pats_kept_scan, 26);
    reveal_with_fuel(spec_cls_member_upto, 26);
    reveal_with_fuel(spec_last_slash_upto, 26);
    reveal_with_fuel(spec_last_dot_upto, 26);
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
    assert(path.len() == 21);
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 9);
    assert(path.index(12) == 'h');
    assert(path.index(13) == 'e');
    assert(path.index(14) == 'l');
    assert(path.index(15) == 'l');
    assert(path.index(16) == 'o');
    assert(path.index(17) == '.');
    assert(path.index(18) == 't');
    assert(path.index(19) == 'x');
    assert(path.index(20) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'e');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == 'o');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == '.');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 'x');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 't');
    assert forall|i: int| 0 <= i <= 8 implies path.index(12 + i) == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(i) by {
    }
    let wsub = path.subrange(12, 21);
    assert(wsub.len() == 9);
    assert(wsub == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']);
    assert(spec_c_ends_with(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == true);
    let wsubc = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 9 as int);
    assert(wsubc.len() == 8 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchpat3  (pat='*hello.txt' path='some/path/to/hello.txt' opts=DEF expected=true fuel=27)
proof fn ut_gl5_matchpat3() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'];
    let fuel: nat = 27 as nat;
    let crev: nat = 27 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 27);
    reveal_with_fuel(spec_tm_recp_star, 27);
    reveal_with_fuel(spec_tm_dot_star, 27);
    reveal_with_fuel(spec_tm_recz_tail, 27);
    reveal_with_fuel(spec_tm_all_chars, 27);
    reveal_with_fuel(spec_tm_alts_try, 27);
    reveal_with_fuel(spec_tm_mid_try, 81);
    reveal_with_fuel(spec_tok_emits, 27);
    reveal_with_fuel(spec_tok_seq_emits, 27);
    reveal_with_fuel(spec_seq_emits_upto, 27);
    reveal_with_fuel(spec_pats_kept_scan, 27);
    reveal_with_fuel(spec_cls_member_upto, 27);
    reveal_with_fuel(spec_last_slash_upto, 27);
    reveal_with_fuel(spec_last_dot_upto, 27);
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
    assert(path.len() == 22);
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 9);
    assert(path.index(13) == 'h');
    assert(path.index(14) == 'e');
    assert(path.index(15) == 'l');
    assert(path.index(16) == 'l');
    assert(path.index(17) == 'o');
    assert(path.index(18) == '.');
    assert(path.index(19) == 't');
    assert(path.index(20) == 'x');
    assert(path.index(21) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'e');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == 'o');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == '.');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 'x');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 't');
    assert forall|i: int| 0 <= i <= 8 implies path.index(13 + i) == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(i) by {
    }
    let wsub = path.subrange(13, 22);
    assert(wsub.len() == 9);
    assert(wsub == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']);
    assert(spec_c_ends_with(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == true);
    let wsubc = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 9 as int);
    assert(wsubc.len() == 8 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchpat4  (pat='*hello.txt' path='some\\path\\to\\hello.txt' opts=DEF expected=true fuel=27)
proof fn ut_gl5_matchpat4() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '\\', 'p', 'a', 't', 'h', '\\', 't', 'o', '\\', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'];
    let fuel: nat = 27 as nat;
    let crev: nat = 27 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 27);
    reveal_with_fuel(spec_tm_recp_star, 27);
    reveal_with_fuel(spec_tm_dot_star, 27);
    reveal_with_fuel(spec_tm_recz_tail, 27);
    reveal_with_fuel(spec_tm_all_chars, 27);
    reveal_with_fuel(spec_tm_alts_try, 27);
    reveal_with_fuel(spec_tm_mid_try, 81);
    reveal_with_fuel(spec_tok_emits, 27);
    reveal_with_fuel(spec_tok_seq_emits, 27);
    reveal_with_fuel(spec_seq_emits_upto, 27);
    reveal_with_fuel(spec_pats_kept_scan, 27);
    reveal_with_fuel(spec_cls_member_upto, 27);
    reveal_with_fuel(spec_last_slash_upto, 27);
    reveal_with_fuel(spec_last_dot_upto, 27);
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
    assert(path.len() == 22);
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 9);
    assert(path.index(13) == 'h');
    assert(path.index(14) == 'e');
    assert(path.index(15) == 'l');
    assert(path.index(16) == 'l');
    assert(path.index(17) == 'o');
    assert(path.index(18) == '.');
    assert(path.index(19) == 't');
    assert(path.index(20) == 'x');
    assert(path.index(21) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'e');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == 'o');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == '.');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 'x');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 't');
    assert forall|i: int| 0 <= i <= 8 implies path.index(13 + i) == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(i) by {
    }
    let wsub = path.subrange(13, 22);
    assert(wsub.len() == 9);
    assert(wsub == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']);
    assert(spec_c_ends_with(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == true);
    let wsubc = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 9 as int);
    assert(wsubc.len() == 8 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchpat5  (pat='*hello.txt' path='/an/absolute/path/to/hello.txt' opts=DEF expected=true fuel=35)
proof fn ut_gl5_matchpat5() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['/', 'a', 'n', '/', 'a', 'b', 's', 'o', 'l', 'u', 't', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'];
    let fuel: nat = 35 as nat;
    let crev: nat = 35 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 35);
    reveal_with_fuel(spec_tm_recp_star, 35);
    reveal_with_fuel(spec_tm_dot_star, 35);
    reveal_with_fuel(spec_tm_recz_tail, 35);
    reveal_with_fuel(spec_tm_all_chars, 35);
    reveal_with_fuel(spec_tm_alts_try, 35);
    reveal_with_fuel(spec_tm_mid_try, 105);
    reveal_with_fuel(spec_tok_emits, 35);
    reveal_with_fuel(spec_tok_seq_emits, 35);
    reveal_with_fuel(spec_seq_emits_upto, 35);
    reveal_with_fuel(spec_pats_kept_scan, 35);
    reveal_with_fuel(spec_cls_member_upto, 35);
    reveal_with_fuel(spec_last_slash_upto, 35);
    reveal_with_fuel(spec_last_dot_upto, 35);
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
    assert(path.len() == 30);
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 9);
    assert(path.index(21) == 'h');
    assert(path.index(22) == 'e');
    assert(path.index(23) == 'l');
    assert(path.index(24) == 'l');
    assert(path.index(25) == 'o');
    assert(path.index(26) == '.');
    assert(path.index(27) == 't');
    assert(path.index(28) == 'x');
    assert(path.index(29) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(0) == 'h');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(1) == 'e');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(2) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(3) == 'l');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(4) == 'o');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(5) == '.');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(6) == 't');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(7) == 'x');
    assert(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(8) == 't');
    assert forall|i: int| 0 <= i <= 8 implies path.index(21 + i) == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(i) by {
    }
    let wsub = path.subrange(21, 30);
    assert(wsub.len() == 9);
    assert(wsub == seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']);
    assert(spec_c_ends_with(seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == true);
    let wsubc = seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 9 as int);
    assert(wsubc.len() == 8 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchpat6  (pat='*some/path/to/hello.txt' path='some/path/to/hello.txt' opts=DEF expected=true fuel=27)
proof fn ut_gl5_matchpat6() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::Lit('/'), TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('/'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'];
    let fuel: nat = 27 as nat;
    let crev: nat = 27 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 27);
    reveal_with_fuel(spec_tm_recp_star, 27);
    reveal_with_fuel(spec_tm_dot_star, 27);
    reveal_with_fuel(spec_tm_recz_tail, 27);
    reveal_with_fuel(spec_tm_all_chars, 27);
    reveal_with_fuel(spec_tm_alts_try, 27);
    reveal_with_fuel(spec_tm_mid_try, 81);
    reveal_with_fuel(spec_tok_emits, 27);
    reveal_with_fuel(spec_tok_seq_emits, 27);
    reveal_with_fuel(spec_seq_emits_upto, 27);
    reveal_with_fuel(spec_pats_kept_scan, 27);
    reveal_with_fuel(spec_cls_member_upto, 27);
    reveal_with_fuel(spec_last_slash_upto, 27);
    reveal_with_fuel(spec_last_dot_upto, 27);
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
    assert(path.len() == 22);
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 22);
    assert(path.index(0) == 's');
    assert(path.index(1) == 'o');
    assert(path.index(2) == 'm');
    assert(path.index(3) == 'e');
    assert(path.index(4) == '/');
    assert(path.index(5) == 'p');
    assert(path.index(6) == 'a');
    assert(path.index(7) == 't');
    assert(path.index(8) == 'h');
    assert(path.index(9) == '/');
    assert(path.index(10) == 't');
    assert(path.index(11) == 'o');
    assert(path.index(12) == '/');
    assert(path.index(13) == 'h');
    assert(path.index(14) == 'e');
    assert(path.index(15) == 'l');
    assert(path.index(16) == 'l');
    assert(path.index(17) == 'o');
    assert(path.index(18) == '.');
    assert(path.index(19) == 't');
    assert(path.index(20) == 'x');
    assert(path.index(21) == 't');
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
    assert forall|i: int| 0 <= i <= 21 implies path.index(0 + i) == seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(i) by {
    }
    let wsub = path.subrange(0, 22);
    assert(wsub.len() == 22);
    assert(wsub == seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']);
    assert(spec_c_ends_with(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == true);
    let wsubc = seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 22 as int);
    assert(wsubc.len() == 21 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchpat7  (pat='*some/path/to/hello.txt' path='a/bigger/some/path/to/hello.txt' opts=DEF expected=true fuel=36)
proof fn ut_gl5_matchpat7() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Zom, TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::Lit('/'), TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('/'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('h'), TokenS::Lit('e'), TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['a', '/', 'b', 'i', 'g', 'g', 'e', 'r', '/', 's', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'];
    let fuel: nat = 36 as nat;
    let crev: nat = 36 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 36);
    reveal_with_fuel(spec_tm_recp_star, 36);
    reveal_with_fuel(spec_tm_dot_star, 36);
    reveal_with_fuel(spec_tm_recz_tail, 36);
    reveal_with_fuel(spec_tm_all_chars, 36);
    reveal_with_fuel(spec_tm_alts_try, 36);
    reveal_with_fuel(spec_tm_mid_try, 108);
    reveal_with_fuel(spec_tok_emits, 36);
    reveal_with_fuel(spec_tok_seq_emits, 36);
    reveal_with_fuel(spec_seq_emits_upto, 36);
    reveal_with_fuel(spec_pats_kept_scan, 36);
    reveal_with_fuel(spec_cls_member_upto, 36);
    reveal_with_fuel(spec_last_slash_upto, 36);
    reveal_with_fuel(spec_last_dot_upto, 36);
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
    assert(path.len() == 31);
    assert(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].len() == 22);
    assert(path.index(9) == 's');
    assert(path.index(10) == 'o');
    assert(path.index(11) == 'm');
    assert(path.index(12) == 'e');
    assert(path.index(13) == '/');
    assert(path.index(14) == 'p');
    assert(path.index(15) == 'a');
    assert(path.index(16) == 't');
    assert(path.index(17) == 'h');
    assert(path.index(18) == '/');
    assert(path.index(19) == 't');
    assert(path.index(20) == 'o');
    assert(path.index(21) == '/');
    assert(path.index(22) == 'h');
    assert(path.index(23) == 'e');
    assert(path.index(24) == 'l');
    assert(path.index(25) == 'l');
    assert(path.index(26) == 'o');
    assert(path.index(27) == '.');
    assert(path.index(28) == 't');
    assert(path.index(29) == 'x');
    assert(path.index(30) == 't');
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
    assert forall|i: int| 0 <= i <= 21 implies path.index(9 + i) == seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].index(i) by {
    }
    let wsub = path.subrange(9, 31);
    assert(wsub.len() == 22);
    assert(wsub == seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't']);
    assert(spec_c_ends_with(seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], path) == true);
    let wsubc = seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'].subrange(1, 22 as int);
    assert(wsubc.len() == 21 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel) == true);
    assert(spec_tokens_match(opts, tokens, path, fuel) == true);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['s', 'o', 'm', 'e', '/', 'p', 'a', 't', 'h', '/', 't', 'o', '/', 'h', 'e', 'l', 'l', 'o', '.', 't', 'x', 't'], component: false }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchescape  (pat='_[[]_[]]_[?]_[*]_!_' path='_[_]_?_*_!_' opts=DEF expected=true fuel=15)
proof fn ut_gl5_matchescape() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('_'), TokenS::Cls { negated: false, ranges: seq![('[', '[')] }, TokenS::Lit('_'), TokenS::Cls { negated: false, ranges: seq![(']', ']')] }, TokenS::Lit('_'), TokenS::Cls { negated: false, ranges: seq![('?', '?')] }, TokenS::Lit('_'), TokenS::Cls { negated: false, ranges: seq![('*', '*')] }, TokenS::Lit('_'), TokenS::Lit('!'), TokenS::Lit('_')];
    let path = seq!['_', '[', '_', ']', '_', '?', '_', '*', '_', '!', '_'];
    let fuel: nat = 15 as nat;
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
