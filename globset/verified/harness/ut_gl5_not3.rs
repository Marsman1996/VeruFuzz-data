//! GL5 weld corpus -- the 10 vectors of not3
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
// matchnot21  (pat='./foo' path='foo' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot21() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('.'), TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')];
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
    assert(tokens.len() == 5);
    assert(tokens.subrange(0, 5).len() == 5);
    assert(tokens.subrange(0, 5).index(0) == TokenS::Lit('.'));
    assert(spec_suffix_walk(tokens.subrange(5, 5), seq!['.', '/', 'f', 'o', 'o'], 0) == Some(seq!['.', '/', 'f', 'o', 'o'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(0, 5), Seq::empty(), 6) == Some(seq!['.', '/', 'f', 'o', 'o']));
    assert(spec_literal(opts, tokens) == Some(seq!['.', '/', 'f', 'o', 'o']));
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == Some(seq!['.', '/', 'f', 'o', 'o']));
    assert(spec_suffix(opts, tokens) == Some((seq!['.', '/', 'f', 'o', 'o'], false)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Literal(seq!['.', '/', 'f', 'o', 'o']));
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['.', '/', 'f', 'o', 'o']), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Literal(seq!['.', '/', 'f', 'o', 'o']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot22  (pat='**/foo' path='foofoo' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot22() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')];
    let path = seq!['f', 'o', 'o', 'f', 'o', 'o'];
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
    assert(tokens.len() == 4);
    assert(tokens.subrange(1, 4).len() == 3);
    assert(tokens.subrange(1, 4).index(0) == TokenS::Lit('f'));
    assert(spec_suffix_walk(tokens.subrange(4, 4), seq!['/', 'f', 'o', 'o'], 0) == Some(seq!['/', 'f', 'o', 'o'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 4), seq!['/'], 5) == Some(seq!['/', 'f', 'o', 'o']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == None);
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['/', 'f', 'o', 'o'], true)));
    assert(spec_basename_tokens(opts, tokens) == Some(seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]));
    assert(spec_basename_literal(opts, tokens) == Some(seq!['f', 'o', 'o']));
    assert(spec_c_basename(path) == seq!['f', 'o', 'o', 'f', 'o', 'o']);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::BasenameLiteral(seq!['f', 'o', 'o']));
    assert(spec_strat_check(opts, MatchStrategyS::BasenameLiteral(seq!['f', 'o', 'o']), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::BasenameLiteral(seq!['f', 'o', 'o']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot23  (pat='**/foo/bar' path='foofoo/bar' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot23() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')];
    let path = seq!['f', 'o', 'o', 'f', 'o', 'o', '/', 'b', 'a', 'r'];
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
    assert(path.len() == 10);
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].len() == 8);
    assert(path.index(2) == 'o');
    assert(path.index(3) == 'f');
    assert(path.index(4) == 'o');
    assert(path.index(5) == 'o');
    assert(path.index(6) == '/');
    assert(path.index(7) == 'b');
    assert(path.index(8) == 'a');
    assert(path.index(9) == 'r');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(0) == '/');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(1) == 'f');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(2) == 'o');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(3) == 'o');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(4) == '/');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(5) == 'b');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(6) == 'a');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(7) == 'r');
    assert(path.index(2) == 'o');
    assert(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].index(0) == '/');
    assert(spec_c_ends_with(seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], path) == false);
    let wsubc = seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'].subrange(1, 8 as int);
    assert(wsubc.len() == 7 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], component: true });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], component: true }, tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['/', 'f', 'o', 'o', '/', 'b', 'a', 'r'], component: true }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot24  (pat='/*.c' path='mozilla-sha1/sha1.c' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot24() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('c')];
    let path = seq!['m', 'o', 'z', 'i', 'l', 'l', 'a', '-', 's', 'h', 'a', '1', '/', 's', 'h', 'a', '1', '.', 'c'];
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
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 'c']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_ext(path) == seq!['.', 'c']);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::RequiredExtension(seq!['.', 'c']));
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 'c']), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 'c']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot25  (pat='*.c' path='mozilla-sha1/sha1.c' opts=SLASHLIT expected=false fuel=2)
proof fn ut_gl5_matchnot25() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('c')];
    let path = seq!['m', 'o', 'z', 'i', 'l', 'l', 'a', '-', 's', 'h', 'a', '1', '/', 's', 'h', 'a', '1', '.', 'c'];
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
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 'c']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == None);
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(spec_c_ext(path) == seq!['.', 'c']);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::RequiredExtension(seq!['.', 'c']));
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 'c']), tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::RequiredExtension(seq!['.', 'c']), tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot26  (pat='**/m4/ltoptions.m4' path='csharp/src/packages/repositories.config' opts=SLASHLIT expected=false fuel=2)
proof fn ut_gl5_matchnot26() {
    let opts = GlobOptions { literal_separator: true, ..spec_opts_unix_default() };
    let tokens = seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('s'), TokenS::Lit('.'), TokenS::Lit('m'), TokenS::Lit('4')];
    let path = seq!['c', 's', 'h', 'a', 'r', 'p', '/', 's', 'r', 'c', '/', 'p', 'a', 'c', 'k', 'a', 'g', 'e', 's', '/', 'r', 'e', 'p', 'o', 's', 'i', 't', 'o', 'r', 'i', 'e', 's', '.', 'c', 'o', 'n', 'f', 'i', 'g'];
    let fuel: nat = 2 as nat;
    let crev: nat = 41 as nat; // the reveal budget (>= fuel, >= path scan)
    reveal_with_fuel(spec_tm_at, 41);
    reveal_with_fuel(spec_tm_recp_star, 41);
    reveal_with_fuel(spec_tm_dot_star, 41);
    reveal_with_fuel(spec_tm_recz_tail, 41);
    reveal_with_fuel(spec_tm_all_chars, 41);
    reveal_with_fuel(spec_tm_alts_try, 41);
    reveal_with_fuel(spec_tm_mid_try, 123);
    reveal_with_fuel(spec_tok_emits, 41);
    reveal_with_fuel(spec_tok_seq_emits, 41);
    reveal_with_fuel(spec_seq_emits_upto, 41);
    reveal_with_fuel(spec_pats_kept_scan, 41);
    reveal_with_fuel(spec_cls_member_upto, 41);
    reveal_with_fuel(spec_last_slash_upto, 41);
    reveal_with_fuel(spec_last_dot_upto, 41);
    reveal_with_fuel(spec_lit_walk, 24);
    reveal_with_fuel(spec_ext_walk, 24);
    reveal_with_fuel(spec_req_ext_walk, 24);
    reveal_with_fuel(spec_prefix_walk, 24);
    reveal_with_fuel(spec_suffix_walk, 24);
    reveal_with_fuel(spec_basename_literal_walk, 24);
    reveal_with_fuel(spec_basename_gate_scan, 24);
    reveal_with_fuel(spec_ranges_slash_upto, 16);
    assert(tokens.len() == 16);
    assert(tokens.subrange(1, 16).len() == 15);
    assert(tokens.subrange(1, 16).index(0) == TokenS::Lit('m'));
    assert(spec_suffix_walk(tokens.subrange(16, 16), seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'], 0) == Some(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'])) by (compute);
    assert(spec_suffix_walk(tokens.subrange(1, 16), seq!['/'], 17) == Some(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4']));
    assert(spec_literal(opts, tokens) == None);
    assert(spec_ext(opts, tokens) == None);
    assert(spec_required_ext(opts, tokens) == Some(seq!['.', 'm', '4']));
    assert(spec_prefix(opts, tokens) == None);
    assert(spec_suffix(opts, tokens) == Some((seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'], true)));
    assert(spec_basename_tokens(opts, tokens) == None);
    assert(spec_basename_literal(opts, tokens) == None);
    assert(path.len() == 39);
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].len() == 16);
    assert(path.index(23) == 'o');
    assert(path.index(24) == 's');
    assert(path.index(25) == 'i');
    assert(path.index(26) == 't');
    assert(path.index(27) == 'o');
    assert(path.index(28) == 'r');
    assert(path.index(29) == 'i');
    assert(path.index(30) == 'e');
    assert(path.index(31) == 's');
    assert(path.index(32) == '.');
    assert(path.index(33) == 'c');
    assert(path.index(34) == 'o');
    assert(path.index(35) == 'n');
    assert(path.index(36) == 'f');
    assert(path.index(37) == 'i');
    assert(path.index(38) == 'g');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(0) == '/');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(1) == 'm');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(2) == '4');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(3) == '/');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(4) == 'l');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(5) == 't');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(6) == 'o');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(7) == 'p');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(8) == 't');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(9) == 'i');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(10) == 'o');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(11) == 'n');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(12) == 's');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(13) == '.');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(14) == 'm');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(15) == '4');
    assert(path.index(23) == 'o');
    assert(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].index(0) == '/');
    assert(spec_c_ends_with(seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'], path) == false);
    let wsubc = seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'].subrange(1, 16 as int);
    assert(wsubc.len() == 15 as int);
    assert((path == wsubc) == false);
    assert(spec_match_strategy(opts, tokens, 24) == MatchStrategyS::Suffix { suffix: seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'], component: true });
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'], component: true }, tokens, path, fuel) == false);
    assert(spec_tokens_match(opts, tokens, path, fuel) == false);
    assert(spec_strat_check(opts, MatchStrategyS::Suffix { suffix: seq!['/', 'm', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'], component: true }, tokens, path, fuel)
        == spec_tokens_match(opts, tokens, path, fuel));
}
// matchnot27  (pat='a[^0-9]b' path='a0b' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot27() {
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
// matchnot28  (pat='a[^0-9]b' path='a9b' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot28() {
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
// matchnot29  (pat='[^-]' path='-' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot29() {
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
// matchnot30  (pat='some/*/needle.txt' path='some/needle.txt' opts=DEF expected=false fuel=2)
proof fn ut_gl5_matchnot30() {
    let opts = spec_opts_unix_default();
    let tokens = seq![TokenS::Lit('s'), TokenS::Lit('o'), TokenS::Lit('m'), TokenS::Lit('e'), TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('n'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('d'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('.'), TokenS::Lit('t'), TokenS::Lit('x'), TokenS::Lit('t')];
    let path = seq!['s', 'o', 'm', 'e', '/', 'n', 'e', 'e', 'd', 'l', 'e', '.', 't', 'x', 't'];
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

} // verus!

fn main() {}
