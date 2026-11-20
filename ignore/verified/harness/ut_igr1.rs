//! IG-R harness ut_igr1 -- the GlobBuilder-verdict re-anchor unit, the
//! ladder-row regeneration EXECUTED (pit #IG-R-1's prescription, at
//! the IG-R2 window): every DISTINCT (actual, case-flag,
//! unclosed-class toggle) admit instance the ut_ig2/ut_ig3 harness
//! rows consume -- 87 of them, grep-verified complete -- with the
//! verdict machine-checked through GL2's parse value machine by
//! PER-PASS ground state rungs plus three small symbolic lemmas
//! (sstate_eq: the fieldwise state congruence; ladder_step: the
//! budget-descent identity; loop_terminal: the end-of-pattern arm).
//!
//! Why ladders: the ground by(compute) route hangs on star-composite
//! shapes (the '**/'-prefixed bulk of this domain; probes p4a/p5b/p7/
//! p10 of the IG-R batch), and whole-state datatype equality is not
//! derivable fieldwise inline (the p17 expansion evidence: all six
//! fields provable, the constructor injectivity axiom not triggered);
//! splitting the rung into field asserts plus a standalone sstate_eq
//! congruence query closes cleanly (probe p19, 264/0).
//!
//! Trace provenance: the per-pass states come from the GL2 mirror
//! machine (the plain-Rust spec twin, twotree 81/81-validated)
//! instrumented one-pass-per-snapshot (out/kverus-run/IG-R/
//! spec_dump.rs); the trace's verdicts were shadow-checked against
//! the admit truth values 87/87 AGREE before any row was emitted.
//!
//! The admit rows themselves stay put in ut_ig2/ut_ig3 (the
//! uninterp-oracle seam, runtime-column backed); this unit is the
//! formal side of those seams, instance by instance.

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

#[path = "../../../globset/verified/src/lib.rs"]
mod glib;

#[allow(unused_imports)]
use glib::CowBytes;
#[allow(unused_imports)]
use glib::pathutil;

use glib::glob::{
    ErrorKind, GlobOptions, SState, TokenS, spec_parse_class, spec_parse_glob,
    spec_parse_loop, spec_class_loop, spec_parse_star, spec_utf8_encode,
};

verus! {

// The Seq update/push/index axiom broadcast (the twin convention: every
// module mounting Seq mutation facts carries this; without it the
// field-eq rungs over growing branch lists stall).
broadcast use vstd::seq::group_seq_axioms;

/// The call-site options the ignore crate passes to GlobBuilder
/// (upstream gitignore.rs:531-540; empty_alternates stays the
/// upstream default -- the call site never touches it).
pub open spec fn igr_opts(ci: bool, auc: bool) -> GlobOptions {
    GlobOptions {
        case_insensitive: ci,
        literal_separator: true,
        backslash_escape: true,
        empty_alternates: false,
        allow_unclosed_class: auc,
    }
}

/// The char form's utf8 bytes: GL's own encode lane table folded over
/// the char sequence, prefix-style (the byte-tie carrier).
pub open spec fn igr_utf8_of_upto(cs: Seq<char>, i: nat) -> Seq<u8>
    decreases i
{
    if i == 0 {
        Seq::empty()
    } else {
        igr_utf8_of_upto(cs, (i - 1) as nat)
            + spec_utf8_encode(cs.index((i - 1) as int) as u32)
    }
}

/// The full fold (the byte actual the admit rows carry).
pub open spec fn igr_utf8_of(cs: Seq<char>) -> Seq<u8> {
    igr_utf8_of_upto(cs, cs.len() as nat)
}

/// The state congruence: a small standalone query where the datatype
/// injector axiom instantiates cleanly (the p17/p19 evidence).
pub proof fn sstate_eq(x: SState, y: SState)
    requires
        x.chars == y.chars,
        x.stack == y.stack,
        x.brs == y.brs,
        x.pos == y.pos,
        x.unclosed == y.unclosed,
        x.opts == y.opts,
    ensures x == y
{
}

/// The budget-descent identity: one full-budget pass equals the
/// one-budget run plus the recursive remainder (purely symbolic).
pub proof fn ladder_step(st: SState, w: bool, b: int)
    requires
        1 <= b,
        st.pos < st.chars.len(),
    ensures
        spec_parse_loop(st, w, b)
            == if spec_parse_loop(st, w, 1).1 is Some {
                spec_parse_loop(st, w, 1)
            } else {
                spec_parse_loop(spec_parse_loop(st, w, 1).0, w, b - 1)
            }
{
    reveal_with_fuel(spec_parse_loop, 3);
}

/// The end-of-pattern arm: any budget returns the terminal state
/// unchanged with None (purely symbolic).
pub proof fn loop_terminal(st: SState, w: bool, b: int)
    requires st.pos >= st.chars.len()
    ensures spec_parse_loop(st, w, b) == (st, None)
{
    reveal_with_fuel(spec_parse_loop, 2);
}

/// Admit seam instance 0 (actual bytes [], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_slash_root). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b00_() {
    let cs: Seq<char> = seq![];
    reveal_with_fuel(igr_utf8_of_upto, 2);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of(cs) == seq![]);
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    loop_terminal(stf, false, 16);
    assert(spec_parse_loop(stf, false, 16) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 0);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![]));
}

/// Admit seam instance 1 (actual bytes [2A 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig30_ds_dir). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b01_stst() {
    let cs: Seq<char> = seq!['*', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 4);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == stf.chars);
    assert(L0.0.stack == stf.stack);
    assert(L0.0.brs.len() == stf.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == stf.brs.index(0));
    assert(L0.0.brs == stf.brs);
    assert(L0.0.pos == stf.pos);
    assert(L0.0.unclosed == stf.unclosed);
    assert(L0.0.opts == stf.opts);
    sstate_eq(L0.0, stf);
    assert(L0 == (stf, None));
    ladder_step(st0, false, 20);
    loop_terminal(stf, false, 19);
    assert(spec_parse_loop(st0, false, 20) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 1);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP]));
}

/// Admit seam instance 2 (actual bytes [2A 2A 2F], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_bare_bang). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b02_ststsl() {
    let cs: Seq<char> = seq!['*', '*', '/'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    reveal_with_fuel(igr_utf8_of_upto, 5);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == stf.chars);
    assert(L0.0.stack == stf.stack);
    assert(L0.0.brs.len() == stf.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == stf.brs.index(0));
    assert(L0.0.brs == stf.brs);
    assert(L0.0.pos == stf.pos);
    assert(L0.0.unclosed == stf.unclosed);
    assert(L0.0.opts == stf.opts);
    sstate_eq(L0.0, stf);
    assert(L0 == (stf, None));
    ladder_step(st0, false, 22);
    loop_terminal(stf, false, 21);
    assert(spec_parse_loop(st0, false, 22) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 1);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP]));
}

/// Admit seam instance 3 (actual bytes [2A 2A 2F 20 23 66 6F 6F], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_comment_col0_only). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b03_ststslushafoo() {
    let cs: Seq<char> = seq!['*', '*', '/', ' ', '#', 'f', 'o', 'o'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert(' ' as u32 == 0x0020);
    assert('#' as u32 == 0x0023);
    assert('f' as u32 == 0x0066);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    reveal_with_fuel(igr_utf8_of_upto, 10);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x20]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x20, 0x23]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x20, 0x23, 0x66]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x20, 0x23, 0x66, 0x6F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x20, 0x23, 0x66, 0x6F, 0x6F]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x20, 0x23, 0x66, 0x6F, 0x6F]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit(' ')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit(' '), TokenS::Lit('#')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit(' '), TokenS::Lit('#'), TokenS::Lit('f')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit(' '), TokenS::Lit('#'), TokenS::Lit('f'), TokenS::Lit('o')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit(' '), TokenS::Lit('#'), TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 32);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit(' '));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 31);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit(' '));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('#'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 30);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit(' '));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('#'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 29);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit(' '));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('#'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 28);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == stf.chars);
    assert(L5.0.stack == stf.stack);
    assert(L5.0.brs.len() == stf.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit(' '));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('#'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0) == stf.brs.index(0));
    assert(L5.0.brs == stf.brs);
    assert(L5.0.pos == stf.pos);
    assert(L5.0.unclosed == stf.unclosed);
    assert(L5.0.opts == stf.opts);
    sstate_eq(L5.0, stf);
    assert(L5 == (stf, None));
    ladder_step(st5, false, 27);
    loop_terminal(stf, false, 26);
    assert(spec_parse_loop(st0, false, 32) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 6);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit(' '));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('#'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit(' '), TokenS::Lit('#'), TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]));
}

/// Admit seam instance 4 (actual bytes [2A 2A 2F 21 78 79], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig21_esc). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b04_ststslexxy() {
    let cs: Seq<char> = seq!['*', '*', '/', '!', 'x', 'y'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('!' as u32 == 0x0021);
    assert('x' as u32 == 0x0078);
    assert('y' as u32 == 0x0079);
    reveal_with_fuel(igr_utf8_of_upto, 8);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x21]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x21, 0x78]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x21, 0x78, 0x79]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x21, 0x78, 0x79]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('!')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('!'), TokenS::Lit('x')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('!'), TokenS::Lit('x'), TokenS::Lit('y')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 28);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('!'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 27);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('!'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('x'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 26);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == stf.chars);
    assert(L3.0.stack == stf.stack);
    assert(L3.0.brs.len() == stf.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('!'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('x'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('y'));
    assert(L3.0.brs.index(0) == stf.brs.index(0));
    assert(L3.0.brs == stf.brs);
    assert(L3.0.pos == stf.pos);
    assert(L3.0.unclosed == stf.unclosed);
    assert(L3.0.opts == stf.opts);
    sstate_eq(L3.0, stf);
    assert(L3 == (stf, None));
    ladder_step(st3, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 28) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 4);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('!'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('x'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('y'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('!'), TokenS::Lit('x'), TokenS::Lit('y')]));
}

/// Admit seam instance 5 (actual bytes [2A 2A 2F 23 66 6F 6F], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig22_esc). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b05_ststslhafoo() {
    let cs: Seq<char> = seq!['*', '*', '/', '#', 'f', 'o', 'o'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('#' as u32 == 0x0023);
    assert('f' as u32 == 0x0066);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x23]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x23, 0x66]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x23, 0x66, 0x6F]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x23, 0x66, 0x6F, 0x6F]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x23, 0x66, 0x6F, 0x6F]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('#')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('#'), TokenS::Lit('f')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('#'), TokenS::Lit('f'), TokenS::Lit('o')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('#'), TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('#'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('#'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('#'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 27);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == stf.chars);
    assert(L4.0.stack == stf.stack);
    assert(L4.0.brs.len() == stf.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('#'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0) == stf.brs.index(0));
    assert(L4.0.brs == stf.brs);
    assert(L4.0.pos == stf.pos);
    assert(L4.0.unclosed == stf.unclosed);
    assert(L4.0.opts == stf.opts);
    sstate_eq(L4.0, stf);
    assert(L4 == (stf, None));
    ladder_step(st4, false, 26);
    loop_terminal(stf, false, 25);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 5);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('#'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('#'), TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]));
}

/// Admit seam instance 6 (actual bytes [2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ignot16a_star). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b06_ststslst() {
    let cs: Seq<char> = seq!['*', '*', '/', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 6);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 24);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, None));
    ladder_step(st1, false, 23);
    loop_terminal(stf, false, 22);
    assert(spec_parse_loop(st0, false, 24) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 2);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Zom]));
}

/// Admit seam instance 7 (actual bytes [2A 2A 2F 2A 2A 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_star3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b07_ststslststst() {
    let cs: Seq<char> = seq!['*', '*', '/', '*', '*', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 8);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Zom]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Zom, TokenS::Zom]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 28);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 3);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L1.0.brs.index(0).index(2) == TokenS::Zom);
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 27);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 4);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(2) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(3) == TokenS::Zom);
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, None));
    ladder_step(st2, false, 26);
    loop_terminal(stf, false, 25);
    assert(spec_parse_loop(st0, false, 28) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 4);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Zom, TokenS::Zom, TokenS::Zom]));
}

/// Admit seam instance 9 (actual bytes [2A 2A 2F 2A 2E 52 53], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_skip_3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b09_ststslstdtRS() {
    let cs: Seq<char> = seq!['*', '*', '/', '*', '.', 'R', 'S'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('.' as u32 == 0x002E);
    assert('R' as u32 == 0x0052);
    assert('S' as u32 == 0x0053);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x52]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x52, 0x53]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x52, 0x53]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('R')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('R'), TokenS::Lit('S')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('R'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 27);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == stf.chars);
    assert(L4.0.stack == stf.stack);
    assert(L4.0.brs.len() == stf.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('R'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('S'));
    assert(L4.0.brs.index(0) == stf.brs.index(0));
    assert(L4.0.brs == stf.brs);
    assert(L4.0.pos == stf.pos);
    assert(L4.0.unclosed == stf.unclosed);
    assert(L4.0.opts == stf.opts);
    sstate_eq(L4.0, stf);
    assert(L4 == (stf, None));
    ladder_step(st4, false, 26);
    loop_terminal(stf, false, 25);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 5);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('R'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('S'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('R'), TokenS::Lit('S')]));
}

/// Admit seam instance 10 (actual bytes [2A 2A 2F 2A 2E 68 74 6D 6C], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_cs1). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b10_ststslstdthtml() {
    let cs: Seq<char> = seq!['*', '*', '/', '*', '.', 'h', 't', 'm', 'l'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('.' as u32 == 0x002E);
    assert('h' as u32 == 0x0068);
    assert('t' as u32 == 0x0074);
    assert('m' as u32 == 0x006D);
    assert('l' as u32 == 0x006C);
    reveal_with_fuel(igr_utf8_of_upto, 11);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h'), TokenS::Lit('t')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h'), TokenS::Lit('t'), TokenS::Lit('m')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h'), TokenS::Lit('t'), TokenS::Lit('m'), TokenS::Lit('l')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 34);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 33);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 32);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 31);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 30);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('m'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 29);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == stf.chars);
    assert(L6.0.stack == stf.stack);
    assert(L6.0.brs.len() == stf.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('m'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0) == stf.brs.index(0));
    assert(L6.0.brs == stf.brs);
    assert(L6.0.pos == stf.pos);
    assert(L6.0.unclosed == stf.unclosed);
    assert(L6.0.opts == stf.opts);
    sstate_eq(L6.0, stf);
    assert(L6 == (stf, None));
    ladder_step(st6, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 34) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 7);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('h'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h'), TokenS::Lit('t'), TokenS::Lit('m'), TokenS::Lit('l')]));
}

/// Admit seam instance 11 (actual bytes [2A 2A 2F 2A 2E 68 74 6D 6C], ci=true, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_skip_3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b11_ststslstdthtml_ci() {
    let cs: Seq<char> = seq!['*', '*', '/', '*', '.', 'h', 't', 'm', 'l'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('.' as u32 == 0x002E);
    assert('h' as u32 == 0x0068);
    assert('t' as u32 == 0x0074);
    assert('m' as u32 == 0x006D);
    assert('l' as u32 == 0x006C);
    reveal_with_fuel(igr_utf8_of_upto, 11);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x68, 0x74, 0x6D, 0x6C]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(true, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(true, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(true, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(true, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(true, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h'), TokenS::Lit('t')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(true, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h'), TokenS::Lit('t'), TokenS::Lit('m')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(true, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h'), TokenS::Lit('t'), TokenS::Lit('m'), TokenS::Lit('l')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(true, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 34);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 33);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 32);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 31);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 30);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('m'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 29);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == stf.chars);
    assert(L6.0.stack == stf.stack);
    assert(L6.0.brs.len() == stf.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('m'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0) == stf.brs.index(0));
    assert(L6.0.brs == stf.brs);
    assert(L6.0.pos == stf.pos);
    assert(L6.0.unclosed == stf.unclosed);
    assert(L6.0.opts == stf.opts);
    sstate_eq(L6.0, stf);
    assert(L6 == (stf, None));
    ladder_step(st6, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 34) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(true, true), false).get_Ok_0().len() == 7);
    assert(spec_parse_glob(cs, igr_opts(true, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(true, true), false).get_Ok_0().index(1) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(true, true), false).get_Ok_0().index(2) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(true, true), false).get_Ok_0().index(3) == TokenS::Lit('h'));
    assert(spec_parse_glob(cs, igr_opts(true, true), false).get_Ok_0().index(4) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(true, true), false).get_Ok_0().index(5) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(true, true), false).get_Ok_0().index(6) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(true, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('h'), TokenS::Lit('t'), TokenS::Lit('m'), TokenS::Lit('l')]));
}

/// Admit seam instance 12 (actual bytes [2A 2A 2F 2A 2E 6C 6F 63 6B], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig2). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b12_ststslstdtlock() {
    let cs: Seq<char> = seq!['*', '*', '/', '*', '.', 'l', 'o', 'c', 'k'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('.' as u32 == 0x002E);
    assert('l' as u32 == 0x006C);
    assert('o' as u32 == 0x006F);
    assert('c' as u32 == 0x0063);
    assert('k' as u32 == 0x006B);
    reveal_with_fuel(igr_utf8_of_upto, 11);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C, 0x6F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C, 0x6F, 0x63]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('l')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('l'), TokenS::Lit('o')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('c')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('c'), TokenS::Lit('k')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 34);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 33);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 32);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 31);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 30);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('c'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 29);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == stf.chars);
    assert(L6.0.stack == stf.stack);
    assert(L6.0.brs.len() == stf.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('c'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('k'));
    assert(L6.0.brs.index(0) == stf.brs.index(0));
    assert(L6.0.brs == stf.brs);
    assert(L6.0.pos == stf.pos);
    assert(L6.0.unclosed == stf.unclosed);
    assert(L6.0.opts == stf.opts);
    sstate_eq(L6.0, stf);
    assert(L6 == (stf, None));
    ladder_step(st6, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 34) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 7);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('c'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('k'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('c'), TokenS::Lit('k')]));
}

/// Admit seam instance 13 (actual bytes [2A 2A 2F 2A 2E 72 73], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b13_ststslstdtrs() {
    let cs: Seq<char> = seq!['*', '*', '/', '*', '.', 'r', 's'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('.' as u32 == 0x002E);
    assert('r' as u32 == 0x0072);
    assert('s' as u32 == 0x0073);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r'), TokenS::Lit('s')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 27);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == stf.chars);
    assert(L4.0.stack == stf.stack);
    assert(L4.0.brs.len() == stf.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('.'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('s'));
    assert(L4.0.brs.index(0) == stf.brs.index(0));
    assert(L4.0.brs == stf.brs);
    assert(L4.0.pos == stf.pos);
    assert(L4.0.unclosed == stf.unclosed);
    assert(L4.0.opts == stf.opts);
    sstate_eq(L4.0, stf);
    assert(L4 == (stf, None));
    ladder_step(st4, false, 26);
    loop_terminal(stf, false, 25);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 5);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r'), TokenS::Lit('s')]));
}

/// Admit seam instance 14 (actual bytes [2A 2A 2F 3F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_qstar). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b14_ststslqmst() {
    let cs: Seq<char> = seq!['*', '*', '/', '?', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('?' as u32 == 0x003F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x3F]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x3F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x3F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Any]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Any, TokenS::Zom]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Any);
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 25);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Any);
    assert(L2.0.brs.index(0).index(2) == TokenS::Zom);
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, None));
    ladder_step(st2, false, 24);
    loop_terminal(stf, false, 23);
    assert(spec_parse_loop(st0, false, 26) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 3);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Any);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Any, TokenS::Zom]));
}

/// Admit seam instance 15 (actual bytes [2A 2A 2F 43 61 72 67 6F 2E 6C 6F 63 6B], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig25_plain). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b15_ststslCargodtlock() {
    let cs: Seq<char> = seq!['*', '*', '/', 'C', 'a', 'r', 'g', 'o', '.', 'l', 'o', 'c', 'k'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('C' as u32 == 0x0043);
    assert('a' as u32 == 0x0061);
    assert('r' as u32 == 0x0072);
    assert('g' as u32 == 0x0067);
    assert('o' as u32 == 0x006F);
    assert('.' as u32 == 0x002E);
    assert('l' as u32 == 0x006C);
    assert('o' as u32 == 0x006F);
    assert('c' as u32 == 0x0063);
    assert('k' as u32 == 0x006B);
    reveal_with_fuel(igr_utf8_of_upto, 15);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x43]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x43, 0x61, 0x72, 0x67, 0x6F, 0x2E, 0x6C, 0x6F, 0x63, 0x6B]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('o')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('.')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('l')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('l'), TokenS::Lit('o')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('c')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('c'), TokenS::Lit('k')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 42);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 41);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 40);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 39);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 38);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 37);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('.'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 36);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('.'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 35);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('.'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 34);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('.'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('c'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 33);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == stf.chars);
    assert(L10.0.stack == stf.stack);
    assert(L10.0.brs.len() == stf.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('C'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('.'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('c'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('k'));
    assert(L10.0.brs.index(0) == stf.brs.index(0));
    assert(L10.0.brs == stf.brs);
    assert(L10.0.pos == stf.pos);
    assert(L10.0.unclosed == stf.unclosed);
    assert(L10.0.opts == stf.opts);
    sstate_eq(L10.0, stf);
    assert(L10 == (stf, None));
    ladder_step(st10, false, 32);
    loop_terminal(stf, false, 31);
    assert(spec_parse_loop(st0, false, 42) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 11);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('C'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('g'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('c'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('k'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('C'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('.'), TokenS::Lit('l'), TokenS::Lit('o'), TokenS::Lit('c'), TokenS::Lit('k')]));
}

/// Admit seam instance 16 (actual bytes [2A 2A 2F 5B 61 62 63], ci=false, auc=false,
/// admit truth false; provenance ut_ig2.rs kat_skip_3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b16_ststslbkabc_noauc() {
    let cs: Seq<char> = seq!['*', '*', '/', '[', 'a', 'b', 'c'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('[' as u32 == 0x005B);
    assert('a' as u32 == 0x0061);
    assert('b' as u32 == 0x0062);
    assert('c' as u32 == 0x0063);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5B]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62, 0x63]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62, 0x63]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, false),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, false),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, false),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    reveal_with_fuel(spec_parse_class, 1);
    reveal_with_fuel(spec_class_loop, 13);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 matches Some(_));
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 1);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, Some(ErrorKind::UnclosedClass)));
    assert(spec_parse_loop(st0, false, 30)
        == (stf, Some(ErrorKind::UnclosedClass)));
    assert(spec_parse_glob(cs, igr_opts(false, false), false)
        == Err(ErrorKind::UnclosedClass));
}

/// Admit seam instance 17 (actual bytes [2A 2A 2F 5B 61 62 63], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_skip_3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b17_ststslbkabc() {
    let cs: Seq<char> = seq!['*', '*', '/', '[', 'a', 'b', 'c'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('[' as u32 == 0x005B);
    assert('a' as u32 == 0x0061);
    assert('b' as u32 == 0x0062);
    assert('c' as u32 == 0x0063);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5B]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62, 0x63]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x61, 0x62, 0x63]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('[')]],
    pos: 4,
    unclosed: true,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('['), TokenS::Lit('a')]],
    pos: 5,
    unclosed: true,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('['), TokenS::Lit('a'), TokenS::Lit('b')]],
    pos: 6,
    unclosed: true,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('['), TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c')]],
    pos: 7,
    unclosed: true,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    reveal_with_fuel(spec_parse_class, 1);
    reveal_with_fuel(spec_class_loop, 13);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('b'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 27);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == stf.chars);
    assert(L4.0.stack == stf.stack);
    assert(L4.0.brs.len() == stf.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('b'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('c'));
    assert(L4.0.brs.index(0) == stf.brs.index(0));
    assert(L4.0.brs == stf.brs);
    assert(L4.0.pos == stf.pos);
    assert(L4.0.unclosed == stf.unclosed);
    assert(L4.0.opts == stf.opts);
    sstate_eq(L4.0, stf);
    assert(L4 == (stf, None));
    ladder_step(st4, false, 26);
    loop_terminal(stf, false, 25);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 5);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('['));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('c'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('['), TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c')]));
}

/// Admit seam instance 18 (actual bytes [2A 2A 2F 5B 66 6F 6F], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_bracket_foo). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b18_ststslbkfoo() {
    let cs: Seq<char> = seq!['*', '*', '/', '[', 'f', 'o', 'o'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('[' as u32 == 0x005B);
    assert('f' as u32 == 0x0066);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5B]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x66]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x66, 0x6F]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x66, 0x6F, 0x6F]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5B, 0x66, 0x6F, 0x6F]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('[')]],
    pos: 4,
    unclosed: true,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('['), TokenS::Lit('f')]],
    pos: 5,
    unclosed: true,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('['), TokenS::Lit('f'), TokenS::Lit('o')]],
    pos: 6,
    unclosed: true,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('['), TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 7,
    unclosed: true,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    reveal_with_fuel(spec_parse_class, 1);
    reveal_with_fuel(spec_class_loop, 13);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 27);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == stf.chars);
    assert(L4.0.stack == stf.stack);
    assert(L4.0.brs.len() == stf.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0) == stf.brs.index(0));
    assert(L4.0.brs == stf.brs);
    assert(L4.0.pos == stf.pos);
    assert(L4.0.unclosed == stf.unclosed);
    assert(L4.0.opts == stf.opts);
    sstate_eq(L4.0, stf);
    assert(L4 == (stf, None));
    ladder_step(st4, false, 26);
    loop_terminal(stf, false, 25);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 5);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('['));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('['), TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]));
}

/// Admit seam instance 19 (actual bytes [2A 2A 2F 5C], ci=false, auc=true,
/// admit truth false; provenance ut_ig2.rs kat_corner_dangling_bs). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b19_ststslbs() {
    let cs: Seq<char> = seq!['*', '*', '/', '\\'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('\\' as u32 == 0x005C);
    reveal_with_fuel(igr_utf8_of_upto, 6);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5C]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5C]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 24);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 matches Some(_));
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 1);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, Some(ErrorKind::DanglingEscape)));
    assert(spec_parse_loop(st0, false, 24)
        == (stf, Some(ErrorKind::DanglingEscape)));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::DanglingEscape));
}

/// Admit seam instance 20 (actual bytes [2A 2A 2F 5C 20], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_esc_space_only). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b20_ststslbsus() {
    let cs: Seq<char> = seq!['*', '*', '/', '\\', ' '];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('\\' as u32 == 0x005C);
    assert(' ' as u32 == 0x0020);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5C]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x20]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x20]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit(' ')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit(' '));
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, None));
    ladder_step(st1, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 26) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 2);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit(' '));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit(' ')]));
}

/// Admit seam instance 21 (actual bytes [2A 2A 2F 5C 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig40_esc). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b21_ststslbsst() {
    let cs: Seq<char> = seq!['*', '*', '/', '\\', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('\\' as u32 == 0x005C);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5C]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('*')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('*'));
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, None));
    ladder_step(st1, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 26) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 2);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('*'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('*')]));
}

/// Admit seam instance 22 (actual bytes [2A 2A 2F 5C 3F], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig39_esc). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b22_ststslbsqm() {
    let cs: Seq<char> = seq!['*', '*', '/', '\\', '?'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('\\' as u32 == 0x005C);
    assert('?' as u32 == 0x003F);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5C]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x3F]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x3F]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('?')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('?'));
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, None));
    ladder_step(st1, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 26) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 2);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('?'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('?')]));
}

/// Admit seam instance 23 (actual bytes [2A 2A 2F 5C 5B], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig38_esc). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b23_ststslbsbk() {
    let cs: Seq<char> = seq!['*', '*', '/', '\\', '['];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('\\' as u32 == 0x005C);
    assert('[' as u32 == 0x005B);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5C]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x5B]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x5B]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('[')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('['));
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, None));
    ladder_step(st1, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 26) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 2);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('['));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('[')]));
}

/// Admit seam instance 24 (actual bytes [2A 2A 2F 5C 61], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig41_esc). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b24_ststslbsa() {
    let cs: Seq<char> = seq!['*', '*', '/', '\\', 'a'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('\\' as u32 == 0x005C);
    assert('a' as u32 == 0x0061);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x5C]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x61]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x5C, 0x61]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, None));
    ladder_step(st1, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 26) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 2);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('a')]));
}

/// Admit seam instance 25 (actual bytes [2A 2A 2F 61], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_esc_slash_dir). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b25_ststsla() {
    let cs: Seq<char> = seq!['*', '*', '/', 'a'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('a' as u32 == 0x0061);
    reveal_with_fuel(igr_utf8_of_upto, 6);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x61]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x61]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 24);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, None));
    ladder_step(st1, false, 23);
    loop_terminal(stf, false, 22);
    assert(spec_parse_loop(st0, false, 24) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 2);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('a')]));
}

/// Admit seam instance 26 (actual bytes [2A 2A 2F 61 5C], ci=false, auc=true,
/// admit truth false; provenance ut_ig2.rs kat_corner_dbl_bs_dir_dangling). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b26_ststslabs() {
    let cs: Seq<char> = seq!['*', '*', '/', 'a', '\\'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('a' as u32 == 0x0061);
    assert('\\' as u32 == 0x005C);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x61]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x5C]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x5C]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 25);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 matches Some(_));
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 2);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, Some(ErrorKind::DanglingEscape)));
    assert(spec_parse_loop(st0, false, 26)
        == (stf, Some(ErrorKind::DanglingEscape)));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::DanglingEscape));
}

/// Admit seam instance 27 (actual bytes [2A 2A 2F 61 6D 6F 6E 74 68 73], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ignot1_plain). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b27_ststslamonths() {
    let cs: Seq<char> = seq!['*', '*', '/', 'a', 'm', 'o', 'n', 't', 'h', 's'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('a' as u32 == 0x0061);
    assert('m' as u32 == 0x006D);
    assert('o' as u32 == 0x006F);
    assert('n' as u32 == 0x006E);
    assert('t' as u32 == 0x0074);
    assert('h' as u32 == 0x0068);
    assert('s' as u32 == 0x0073);
    reveal_with_fuel(igr_utf8_of_upto, 12);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x61]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E, 0x74]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a'), TokenS::Lit('m')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a'), TokenS::Lit('m'), TokenS::Lit('o')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('s')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 36);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 35);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('m'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 34);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('m'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 33);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('m'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('n'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 32);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('m'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('n'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('t'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 31);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('m'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('n'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('h'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 30);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == stf.chars);
    assert(L7.0.stack == stf.stack);
    assert(L7.0.brs.len() == stf.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('m'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('n'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('t'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('h'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('s'));
    assert(L7.0.brs.index(0) == stf.brs.index(0));
    assert(L7.0.brs == stf.brs);
    assert(L7.0.pos == stf.pos);
    assert(L7.0.unclosed == stf.unclosed);
    assert(L7.0.opts == stf.opts);
    sstate_eq(L7.0, stf);
    assert(L7 == (stf, None));
    ladder_step(st7, false, 29);
    loop_terminal(stf, false, 28);
    assert(spec_parse_loop(st0, false, 36) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 8);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('n'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('h'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('a'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('s')]));
}

/// Admit seam instance 28 (actual bytes [2A 2A 2F 61 7B 62], ci=false, auc=true,
/// admit truth false; provenance ut_ig2.rs kat_corner_unclosed_group). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b28_ststslaobb() {
    let cs: Seq<char> = seq!['*', '*', '/', 'a', '{', 'b'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('a' as u32 == 0x0061);
    assert('{' as u32 == 0x007B);
    assert('b' as u32 == 0x0062);
    reveal_with_fuel(igr_utf8_of_upto, 8);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x61]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![1],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')], seq![]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![1],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')], seq![TokenS::Lit('b')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 28);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 27);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 2);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs.index(1).len() == 0);
    assert(L2.0.brs.index(1) == st3.brs.index(1));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 26);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == stf.chars);
    assert(L3.0.stack == stf.stack);
    assert(L3.0.brs.len() == stf.brs.len());
    assert(L3.0.brs.index(0).len() == 2);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0) == stf.brs.index(0));
    assert(L3.0.brs.index(1).len() == 1);
    assert(L3.0.brs.index(1).index(0) == TokenS::Lit('b'));
    assert(L3.0.brs.index(1) == stf.brs.index(1));
    assert(L3.0.brs == stf.brs);
    assert(L3.0.pos == stf.pos);
    assert(L3.0.unclosed == stf.unclosed);
    assert(L3.0.opts == stf.opts);
    sstate_eq(L3.0, stf);
    assert(L3 == (stf, None));
    ladder_step(st3, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 28) == (stf, None));
    assert(stf.brs.len() > 1);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::UnclosedAlternates));
}

/// Admit seam instance 29 (actual bytes [2A 2A 2F 61 7B 62 2C 63], ci=false, auc=true,
/// admit truth false; provenance ut_ig2.rs kat_corner_comma_group). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b29_ststslaobbcmc() {
    let cs: Seq<char> = seq!['*', '*', '/', 'a', '{', 'b', ',', 'c'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('a' as u32 == 0x0061);
    assert('{' as u32 == 0x007B);
    assert('b' as u32 == 0x0062);
    assert(',' as u32 == 0x002C);
    assert('c' as u32 == 0x0063);
    reveal_with_fuel(igr_utf8_of_upto, 10);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x61]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62, 0x2C]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62, 0x2C, 0x63]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7B, 0x62, 0x2C, 0x63]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![1],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')], seq![]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![1],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')], seq![TokenS::Lit('b')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![1],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')], seq![TokenS::Lit('b')], seq![]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![1],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')], seq![TokenS::Lit('b')], seq![TokenS::Lit('c')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 32);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 31);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 2);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs.index(1).len() == 0);
    assert(L2.0.brs.index(1) == st3.brs.index(1));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 30);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 2);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs.index(1).len() == 1);
    assert(L3.0.brs.index(1).index(0) == TokenS::Lit('b'));
    assert(L3.0.brs.index(1) == st4.brs.index(1));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 29);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 2);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs.index(1).len() == 1);
    assert(L4.0.brs.index(1).index(0) == TokenS::Lit('b'));
    assert(L4.0.brs.index(1) == st5.brs.index(1));
    assert(L4.0.brs.index(2).len() == 0);
    assert(L4.0.brs.index(2) == st5.brs.index(2));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 28);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == stf.chars);
    assert(L5.0.stack == stf.stack);
    assert(L5.0.brs.len() == stf.brs.len());
    assert(L5.0.brs.index(0).len() == 2);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L5.0.brs.index(0) == stf.brs.index(0));
    assert(L5.0.brs.index(1).len() == 1);
    assert(L5.0.brs.index(1).index(0) == TokenS::Lit('b'));
    assert(L5.0.brs.index(1) == stf.brs.index(1));
    assert(L5.0.brs.index(2).len() == 1);
    assert(L5.0.brs.index(2).index(0) == TokenS::Lit('c'));
    assert(L5.0.brs.index(2) == stf.brs.index(2));
    assert(L5.0.brs == stf.brs);
    assert(L5.0.pos == stf.pos);
    assert(L5.0.unclosed == stf.unclosed);
    assert(L5.0.opts == stf.opts);
    sstate_eq(L5.0, stf);
    assert(L5 == (stf, None));
    ladder_step(st5, false, 27);
    loop_terminal(stf, false, 26);
    assert(spec_parse_loop(st0, false, 32) == (stf, None));
    assert(stf.brs.len() > 1);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::UnclosedAlternates));
}

/// Admit seam instance 30 (actual bytes [2A 2A 2F 61 7D], ci=false, auc=true,
/// admit truth false; provenance ut_ig2.rs kat_corner_unopened_group). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b30_ststslacb() {
    let cs: Seq<char> = seq!['*', '*', '/', 'a', '}'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('a' as u32 == 0x0061);
    assert('}' as u32 == 0x007D);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x61]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7D]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x61, 0x7D]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('a')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 25);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 matches Some(_));
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 2);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, Some(ErrorKind::UnopenedAlternates)));
    assert(spec_parse_loop(st0, false, 26)
        == (stf, Some(ErrorKind::UnopenedAlternates)));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::UnopenedAlternates));
}

/// Admit seam instance 31 (actual bytes [2A 2A 2F 62 61 72], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_skip_3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b31_ststslbar() {
    let cs: Seq<char> = seq!['*', '*', '/', 'b', 'a', 'r'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('b' as u32 == 0x0062);
    assert('a' as u32 == 0x0061);
    assert('r' as u32 == 0x0072);
    reveal_with_fuel(igr_utf8_of_upto, 8);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x62]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x62, 0x61, 0x72]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('b')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('b'), TokenS::Lit('a')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 28);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('b'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 27);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('b'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 26);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == stf.chars);
    assert(L3.0.stack == stf.stack);
    assert(L3.0.brs.len() == stf.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('b'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L3.0.brs.index(0) == stf.brs.index(0));
    assert(L3.0.brs == stf.brs);
    assert(L3.0.pos == stf.pos);
    assert(L3.0.unclosed == stf.unclosed);
    assert(L3.0.opts == stf.opts);
    sstate_eq(L3.0, stf);
    assert(L3 == (stf, None));
    ladder_step(st3, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 28) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 4);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]));
}

/// Admit seam instance 32 (actual bytes [2A 2A 2F 64 5C], ci=false, auc=true,
/// admit truth false; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b32_ststsldbs() {
    let cs: Seq<char> = seq!['*', '*', '/', 'd', '\\'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('d' as u32 == 0x0064);
    assert('\\' as u32 == 0x005C);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x64]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x64, 0x5C]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x64, 0x5C]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('d')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('d')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('d'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 25);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 matches Some(_));
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 2);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('d'));
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, Some(ErrorKind::DanglingEscape)));
    assert(spec_parse_loop(st0, false, 26)
        == (stf, Some(ErrorKind::DanglingEscape)));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::DanglingEscape));
}

/// Admit seam instance 33 (actual bytes [2A 2A 2F 64 69 72 5C], ci=false, auc=true,
/// admit truth false; provenance ut_ig2.rs kat_corner_dbl_bs_dir_dangling2). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b33_ststsldirbs() {
    let cs: Seq<char> = seq!['*', '*', '/', 'd', 'i', 'r', '\\'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('d' as u32 == 0x0064);
    assert('i' as u32 == 0x0069);
    assert('r' as u32 == 0x0072);
    assert('\\' as u32 == 0x005C);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x64]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x64, 0x69]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x64, 0x69, 0x72]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x64, 0x69, 0x72, 0x5C]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x64, 0x69, 0x72, 0x5C]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('d')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('d'), TokenS::Lit('i')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('d'), TokenS::Lit('i'), TokenS::Lit('r')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('d'), TokenS::Lit('i'), TokenS::Lit('r')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('d'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('d'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('d'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 27);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 matches Some(_));
    assert(L4.0.chars == stf.chars);
    assert(L4.0.stack == stf.stack);
    assert(L4.0.brs.len() == stf.brs.len());
    assert(L4.0.brs.index(0).len() == 4);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('d'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L4.0.brs.index(0) == stf.brs.index(0));
    assert(L4.0.brs == stf.brs);
    assert(L4.0.pos == stf.pos);
    assert(L4.0.unclosed == stf.unclosed);
    assert(L4.0.opts == stf.opts);
    sstate_eq(L4.0, stf);
    assert(L4 == (stf, Some(ErrorKind::DanglingEscape)));
    assert(spec_parse_loop(st0, false, 30)
        == (stf, Some(ErrorKind::DanglingEscape)));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::DanglingEscape));
}

/// Admit seam instance 34 (actual bytes [2A 2A 2F 66 69 6C 65 5F 64 65 65 70 5F 30 31], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b34_ststslfileq5fdeepq5f01() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '1'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('0' as u32 == 0x0030);
    assert('1' as u32 == 0x0031);
    reveal_with_fuel(igr_utf8_of_upto, 17);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x31]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x31]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('1')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 46);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 45);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 44);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 43);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 42);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 41);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 40);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 39);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 38);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 37);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 36);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('0'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 35);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == stf.chars);
    assert(L12.0.stack == stf.stack);
    assert(L12.0.brs.len() == stf.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('0'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('1'));
    assert(L12.0.brs.index(0) == stf.brs.index(0));
    assert(L12.0.brs == stf.brs);
    assert(L12.0.pos == stf.pos);
    assert(L12.0.unclosed == stf.unclosed);
    assert(L12.0.opts == stf.opts);
    sstate_eq(L12.0, stf);
    assert(L12 == (stf, None));
    ladder_step(st12, false, 34);
    loop_terminal(stf, false, 33);
    assert(spec_parse_loop(st0, false, 46) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 13);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('0'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('1')]));
}

/// Admit seam instance 35 (actual bytes [2A 2A 2F 66 69 6C 65 5F 64 65 65 70 5F 33 31], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b35_ststslfileq5fdeepq5f31() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '1'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('3' as u32 == 0x0033);
    assert('1' as u32 == 0x0031);
    reveal_with_fuel(igr_utf8_of_upto, 17);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x31]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x31]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('1')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 46);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 45);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 44);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 43);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 42);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 41);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 40);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 39);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 38);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 37);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 36);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 35);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == stf.chars);
    assert(L12.0.stack == stf.stack);
    assert(L12.0.brs.len() == stf.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('1'));
    assert(L12.0.brs.index(0) == stf.brs.index(0));
    assert(L12.0.brs == stf.brs);
    assert(L12.0.pos == stf.pos);
    assert(L12.0.unclosed == stf.unclosed);
    assert(L12.0.opts == stf.opts);
    sstate_eq(L12.0, stf);
    assert(L12 == (stf, None));
    ladder_step(st12, false, 34);
    loop_terminal(stf, false, 33);
    assert(spec_parse_loop(st0, false, 46) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 13);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('1')]));
}

/// Admit seam instance 36 (actual bytes [2A 2A 2F 66 69 6C 65 5F 64 65 65 70 5F 33 32 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b36_ststslfileq5fdeepq5f32slst() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '2', '/', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('3' as u32 == 0x0033);
    assert('2' as u32 == 0x0032);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 19);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x32]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x32, 0x2F]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x32, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x32, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('2')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('2'), TokenS::Lit('/')]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 17,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 50);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 49);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 48);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 47);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 46);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 45);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 44);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 43);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 42);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 41);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 40);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 39);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 38);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == st14.chars);
    assert(L13.0.stack == st14.stack);
    assert(L13.0.brs.len() == st14.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 37);
    let L14 = spec_parse_loop(st14, false, 1);
    assert(L14.1 is None);
    assert(L14.0.chars == stf.chars);
    assert(L14.0.stack == stf.stack);
    assert(L14.0.brs.len() == stf.brs.len());
    assert(L14.0.brs.index(0).len() == 15);
    assert(L14.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L14.0.brs.index(0).index(13) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0).index(14) == TokenS::Zom);
    assert(L14.0.brs.index(0) == stf.brs.index(0));
    assert(L14.0.brs == stf.brs);
    assert(L14.0.pos == stf.pos);
    assert(L14.0.unclosed == stf.unclosed);
    assert(L14.0.opts == stf.opts);
    sstate_eq(L14.0, stf);
    assert(L14 == (stf, None));
    ladder_step(st14, false, 36);
    loop_terminal(stf, false, 35);
    assert(spec_parse_loop(st0, false, 50) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 15);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 38 (actual bytes [2A 2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 30 30], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b38_ststslfileq5frootq5f00() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '0'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('0' as u32 == 0x0030);
    assert('0' as u32 == 0x0030);
    reveal_with_fuel(igr_utf8_of_upto, 17);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x30]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x30]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('0')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 46);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 45);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 44);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 43);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 42);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 41);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 40);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 39);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 38);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 37);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 36);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('0'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 35);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == stf.chars);
    assert(L12.0.stack == stf.stack);
    assert(L12.0.brs.len() == stf.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('0'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('0'));
    assert(L12.0.brs.index(0) == stf.brs.index(0));
    assert(L12.0.brs == stf.brs);
    assert(L12.0.pos == stf.pos);
    assert(L12.0.unclosed == stf.unclosed);
    assert(L12.0.opts == stf.opts);
    sstate_eq(L12.0, stf);
    assert(L12 == (stf, None));
    ladder_step(st12, false, 34);
    loop_terminal(stf, false, 33);
    assert(spec_parse_loop(st0, false, 46) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 13);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('0'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('0'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('0')]));
}

/// Admit seam instance 39 (actual bytes [2A 2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 30 31], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b39_ststslfileq5frootq5f01() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '1'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('0' as u32 == 0x0030);
    assert('1' as u32 == 0x0031);
    reveal_with_fuel(igr_utf8_of_upto, 17);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x31]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x31]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('1')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 46);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 45);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 44);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 43);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 42);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 41);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 40);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 39);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 38);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 37);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 36);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('0'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 35);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == stf.chars);
    assert(L12.0.stack == stf.stack);
    assert(L12.0.brs.len() == stf.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('0'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('1'));
    assert(L12.0.brs.index(0) == stf.brs.index(0));
    assert(L12.0.brs == stf.brs);
    assert(L12.0.pos == stf.pos);
    assert(L12.0.unclosed == stf.unclosed);
    assert(L12.0.opts == stf.opts);
    sstate_eq(L12.0, stf);
    assert(L12 == (stf, None));
    ladder_step(st12, false, 34);
    loop_terminal(stf, false, 33);
    assert(spec_parse_loop(st0, false, 46) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 13);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('0'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('1')]));
}

/// Admit seam instance 40 (actual bytes [2A 2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 33 31], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b40_ststslfileq5frootq5f31() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '1'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('3' as u32 == 0x0033);
    assert('1' as u32 == 0x0031);
    reveal_with_fuel(igr_utf8_of_upto, 17);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x31]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x31]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('1')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 46);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 45);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 44);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 43);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 42);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 41);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 40);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 39);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 38);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 37);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 36);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 35);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == stf.chars);
    assert(L12.0.stack == stf.stack);
    assert(L12.0.brs.len() == stf.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('1'));
    assert(L12.0.brs.index(0) == stf.brs.index(0));
    assert(L12.0.brs == stf.brs);
    assert(L12.0.pos == stf.pos);
    assert(L12.0.unclosed == stf.unclosed);
    assert(L12.0.opts == stf.opts);
    sstate_eq(L12.0, stf);
    assert(L12 == (stf, None));
    ladder_step(st12, false, 34);
    loop_terminal(stf, false, 33);
    assert(spec_parse_loop(st0, false, 46) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 13);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('1')]));
}

/// Admit seam instance 41 (actual bytes [2A 2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 33 32 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b41_ststslfileq5frootq5f32slst() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '2', '/', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('3' as u32 == 0x0033);
    assert('2' as u32 == 0x0032);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 19);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x32]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x32, 0x2F]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x32, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x32, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('2')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('2'), TokenS::Lit('/')]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 17,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 50);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 49);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 48);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 47);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 46);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 45);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 44);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 43);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 42);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 41);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 40);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 39);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 38);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == st14.chars);
    assert(L13.0.stack == st14.stack);
    assert(L13.0.brs.len() == st14.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 37);
    let L14 = spec_parse_loop(st14, false, 1);
    assert(L14.1 is None);
    assert(L14.0.chars == stf.chars);
    assert(L14.0.stack == stf.stack);
    assert(L14.0.brs.len() == stf.brs.len());
    assert(L14.0.brs.index(0).len() == 15);
    assert(L14.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L14.0.brs.index(0).index(13) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0).index(14) == TokenS::Zom);
    assert(L14.0.brs.index(0) == stf.brs.index(0));
    assert(L14.0.brs == stf.brs);
    assert(L14.0.pos == stf.pos);
    assert(L14.0.unclosed == stf.unclosed);
    assert(L14.0.opts == stf.opts);
    sstate_eq(L14.0, stf);
    assert(L14 == (stf, None));
    ladder_step(st14, false, 36);
    loop_terminal(stf, false, 35);
    assert(spec_parse_loop(st0, false, 50) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 15);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 43 (actual bytes [2A 2A 2F 66 6F 6F], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig8_dir). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b43_ststslfoo() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'o', 'o'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    reveal_with_fuel(igr_utf8_of_upto, 8);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 28);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 27);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 26);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == stf.chars);
    assert(L3.0.stack == stf.stack);
    assert(L3.0.brs.len() == stf.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0) == stf.brs.index(0));
    assert(L3.0.brs == stf.brs);
    assert(L3.0.pos == stf.pos);
    assert(L3.0.unclosed == stf.unclosed);
    assert(L3.0.opts == stf.opts);
    sstate_eq(L3.0, stf);
    assert(L3 == (stf, None));
    ladder_step(st3, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 28) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 4);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]));
}

/// Admit seam instance 45 (actual bytes [2A 2A 2F 66 6F 6F 2F 62 61 72], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig13_ds). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b45_ststslfooslbar() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'o', 'o', '/', 'b', 'a', 'r'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('/' as u32 == 0x002F);
    assert('b' as u32 == 0x0062);
    assert('a' as u32 == 0x0061);
    assert('r' as u32 == 0x0072);
    reveal_with_fuel(igr_utf8_of_upto, 12);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 36);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 35);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 34);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 33);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 32);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('b'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 31);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('b'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('a'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 30);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == stf.chars);
    assert(L7.0.stack == stf.stack);
    assert(L7.0.brs.len() == stf.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('b'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('a'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0) == stf.brs.index(0));
    assert(L7.0.brs == stf.brs);
    assert(L7.0.pos == stf.pos);
    assert(L7.0.unclosed == stf.unclosed);
    assert(L7.0.opts == stf.opts);
    sstate_eq(L7.0, stf);
    assert(L7 == (stf, None));
    ladder_step(st7, false, 29);
    loop_terminal(stf, false, 28);
    assert(spec_parse_loop(st0, false, 36) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 8);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]));
}

/// Admit seam instance 46 (actual bytes [2A 2A 2F 6D 6F 6E 74 68 73], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig1). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b46_ststslmonths() {
    let cs: Seq<char> = seq!['*', '*', '/', 'm', 'o', 'n', 't', 'h', 's'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('m' as u32 == 0x006D);
    assert('o' as u32 == 0x006F);
    assert('n' as u32 == 0x006E);
    assert('t' as u32 == 0x0074);
    assert('h' as u32 == 0x0068);
    assert('s' as u32 == 0x0073);
    reveal_with_fuel(igr_utf8_of_upto, 11);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x6D]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('s')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 34);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 33);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 32);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 31);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 30);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('h'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 29);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == stf.chars);
    assert(L6.0.stack == stf.stack);
    assert(L6.0.brs.len() == stf.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('h'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('s'));
    assert(L6.0.brs.index(0) == stf.brs.index(0));
    assert(L6.0.brs == stf.brs);
    assert(L6.0.pos == stf.pos);
    assert(L6.0.unclosed == stf.unclosed);
    assert(L6.0.opts == stf.opts);
    sstate_eq(L6.0, stf);
    assert(L6 == (stf, None));
    ladder_step(st6, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 34) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 7);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('n'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('h'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('s')]));
}

/// Admit seam instance 47 (actual bytes [2A 2A 2F 6D 6F 6E 74 68 73 61], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b47_ststslmonthsa() {
    let cs: Seq<char> = seq!['*', '*', '/', 'm', 'o', 'n', 't', 'h', 's', 'a'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('m' as u32 == 0x006D);
    assert('o' as u32 == 0x006F);
    assert('n' as u32 == 0x006E);
    assert('t' as u32 == 0x0074);
    assert('h' as u32 == 0x0068);
    assert('s' as u32 == 0x0073);
    assert('a' as u32 == 0x0061);
    reveal_with_fuel(igr_utf8_of_upto, 12);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x6D]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73, 0x61]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x6D, 0x6F, 0x6E, 0x74, 0x68, 0x73, 0x61]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('s')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('s'), TokenS::Lit('a')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 36);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 35);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 34);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 33);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 32);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('h'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 31);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('h'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('s'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 30);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == stf.chars);
    assert(L7.0.stack == stf.stack);
    assert(L7.0.brs.len() == stf.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('m'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('n'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('h'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('s'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('a'));
    assert(L7.0.brs.index(0) == stf.brs.index(0));
    assert(L7.0.brs == stf.brs);
    assert(L7.0.pos == stf.pos);
    assert(L7.0.unclosed == stf.unclosed);
    assert(L7.0.opts == stf.opts);
    sstate_eq(L7.0, stf);
    assert(L7 == (stf, None));
    ladder_step(st7, false, 29);
    loop_terminal(stf, false, 28);
    assert(spec_parse_loop(st0, false, 36) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 8);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('n'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('h'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('s'), TokenS::Lit('a')]));
}

/// Admit seam instance 48 (actual bytes [2A 2A 2F 6E 6F 64 65 5F 6D 6F 64 75 6C 65 73], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig29_trailsp). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b48_ststslnodeq5fmodules() {
    let cs: Seq<char> = seq!['*', '*', '/', 'n', 'o', 'd', 'e', '_', 'm', 'o', 'd', 'u', 'l', 'e', 's'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('n' as u32 == 0x006E);
    assert('o' as u32 == 0x006F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('m' as u32 == 0x006D);
    assert('o' as u32 == 0x006F);
    assert('d' as u32 == 0x0064);
    assert('u' as u32 == 0x0075);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('s' as u32 == 0x0073);
    reveal_with_fuel(igr_utf8_of_upto, 17);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x6E]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x6E, 0x6F, 0x64, 0x65, 0x5F, 0x6D, 0x6F, 0x64, 0x75, 0x6C, 0x65, 0x73]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('m')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('m'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('d')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('u')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('u'), TokenS::Lit('l')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('u'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('u'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('s')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 46);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 45);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 44);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 43);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 42);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 41);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('m'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 40);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('m'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 39);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('m'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 38);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('m'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('u'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 37);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('m'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('u'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 36);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('m'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('u'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 35);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == stf.chars);
    assert(L12.0.stack == stf.stack);
    assert(L12.0.brs.len() == stf.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('n'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('m'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('u'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('s'));
    assert(L12.0.brs.index(0) == stf.brs.index(0));
    assert(L12.0.brs == stf.brs);
    assert(L12.0.pos == stf.pos);
    assert(L12.0.unclosed == stf.unclosed);
    assert(L12.0.opts == stf.opts);
    sstate_eq(L12.0, stf);
    assert(L12 == (stf, None));
    ladder_step(st12, false, 34);
    loop_terminal(stf, false, 33);
    assert(spec_parse_loop(st0, false, 46) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 13);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('n'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('u'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('n'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('m'), TokenS::Lit('o'), TokenS::Lit('d'), TokenS::Lit('u'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('s')]));
}

/// Admit seam instance 49 (actual bytes [2A 2A 2F 73 2A 2E 72 73], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig42_star). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b49_ststslsstdtrs() {
    let cs: Seq<char> = seq!['*', '*', '/', 's', '*', '.', 'r', 's'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('s' as u32 == 0x0073);
    assert('*' as u32 == 0x002A);
    assert('.' as u32 == 0x002E);
    assert('r' as u32 == 0x0072);
    assert('s' as u32 == 0x0073);
    reveal_with_fuel(igr_utf8_of_upto, 10);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x73]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E, 0x72]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E, 0x72, 0x73]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x73, 0x2A, 0x2E, 0x72, 0x73]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('s')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('s'), TokenS::Zom]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('s'), TokenS::Zom, TokenS::Lit('.')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('s'), TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('s'), TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r'), TokenS::Lit('s')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 32);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('s'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 31);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('s'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Zom);
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 30);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('s'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('.'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 29);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('s'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('.'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('r'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 28);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == stf.chars);
    assert(L5.0.stack == stf.stack);
    assert(L5.0.brs.len() == stf.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('s'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('.'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('r'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('s'));
    assert(L5.0.brs.index(0) == stf.brs.index(0));
    assert(L5.0.brs == stf.brs);
    assert(L5.0.pos == stf.pos);
    assert(L5.0.unclosed == stf.unclosed);
    assert(L5.0.opts == stf.opts);
    sstate_eq(L5.0, stf);
    assert(L5 == (stf, None));
    ladder_step(st5, false, 27);
    loop_terminal(stf, false, 26);
    assert(spec_parse_loop(st0, false, 32) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 6);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('s'), TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r'), TokenS::Lit('s')]));
}

/// Admit seam instance 50 (actual bytes [2A 2A 2F 74 61 72 67 65 74], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig24_plain). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b50_ststsltarget() {
    let cs: Seq<char> = seq!['*', '*', '/', 't', 'a', 'r', 'g', 'e', 't'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('t' as u32 == 0x0074);
    assert('a' as u32 == 0x0061);
    assert('r' as u32 == 0x0072);
    assert('g' as u32 == 0x0067);
    assert('e' as u32 == 0x0065);
    assert('t' as u32 == 0x0074);
    reveal_with_fuel(igr_utf8_of_upto, 11);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x74]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x74, 0x61]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72, 0x67]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72, 0x67, 0x65]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x74, 0x61, 0x72, 0x67, 0x65, 0x74]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('t')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('a')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('a'), TokenS::Lit('r')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('e')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('e'), TokenS::Lit('t')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 34);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('t'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 33);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('t'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 32);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('t'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 31);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('t'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 30);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('t'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 29);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == stf.chars);
    assert(L6.0.stack == stf.stack);
    assert(L6.0.brs.len() == stf.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('a'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('g'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0) == stf.brs.index(0));
    assert(L6.0.brs == stf.brs);
    assert(L6.0.pos == stf.pos);
    assert(L6.0.unclosed == stf.unclosed);
    assert(L6.0.opts == stf.opts);
    sstate_eq(L6.0, stf);
    assert(L6 == (stf, None));
    ladder_step(st6, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 34) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 7);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('g'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('t'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('g'), TokenS::Lit('e'), TokenS::Lit('t')]));
}

/// Admit seam instance 51 (actual bytes [2A 2A 2F 78 5C 20], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_esc_space_tail). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b51_ststslxbsus() {
    let cs: Seq<char> = seq!['*', '*', '/', 'x', '\\', ' '];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('x' as u32 == 0x0078);
    assert('\\' as u32 == 0x005C);
    assert(' ' as u32 == 0x0020);
    reveal_with_fuel(igr_utf8_of_upto, 8);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x78]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x20]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x20]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('x')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('x'), TokenS::Lit(' ')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 28);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('x'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 27);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('x'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit(' '));
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, None));
    ladder_step(st2, false, 26);
    loop_terminal(stf, false, 25);
    assert(spec_parse_loop(st0, false, 28) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 3);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('x'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit(' '));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('x'), TokenS::Lit(' ')]));
}

/// Admit seam instance 52 (actual bytes [2A 2A 2F 78 5C 5C 20], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_corner_dbl_bs_esc_space). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b52_ststslxbsbsus() {
    let cs: Seq<char> = seq!['*', '*', '/', 'x', '\\', '\\', ' '];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('x' as u32 == 0x0078);
    assert('\\' as u32 == 0x005C);
    assert('\\' as u32 == 0x005C);
    assert(' ' as u32 == 0x0020);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x78]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x5C]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x5C, 0x20]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x78, 0x5C, 0x5C, 0x20]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('x')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('x'), TokenS::Lit('\\')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('x'), TokenS::Lit('\\'), TokenS::Lit(' ')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('x'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('x'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('\\'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == stf.chars);
    assert(L3.0.stack == stf.stack);
    assert(L3.0.brs.len() == stf.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('x'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('\\'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit(' '));
    assert(L3.0.brs.index(0) == stf.brs.index(0));
    assert(L3.0.brs == stf.brs);
    assert(L3.0.pos == stf.pos);
    assert(L3.0.unclosed == stf.unclosed);
    assert(L3.0.opts == stf.opts);
    sstate_eq(L3.0, stf);
    assert(L3 == (stf, None));
    ladder_step(st3, false, 27);
    loop_terminal(stf, false, 26);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 4);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('x'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('\\'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit(' '));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('x'), TokenS::Lit('\\'), TokenS::Lit(' ')]));
}

/// Admit seam instance 53 (actual bytes [2A 2A 2F 7A 7A 67 6F 6F 64], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_skip_3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b53_ststslzzgood() {
    let cs: Seq<char> = seq!['*', '*', '/', 'z', 'z', 'g', 'o', 'o', 'd'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('z' as u32 == 0x007A);
    assert('z' as u32 == 0x007A);
    assert('g' as u32 == 0x0067);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('d' as u32 == 0x0064);
    reveal_with_fuel(igr_utf8_of_upto, 11);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x7A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x7A, 0x7A, 0x67, 0x6F, 0x6F, 0x64]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('z')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('z'), TokenS::Lit('z')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('z'), TokenS::Lit('z'), TokenS::Lit('g')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('z'), TokenS::Lit('z'), TokenS::Lit('g'), TokenS::Lit('o')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('z'), TokenS::Lit('z'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('z'), TokenS::Lit('z'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('d')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 34);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('z'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 33);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('z'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('z'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 32);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('z'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('z'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('g'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 31);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('z'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('z'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('g'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 30);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('z'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('z'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('g'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 29);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == stf.chars);
    assert(L6.0.stack == stf.stack);
    assert(L6.0.brs.len() == stf.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('z'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('z'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('g'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0) == stf.brs.index(0));
    assert(L6.0.brs == stf.brs);
    assert(L6.0.pos == stf.pos);
    assert(L6.0.unclosed == stf.unclosed);
    assert(L6.0.opts == stf.opts);
    sstate_eq(L6.0, stf);
    assert(L6 == (stf, None));
    ladder_step(st6, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 34) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 7);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('z'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('z'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('g'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('z'), TokenS::Lit('z'), TokenS::Lit('g'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('d')]));
}

/// Admit seam instance 54 (actual bytes [2A 2A 2F 7B 61], ci=false, auc=true,
/// admit truth false; provenance ut_ig2.rs kat_corner_unclosed_group2). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b54_ststsloba() {
    let cs: Seq<char> = seq!['*', '*', '/', '{', 'a'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('{' as u32 == 0x007B);
    assert('a' as u32 == 0x0061);
    reveal_with_fuel(igr_utf8_of_upto, 7);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x7B]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x7B, 0x61]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x7B, 0x61]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![1],
    brs: seq![seq![TokenS::RecP], seq![]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![1],
    brs: seq![seq![TokenS::RecP], seq![TokenS::Lit('a')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 26);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 1);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs.index(1).len() == 0);
    assert(L1.0.brs.index(1) == st2.brs.index(1));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 25);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 1);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs.index(1).len() == 1);
    assert(L2.0.brs.index(1).index(0) == TokenS::Lit('a'));
    assert(L2.0.brs.index(1) == stf.brs.index(1));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, None));
    ladder_step(st2, false, 24);
    loop_terminal(stf, false, 23);
    assert(spec_parse_loop(st0, false, 26) == (stf, None));
    assert(stf.brs.len() > 1);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::UnclosedAlternates));
}

/// Admit seam instance 55 (actual bytes [2A 2A 2F 7D 5C 78], ci=false, auc=true,
/// admit truth false; provenance ut_ig2.rs kat_corner_brace_bs_x). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b55_ststslcbbsx() {
    let cs: Seq<char> = seq!['*', '*', '/', '}', '\\', 'x'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('}' as u32 == 0x007D);
    assert('\\' as u32 == 0x005C);
    assert('x' as u32 == 0x0078);
    reveal_with_fuel(igr_utf8_of_upto, 8);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x7D]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x7D, 0x5C]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x7D, 0x5C, 0x78]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x7D, 0x5C, 0x78]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 28);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 matches Some(_));
    assert(L1.0.chars == stf.chars);
    assert(L1.0.stack == stf.stack);
    assert(L1.0.brs.len() == stf.brs.len());
    assert(L1.0.brs.index(0).len() == 1);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0) == stf.brs.index(0));
    assert(L1.0.brs == stf.brs);
    assert(L1.0.pos == stf.pos);
    assert(L1.0.unclosed == stf.unclosed);
    assert(L1.0.opts == stf.opts);
    sstate_eq(L1.0, stf);
    assert(L1 == (stf, Some(ErrorKind::UnopenedAlternates)));
    assert(spec_parse_loop(st0, false, 28)
        == (stf, Some(ErrorKind::UnopenedAlternates)));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Err(ErrorKind::UnopenedAlternates));
}

/// Admit seam instance 56 (actual bytes [2A 2A 2F EF BB BF 62 61 72], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_skip_3). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b56_ststslx0xefx0xbbx0xbfbar() {
    let cs: Seq<char> = seq!['*', '*', '/', '\u{FEFF}', 'b', 'a', 'r'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('\u{FEFF}' as u32 == 0xFEFF);
    assert('b' as u32 == 0x0062);
    assert('a' as u32 == 0x0061);
    assert('r' as u32 == 0x0072);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0xEF, 0xBB, 0xBF]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0xEF, 0xBB, 0xBF, 0x62]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0xEF, 0xBB, 0xBF, 0x62, 0x61]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0xEF, 0xBB, 0xBF, 0x62, 0x61, 0x72]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('\u{FEFF}')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('\u{FEFF}'), TokenS::Lit('b')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('\u{FEFF}'), TokenS::Lit('b'), TokenS::Lit('a')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('\u{FEFF}'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('\u{FEFF}'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('\u{FEFF}'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('b'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('\u{FEFF}'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('b'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 27);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == stf.chars);
    assert(L4.0.stack == stf.stack);
    assert(L4.0.brs.len() == stf.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('\u{FEFF}'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('b'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('a'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('r'));
    assert(L4.0.brs.index(0) == stf.brs.index(0));
    assert(L4.0.brs == stf.brs);
    assert(L4.0.pos == stf.pos);
    assert(L4.0.unclosed == stf.unclosed);
    assert(L4.0.opts == stf.opts);
    sstate_eq(L4.0, stf);
    assert(L4 == (stf, None));
    ladder_step(st4, false, 26);
    loop_terminal(stf, false, 25);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 5);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('\u{FEFF}'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('\u{FEFF}'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]));
}

/// Admit seam instance 57 (actual bytes [2A 2E 63], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig5). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b57_stdtc() {
    let cs: Seq<char> = seq!['*', '.', 'c'];
    assert('*' as u32 == 0x002A);
    assert('.' as u32 == 0x002E);
    assert('c' as u32 == 0x0063);
    reveal_with_fuel(igr_utf8_of_upto, 5);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2E]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2E, 0x63]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2E, 0x63]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('.')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('c')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 22);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('.'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 21);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('.'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, None));
    ladder_step(st2, false, 20);
    loop_terminal(stf, false, 19);
    assert(spec_parse_loop(st0, false, 22) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 3);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('c'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('c')]));
}

/// Admit seam instance 58 (actual bytes [2A 2F 66 69 6C 65 5F 64 65 65 70 5F 32 31], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b58_stslfileq5fdeepq5f21() {
    let cs: Seq<char> = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '1'];
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('2' as u32 == 0x0032);
    assert('1' as u32 == 0x0031);
    reveal_with_fuel(igr_utf8_of_upto, 16);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x31]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x31]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('1')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 44);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 43);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 42);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 41);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 40);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 39);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 38);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 37);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 36);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 35);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 34);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 33);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 32);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == stf.chars);
    assert(L13.0.stack == stf.stack);
    assert(L13.0.brs.len() == stf.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('1'));
    assert(L13.0.brs.index(0) == stf.brs.index(0));
    assert(L13.0.brs == stf.brs);
    assert(L13.0.pos == stf.pos);
    assert(L13.0.unclosed == stf.unclosed);
    assert(L13.0.opts == stf.opts);
    sstate_eq(L13.0, stf);
    assert(L13 == (stf, None));
    ladder_step(st13, false, 31);
    loop_terminal(stf, false, 30);
    assert(spec_parse_loop(st0, false, 44) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 14);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('1')]));
}

/// Admit seam instance 59 (actual bytes [2A 2F 66 69 6C 65 5F 64 65 65 70 5F 32 32 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b59_stslfileq5fdeepq5f22slst() {
    let cs: Seq<char> = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '2', '/', '*'];
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('2' as u32 == 0x0032);
    assert('2' as u32 == 0x0032);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 18);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x32]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x32, 0x2F]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x32, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x32, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('2')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st15 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('2'), TokenS::Lit('/')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 48);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 47);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 46);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 45);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 44);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 43);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 42);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 41);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 40);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 39);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 38);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 37);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 36);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == st14.chars);
    assert(L13.0.stack == st14.stack);
    assert(L13.0.brs.len() == st14.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 35);
    let L14 = spec_parse_loop(st14, false, 1);
    assert(L14.1 is None);
    assert(L14.0.chars == st15.chars);
    assert(L14.0.stack == st15.stack);
    assert(L14.0.brs.len() == st15.brs.len());
    assert(L14.0.brs.index(0).len() == 15);
    assert(L14.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L14.0.brs.index(0).index(13) == TokenS::Lit('2'));
    assert(L14.0.brs.index(0).index(14) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0) == st15.brs.index(0));
    assert(L14.0.brs == st15.brs);
    assert(L14.0.pos == st15.pos);
    assert(L14.0.unclosed == st15.unclosed);
    assert(L14.0.opts == st15.opts);
    sstate_eq(L14.0, st15);
    assert(L14 == (st15, None));
    ladder_step(st14, false, 34);
    let L15 = spec_parse_loop(st15, false, 1);
    assert(L15.1 is None);
    assert(L15.0.chars == stf.chars);
    assert(L15.0.stack == stf.stack);
    assert(L15.0.brs.len() == stf.brs.len());
    assert(L15.0.brs.index(0).len() == 16);
    assert(L15.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L15.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L15.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L15.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L15.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L15.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L15.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L15.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L15.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L15.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L15.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L15.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L15.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L15.0.brs.index(0).index(13) == TokenS::Lit('2'));
    assert(L15.0.brs.index(0).index(14) == TokenS::Lit('/'));
    assert(L15.0.brs.index(0).index(15) == TokenS::Zom);
    assert(L15.0.brs.index(0) == stf.brs.index(0));
    assert(L15.0.brs == stf.brs);
    assert(L15.0.pos == stf.pos);
    assert(L15.0.unclosed == stf.unclosed);
    assert(L15.0.opts == stf.opts);
    sstate_eq(L15.0, stf);
    assert(L15 == (stf, None));
    ladder_step(st15, false, 33);
    loop_terminal(stf, false, 32);
    assert(spec_parse_loop(st0, false, 48) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 16);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(15) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 61 (actual bytes [2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 32 30], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b61_stslfileq5frootq5f20() {
    let cs: Seq<char> = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '0'];
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('2' as u32 == 0x0032);
    assert('0' as u32 == 0x0030);
    reveal_with_fuel(igr_utf8_of_upto, 16);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x30]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x30]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('0')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 44);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 43);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 42);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 41);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 40);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 39);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 38);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 37);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 36);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 35);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 34);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 33);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 32);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == stf.chars);
    assert(L13.0.stack == stf.stack);
    assert(L13.0.brs.len() == stf.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('0'));
    assert(L13.0.brs.index(0) == stf.brs.index(0));
    assert(L13.0.brs == stf.brs);
    assert(L13.0.pos == stf.pos);
    assert(L13.0.unclosed == stf.unclosed);
    assert(L13.0.opts == stf.opts);
    sstate_eq(L13.0, stf);
    assert(L13 == (stf, None));
    ladder_step(st13, false, 31);
    loop_terminal(stf, false, 30);
    assert(spec_parse_loop(st0, false, 44) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 14);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('0'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('0')]));
}

/// Admit seam instance 62 (actual bytes [2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 32 31], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b62_stslfileq5frootq5f21() {
    let cs: Seq<char> = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '1'];
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('2' as u32 == 0x0032);
    assert('1' as u32 == 0x0031);
    reveal_with_fuel(igr_utf8_of_upto, 16);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x31]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x31]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('1')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 44);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 43);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 42);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 41);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 40);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 39);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 38);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 37);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 36);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 35);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 34);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 33);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 32);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == stf.chars);
    assert(L13.0.stack == stf.stack);
    assert(L13.0.brs.len() == stf.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('1'));
    assert(L13.0.brs.index(0) == stf.brs.index(0));
    assert(L13.0.brs == stf.brs);
    assert(L13.0.pos == stf.pos);
    assert(L13.0.unclosed == stf.unclosed);
    assert(L13.0.opts == stf.opts);
    sstate_eq(L13.0, stf);
    assert(L13 == (stf, None));
    ladder_step(st13, false, 31);
    loop_terminal(stf, false, 30);
    assert(spec_parse_loop(st0, false, 44) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 14);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('1')]));
}

/// Admit seam instance 63 (actual bytes [2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 32 32 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b63_stslfileq5frootq5f22slst() {
    let cs: Seq<char> = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '2', '/', '*'];
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('2' as u32 == 0x0032);
    assert('2' as u32 == 0x0032);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 18);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2F, 0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x32]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x32, 0x2F]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x32, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x32, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('2')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st15 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('2'), TokenS::Lit('/')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 48);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 47);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 46);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 45);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 44);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 43);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 42);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 41);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 40);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 39);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 38);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 37);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 36);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == st14.chars);
    assert(L13.0.stack == st14.stack);
    assert(L13.0.brs.len() == st14.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 35);
    let L14 = spec_parse_loop(st14, false, 1);
    assert(L14.1 is None);
    assert(L14.0.chars == st15.chars);
    assert(L14.0.stack == st15.stack);
    assert(L14.0.brs.len() == st15.brs.len());
    assert(L14.0.brs.index(0).len() == 15);
    assert(L14.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L14.0.brs.index(0).index(13) == TokenS::Lit('2'));
    assert(L14.0.brs.index(0).index(14) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0) == st15.brs.index(0));
    assert(L14.0.brs == st15.brs);
    assert(L14.0.pos == st15.pos);
    assert(L14.0.unclosed == st15.unclosed);
    assert(L14.0.opts == st15.opts);
    sstate_eq(L14.0, st15);
    assert(L14 == (st15, None));
    ladder_step(st14, false, 34);
    let L15 = spec_parse_loop(st15, false, 1);
    assert(L15.1 is None);
    assert(L15.0.chars == stf.chars);
    assert(L15.0.stack == stf.stack);
    assert(L15.0.brs.len() == stf.brs.len());
    assert(L15.0.brs.index(0).len() == 16);
    assert(L15.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L15.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L15.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L15.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L15.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L15.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L15.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L15.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L15.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L15.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L15.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L15.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L15.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L15.0.brs.index(0).index(13) == TokenS::Lit('2'));
    assert(L15.0.brs.index(0).index(14) == TokenS::Lit('/'));
    assert(L15.0.brs.index(0).index(15) == TokenS::Zom);
    assert(L15.0.brs.index(0) == stf.brs.index(0));
    assert(L15.0.brs == stf.brs);
    assert(L15.0.pos == stf.pos);
    assert(L15.0.unclosed == stf.unclosed);
    assert(L15.0.opts == stf.opts);
    sstate_eq(L15.0, stf);
    assert(L15 == (stf, None));
    ladder_step(st15, false, 33);
    loop_terminal(stf, false, 32);
    assert(spec_parse_loop(st0, false, 48) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 16);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(15) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 65 (actual bytes [2E 61 2F 62], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig32_dot). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b65_dtaslb() {
    let cs: Seq<char> = seq!['.', 'a', '/', 'b'];
    assert('.' as u32 == 0x002E);
    assert('a' as u32 == 0x0061);
    assert('/' as u32 == 0x002F);
    assert('b' as u32 == 0x0062);
    reveal_with_fuel(igr_utf8_of_upto, 6);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2E]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2E, 0x61]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2E, 0x61, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2E, 0x61, 0x2F, 0x62]);
    assert(igr_utf8_of(cs) == seq![0x2E, 0x61, 0x2F, 0x62]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('.')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('.'), TokenS::Lit('a')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('.'), TokenS::Lit('a'), TokenS::Lit('/')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('.'), TokenS::Lit('a'), TokenS::Lit('/'), TokenS::Lit('b')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('.'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 24);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('.'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 23);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('.'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 22);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == stf.chars);
    assert(L3.0.stack == stf.stack);
    assert(L3.0.brs.len() == stf.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('.'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('b'));
    assert(L3.0.brs.index(0) == stf.brs.index(0));
    assert(L3.0.brs == stf.brs);
    assert(L3.0.pos == stf.pos);
    assert(L3.0.unclosed == stf.unclosed);
    assert(L3.0.opts == stf.opts);
    sstate_eq(L3.0, stf);
    assert(L3 == (stf, None));
    ladder_step(st3, false, 21);
    loop_terminal(stf, false, 20);
    assert(spec_parse_loop(st0, false, 24) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 4);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('.'), TokenS::Lit('a'), TokenS::Lit('/'), TokenS::Lit('b')]));
}

/// Admit seam instance 68 (actual bytes [62 61 72], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ignot15_wl_anchor). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b68_bar() {
    let cs: Seq<char> = seq!['b', 'a', 'r'];
    assert('b' as u32 == 0x0062);
    assert('a' as u32 == 0x0061);
    assert('r' as u32 == 0x0072);
    reveal_with_fuel(igr_utf8_of_upto, 5);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x62]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x62, 0x61]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x62, 0x61, 0x72]);
    assert(igr_utf8_of(cs) == seq![0x62, 0x61, 0x72]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('b')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('b'), TokenS::Lit('a')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('b'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 22);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('b'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 21);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('b'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('r'));
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, None));
    ladder_step(st2, false, 20);
    loop_terminal(stf, false, 19);
    assert(spec_parse_loop(st0, false, 22) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 3);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]));
}

/// Admit seam instance 69 (actual bytes [66 69 6C 65 5F 64 65 65 70 5F 30 32 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b69_fileq5fdeepq5f02slst() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '2', '/', '*'];
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('0' as u32 == 0x0030);
    assert('2' as u32 == 0x0032);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 16);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x32]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x32, 0x2F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x32, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x32, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('2')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('2'), TokenS::Lit('/')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 44);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 43);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 42);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 41);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 40);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 39);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 38);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 37);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 36);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 35);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 34);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 33);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 32);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == stf.chars);
    assert(L13.0.stack == stf.stack);
    assert(L13.0.brs.len() == stf.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Zom);
    assert(L13.0.brs.index(0) == stf.brs.index(0));
    assert(L13.0.brs == stf.brs);
    assert(L13.0.pos == stf.pos);
    assert(L13.0.unclosed == stf.unclosed);
    assert(L13.0.opts == stf.opts);
    sstate_eq(L13.0, stf);
    assert(L13 == (stf, None));
    ladder_step(st13, false, 31);
    loop_terminal(stf, false, 30);
    assert(spec_parse_loop(st0, false, 44) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 14);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('0'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 71 (actual bytes [66 69 6C 65 5F 64 65 65 70 5F 31 30], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b71_fileq5fdeepq5f10() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '0'];
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('1' as u32 == 0x0031);
    assert('0' as u32 == 0x0030);
    reveal_with_fuel(igr_utf8_of_upto, 14);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x30]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x30]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('0')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 40);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 39);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 38);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 37);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 36);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 35);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 34);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 33);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 32);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 31);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 30);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == stf.chars);
    assert(L11.0.stack == stf.stack);
    assert(L11.0.brs.len() == stf.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('0'));
    assert(L11.0.brs.index(0) == stf.brs.index(0));
    assert(L11.0.brs == stf.brs);
    assert(L11.0.pos == stf.pos);
    assert(L11.0.unclosed == stf.unclosed);
    assert(L11.0.opts == stf.opts);
    sstate_eq(L11.0, stf);
    assert(L11 == (stf, None));
    ladder_step(st11, false, 29);
    loop_terminal(stf, false, 28);
    assert(spec_parse_loop(st0, false, 40) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 12);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('0'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('0')]));
}

/// Admit seam instance 72 (actual bytes [66 69 6C 65 5F 64 65 65 70 5F 31 31], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b72_fileq5fdeepq5f11() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '1'];
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('1' as u32 == 0x0031);
    assert('1' as u32 == 0x0031);
    reveal_with_fuel(igr_utf8_of_upto, 14);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x31]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x31]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('1')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 40);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 39);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 38);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 37);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 36);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 35);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 34);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 33);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 32);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 31);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 30);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == stf.chars);
    assert(L11.0.stack == stf.stack);
    assert(L11.0.brs.len() == stf.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('1'));
    assert(L11.0.brs.index(0) == stf.brs.index(0));
    assert(L11.0.brs == stf.brs);
    assert(L11.0.pos == stf.pos);
    assert(L11.0.unclosed == stf.unclosed);
    assert(L11.0.opts == stf.opts);
    sstate_eq(L11.0, stf);
    assert(L11 == (stf, None));
    ladder_step(st11, false, 29);
    loop_terminal(stf, false, 28);
    assert(spec_parse_loop(st0, false, 40) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 12);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('1')]));
}

/// Admit seam instance 73 (actual bytes [66 69 6C 65 5F 64 65 65 70 5F 31 32 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b73_fileq5fdeepq5f12slst() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '2', '/', '*'];
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('d' as u32 == 0x0064);
    assert('e' as u32 == 0x0065);
    assert('e' as u32 == 0x0065);
    assert('p' as u32 == 0x0070);
    assert('_' as u32 == 0x005F);
    assert('1' as u32 == 0x0031);
    assert('2' as u32 == 0x0032);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 16);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x32]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x32, 0x2F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x32, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x32, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('2')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('2'), TokenS::Lit('/')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 44);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 43);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 42);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 41);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 40);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 39);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 38);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 37);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 36);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 35);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 34);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 33);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 32);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == stf.chars);
    assert(L13.0.stack == stf.stack);
    assert(L13.0.brs.len() == stf.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Zom);
    assert(L13.0.brs.index(0) == stf.brs.index(0));
    assert(L13.0.brs == stf.brs);
    assert(L13.0.pos == stf.pos);
    assert(L13.0.unclosed == stf.unclosed);
    assert(L13.0.opts == stf.opts);
    sstate_eq(L13.0, stf);
    assert(L13 == (stf, None));
    ladder_step(st13, false, 31);
    loop_terminal(stf, false, 30);
    assert(spec_parse_loop(st0, false, 44) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 14);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('d'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 75 (actual bytes [66 69 6C 65 5F 72 6F 6F 74 5F 30 32 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b75_fileq5frootq5f02slst() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '2', '/', '*'];
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('0' as u32 == 0x0030);
    assert('2' as u32 == 0x0032);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 16);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x32]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x32, 0x2F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x32, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x32, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('2')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('2'), TokenS::Lit('/')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 44);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 43);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 42);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 41);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 40);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 39);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 38);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 37);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 36);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 35);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 34);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 33);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 32);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == stf.chars);
    assert(L13.0.stack == stf.stack);
    assert(L13.0.brs.len() == stf.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Zom);
    assert(L13.0.brs.index(0) == stf.brs.index(0));
    assert(L13.0.brs == stf.brs);
    assert(L13.0.pos == stf.pos);
    assert(L13.0.unclosed == stf.unclosed);
    assert(L13.0.opts == stf.opts);
    sstate_eq(L13.0, stf);
    assert(L13 == (stf, None));
    ladder_step(st13, false, 31);
    loop_terminal(stf, false, 30);
    assert(spec_parse_loop(st0, false, 44) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 14);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('0'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 77 (actual bytes [66 69 6C 65 5F 72 6F 6F 74 5F 31 31], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b77_fileq5frootq5f11() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '1'];
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('1' as u32 == 0x0031);
    assert('1' as u32 == 0x0031);
    reveal_with_fuel(igr_utf8_of_upto, 14);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x31]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x31]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('1')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 40);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 39);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 38);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 37);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 36);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 35);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 34);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 33);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 32);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 31);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 30);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == stf.chars);
    assert(L11.0.stack == stf.stack);
    assert(L11.0.brs.len() == stf.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('1'));
    assert(L11.0.brs.index(0) == stf.brs.index(0));
    assert(L11.0.brs == stf.brs);
    assert(L11.0.pos == stf.pos);
    assert(L11.0.unclosed == stf.unclosed);
    assert(L11.0.opts == stf.opts);
    sstate_eq(L11.0, stf);
    assert(L11 == (stf, None));
    ladder_step(st11, false, 29);
    loop_terminal(stf, false, 28);
    assert(spec_parse_loop(st0, false, 40) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 12);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('1')]));
}

/// Admit seam instance 78 (actual bytes [66 69 6C 65 5F 72 6F 6F 74 5F 31 32 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b78_fileq5frootq5f12slst() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '2', '/', '*'];
    assert('f' as u32 == 0x0066);
    assert('i' as u32 == 0x0069);
    assert('l' as u32 == 0x006C);
    assert('e' as u32 == 0x0065);
    assert('_' as u32 == 0x005F);
    assert('r' as u32 == 0x0072);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('t' as u32 == 0x0074);
    assert('_' as u32 == 0x005F);
    assert('1' as u32 == 0x0031);
    assert('2' as u32 == 0x0032);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 16);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x69]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x69, 0x6C]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x69, 0x6C, 0x65]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x32]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x32, 0x2F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x32, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x32, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('2')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('2'), TokenS::Lit('/')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 44);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 43);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 42);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 41);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 40);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 39);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 38);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 37);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 36);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 35);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 34);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 33);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 32);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == stf.chars);
    assert(L13.0.stack == stf.stack);
    assert(L13.0.brs.len() == stf.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('2'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Zom);
    assert(L13.0.brs.index(0) == stf.brs.index(0));
    assert(L13.0.brs == stf.brs);
    assert(L13.0.pos == stf.pos);
    assert(L13.0.unclosed == stf.unclosed);
    assert(L13.0.opts == stf.opts);
    sstate_eq(L13.0, stf);
    assert(L13 == (stf, None));
    ladder_step(st13, false, 31);
    loop_terminal(stf, false, 30);
    assert(spec_parse_loop(st0, false, 44) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 14);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('e'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('_'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('2'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('2'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 81 (actual bytes [66 6F 6F 2F 62 61 72 2F 62 61 7A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig26_anchor). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b81_fooslbarslbaz() {
    let cs: Seq<char> = seq!['f', 'o', 'o', '/', 'b', 'a', 'r', '/', 'b', 'a', 'z'];
    assert('f' as u32 == 0x0066);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('/' as u32 == 0x002F);
    assert('b' as u32 == 0x0062);
    assert('a' as u32 == 0x0061);
    assert('r' as u32 == 0x0072);
    assert('/' as u32 == 0x002F);
    assert('b' as u32 == 0x0062);
    assert('a' as u32 == 0x0061);
    assert('z' as u32 == 0x007A);
    reveal_with_fuel(igr_utf8_of_upto, 13);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x6F]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x6F, 0x6F, 0x2F]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x62, 0x61, 0x72, 0x2F, 0x62, 0x61, 0x7A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('/')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('/'), TokenS::Lit('b')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('z')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 38);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 37);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 36);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 35);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('b'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 34);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('b'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 33);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('b'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 32);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('b'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 31);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('b'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('b'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 30);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('b'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('b'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('a'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 29);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == stf.chars);
    assert(L10.0.stack == stf.stack);
    assert(L10.0.brs.len() == stf.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('b'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('b'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('a'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('z'));
    assert(L10.0.brs.index(0) == stf.brs.index(0));
    assert(L10.0.brs == stf.brs);
    assert(L10.0.pos == stf.pos);
    assert(L10.0.unclosed == stf.unclosed);
    assert(L10.0.opts == stf.opts);
    sstate_eq(L10.0, stf);
    assert(L10 == (stf, None));
    ladder_step(st10, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 38) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 11);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('z'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('r'), TokenS::Lit('/'), TokenS::Lit('b'), TokenS::Lit('a'), TokenS::Lit('z')]));
}

/// Admit seam instance 82 (actual bytes [6C 6C 76 6D], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig28_anchor_dir). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b82_llvm() {
    let cs: Seq<char> = seq!['l', 'l', 'v', 'm'];
    assert('l' as u32 == 0x006C);
    assert('l' as u32 == 0x006C);
    assert('v' as u32 == 0x0076);
    assert('m' as u32 == 0x006D);
    reveal_with_fuel(igr_utf8_of_upto, 6);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x6C]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x6C, 0x6C]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x6C, 0x6C, 0x76]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x6C, 0x6C, 0x76, 0x6D]);
    assert(igr_utf8_of(cs) == seq![0x6C, 0x6C, 0x76, 0x6D]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('l')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('l'), TokenS::Lit('l')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('v')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('v'), TokenS::Lit('m')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('l'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 24);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('l'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('l'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 23);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('l'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('v'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 22);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == stf.chars);
    assert(L3.0.stack == stf.stack);
    assert(L3.0.brs.len() == stf.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('v'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('m'));
    assert(L3.0.brs.index(0) == stf.brs.index(0));
    assert(L3.0.brs == stf.brs);
    assert(L3.0.pos == stf.pos);
    assert(L3.0.unclosed == stf.unclosed);
    assert(L3.0.opts == stf.opts);
    sstate_eq(L3.0, stf);
    assert(L3 == (stf, None));
    ladder_step(st3, false, 21);
    loop_terminal(stf, false, 20);
    assert(spec_parse_loop(st0, false, 24) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 4);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('v'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('l'), TokenS::Lit('l'), TokenS::Lit('v'), TokenS::Lit('m')]));
}

/// Admit seam instance 83 (actual bytes [6D 34 2F 6C 74 6F 70 74 69 6F 6E 73 2E 6D 34], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b83_m4slltoptionsdtm4() {
    let cs: Seq<char> = seq!['m', '4', '/', 'l', 't', 'o', 'p', 't', 'i', 'o', 'n', 's', '.', 'm', '4'];
    assert('m' as u32 == 0x006D);
    assert('4' as u32 == 0x0034);
    assert('/' as u32 == 0x002F);
    assert('l' as u32 == 0x006C);
    assert('t' as u32 == 0x0074);
    assert('o' as u32 == 0x006F);
    assert('p' as u32 == 0x0070);
    assert('t' as u32 == 0x0074);
    assert('i' as u32 == 0x0069);
    assert('o' as u32 == 0x006F);
    assert('n' as u32 == 0x006E);
    assert('s' as u32 == 0x0073);
    assert('.' as u32 == 0x002E);
    assert('m' as u32 == 0x006D);
    assert('4' as u32 == 0x0034);
    reveal_with_fuel(igr_utf8_of_upto, 17);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x6D]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x6D, 0x34]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x6D, 0x34, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x6D, 0x34, 0x2F, 0x6C]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69, 0x6F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E]);
    assert(igr_utf8_of_upto(cs, 12) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73, 0x2E]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73, 0x2E, 0x6D]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73, 0x2E, 0x6D, 0x34]);
    assert(igr_utf8_of(cs) == seq![0x6D, 0x34, 0x2F, 0x6C, 0x74, 0x6F, 0x70, 0x74, 0x69, 0x6F, 0x6E, 0x73, 0x2E, 0x6D, 0x34]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i'), TokenS::Lit('o')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st11 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i'), TokenS::Lit('o'), TokenS::Lit('n')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st12 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('s')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('s'), TokenS::Lit('.')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('s'), TokenS::Lit('.'), TokenS::Lit('m')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('s'), TokenS::Lit('.'), TokenS::Lit('m'), TokenS::Lit('4')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 46);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 45);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 44);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 43);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 42);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 41);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 40);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('t'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 39);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('t'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 38);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('t'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 37);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == st11.chars);
    assert(L10.0.stack == st11.stack);
    assert(L10.0.brs.len() == st11.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('t'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('n'));
    assert(L10.0.brs.index(0) == st11.brs.index(0));
    assert(L10.0.brs == st11.brs);
    assert(L10.0.pos == st11.pos);
    assert(L10.0.unclosed == st11.unclosed);
    assert(L10.0.opts == st11.opts);
    sstate_eq(L10.0, st11);
    assert(L10 == (st11, None));
    ladder_step(st10, false, 36);
    let L11 = spec_parse_loop(st11, false, 1);
    assert(L11.1 is None);
    assert(L11.0.chars == st12.chars);
    assert(L11.0.stack == st12.stack);
    assert(L11.0.brs.len() == st12.brs.len());
    assert(L11.0.brs.index(0).len() == 12);
    assert(L11.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L11.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L11.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L11.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L11.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L11.0.brs.index(0).index(7) == TokenS::Lit('t'));
    assert(L11.0.brs.index(0).index(8) == TokenS::Lit('i'));
    assert(L11.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L11.0.brs.index(0).index(10) == TokenS::Lit('n'));
    assert(L11.0.brs.index(0).index(11) == TokenS::Lit('s'));
    assert(L11.0.brs.index(0) == st12.brs.index(0));
    assert(L11.0.brs == st12.brs);
    assert(L11.0.pos == st12.pos);
    assert(L11.0.unclosed == st12.unclosed);
    assert(L11.0.opts == st12.opts);
    sstate_eq(L11.0, st12);
    assert(L11 == (st12, None));
    ladder_step(st11, false, 35);
    let L12 = spec_parse_loop(st12, false, 1);
    assert(L12.1 is None);
    assert(L12.0.chars == st13.chars);
    assert(L12.0.stack == st13.stack);
    assert(L12.0.brs.len() == st13.brs.len());
    assert(L12.0.brs.index(0).len() == 13);
    assert(L12.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L12.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L12.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L12.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L12.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L12.0.brs.index(0).index(7) == TokenS::Lit('t'));
    assert(L12.0.brs.index(0).index(8) == TokenS::Lit('i'));
    assert(L12.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L12.0.brs.index(0).index(10) == TokenS::Lit('n'));
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('s'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('.'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 34);
    let L13 = spec_parse_loop(st13, false, 1);
    assert(L13.1 is None);
    assert(L13.0.chars == st14.chars);
    assert(L13.0.stack == st14.stack);
    assert(L13.0.brs.len() == st14.brs.len());
    assert(L13.0.brs.index(0).len() == 14);
    assert(L13.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L13.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L13.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L13.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L13.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L13.0.brs.index(0).index(7) == TokenS::Lit('t'));
    assert(L13.0.brs.index(0).index(8) == TokenS::Lit('i'));
    assert(L13.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L13.0.brs.index(0).index(10) == TokenS::Lit('n'));
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('s'));
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('.'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('m'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 33);
    let L14 = spec_parse_loop(st14, false, 1);
    assert(L14.1 is None);
    assert(L14.0.chars == stf.chars);
    assert(L14.0.stack == stf.stack);
    assert(L14.0.brs.len() == stf.brs.len());
    assert(L14.0.brs.index(0).len() == 15);
    assert(L14.0.brs.index(0).index(0) == TokenS::Lit('m'));
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('4'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('t'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('p'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('t'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('n'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('s'));
    assert(L14.0.brs.index(0).index(12) == TokenS::Lit('.'));
    assert(L14.0.brs.index(0).index(13) == TokenS::Lit('m'));
    assert(L14.0.brs.index(0).index(14) == TokenS::Lit('4'));
    assert(L14.0.brs.index(0) == stf.brs.index(0));
    assert(L14.0.brs == stf.brs);
    assert(L14.0.pos == stf.pos);
    assert(L14.0.unclosed == stf.unclosed);
    assert(L14.0.opts == stf.opts);
    sstate_eq(L14.0, stf);
    assert(L14 == (stf, None));
    ladder_step(st14, false, 32);
    loop_terminal(stf, false, 31);
    assert(spec_parse_loop(st0, false, 46) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 15);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('4'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('l'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('n'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::Lit('4'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('m'), TokenS::Lit('4'), TokenS::Lit('/'), TokenS::Lit('l'), TokenS::Lit('t'), TokenS::Lit('o'), TokenS::Lit('p'), TokenS::Lit('t'), TokenS::Lit('i'), TokenS::Lit('o'), TokenS::Lit('n'), TokenS::Lit('s'), TokenS::Lit('.'), TokenS::Lit('m'), TokenS::Lit('4')]));
}

/// Admit seam instance 84 (actual bytes [70 61 74 68 31 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig31_slash). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b84_path1slst() {
    let cs: Seq<char> = seq!['p', 'a', 't', 'h', '1', '/', '*'];
    assert('p' as u32 == 0x0070);
    assert('a' as u32 == 0x0061);
    assert('t' as u32 == 0x0074);
    assert('h' as u32 == 0x0068);
    assert('1' as u32 == 0x0031);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x70]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x70, 0x61]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x70, 0x61, 0x74]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x70, 0x61, 0x74, 0x68]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x70, 0x61, 0x74, 0x68, 0x31]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x70, 0x61, 0x74, 0x68, 0x31, 0x2F, 0x2A]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('p')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('p'), TokenS::Lit('a')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('1')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('1'), TokenS::Lit('/')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('1'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('p'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 30);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('p'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 29);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('p'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('t'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 28);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('p'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('t'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 27);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('p'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('t'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('1'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 26);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('p'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('t'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('1'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 25);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == stf.chars);
    assert(L6.0.stack == stf.stack);
    assert(L6.0.brs.len() == stf.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('p'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('a'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('t'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('h'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('1'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Zom);
    assert(L6.0.brs.index(0) == stf.brs.index(0));
    assert(L6.0.brs == stf.brs);
    assert(L6.0.pos == stf.pos);
    assert(L6.0.unclosed == stf.unclosed);
    assert(L6.0.opts == stf.opts);
    sstate_eq(L6.0, stf);
    assert(L6 == (stf, None));
    ladder_step(st6, false, 24);
    loop_terminal(stf, false, 23);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 7);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('p'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('t'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('h'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('1'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('p'), TokenS::Lit('a'), TokenS::Lit('t'), TokenS::Lit('h'), TokenS::Lit('1'), TokenS::Lit('/'), TokenS::Zom]));
}

/// Admit seam instance 85 (actual bytes [73 72 63 2F 2A 2E 72 73], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig4). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b85_srcslstdtrs() {
    let cs: Seq<char> = seq!['s', 'r', 'c', '/', '*', '.', 'r', 's'];
    assert('s' as u32 == 0x0073);
    assert('r' as u32 == 0x0072);
    assert('c' as u32 == 0x0063);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('.' as u32 == 0x002E);
    assert('r' as u32 == 0x0072);
    assert('s' as u32 == 0x0073);
    reveal_with_fuel(igr_utf8_of_upto, 10);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x73]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x73, 0x72]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x73, 0x72, 0x63]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x73, 0x72, 0x63, 0x2F]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x73, 0x72, 0x63, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    assert(igr_utf8_of(cs) == seq![0x73, 0x72, 0x63, 0x2F, 0x2A, 0x2E, 0x72, 0x73]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Zom]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('.')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r'), TokenS::Lit('s')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    reveal_with_fuel(spec_parse_star, 1);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 32);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 31);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 30);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 29);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Zom);
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 28);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Zom);
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('.'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 27);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Zom);
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('.'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 26);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == stf.chars);
    assert(L7.0.stack == stf.stack);
    assert(L7.0.brs.len() == stf.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Zom);
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('.'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('s'));
    assert(L7.0.brs.index(0) == stf.brs.index(0));
    assert(L7.0.brs == stf.brs);
    assert(L7.0.pos == stf.pos);
    assert(L7.0.unclosed == stf.unclosed);
    assert(L7.0.opts == stf.opts);
    sstate_eq(L7.0, stf);
    assert(L7 == (stf, None));
    ladder_step(st7, false, 25);
    loop_terminal(stf, false, 24);
    assert(spec_parse_loop(st0, false, 32) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 8);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('c'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Zom, TokenS::Lit('.'), TokenS::Lit('r'), TokenS::Lit('s')]));
}

/// Admit seam instance 86 (actual bytes [73 72 63 2F 6D 61 69 6E 2E 72 73], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig7a_wl). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b86_srcslmaindtrs() {
    let cs: Seq<char> = seq!['s', 'r', 'c', '/', 'm', 'a', 'i', 'n', '.', 'r', 's'];
    assert('s' as u32 == 0x0073);
    assert('r' as u32 == 0x0072);
    assert('c' as u32 == 0x0063);
    assert('/' as u32 == 0x002F);
    assert('m' as u32 == 0x006D);
    assert('a' as u32 == 0x0061);
    assert('i' as u32 == 0x0069);
    assert('n' as u32 == 0x006E);
    assert('.' as u32 == 0x002E);
    assert('r' as u32 == 0x0072);
    assert('s' as u32 == 0x0073);
    reveal_with_fuel(igr_utf8_of_upto, 13);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x73]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x73, 0x72]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x73, 0x72, 0x63]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x73, 0x72, 0x63, 0x2F]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]);
    assert(igr_utf8_of(cs) == seq![0x73, 0x72, 0x63, 0x2F, 0x6D, 0x61, 0x69, 0x6E, 0x2E, 0x72, 0x73]);
    let st0 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![]],
    pos: 0,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st1 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Lit('m')]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st6 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Lit('m'), TokenS::Lit('a')]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st7 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Lit('m'), TokenS::Lit('a'), TokenS::Lit('i')]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st8 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Lit('m'), TokenS::Lit('a'), TokenS::Lit('i'), TokenS::Lit('n')]],
    pos: 8,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st9 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Lit('m'), TokenS::Lit('a'), TokenS::Lit('i'), TokenS::Lit('n'), TokenS::Lit('.')]],
    pos: 9,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st10 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Lit('m'), TokenS::Lit('a'), TokenS::Lit('i'), TokenS::Lit('n'), TokenS::Lit('.'), TokenS::Lit('r')]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Lit('m'), TokenS::Lit('a'), TokenS::Lit('i'), TokenS::Lit('n'), TokenS::Lit('.'), TokenS::Lit('r'), TokenS::Lit('s')]],
    pos: 11,
    unclosed: false,
    opts: igr_opts(false, true),
};
    reveal_with_fuel(spec_parse_loop, 3);
    let L0 = spec_parse_loop(st0, false, 1);
    assert(L0.1 is None);
    assert(L0.0.chars == st1.chars);
    assert(L0.0.stack == st1.stack);
    assert(L0.0.brs.len() == st1.brs.len());
    assert(L0.0.brs.index(0).len() == 1);
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L0.0.brs.index(0) == st1.brs.index(0));
    assert(L0.0.brs == st1.brs);
    assert(L0.0.pos == st1.pos);
    assert(L0.0.unclosed == st1.unclosed);
    assert(L0.0.opts == st1.opts);
    sstate_eq(L0.0, st1);
    assert(L0 == (st1, None));
    ladder_step(st0, false, 38);
    let L1 = spec_parse_loop(st1, false, 1);
    assert(L1.1 is None);
    assert(L1.0.chars == st2.chars);
    assert(L1.0.stack == st2.stack);
    assert(L1.0.brs.len() == st2.brs.len());
    assert(L1.0.brs.index(0).len() == 2);
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L1.0.brs.index(0) == st2.brs.index(0));
    assert(L1.0.brs == st2.brs);
    assert(L1.0.pos == st2.pos);
    assert(L1.0.unclosed == st2.unclosed);
    assert(L1.0.opts == st2.opts);
    sstate_eq(L1.0, st2);
    assert(L1 == (st2, None));
    ladder_step(st1, false, 37);
    let L2 = spec_parse_loop(st2, false, 1);
    assert(L2.1 is None);
    assert(L2.0.chars == st3.chars);
    assert(L2.0.stack == st3.stack);
    assert(L2.0.brs.len() == st3.brs.len());
    assert(L2.0.brs.index(0).len() == 3);
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L2.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L2.0.brs.index(0) == st3.brs.index(0));
    assert(L2.0.brs == st3.brs);
    assert(L2.0.pos == st3.pos);
    assert(L2.0.unclosed == st3.unclosed);
    assert(L2.0.opts == st3.opts);
    sstate_eq(L2.0, st3);
    assert(L2 == (st3, None));
    ladder_step(st2, false, 36);
    let L3 = spec_parse_loop(st3, false, 1);
    assert(L3.1 is None);
    assert(L3.0.chars == st4.chars);
    assert(L3.0.stack == st4.stack);
    assert(L3.0.brs.len() == st4.brs.len());
    assert(L3.0.brs.index(0).len() == 4);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L3.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L3.0.brs.index(0) == st4.brs.index(0));
    assert(L3.0.brs == st4.brs);
    assert(L3.0.pos == st4.pos);
    assert(L3.0.unclosed == st4.unclosed);
    assert(L3.0.opts == st4.opts);
    sstate_eq(L3.0, st4);
    assert(L3 == (st4, None));
    ladder_step(st3, false, 35);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 5);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L4.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L4.0.brs.index(0).index(4) == TokenS::Lit('m'));
    assert(L4.0.brs.index(0) == st5.brs.index(0));
    assert(L4.0.brs == st5.brs);
    assert(L4.0.pos == st5.pos);
    assert(L4.0.unclosed == st5.unclosed);
    assert(L4.0.opts == st5.opts);
    sstate_eq(L4.0, st5);
    assert(L4 == (st5, None));
    ladder_step(st4, false, 34);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 6);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L5.0.brs.index(0).index(4) == TokenS::Lit('m'));
    assert(L5.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L5.0.brs.index(0) == st6.brs.index(0));
    assert(L5.0.brs == st6.brs);
    assert(L5.0.pos == st6.pos);
    assert(L5.0.unclosed == st6.unclosed);
    assert(L5.0.opts == st6.opts);
    sstate_eq(L5.0, st6);
    assert(L5 == (st6, None));
    ladder_step(st5, false, 33);
    let L6 = spec_parse_loop(st6, false, 1);
    assert(L6.1 is None);
    assert(L6.0.chars == st7.chars);
    assert(L6.0.stack == st7.stack);
    assert(L6.0.brs.len() == st7.brs.len());
    assert(L6.0.brs.index(0).len() == 7);
    assert(L6.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L6.0.brs.index(0).index(4) == TokenS::Lit('m'));
    assert(L6.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L6.0.brs.index(0).index(6) == TokenS::Lit('i'));
    assert(L6.0.brs.index(0) == st7.brs.index(0));
    assert(L6.0.brs == st7.brs);
    assert(L6.0.pos == st7.pos);
    assert(L6.0.unclosed == st7.unclosed);
    assert(L6.0.opts == st7.opts);
    sstate_eq(L6.0, st7);
    assert(L6 == (st7, None));
    ladder_step(st6, false, 32);
    let L7 = spec_parse_loop(st7, false, 1);
    assert(L7.1 is None);
    assert(L7.0.chars == st8.chars);
    assert(L7.0.stack == st8.stack);
    assert(L7.0.brs.len() == st8.brs.len());
    assert(L7.0.brs.index(0).len() == 8);
    assert(L7.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L7.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L7.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L7.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L7.0.brs.index(0).index(4) == TokenS::Lit('m'));
    assert(L7.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L7.0.brs.index(0).index(6) == TokenS::Lit('i'));
    assert(L7.0.brs.index(0).index(7) == TokenS::Lit('n'));
    assert(L7.0.brs.index(0) == st8.brs.index(0));
    assert(L7.0.brs == st8.brs);
    assert(L7.0.pos == st8.pos);
    assert(L7.0.unclosed == st8.unclosed);
    assert(L7.0.opts == st8.opts);
    sstate_eq(L7.0, st8);
    assert(L7 == (st8, None));
    ladder_step(st7, false, 31);
    let L8 = spec_parse_loop(st8, false, 1);
    assert(L8.1 is None);
    assert(L8.0.chars == st9.chars);
    assert(L8.0.stack == st9.stack);
    assert(L8.0.brs.len() == st9.brs.len());
    assert(L8.0.brs.index(0).len() == 9);
    assert(L8.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L8.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L8.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L8.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L8.0.brs.index(0).index(4) == TokenS::Lit('m'));
    assert(L8.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L8.0.brs.index(0).index(6) == TokenS::Lit('i'));
    assert(L8.0.brs.index(0).index(7) == TokenS::Lit('n'));
    assert(L8.0.brs.index(0).index(8) == TokenS::Lit('.'));
    assert(L8.0.brs.index(0) == st9.brs.index(0));
    assert(L8.0.brs == st9.brs);
    assert(L8.0.pos == st9.pos);
    assert(L8.0.unclosed == st9.unclosed);
    assert(L8.0.opts == st9.opts);
    sstate_eq(L8.0, st9);
    assert(L8 == (st9, None));
    ladder_step(st8, false, 30);
    let L9 = spec_parse_loop(st9, false, 1);
    assert(L9.1 is None);
    assert(L9.0.chars == st10.chars);
    assert(L9.0.stack == st10.stack);
    assert(L9.0.brs.len() == st10.brs.len());
    assert(L9.0.brs.index(0).len() == 10);
    assert(L9.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L9.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L9.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L9.0.brs.index(0).index(4) == TokenS::Lit('m'));
    assert(L9.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L9.0.brs.index(0).index(6) == TokenS::Lit('i'));
    assert(L9.0.brs.index(0).index(7) == TokenS::Lit('n'));
    assert(L9.0.brs.index(0).index(8) == TokenS::Lit('.'));
    assert(L9.0.brs.index(0).index(9) == TokenS::Lit('r'));
    assert(L9.0.brs.index(0) == st10.brs.index(0));
    assert(L9.0.brs == st10.brs);
    assert(L9.0.pos == st10.pos);
    assert(L9.0.unclosed == st10.unclosed);
    assert(L9.0.opts == st10.opts);
    sstate_eq(L9.0, st10);
    assert(L9 == (st10, None));
    ladder_step(st9, false, 29);
    let L10 = spec_parse_loop(st10, false, 1);
    assert(L10.1 is None);
    assert(L10.0.chars == stf.chars);
    assert(L10.0.stack == stf.stack);
    assert(L10.0.brs.len() == stf.brs.len());
    assert(L10.0.brs.index(0).len() == 11);
    assert(L10.0.brs.index(0).index(0) == TokenS::Lit('s'));
    assert(L10.0.brs.index(0).index(1) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L10.0.brs.index(0).index(3) == TokenS::Lit('/'));
    assert(L10.0.brs.index(0).index(4) == TokenS::Lit('m'));
    assert(L10.0.brs.index(0).index(5) == TokenS::Lit('a'));
    assert(L10.0.brs.index(0).index(6) == TokenS::Lit('i'));
    assert(L10.0.brs.index(0).index(7) == TokenS::Lit('n'));
    assert(L10.0.brs.index(0).index(8) == TokenS::Lit('.'));
    assert(L10.0.brs.index(0).index(9) == TokenS::Lit('r'));
    assert(L10.0.brs.index(0).index(10) == TokenS::Lit('s'));
    assert(L10.0.brs.index(0) == stf.brs.index(0));
    assert(L10.0.brs == stf.brs);
    assert(L10.0.pos == stf.pos);
    assert(L10.0.unclosed == stf.unclosed);
    assert(L10.0.opts == stf.opts);
    sstate_eq(L10.0, stf);
    assert(L10 == (stf, None));
    ladder_step(st10, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 38) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 11);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('c'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('/'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Lit('m'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(6) == TokenS::Lit('i'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(7) == TokenS::Lit('n'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(8) == TokenS::Lit('.'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(9) == TokenS::Lit('r'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(10) == TokenS::Lit('s'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('s'), TokenS::Lit('r'), TokenS::Lit('c'), TokenS::Lit('/'), TokenS::Lit('m'), TokenS::Lit('a'), TokenS::Lit('i'), TokenS::Lit('n'), TokenS::Lit('.'), TokenS::Lit('r'), TokenS::Lit('s')]));
}

} // verus!

fn main() {}
