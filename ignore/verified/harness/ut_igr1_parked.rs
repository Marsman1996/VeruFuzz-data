//! IG-R harness ut_igr1_parked -- the 16 ladder rows whose residues
//! still stand after the IG-R2 window, split out of ut_igr1 (which
//! carries the 71 green rows into the family sweep).
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
//! [IG-R3 status: family A (the epilogue-type '{'-unclosed rows)
//! CLOSED by the p22/p23 prescription (spec_parse_glob's
//! branch-count tail emits the error; the loop itself returns
//! normally) -- those rows moved back into the green ut_igr1.
//! Family B remains: the nested-star rewrite rows (pop+push arms)
//! -- probe p23 forensics: whole-arm compute fails, mid-variable
//! split fails, whole-arm plain z3 fails on the brs-field
//! datatype-injectivity (expansion: all sibling fields green), and
//! even the merged expensive seq-axiom broadcast moves the red only
//! one step (len closes, index(1) still opaque) at rlimit 600.
//! Left parked per the batch budget discipline; the next lever is
//! a dedicated pop-tail bridge lemma family (small standalone
//! queries where the update+push injectivity fires cleanly).
/// Admit seam instance 8 (actual bytes [2A 2A 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig44_ds). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b08_ststslststslst() {
    let cs: Seq<char> = seq!['*', '*', '/', '*', '*', '/', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 9);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::RecP]],
    pos: 6,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Zom]],
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
    assert(L1.0.brs.index(0).len() == 1);
    assert(L1.0.brs.index(0).index(0) == TokenS::RecP);
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
    assert(L2.0.chars == stf.chars);
    assert(L2.0.stack == stf.stack);
    assert(L2.0.brs.len() == stf.brs.len());
    assert(L2.0.brs.index(0).len() == 2);
    assert(L2.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L2.0.brs.index(0).index(1) == TokenS::Zom);
    assert(L2.0.brs.index(0) == stf.brs.index(0));
    assert(L2.0.brs == stf.brs);
    assert(L2.0.pos == stf.pos);
    assert(L2.0.unclosed == stf.unclosed);
    assert(L2.0.opts == stf.opts);
    sstate_eq(L2.0, stf);
    assert(L2 == (stf, None));
    ladder_step(st2, false, 28);
    loop_terminal(stf, false, 27);
    assert(spec_parse_loop(st0, false, 30) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 2);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Zom]));
}

/// Admit seam instance 37 (actual bytes [2A 2A 2F 66 69 6C 65 5F 64 65 65 70 5F 33 33 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b37_ststslfileq5fdeepq5f33slststsl() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '3', '3', '/', '*', '*', '/', '*'];
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
    assert('3' as u32 == 0x0033);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 22);
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
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33, 0x2F]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 18) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 19) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 20) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3'), TokenS::Lit('/')]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st15 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3'), TokenS::RecZ]],
    pos: 19,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]],
    pos: 20,
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
    ladder_step(st0, false, 56);
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
    ladder_step(st1, false, 55);
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
    ladder_step(st2, false, 54);
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
    ladder_step(st3, false, 53);
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
    ladder_step(st4, false, 52);
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
    ladder_step(st5, false, 51);
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
    ladder_step(st6, false, 50);
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
    ladder_step(st7, false, 49);
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
    ladder_step(st8, false, 48);
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
    ladder_step(st9, false, 47);
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
    ladder_step(st10, false, 46);
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
    ladder_step(st11, false, 45);
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
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 44);
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
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 43);
    let L14 = spec_parse_loop(st14, false, 1);
    assert(L14.1 is None);
    assert(L14.0.chars == st15.chars);
    assert(L14.0.stack == st15.stack);
    assert(L14.0.brs.len() == st15.brs.len());
    assert(L14.0.brs.index(0).len() == 14);
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
    assert(L14.0.brs.index(0).index(12) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(13) == TokenS::RecZ);
    assert(L14.0.brs.index(0) == st15.brs.index(0));
    assert(L14.0.brs == st15.brs);
    assert(L14.0.pos == st15.pos);
    assert(L14.0.unclosed == st15.unclosed);
    assert(L14.0.opts == st15.opts);
    sstate_eq(L14.0, st15);
    assert(L14 == (st15, None));
    ladder_step(st14, false, 42);
    let L15 = spec_parse_loop(st15, false, 1);
    assert(L15.1 is None);
    assert(L15.0.chars == stf.chars);
    assert(L15.0.stack == stf.stack);
    assert(L15.0.brs.len() == stf.brs.len());
    assert(L15.0.brs.index(0).len() == 15);
    assert(L15.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L15.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L15.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L15.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L15.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L15.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L15.0.brs.index(0).index(6) == TokenS::Lit('d'));
    assert(L15.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L15.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L15.0.brs.index(0).index(9) == TokenS::Lit('p'));
    assert(L15.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L15.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L15.0.brs.index(0).index(12) == TokenS::Lit('3'));
    assert(L15.0.brs.index(0).index(13) == TokenS::RecZ);
    assert(L15.0.brs.index(0).index(14) == TokenS::Zom);
    assert(L15.0.brs.index(0) == stf.brs.index(0));
    assert(L15.0.brs == stf.brs);
    assert(L15.0.pos == stf.pos);
    assert(L15.0.unclosed == stf.unclosed);
    assert(L15.0.opts == stf.opts);
    sstate_eq(L15.0, stf);
    assert(L15 == (stf, None));
    ladder_step(st15, false, 41);
    loop_terminal(stf, false, 40);
    assert(spec_parse_loop(st0, false, 56) == (stf, None));
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 42 (actual bytes [2A 2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 33 33 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b42_ststslfileq5frootq5f33slststsl() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '3', '3', '/', '*', '*', '/', '*'];
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
    assert('3' as u32 == 0x0033);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 22);
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
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33, 0x2F]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 18) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 19) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 20) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x33, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3'), TokenS::Lit('/')]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st15 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3'), TokenS::RecZ]],
    pos: 19,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]],
    pos: 20,
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
    ladder_step(st0, false, 56);
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
    ladder_step(st1, false, 55);
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
    ladder_step(st2, false, 54);
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
    ladder_step(st3, false, 53);
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
    ladder_step(st4, false, 52);
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
    ladder_step(st5, false, 51);
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
    ladder_step(st6, false, 50);
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
    ladder_step(st7, false, 49);
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
    ladder_step(st8, false, 48);
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
    ladder_step(st9, false, 47);
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
    ladder_step(st10, false, 46);
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
    ladder_step(st11, false, 45);
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
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0) == st13.brs.index(0));
    assert(L12.0.brs == st13.brs);
    assert(L12.0.pos == st13.pos);
    assert(L12.0.unclosed == st13.unclosed);
    assert(L12.0.opts == st13.opts);
    sstate_eq(L12.0, st13);
    assert(L12 == (st13, None));
    ladder_step(st12, false, 44);
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
    assert(L13.0.brs.index(0).index(12) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('/'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 43);
    let L14 = spec_parse_loop(st14, false, 1);
    assert(L14.1 is None);
    assert(L14.0.chars == st15.chars);
    assert(L14.0.stack == st15.stack);
    assert(L14.0.brs.len() == st15.brs.len());
    assert(L14.0.brs.index(0).len() == 14);
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
    assert(L14.0.brs.index(0).index(12) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(13) == TokenS::RecZ);
    assert(L14.0.brs.index(0) == st15.brs.index(0));
    assert(L14.0.brs == st15.brs);
    assert(L14.0.pos == st15.pos);
    assert(L14.0.unclosed == st15.unclosed);
    assert(L14.0.opts == st15.opts);
    sstate_eq(L14.0, st15);
    assert(L14 == (st15, None));
    ladder_step(st14, false, 42);
    let L15 = spec_parse_loop(st15, false, 1);
    assert(L15.1 is None);
    assert(L15.0.chars == stf.chars);
    assert(L15.0.stack == stf.stack);
    assert(L15.0.brs.len() == stf.brs.len());
    assert(L15.0.brs.index(0).len() == 15);
    assert(L15.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L15.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L15.0.brs.index(0).index(2) == TokenS::Lit('i'));
    assert(L15.0.brs.index(0).index(3) == TokenS::Lit('l'));
    assert(L15.0.brs.index(0).index(4) == TokenS::Lit('e'));
    assert(L15.0.brs.index(0).index(5) == TokenS::Lit('_'));
    assert(L15.0.brs.index(0).index(6) == TokenS::Lit('r'));
    assert(L15.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L15.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L15.0.brs.index(0).index(9) == TokenS::Lit('t'));
    assert(L15.0.brs.index(0).index(10) == TokenS::Lit('_'));
    assert(L15.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L15.0.brs.index(0).index(12) == TokenS::Lit('3'));
    assert(L15.0.brs.index(0).index(13) == TokenS::RecZ);
    assert(L15.0.brs.index(0).index(14) == TokenS::Zom);
    assert(L15.0.brs.index(0) == stf.brs.index(0));
    assert(L15.0.brs == stf.brs);
    assert(L15.0.pos == stf.pos);
    assert(L15.0.unclosed == stf.unclosed);
    assert(L15.0.opts == stf.opts);
    sstate_eq(L15.0, stf);
    assert(L15 == (stf, None));
    ladder_step(st15, false, 41);
    loop_terminal(stf, false, 40);
    assert(spec_parse_loop(st0, false, 56) == (stf, None));
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('3'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 44 (actual bytes [2A 2A 2F 66 6F 6F 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig11_sfx). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b44_ststslfooslststslst() {
    let cs: Seq<char> = seq!['*', '*', '/', 'f', 'o', 'o', '/', '*', '*', '/', '*'];
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('f' as u32 == 0x0066);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 13);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x2A, 0x2A, 0x2F, 0x66]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 9) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 10) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 11) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A, 0x2F, 0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::RecZ]],
    pos: 10,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::RecZ, TokenS::Zom]],
    pos: 11,
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
    ladder_step(st0, false, 38);
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
    ladder_step(st1, false, 37);
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
    ladder_step(st2, false, 36);
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
    ladder_step(st3, false, 35);
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
    ladder_step(st4, false, 34);
    let L5 = spec_parse_loop(st5, false, 1);
    assert(L5.1 is None);
    assert(L5.0.chars == st6.chars);
    assert(L5.0.stack == st6.stack);
    assert(L5.0.brs.len() == st6.brs.len());
    assert(L5.0.brs.index(0).len() == 5);
    assert(L5.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(4) == TokenS::RecZ);
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
    assert(L6.0.chars == stf.chars);
    assert(L6.0.stack == stf.stack);
    assert(L6.0.brs.len() == stf.brs.len());
    assert(L6.0.brs.index(0).len() == 6);
    assert(L6.0.brs.index(0).index(0) == TokenS::RecP);
    assert(L6.0.brs.index(0).index(1) == TokenS::Lit('f'));
    assert(L6.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(3) == TokenS::Lit('o'));
    assert(L6.0.brs.index(0).index(4) == TokenS::RecZ);
    assert(L6.0.brs.index(0).index(5) == TokenS::Zom);
    assert(L6.0.brs.index(0) == stf.brs.index(0));
    assert(L6.0.brs == stf.brs);
    assert(L6.0.pos == stf.pos);
    assert(L6.0.unclosed == stf.unclosed);
    assert(L6.0.opts == stf.opts);
    sstate_eq(L6.0, stf);
    assert(L6 == (stf, None));
    ladder_step(st6, false, 32);
    loop_terminal(stf, false, 31);
    assert(spec_parse_loop(st0, false, 38) == (stf, None));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 6);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::RecP);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(5) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::RecP, TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 60 (actual bytes [2A 2F 66 69 6C 65 5F 64 65 65 70 5F 32 33 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b60_stslfileq5fdeepq5f23slststslst() {
    let cs: Seq<char> = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '2', '3', '/', '*', '*', '/', '*'];
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
    assert('3' as u32 == 0x0033);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 21);
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
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33, 0x2F]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 18) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 19) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st15 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3'), TokenS::Lit('/')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st16 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3'), TokenS::RecZ]],
    pos: 18,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]],
    pos: 19,
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
    ladder_step(st0, false, 54);
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
    ladder_step(st1, false, 53);
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
    ladder_step(st2, false, 52);
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
    ladder_step(st3, false, 51);
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
    ladder_step(st4, false, 50);
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
    ladder_step(st5, false, 49);
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
    ladder_step(st6, false, 48);
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
    ladder_step(st7, false, 47);
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
    ladder_step(st8, false, 46);
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
    ladder_step(st9, false, 45);
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
    ladder_step(st10, false, 44);
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
    ladder_step(st11, false, 43);
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
    ladder_step(st12, false, 42);
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
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 41);
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
    assert(L14.0.brs.index(0).index(13) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(14) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0) == st15.brs.index(0));
    assert(L14.0.brs == st15.brs);
    assert(L14.0.pos == st15.pos);
    assert(L14.0.unclosed == st15.unclosed);
    assert(L14.0.opts == st15.opts);
    sstate_eq(L14.0, st15);
    assert(L14 == (st15, None));
    ladder_step(st14, false, 40);
    let L15 = spec_parse_loop(st15, false, 1);
    assert(L15.1 is None);
    assert(L15.0.chars == st16.chars);
    assert(L15.0.stack == st16.stack);
    assert(L15.0.brs.len() == st16.brs.len());
    assert(L15.0.brs.index(0).len() == 15);
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
    assert(L15.0.brs.index(0).index(13) == TokenS::Lit('3'));
    assert(L15.0.brs.index(0).index(14) == TokenS::RecZ);
    assert(L15.0.brs.index(0) == st16.brs.index(0));
    assert(L15.0.brs == st16.brs);
    assert(L15.0.pos == st16.pos);
    assert(L15.0.unclosed == st16.unclosed);
    assert(L15.0.opts == st16.opts);
    sstate_eq(L15.0, st16);
    assert(L15 == (st16, None));
    ladder_step(st15, false, 39);
    let L16 = spec_parse_loop(st16, false, 1);
    assert(L16.1 is None);
    assert(L16.0.chars == stf.chars);
    assert(L16.0.stack == stf.stack);
    assert(L16.0.brs.len() == stf.brs.len());
    assert(L16.0.brs.index(0).len() == 16);
    assert(L16.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L16.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L16.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L16.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L16.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L16.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L16.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L16.0.brs.index(0).index(7) == TokenS::Lit('d'));
    assert(L16.0.brs.index(0).index(8) == TokenS::Lit('e'));
    assert(L16.0.brs.index(0).index(9) == TokenS::Lit('e'));
    assert(L16.0.brs.index(0).index(10) == TokenS::Lit('p'));
    assert(L16.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L16.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L16.0.brs.index(0).index(13) == TokenS::Lit('3'));
    assert(L16.0.brs.index(0).index(14) == TokenS::RecZ);
    assert(L16.0.brs.index(0).index(15) == TokenS::Zom);
    assert(L16.0.brs.index(0) == stf.brs.index(0));
    assert(L16.0.brs == stf.brs);
    assert(L16.0.pos == stf.pos);
    assert(L16.0.unclosed == stf.unclosed);
    assert(L16.0.opts == stf.opts);
    sstate_eq(L16.0, stf);
    assert(L16 == (stf, None));
    ladder_step(st16, false, 38);
    loop_terminal(stf, false, 37);
    assert(spec_parse_loop(st0, false, 54) == (stf, None));
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(15) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 64 (actual bytes [2A 2F 66 69 6C 65 5F 72 6F 6F 74 5F 32 33 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b64_stslfileq5frootq5f23slststslst() {
    let cs: Seq<char> = seq!['*', '/', 'f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '2', '3', '/', '*', '*', '/', '*'];
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
    assert('3' as u32 == 0x0033);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 21);
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
    assert(igr_utf8_of_upto(cs, 14) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33, 0x2F]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 18) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 19) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2F, 0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x32, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3')]],
    pos: 14,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st15 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3'), TokenS::Lit('/')]],
    pos: 15,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st16 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3'), TokenS::RecZ]],
    pos: 18,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]],
    pos: 19,
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
    ladder_step(st0, false, 54);
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
    ladder_step(st1, false, 53);
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
    ladder_step(st2, false, 52);
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
    ladder_step(st3, false, 51);
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
    ladder_step(st4, false, 50);
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
    ladder_step(st5, false, 49);
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
    ladder_step(st6, false, 48);
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
    ladder_step(st7, false, 47);
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
    ladder_step(st8, false, 46);
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
    ladder_step(st9, false, 45);
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
    ladder_step(st10, false, 44);
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
    ladder_step(st11, false, 43);
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
    ladder_step(st12, false, 42);
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
    assert(L13.0.brs.index(0).index(13) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0) == st14.brs.index(0));
    assert(L13.0.brs == st14.brs);
    assert(L13.0.pos == st14.pos);
    assert(L13.0.unclosed == st14.unclosed);
    assert(L13.0.opts == st14.opts);
    sstate_eq(L13.0, st14);
    assert(L13 == (st14, None));
    ladder_step(st13, false, 41);
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
    assert(L14.0.brs.index(0).index(13) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(14) == TokenS::Lit('/'));
    assert(L14.0.brs.index(0) == st15.brs.index(0));
    assert(L14.0.brs == st15.brs);
    assert(L14.0.pos == st15.pos);
    assert(L14.0.unclosed == st15.unclosed);
    assert(L14.0.opts == st15.opts);
    sstate_eq(L14.0, st15);
    assert(L14 == (st15, None));
    ladder_step(st14, false, 40);
    let L15 = spec_parse_loop(st15, false, 1);
    assert(L15.1 is None);
    assert(L15.0.chars == st16.chars);
    assert(L15.0.stack == st16.stack);
    assert(L15.0.brs.len() == st16.brs.len());
    assert(L15.0.brs.index(0).len() == 15);
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
    assert(L15.0.brs.index(0).index(13) == TokenS::Lit('3'));
    assert(L15.0.brs.index(0).index(14) == TokenS::RecZ);
    assert(L15.0.brs.index(0) == st16.brs.index(0));
    assert(L15.0.brs == st16.brs);
    assert(L15.0.pos == st16.pos);
    assert(L15.0.unclosed == st16.unclosed);
    assert(L15.0.opts == st16.opts);
    sstate_eq(L15.0, st16);
    assert(L15 == (st16, None));
    ladder_step(st15, false, 39);
    let L16 = spec_parse_loop(st16, false, 1);
    assert(L16.1 is None);
    assert(L16.0.chars == stf.chars);
    assert(L16.0.stack == stf.stack);
    assert(L16.0.brs.len() == stf.brs.len());
    assert(L16.0.brs.index(0).len() == 16);
    assert(L16.0.brs.index(0).index(0) == TokenS::Zom);
    assert(L16.0.brs.index(0).index(1) == TokenS::Lit('/'));
    assert(L16.0.brs.index(0).index(2) == TokenS::Lit('f'));
    assert(L16.0.brs.index(0).index(3) == TokenS::Lit('i'));
    assert(L16.0.brs.index(0).index(4) == TokenS::Lit('l'));
    assert(L16.0.brs.index(0).index(5) == TokenS::Lit('e'));
    assert(L16.0.brs.index(0).index(6) == TokenS::Lit('_'));
    assert(L16.0.brs.index(0).index(7) == TokenS::Lit('r'));
    assert(L16.0.brs.index(0).index(8) == TokenS::Lit('o'));
    assert(L16.0.brs.index(0).index(9) == TokenS::Lit('o'));
    assert(L16.0.brs.index(0).index(10) == TokenS::Lit('t'));
    assert(L16.0.brs.index(0).index(11) == TokenS::Lit('_'));
    assert(L16.0.brs.index(0).index(12) == TokenS::Lit('2'));
    assert(L16.0.brs.index(0).index(13) == TokenS::Lit('3'));
    assert(L16.0.brs.index(0).index(14) == TokenS::RecZ);
    assert(L16.0.brs.index(0).index(15) == TokenS::Zom);
    assert(L16.0.brs.index(0) == stf.brs.index(0));
    assert(L16.0.brs == stf.brs);
    assert(L16.0.pos == stf.pos);
    assert(L16.0.unclosed == stf.unclosed);
    assert(L16.0.opts == stf.opts);
    sstate_eq(L16.0, stf);
    assert(L16 == (stf, None));
    ladder_step(st16, false, 38);
    loop_terminal(stf, false, 37);
    assert(spec_parse_loop(st0, false, 54) == (stf, None));
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(14) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(15) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Zom, TokenS::Lit('/'), TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('2'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 66 (actual bytes [61 2F 2A 2A 2F 62], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig18_mid). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b66_aslststslb() {
    let cs: Seq<char> = seq!['a', '/', '*', '*', '/', 'b'];
    assert('a' as u32 == 0x0061);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('b' as u32 == 0x0062);
    reveal_with_fuel(igr_utf8_of_upto, 8);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x61]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x61, 0x2F]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x61, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x61, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62]);
    assert(igr_utf8_of(cs) == seq![0x61, 0x2F, 0x2A, 0x2A, 0x2F, 0x62]);
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
    brs: seq![seq![TokenS::Lit('a')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('a'), TokenS::Lit('/')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('a'), TokenS::RecZ]],
    pos: 5,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('a'), TokenS::RecZ, TokenS::Lit('b')]],
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
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('a'));
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
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('/'));
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
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0).index(1) == TokenS::RecZ);
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
    assert(L3.0.brs.index(0).len() == 3);
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(1) == TokenS::RecZ);
    assert(L3.0.brs.index(0).index(2) == TokenS::Lit('b'));
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 3);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('a'), TokenS::RecZ, TokenS::Lit('b')]));
}

/// Admit seam instance 67 (actual bytes [61 62 63 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ig15_sfx). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b67_abcslststslst() {
    let cs: Seq<char> = seq!['a', 'b', 'c', '/', '*', '*', '/', '*'];
    assert('a' as u32 == 0x0061);
    assert('b' as u32 == 0x0062);
    assert('c' as u32 == 0x0063);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 10);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x61]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x61, 0x62]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x61, 0x62, 0x63]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x61, 0x62, 0x63, 0x2F]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x61, 0x62, 0x63, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x61, 0x62, 0x63, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::Lit('a')]],
    pos: 1,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st2 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('a'), TokenS::Lit('b')]],
    pos: 2,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st3 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c')]],
    pos: 3,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st4 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c'), TokenS::Lit('/')]],
    pos: 4,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st5 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c'), TokenS::RecZ]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c'), TokenS::RecZ, TokenS::Zom]],
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
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('a'));
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
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('a'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('b'));
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
    assert(L2.0.brs.index(0).index(0) == TokenS::Lit('a'));
    assert(L2.0.brs.index(0).index(1) == TokenS::Lit('b'));
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
    assert(L3.0.brs.index(0).index(0) == TokenS::Lit('a'));
    assert(L3.0.brs.index(0).index(1) == TokenS::Lit('b'));
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
    assert(L4.0.brs.index(0).len() == 4);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('a'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('b'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L4.0.brs.index(0).index(3) == TokenS::RecZ);
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
    assert(L5.0.brs.index(0).len() == 5);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('a'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('b'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('c'));
    assert(L5.0.brs.index(0).index(3) == TokenS::RecZ);
    assert(L5.0.brs.index(0).index(4) == TokenS::Zom);
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 5);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('a'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('b'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('c'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('a'), TokenS::Lit('b'), TokenS::Lit('c'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 70 (actual bytes [66 69 6C 65 5F 64 65 65 70 5F 30 33 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b70_fileq5fdeepq5f03slststslst() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '0', '3', '/', '*', '*', '/', '*'];
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
    assert('3' as u32 == 0x0033);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 19);
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
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33, 0x2F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3'), TokenS::Lit('/')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3'), TokenS::RecZ]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]],
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
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
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
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
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
    ladder_step(st2, false, 48);
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
    ladder_step(st3, false, 47);
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
    ladder_step(st4, false, 46);
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
    ladder_step(st5, false, 45);
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
    ladder_step(st6, false, 44);
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
    ladder_step(st7, false, 43);
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
    ladder_step(st8, false, 42);
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
    ladder_step(st9, false, 41);
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
    ladder_step(st10, false, 40);
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
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('/'));
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
    assert(L13.0.brs.index(0).len() == 13);
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
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0).index(12) == TokenS::RecZ);
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
    assert(L14.0.brs.index(0).len() == 14);
    assert(L14.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(12) == TokenS::RecZ);
    assert(L14.0.brs.index(0).index(13) == TokenS::Zom);
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 74 (actual bytes [66 69 6C 65 5F 64 65 65 70 5F 31 33 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b74_fileq5fdeepq5f13slststslst() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'd', 'e', 'e', 'p', '_', '1', '3', '/', '*', '*', '/', '*'];
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
    assert('3' as u32 == 0x0033);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 19);
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
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33, 0x2F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x64, 0x65, 0x65, 0x70, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3'), TokenS::Lit('/')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3'), TokenS::RecZ]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]],
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
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
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
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
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
    ladder_step(st2, false, 48);
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
    ladder_step(st3, false, 47);
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
    ladder_step(st4, false, 46);
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
    ladder_step(st5, false, 45);
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
    ladder_step(st6, false, 44);
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
    ladder_step(st7, false, 43);
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
    ladder_step(st8, false, 42);
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
    ladder_step(st9, false, 41);
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
    ladder_step(st10, false, 40);
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
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('/'));
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
    assert(L13.0.brs.index(0).len() == 13);
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
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0).index(12) == TokenS::RecZ);
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
    assert(L14.0.brs.index(0).len() == 14);
    assert(L14.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('d'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('p'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(12) == TokenS::RecZ);
    assert(L14.0.brs.index(0).index(13) == TokenS::Zom);
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('d'), TokenS::Lit('e'), TokenS::Lit('e'), TokenS::Lit('p'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 76 (actual bytes [66 69 6C 65 5F 72 6F 6F 74 5F 30 33 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b76_fileq5frootq5f03slststslst() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '0', '3', '/', '*', '*', '/', '*'];
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
    assert('3' as u32 == 0x0033);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 19);
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
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33, 0x2F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x30, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3'), TokenS::Lit('/')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3'), TokenS::RecZ]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]],
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
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
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
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
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
    ladder_step(st2, false, 48);
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
    ladder_step(st3, false, 47);
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
    ladder_step(st4, false, 46);
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
    ladder_step(st5, false, 45);
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
    ladder_step(st6, false, 44);
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
    ladder_step(st7, false, 43);
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
    ladder_step(st8, false, 42);
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
    ladder_step(st9, false, 41);
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
    ladder_step(st10, false, 40);
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
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('/'));
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
    assert(L13.0.brs.index(0).len() == 13);
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
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0).index(12) == TokenS::RecZ);
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
    assert(L14.0.brs.index(0).len() == 14);
    assert(L14.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('0'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(12) == TokenS::RecZ);
    assert(L14.0.brs.index(0).index(13) == TokenS::Zom);
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('0'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 79 (actual bytes [66 69 6C 65 5F 72 6F 6F 74 5F 31 33 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig3.rs ?). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b79_fileq5frootq5f13slststslst() {
    let cs: Seq<char> = seq!['f', 'i', 'l', 'e', '_', 'r', 'o', 'o', 't', '_', '1', '3', '/', '*', '*', '/', '*'];
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
    assert('3' as u32 == 0x0033);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 19);
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
    assert(igr_utf8_of_upto(cs, 12) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33]);
    assert(igr_utf8_of_upto(cs, 13) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33, 0x2F]);
    assert(igr_utf8_of_upto(cs, 14) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 15) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 16) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 17) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x69, 0x6C, 0x65, 0x5F, 0x72, 0x6F, 0x6F, 0x74, 0x5F, 0x31, 0x33, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3')]],
    pos: 12,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st13 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3'), TokenS::Lit('/')]],
    pos: 13,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let st14 = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3'), TokenS::RecZ]],
    pos: 16,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]],
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
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
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
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('i'));
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
    ladder_step(st2, false, 48);
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
    ladder_step(st3, false, 47);
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
    ladder_step(st4, false, 46);
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
    ladder_step(st5, false, 45);
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
    ladder_step(st6, false, 44);
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
    ladder_step(st7, false, 43);
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
    ladder_step(st8, false, 42);
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
    ladder_step(st9, false, 41);
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
    ladder_step(st10, false, 40);
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
    assert(L12.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L12.0.brs.index(0).index(12) == TokenS::Lit('/'));
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
    assert(L13.0.brs.index(0).len() == 13);
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
    assert(L13.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L13.0.brs.index(0).index(12) == TokenS::RecZ);
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
    assert(L14.0.brs.index(0).len() == 14);
    assert(L14.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L14.0.brs.index(0).index(1) == TokenS::Lit('i'));
    assert(L14.0.brs.index(0).index(2) == TokenS::Lit('l'));
    assert(L14.0.brs.index(0).index(3) == TokenS::Lit('e'));
    assert(L14.0.brs.index(0).index(4) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(5) == TokenS::Lit('r'));
    assert(L14.0.brs.index(0).index(6) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(7) == TokenS::Lit('o'));
    assert(L14.0.brs.index(0).index(8) == TokenS::Lit('t'));
    assert(L14.0.brs.index(0).index(9) == TokenS::Lit('_'));
    assert(L14.0.brs.index(0).index(10) == TokenS::Lit('1'));
    assert(L14.0.brs.index(0).index(11) == TokenS::Lit('3'));
    assert(L14.0.brs.index(0).index(12) == TokenS::RecZ);
    assert(L14.0.brs.index(0).index(13) == TokenS::Zom);
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(11) == TokenS::Lit('3'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(12) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(13) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('i'), TokenS::Lit('l'), TokenS::Lit('e'), TokenS::Lit('_'), TokenS::Lit('r'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::Lit('t'), TokenS::Lit('_'), TokenS::Lit('1'), TokenS::Lit('3'), TokenS::RecZ, TokenS::Zom]));
}

/// Admit seam instance 80 (actual bytes [66 6F 6F 2F 2A 2A 2F 2A], ci=false, auc=true,
/// admit truth true; provenance ut_ig2.rs kat_ignot13_sfx). The ladder re-anchors the verdict:
/// per-pass ground rungs (fieldwise + sstate_eq) and the budget descent;
/// the top verdict is the admit value machine-checked.
proof fn igr_b80_fooslststslst() {
    let cs: Seq<char> = seq!['f', 'o', 'o', '/', '*', '*', '/', '*'];
    assert('f' as u32 == 0x0066);
    assert('o' as u32 == 0x006F);
    assert('o' as u32 == 0x006F);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    assert('*' as u32 == 0x002A);
    assert('/' as u32 == 0x002F);
    assert('*' as u32 == 0x002A);
    reveal_with_fuel(igr_utf8_of_upto, 10);
    assert(igr_utf8_of_upto(cs, 0) == seq![]);
    assert(igr_utf8_of_upto(cs, 1) == seq![0x66]);
    assert(igr_utf8_of_upto(cs, 2) == seq![0x66, 0x6F]);
    assert(igr_utf8_of_upto(cs, 3) == seq![0x66, 0x6F, 0x6F]);
    assert(igr_utf8_of_upto(cs, 4) == seq![0x66, 0x6F, 0x6F, 0x2F]);
    assert(igr_utf8_of_upto(cs, 5) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A]);
    assert(igr_utf8_of_upto(cs, 6) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A]);
    assert(igr_utf8_of_upto(cs, 7) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F]);
    assert(igr_utf8_of_upto(cs, 8) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
    assert(igr_utf8_of(cs) == seq![0x66, 0x6F, 0x6F, 0x2F, 0x2A, 0x2A, 0x2F, 0x2A]);
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
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::RecZ]],
    pos: 7,
    unclosed: false,
    opts: igr_opts(false, true),
};
    let stf = SState {
    chars: cs,
    stack: seq![],
    brs: seq![seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::RecZ, TokenS::Zom]],
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
    assert(L0.0.brs.index(0).index(0) == TokenS::Lit('f'));
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
    assert(L1.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L1.0.brs.index(0).index(1) == TokenS::Lit('o'));
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
    ladder_step(st2, false, 30);
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
    ladder_step(st3, false, 29);
    let L4 = spec_parse_loop(st4, false, 1);
    assert(L4.1 is None);
    assert(L4.0.chars == st5.chars);
    assert(L4.0.stack == st5.stack);
    assert(L4.0.brs.len() == st5.brs.len());
    assert(L4.0.brs.index(0).len() == 4);
    assert(L4.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L4.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L4.0.brs.index(0).index(3) == TokenS::RecZ);
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
    assert(L5.0.brs.index(0).len() == 5);
    assert(L5.0.brs.index(0).index(0) == TokenS::Lit('f'));
    assert(L5.0.brs.index(0).index(1) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(2) == TokenS::Lit('o'));
    assert(L5.0.brs.index(0).index(3) == TokenS::RecZ);
    assert(L5.0.brs.index(0).index(4) == TokenS::Zom);
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
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().len() == 5);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(0) == TokenS::Lit('f'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(1) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(2) == TokenS::Lit('o'));
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(3) == TokenS::RecZ);
    assert(spec_parse_glob(cs, igr_opts(false, true), false).get_Ok_0().index(4) == TokenS::Zom);
    assert(spec_parse_glob(cs, igr_opts(false, true), false)
        == Ok(seq![TokenS::Lit('f'), TokenS::Lit('o'), TokenS::Lit('o'), TokenS::RecZ, TokenS::Zom]));
}

} // verus!

fn main() {}

