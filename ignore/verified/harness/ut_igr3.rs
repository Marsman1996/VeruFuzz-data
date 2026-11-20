//! IG-R harness ut_igr3 -- the SHORT-DOMAIN GlobBuilder verdict
//! anchor unit (the green slice of the GlobSet-consumption re-anchor):
//! the admit-seam instances whose actuals stay in the proven-fast size
//! class of the GL2 parse value machine. Every row machine-checks the
//! upstream GlobBuilder::build verdict on the instance via GL2's
//! spec_parse_glob over the exact call-site options the ignore crate
//! passes (gitignore.rs:531-540), with the char form's utf8 bytes tied
//! by a per-char-grounded step chain (the #GL-8 cast residue needs the
//! grounds; the p14 probe recipe).
//!
//! The long-domain remainder: the rows authored but parked in ut_igr1
//! -- the parse compute on star-composite shapes hangs (the GL2-era
//! deep-composite wall, reproduced this batch at '**/'-shaped sizes
//! 3..9 by probes p4a/p5b/p7/p10); the ladder-row regeneration recipe
//! is recorded as pit #IG-R-1. The admit rows themselves stay
//! runtime-column backed in ut_ig2/ut_ig3; this unit is the formal
//! side of the seams for the instances it covers.

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::seq::seq;

#[path = "../../../globset/verified/src/lib.rs"]
mod glib;

#[allow(unused_imports)]
use glib::CowBytes;
#[allow(unused_imports)]
use glib::pathutil;

use glib::glob::{GlobOptions, spec_parse_glob, spec_utf8_encode};

verus! {

/// The call-site options the ignore crate passes to GlobBuilder
/// (upstream gitignore.rs:531-540).
pub open spec fn igr_opts(ci: bool, auc: bool) -> GlobOptions {
    GlobOptions {
        case_insensitive: ci,
        literal_separator: true,
        backslash_escape: true,
        empty_alternates: false,
        allow_unclosed_class: auc,
    }
}

/// The prefix fold of the char form's utf8 bytes (GL's encode lane).
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

/// The full fold.
pub open spec fn igr_utf8_of(cs: Seq<char>) -> Seq<u8> {
    igr_utf8_of_upto(cs, cs.len() as nat)
}

/// Ground helper: the empty Seq is empty.
pub proof fn assert_empty_seq_setup() {
    let e: Seq<u8> = Seq::empty();
    assert(e.len() == 0);
}

/// Builder-admit seam instance (actual bytes '**', ci=false, auc=true).
/// Provenance: ut_ig2 kat_ig30 (the dir-suffix drop feeds GlobBuilder the bare '**').
proof fn igr3_b_stst() {
    assert('*' as u32 == 0x2A);
    assert('*' as u32 == 0x2A);
    let cs = seq!['*', '*'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2A]) by {
        assert_empty_seq_setup();
        assert(cs.index(0) as u32 == 0x2A);
        assert(spec_utf8_encode(cs.index(0) as u32) == seq![0x2A]);
        assert(cs.index(1) as u32 == 0x2A);
        assert(spec_utf8_encode(cs.index(1) as u32) == seq![0x2A]);
        assert(igr_utf8_of_upto(cs, 0) == seq![]);
        assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
        assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2A]);
        assert(cs.len() == 2);
    }
    assert(spec_parse_glob(
        seq!['*', '*'],
        igr_opts(false, true),
        false,
    ) is Ok) by (compute);
}

/// Builder-admit seam instance (actual bytes '*.c', ci=false, auc=true).
/// Provenance: the '*.c' admit row in ut_ig2 (verdict true).
proof fn igr3_b_stc() {
    assert('*' as u32 == 0x2A);
    assert('.' as u32 == 0x2E);
    assert('c' as u32 == 0x63);
    let cs = seq!['*', '.', 'c'];
    assert(igr_utf8_of(cs) == seq![0x2A, 0x2E, 0x63]) by {
        assert_empty_seq_setup();
        assert(cs.index(0) as u32 == 0x2A);
        assert(spec_utf8_encode(cs.index(0) as u32) == seq![0x2A]);
        assert(cs.index(1) as u32 == 0x2E);
        assert(spec_utf8_encode(cs.index(1) as u32) == seq![0x2E]);
        assert(cs.index(2) as u32 == 0x63);
        assert(spec_utf8_encode(cs.index(2) as u32) == seq![0x63]);
        assert(igr_utf8_of_upto(cs, 0) == seq![]);
        assert(igr_utf8_of_upto(cs, 1) == seq![0x2A]);
        assert(igr_utf8_of_upto(cs, 2) == seq![0x2A, 0x2E]);
        assert(igr_utf8_of_upto(cs, 3) == seq![0x2A, 0x2E, 0x63]);
        assert(cs.len() == 3);
    }
    assert(spec_parse_glob(
        seq!['*', '.', 'c'],
        igr_opts(false, true),
        false,
    ) is Ok) by (compute);
}

/// Builder-admit seam instance (actual bytes '', ci=false, auc=true).
/// Provenance: the bare '/' line whose rewrite chain yields the empty actual (the GlobBuilder('') row; verdict true).
proof fn igr3_b_empty() {
    let cs = seq![];
    assert(igr_utf8_of(cs) == seq![]) by {
        assert_empty_seq_setup();
        assert(igr_utf8_of_upto(cs, 0) == seq![]);
        assert(cs.len() == 0);
    }
    assert(spec_parse_glob(
        seq![],
        igr_opts(false, true),
        false,
    ) is Ok) by (compute);
}

} // verus!

fn main() {}
