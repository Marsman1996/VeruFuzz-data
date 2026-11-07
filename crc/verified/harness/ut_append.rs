//! verified/harness/ut_append.rs -- the verification-form harness of the digest split-update (message-splitting) equivalence.
//!
//! [Origin Rust: code/src/test.rs / doc -- a split update and a one-shot update agree on the result;
//!   the concrete shape: Digest::update split == one-shot update (split-then-append)]
//! Verification form:
//!   - for each machine byte-chain spec (u8nrun/u8run_table/u16run*/u32run*/u64run*/u128run*)
//!     the "chain split-append" lemma: run(poly, ..., crc, s + t) == run(poly, ..., run(..., crc, s), t).
//!   - these lemmas are the model-level core of Digest::update splitting (update's ensures are all defined
//!     via run; the split equality instantiates segment by segment at the call site, no extra exec obligation);
//!   - [Origin Rust: code/src/test.rs mod test test_clone -- the Digest Clone semantics]
//!     Clone is a derived structural copy (Digest is {(crc shared reference), value}); its split semantics are
//!     taken over directly by this file's chain-append lemmas + the update ensures in crc*.rs, with no separate exec obligation.

use vstd::prelude::*;
use crate::model::*;
use crate::crc8::{u8nrun, u8nrun_append, u8run_table, u8run_table_append, u8step_none, u8step_table};
use crate::crc16::*;
use crate::crc32::*;
use crate::crc64::*;
use crate::crc128::*;

verus! {
// =========================================================================
// Proof lemmas (assertion theorems; already at the end of the file).
// =========================================================================



/* -- u8 -- */

pub proof fn lem_u8nrun_cat(poly: u8, reflect: bool, crc: u8, s: Seq<u8>, t: Seq<u8>)
    ensures u8nrun(poly, reflect, crc, s + t)
        == u8nrun(poly, reflect, u8nrun(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u8nrun_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u8nrun_append(poly, reflect, crc, s + t2, t.last());
        u8nrun_append(poly, reflect, u8nrun(poly, reflect, crc, s), t2, t.last());
        assert(u8nrun(poly, reflect, u8nrun(poly, reflect, crc, s), t2)
            == u8nrun(poly, reflect, crc, s + t2));
    }
}

pub proof fn lem_u8run_table_cat<const L: usize>(crc: u8, data: [[u8; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u8run_table(crc, data, s + t)
        == u8run_table(u8run_table(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u8run_table_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u8run_table_append(crc, data, s + t2, t.last());
        u8run_table_append(u8run_table(crc, data, s), data, t2, t.last());
    }
}


/* -- u16 -- */

pub proof fn lem_u16run_cat(poly: u16, reflect: bool, crc: u16, s: Seq<u8>, t: Seq<u8>)
    ensures u16run(poly, reflect, crc, s + t)
        == u16run(poly, reflect, u16run(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u16run_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u16run_append(poly, reflect, crc, s + t2, t.last());
        u16run_append(poly, reflect, u16run(poly, reflect, crc, s), t2, t.last());
    }
}

pub proof fn lem_u16run_ref_cat(poly: u16, reflect: bool, crc: u16, s: Seq<u8>, t: Seq<u8>)
    ensures u16run_ref(poly, reflect, crc, s + t)
        == u16run_ref(poly, reflect, u16run_ref(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u16run_ref_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u16run_append_ref(poly, reflect, crc, s + t2, t.last());
        u16run_append_ref(poly, reflect, u16run_ref(poly, reflect, crc, s), t2, t.last());
    }
}

pub proof fn lem_u16run_table_cat<const L: usize>(crc: u16, data: [[u16; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u16run_table(crc, data, s + t)
        == u16run_table(u16run_table(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u16run_table_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u16run_table_append(crc, data, s + t2, t.last());
        u16run_table_append(u16run_table(crc, data, s), data, t2, t.last());
    }
}

pub proof fn lem_u16run_table_ref_cat<const L: usize>(crc: u16, data: [[u16; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u16run_table_ref(crc, data, s + t)
        == u16run_table_ref(u16run_table_ref(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u16run_table_ref_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u16run_table_append_ref(crc, data, s + t2, t.last());
        u16run_table_append_ref(u16run_table_ref(crc, data, s), data, t2, t.last());
    }
}


/* -- u32 -- */

pub proof fn lem_u32run_cat(poly: u32, reflect: bool, crc: u32, s: Seq<u8>, t: Seq<u8>)
    ensures u32run(poly, reflect, crc, s + t)
        == u32run(poly, reflect, u32run(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u32run_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u32run_append(poly, reflect, crc, s + t2, t.last());
        u32run_append(poly, reflect, u32run(poly, reflect, crc, s), t2, t.last());
    }
}

pub proof fn lem_u32run_ref_cat(poly: u32, reflect: bool, crc: u32, s: Seq<u8>, t: Seq<u8>)
    ensures u32run_ref(poly, reflect, crc, s + t)
        == u32run_ref(poly, reflect, u32run_ref(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u32run_ref_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u32run_append_ref(poly, reflect, crc, s + t2, t.last());
        u32run_append_ref(poly, reflect, u32run_ref(poly, reflect, crc, s), t2, t.last());
    }
}

pub proof fn lem_u32run_table_cat<const L: usize>(crc: u32, data: [[u32; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u32run_table(crc, data, s + t)
        == u32run_table(u32run_table(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u32run_table_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u32run_table_append(crc, data, s + t2, t.last());
        u32run_table_append(u32run_table(crc, data, s), data, t2, t.last());
    }
}

pub proof fn lem_u32run_table_ref_cat<const L: usize>(crc: u32, data: [[u32; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u32run_table_ref(crc, data, s + t)
        == u32run_table_ref(u32run_table_ref(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u32run_table_ref_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u32run_table_append_ref(crc, data, s + t2, t.last());
        u32run_table_append_ref(u32run_table_ref(crc, data, s), data, t2, t.last());
    }
}


/* -- u64 -- */

pub proof fn lem_u64run_cat(poly: u64, reflect: bool, crc: u64, s: Seq<u8>, t: Seq<u8>)
    ensures u64run(poly, reflect, crc, s + t)
        == u64run(poly, reflect, u64run(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u64run_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u64run_append(poly, reflect, crc, s + t2, t.last());
        u64run_append(poly, reflect, u64run(poly, reflect, crc, s), t2, t.last());
    }
}

pub proof fn lem_u64run_ref_cat(poly: u64, reflect: bool, crc: u64, s: Seq<u8>, t: Seq<u8>)
    ensures u64run_ref(poly, reflect, crc, s + t)
        == u64run_ref(poly, reflect, u64run_ref(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u64run_ref_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u64run_append_ref(poly, reflect, crc, s + t2, t.last());
        u64run_append_ref(poly, reflect, u64run_ref(poly, reflect, crc, s), t2, t.last());
    }
}

pub proof fn lem_u64run_table_cat<const L: usize>(crc: u64, data: [[u64; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u64run_table(crc, data, s + t)
        == u64run_table(u64run_table(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u64run_table_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u64run_table_append(crc, data, s + t2, t.last());
        u64run_table_append(u64run_table(crc, data, s), data, t2, t.last());
    }
}

pub proof fn lem_u64run_table_ref_cat<const L: usize>(crc: u64, data: [[u64; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u64run_table_ref(crc, data, s + t)
        == u64run_table_ref(u64run_table_ref(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u64run_table_ref_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u64run_table_append_ref(crc, data, s + t2, t.last());
        u64run_table_append_ref(u64run_table_ref(crc, data, s), data, t2, t.last());
    }
}


/* -- u128 -- */

pub proof fn lem_u128run_cat(poly: u128, reflect: bool, crc: u128, s: Seq<u8>, t: Seq<u8>)
    ensures u128run(poly, reflect, crc, s + t)
        == u128run(poly, reflect, u128run(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u128run_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u128run_append(poly, reflect, crc, s + t2, t.last());
        u128run_append(poly, reflect, u128run(poly, reflect, crc, s), t2, t.last());
    }
}

pub proof fn lem_u128run_ref_cat(poly: u128, reflect: bool, crc: u128, s: Seq<u8>, t: Seq<u8>)
    ensures u128run_ref(poly, reflect, crc, s + t)
        == u128run_ref(poly, reflect, u128run_ref(poly, reflect, crc, s), t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u128run_ref_cat(poly, reflect, crc, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u128run_append_ref(poly, reflect, crc, s + t2, t.last());
        u128run_append_ref(poly, reflect, u128run_ref(poly, reflect, crc, s), t2, t.last());
    }
}

pub proof fn lem_u128run_table_cat<const L: usize>(crc: u128, data: [[u128; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u128run_table(crc, data, s + t)
        == u128run_table(u128run_table(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u128run_table_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u128run_table_append(crc, data, s + t2, t.last());
        u128run_table_append(u128run_table(crc, data, s), data, t2, t.last());
    }
}

pub proof fn lem_u128run_table_ref_cat<const L: usize>(crc: u128, data: [[u128; 256]; L], s: Seq<u8>, t: Seq<u8>)
    ensures u128run_table_ref(crc, data, s + t)
        == u128run_table_ref(u128run_table_ref(crc, data, s), data, t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t == s);
    } else {
        let t2 = t.drop_last();
        lem_u128run_table_ref_cat(crc, data, s, t2);
        assert(s + t == s + t2 + seq![t.last()]);
        u128run_table_append_ref(crc, data, s + t2, t.last());
        u128run_table_append_ref(u128run_table_ref(crc, data, s), data, t2, t.last());
    }
}

} // verus!
