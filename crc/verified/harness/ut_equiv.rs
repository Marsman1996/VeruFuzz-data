//! verified/harness/ut_equiv.rs -- the Table<L> byte-wise path == the NoTable bit-loop path (model level).
//!
//! [Origin Rust: code/src -- the L>0 lookup path of update_table and the L==0 no-table path agree byte for byte:
//!   a lane-0 table entry = the single-byte CRC over the pre-transformed poly (the lane0 ensures of crc*_table is that fact source)]
//! Verification form:
//!   - step-level equivalence lemmas (a lane-0 table contract ==> u*step_table == u*step_none{,_ref}; one per reflect side);
//!   - chain-level equivalence lemmas (induction over s; step unfolding/append facts via explicit drop_last/last asserts +
//!     the append lemmas of each chain in ut_append; specs have a single definition, all referencing verified/src);
//!   - the precondition is precisely the lane-0 ensures-shaped contract of crc*_table (width is any legal value, polymorphism kept).
//! Driver: out/kverus-run/mkp_vt.sh (the harness and verified/src compile as one crate).

use vstd::prelude::*;
use crate::model::*;
use crate::crc8::*;
use crate::crc16::*;
use crate::crc32::*;
use crate::crc64::*;
use crate::crc128::*;
use crate::model::{lem_andmask_u16, lem_andmask_u32, lem_andmask_u64, lem_andmask_u128};
use crate::ut_append::*;

verus! {
// =========================================================================
// Proof lemmas (assertion theorems; already at the end of the file).
// =========================================================================


/* -- u8: the lane-0 table step == the crc8 bit-loop step (u8 has no high/low halves; both reflect sides isomorphic) -- */

pub proof fn lem_u8step_equiv<const L: usize>(data: [[u8; 256]; L], poly: u8, reflect: bool)
    /* the lane-0 table contract = the crc8_table ensures (poly = the width-pre-transformed machine polynomial, in crc8arg shape) */
    requires (reflect == true  ==> (forall |j: u8| data[0][j as int] == crc8r_run(poly, j, 8)))
        && (reflect == false ==> (forall |j: u8| data[0][j as int] == crc8n_run(poly, j, 8)))
    ensures forall |crc: u8, b: u8| #[trigger] u8step_table(crc, data, b) == u8step_none(poly, reflect, crc, b),
{
    assert forall |crc: u8, b: u8| u8step_table(crc, data, b) == u8step_none(poly, reflect, crc, b) by {
        let idx = (crc ^ b) as usize;
        assert(idx < 256);
        let j = (crc ^ b);
        if reflect {
            assert(data[0][(crc ^ b) as int] == crc8r_run(poly, j, 8));
        } else {
            assert(data[0][(crc ^ b) as int] == crc8n_run(poly, j, 8));
        }
    }
}

pub proof fn lem_u8chain_equiv<const L: usize>(data: [[u8; 256]; L], poly: u8, reflect: bool, crc: u8, s: Seq<u8>)
    requires (reflect == true  ==> (forall |j: u8| data[0][j as int] == crc8r_run(poly, j, 8)))
        && (reflect == false ==> (forall |j: u8| data[0][j as int] == crc8n_run(poly, j, 8)))
    ensures u8run_table(crc, data, s) == u8nrun(poly, reflect, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
        /* on the empty sequence both sides are crc (the 0-step base case of the chain definitions) */
        assert(s + seq![] == s);
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u8chain_equiv(data, poly, reflect, crc, s2);
        lem_u8step_equiv(data, poly, reflect);
        u8run_table_append(crc, data, s2, s.last());
        u8nrun_append(poly, reflect, crc, s2, s.last());
        assert(u8step_table(u8run_table(crc, data, s2), data, s.last())
            == u8step_none(poly, reflect, u8run_table(crc, data, s2), s.last()));
    }
}




/* -- u16: the reflect branch -- */

pub proof fn lem_u16step_equiv_r<const L: usize>(data: [[u16; 256]; L], poly: u16, width: u8)
    /* lane-0 table contract (the reflect==true arm of the crc16_table ensures; poly is the raw upstream poly) */
    requires 1 <= width && width <= 16,
        (forall |j: u8| data[0][j as int] == crc16r_run(shrs_u16(revm16(poly), (16 - width) as nat), j as u16, 8))
    ensures forall |crc: u16, b: u8| #[trigger] u16step_table(crc, data, b)
        == u16step_none(shrs_u16(revm16(poly), (16 - width) as nat), true, crc, b),
{
    assert forall |crc: u16, b: u8| u16step_table(crc, data, b)
        == u16step_none(shrs_u16(revm16(poly), (16 - width) as nat), true, crc, b) by {
        let mid = ((crc ^ (b as u16)) & 0xff);
        lem_andmask_u16(((crc ^ (b as u16))));
        assert(mid < 256);
        let to_crc = mid as u16;
        let j = (to_crc) as u8;
        assert(j as u16 == to_crc);
        assert(to_crc as usize as int == j as int);
        assert(data[0][j as int] == crc16r_run(shrs_u16(revm16(poly), (16 - width) as nat), j as u16, 8));
    }
}

pub proof fn lem_u16chain_equiv_r<const L: usize>(data: [[u16; 256]; L], poly: u16, width: u8, crc: u16, s: Seq<u8>)
    requires 1 <= width && width <= 16,
        (forall |j: u8| data[0][j as int] == crc16r_run(shrs_u16(revm16(poly), (16 - width) as nat), j as u16, 8))
    ensures u16run_table(crc, data, s)
        == u16run(shrs_u16(revm16(poly), (16 - width) as nat), true, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u16chain_equiv_r(data, poly, width, crc, s2);
        lem_u16step_equiv_r(data, poly, width);
        u16run_table_append(crc, data, s2, s.last());
        u16run_append(shrs_u16(revm16(poly), (16 - width) as nat), true, crc, s2, s.last());
        assert(u16step_table(u16run_table(crc, data, s2), data, s.last())
            == u16step_none(shrs_u16(revm16(poly), (16 - width) as nat), true, u16run_table(crc, data, s2), s.last()));
    }
}

/* -- u16: the non-reflect branch (the table ref step == the crc16n_run chain step) -- */

pub proof fn lem_u16step_equiv_n<const L: usize>(data: [[u16; 256]; L], poly: u16, width: u8)
    requires 1 <= width && width <= 16,
        (forall |j: u8| data[0][j as int] == crc16n_run(shls_u16(poly, (16 - width) as nat), shl8_u16(j as u16), 8))
    ensures forall |crc: u16, b: u8| #[trigger] u16step_table_ref(crc, data, b)
        == u16step_none_ref(shls_u16(poly, (16 - width) as nat), false, crc, b),
{
    assert forall |crc: u16, b: u8| u16step_table_ref(crc, data, b)
        == u16step_none_ref(shls_u16(poly, (16 - width) as nat), false, crc, b) by {
        let mid = (((crc >> 8) ^ (b as u16)) & 0xff);
        lem_andmask_u16((((crc >> 8) ^ (b as u16))));
        assert(mid < 256);
        let to_crc = mid as u16;
        let j = (to_crc) as u8;
        assert(j as u16 == to_crc);
        assert(to_crc as usize as int == j as int);
        assert(data[0][j as int]
            == crc16n_run(shls_u16(poly, (16 - width) as nat), shl8_u16(j as u16), 8));
    }
}

pub proof fn lem_u16chain_equiv_n<const L: usize>(data: [[u16; 256]; L], poly: u16, width: u8, crc: u16, s: Seq<u8>)
    requires 1 <= width && width <= 16,
        (forall |j: u8| data[0][j as int] == crc16n_run(shls_u16(poly, (16 - width) as nat), shl8_u16(j as u16), 8))
    ensures u16run_table_ref(crc, data, s)
        == u16run_ref(shls_u16(poly, (16 - width) as nat), false, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u16chain_equiv_n(data, poly, width, crc, s2);
        lem_u16step_equiv_n(data, poly, width);
        u16run_table_append_ref(crc, data, s2, s.last());
        u16run_append_ref(shls_u16(poly, (16 - width) as nat), false, crc, s2, s.last());
        assert(u16step_table_ref(u16run_table_ref(crc, data, s2), data, s.last())
            == u16step_none_ref(shls_u16(poly, (16 - width) as nat), false, u16run_table_ref(crc, data, s2), s.last()));
    }
}


/* -- u32: the reflect branch -- */

pub proof fn lem_u32step_equiv_r<const L: usize>(data: [[u32; 256]; L], poly: u32, width: u8)
    /* lane-0 table contract (the reflect==true arm of the crc32_table ensures; poly is the raw upstream poly) */
    requires 1 <= width && width <= 32,
        (forall |j: u8| data[0][j as int] == crc32r_run(shrs_u32(revm32(poly), (32 - width) as nat), j as u32, 8))
    ensures forall |crc: u32, b: u8| #[trigger] u32step_table(crc, data, b)
        == u32step_none(shrs_u32(revm32(poly), (32 - width) as nat), true, crc, b),
{
    assert forall |crc: u32, b: u8| u32step_table(crc, data, b)
        == u32step_none(shrs_u32(revm32(poly), (32 - width) as nat), true, crc, b) by {
        let mid = ((crc ^ (b as u32)) & 0xff);
        lem_andmask_u32(((crc ^ (b as u32))));
        assert(mid < 256);
        let to_crc = mid as u32;
        let j = (to_crc) as u8;
        assert(j as u32 == to_crc);
        assert(data[0][j as int] == crc32r_run(shrs_u32(revm32(poly), (32 - width) as nat), j as u32, 8));
    }
}

pub proof fn lem_u32chain_equiv_r<const L: usize>(data: [[u32; 256]; L], poly: u32, width: u8, crc: u32, s: Seq<u8>)
    requires 1 <= width && width <= 32,
        (forall |j: u8| data[0][j as int] == crc32r_run(shrs_u32(revm32(poly), (32 - width) as nat), j as u32, 8))
    ensures u32run_table(crc, data, s)
        == u32run(shrs_u32(revm32(poly), (32 - width) as nat), true, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u32chain_equiv_r(data, poly, width, crc, s2);
        lem_u32step_equiv_r(data, poly, width);
        u32run_table_append(crc, data, s2, s.last());
        u32run_append(shrs_u32(revm32(poly), (32 - width) as nat), true, crc, s2, s.last());
        assert(u32step_table(u32run_table(crc, data, s2), data, s.last())
            == u32step_none(shrs_u32(revm32(poly), (32 - width) as nat), true, u32run_table(crc, data, s2), s.last()));
    }
}

/* -- u32: the non-reflect branch (the table ref step == the crc32n_run chain step) -- */

pub proof fn lem_u32step_equiv_n<const L: usize>(data: [[u32; 256]; L], poly: u32, width: u8)
    requires 1 <= width && width <= 32,
        (forall |j: u8| data[0][j as int] == crc32n_run(shls_u32(poly, (32 - width) as nat), shl24_u32(j as u32), 8))
    ensures forall |crc: u32, b: u8| #[trigger] u32step_table_ref(crc, data, b)
        == u32step_none_ref(shls_u32(poly, (32 - width) as nat), false, crc, b),
{
    assert forall |crc: u32, b: u8| u32step_table_ref(crc, data, b)
        == u32step_none_ref(shls_u32(poly, (32 - width) as nat), false, crc, b) by {
        let mid = (((crc >> 24) ^ (b as u32)) & 0xff);
        lem_andmask_u32((((crc >> 24) ^ (b as u32))));
        assert(mid < 256);
        let to_crc = mid as u32;
        let j = (to_crc) as u8;
        assert(j as u32 == to_crc);
        assert(to_crc as usize as int == j as int);
        assert(data[0][j as int]
            == crc32n_run(shls_u32(poly, (32 - width) as nat), shl24_u32(j as u32), 8));
    }
}

pub proof fn lem_u32chain_equiv_n<const L: usize>(data: [[u32; 256]; L], poly: u32, width: u8, crc: u32, s: Seq<u8>)
    requires 1 <= width && width <= 32,
        (forall |j: u8| data[0][j as int] == crc32n_run(shls_u32(poly, (32 - width) as nat), shl24_u32(j as u32), 8))
    ensures u32run_table_ref(crc, data, s)
        == u32run_ref(shls_u32(poly, (32 - width) as nat), false, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u32chain_equiv_n(data, poly, width, crc, s2);
        lem_u32step_equiv_n(data, poly, width);
        u32run_table_append_ref(crc, data, s2, s.last());
        u32run_append_ref(shls_u32(poly, (32 - width) as nat), false, crc, s2, s.last());
        assert(u32step_table_ref(u32run_table_ref(crc, data, s2), data, s.last())
            == u32step_none_ref(shls_u32(poly, (32 - width) as nat), false, u32run_table_ref(crc, data, s2), s.last()));
    }
}


/* -- u64: the reflect branch -- */

pub proof fn lem_u64step_equiv_r<const L: usize>(data: [[u64; 256]; L], poly: u64, width: u8)
    /* lane-0 table contract (the reflect==true arm of the crc64_table ensures; poly is the raw upstream poly) */
    requires 1 <= width && width <= 64,
        (forall |j: u8| data[0][j as int] == crc64r_run(shrs_u64(revm64(poly), (64 - width) as nat), j as u64, 8))
    ensures forall |crc: u64, b: u8| #[trigger] u64step_table(crc, data, b)
        == u64step_none(shrs_u64(revm64(poly), (64 - width) as nat), true, crc, b),
{
    assert forall |crc: u64, b: u8| u64step_table(crc, data, b)
        == u64step_none(shrs_u64(revm64(poly), (64 - width) as nat), true, crc, b) by {
        let mid = ((crc ^ (b as u64)) & 0xff);
        lem_andmask_u64(((crc ^ (b as u64))));
        assert(mid < 256);
        let to_crc = mid as u64;
        let j = (to_crc) as u8;
        assert(j as u64 == to_crc);
        assert(data[0][j as int] == crc64r_run(shrs_u64(revm64(poly), (64 - width) as nat), j as u64, 8));
    }
}

pub proof fn lem_u64chain_equiv_r<const L: usize>(data: [[u64; 256]; L], poly: u64, width: u8, crc: u64, s: Seq<u8>)
    requires 1 <= width && width <= 64,
        (forall |j: u8| data[0][j as int] == crc64r_run(shrs_u64(revm64(poly), (64 - width) as nat), j as u64, 8))
    ensures u64run_table(crc, data, s)
        == u64run(shrs_u64(revm64(poly), (64 - width) as nat), true, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u64chain_equiv_r(data, poly, width, crc, s2);
        lem_u64step_equiv_r(data, poly, width);
        u64run_table_append(crc, data, s2, s.last());
        u64run_append(shrs_u64(revm64(poly), (64 - width) as nat), true, crc, s2, s.last());
        assert(u64step_table(u64run_table(crc, data, s2), data, s.last())
            == u64step_none(shrs_u64(revm64(poly), (64 - width) as nat), true, u64run_table(crc, data, s2), s.last()));
    }
}

/* -- u64: the non-reflect branch (the table ref step == the crc64n_run chain step) -- */

pub proof fn lem_u64step_equiv_n<const L: usize>(data: [[u64; 256]; L], poly: u64, width: u8)
    requires 1 <= width && width <= 64,
        (forall |j: u8| data[0][j as int] == crc64n_run(shls_u64(poly, (64 - width) as nat), shl56_u64(j as u64), 8))
    ensures forall |crc: u64, b: u8| #[trigger] u64step_table_ref(crc, data, b)
        == u64step_none_ref(shls_u64(poly, (64 - width) as nat), false, crc, b),
{
    assert forall |crc: u64, b: u8| u64step_table_ref(crc, data, b)
        == u64step_none_ref(shls_u64(poly, (64 - width) as nat), false, crc, b) by {
        let mid = (((crc >> 56) ^ (b as u64)) & 0xff);
        lem_andmask_u64((((crc >> 56) ^ (b as u64))));
        assert(mid < 256);
        let to_crc = mid as u64;
        let j = (to_crc) as u8;
        assert(j as u64 == to_crc);
        assert(to_crc as usize as int == j as int);
        assert(data[0][j as int]
            == crc64n_run(shls_u64(poly, (64 - width) as nat), shl56_u64(j as u64), 8));
    }
}

pub proof fn lem_u64chain_equiv_n<const L: usize>(data: [[u64; 256]; L], poly: u64, width: u8, crc: u64, s: Seq<u8>)
    requires 1 <= width && width <= 64,
        (forall |j: u8| data[0][j as int] == crc64n_run(shls_u64(poly, (64 - width) as nat), shl56_u64(j as u64), 8))
    ensures u64run_table_ref(crc, data, s)
        == u64run_ref(shls_u64(poly, (64 - width) as nat), false, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u64chain_equiv_n(data, poly, width, crc, s2);
        lem_u64step_equiv_n(data, poly, width);
        u64run_table_append_ref(crc, data, s2, s.last());
        u64run_append_ref(shls_u64(poly, (64 - width) as nat), false, crc, s2, s.last());
        assert(u64step_table_ref(u64run_table_ref(crc, data, s2), data, s.last())
            == u64step_none_ref(shls_u64(poly, (64 - width) as nat), false, u64run_table_ref(crc, data, s2), s.last()));
    }
}


/* -- u128: the reflect branch -- */

pub proof fn lem_u128step_equiv_r<const L: usize>(data: [[u128; 256]; L], poly: u128, width: u8)
    /* lane-0 table contract (the reflect==true arm of the crc128_table ensures; poly is the raw upstream poly) */
    requires 1 <= width && width <= 128,
        (forall |j: u8| data[0][j as int] == crc128r_run(shrs_u128(revm128(poly), (128 - width) as nat), j as u128, 8))
    ensures forall |crc: u128, b: u8| #[trigger] u128step_table(crc, data, b)
        == u128step_none(shrs_u128(revm128(poly), (128 - width) as nat), true, crc, b),
{
    assert forall |crc: u128, b: u8| u128step_table(crc, data, b)
        == u128step_none(shrs_u128(revm128(poly), (128 - width) as nat), true, crc, b) by {
        let mid = ((crc ^ (b as u128)) & 0xff);
        lem_andmask_u128(((crc ^ (b as u128))));
        assert(mid < 256);
        let to_crc = mid as u128;
        let j = (to_crc) as u8;
        assert(j as u128 == to_crc);
        assert(data[0][j as int] == crc128r_run(shrs_u128(revm128(poly), (128 - width) as nat), j as u128, 8));
    }
}

pub proof fn lem_u128chain_equiv_r<const L: usize>(data: [[u128; 256]; L], poly: u128, width: u8, crc: u128, s: Seq<u8>)
    requires 1 <= width && width <= 128,
        (forall |j: u8| data[0][j as int] == crc128r_run(shrs_u128(revm128(poly), (128 - width) as nat), j as u128, 8))
    ensures u128run_table(crc, data, s)
        == u128run(shrs_u128(revm128(poly), (128 - width) as nat), true, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u128chain_equiv_r(data, poly, width, crc, s2);
        lem_u128step_equiv_r(data, poly, width);
        u128run_table_append(crc, data, s2, s.last());
        u128run_append(shrs_u128(revm128(poly), (128 - width) as nat), true, crc, s2, s.last());
        assert(u128step_table(u128run_table(crc, data, s2), data, s.last())
            == u128step_none(shrs_u128(revm128(poly), (128 - width) as nat), true, u128run_table(crc, data, s2), s.last()));
    }
}

/* -- u128: the non-reflect branch (the table ref step == the crc128n_run chain step) -- */

pub proof fn lem_u128step_equiv_n<const L: usize>(data: [[u128; 256]; L], poly: u128, width: u8)
    requires 1 <= width && width <= 128,
        (forall |j: u8| data[0][j as int] == crc128n_run(shls_u128(poly, (128 - width) as nat), shl120_u128(j as u128), 8))
    ensures forall |crc: u128, b: u8| #[trigger] u128step_table_ref(crc, data, b)
        == u128step_none_ref(shls_u128(poly, (128 - width) as nat), false, crc, b),
{
    assert forall |crc: u128, b: u8| u128step_table_ref(crc, data, b)
        == u128step_none_ref(shls_u128(poly, (128 - width) as nat), false, crc, b) by {
        let mid = (((crc >> 120) ^ (b as u128)) & 0xff);
        lem_andmask_u128((((crc >> 120) ^ (b as u128))));
        assert(mid < 256);
        let to_crc = mid as u128;
        let j = (to_crc) as u8;
        assert(j as u128 == to_crc);
        assert(to_crc as usize as int == j as int);
        assert(data[0][j as int]
            == crc128n_run(shls_u128(poly, (128 - width) as nat), shl120_u128(j as u128), 8));
    }
}

pub proof fn lem_u128chain_equiv_n<const L: usize>(data: [[u128; 256]; L], poly: u128, width: u8, crc: u128, s: Seq<u8>)
    requires 1 <= width && width <= 128,
        (forall |j: u8| data[0][j as int] == crc128n_run(shls_u128(poly, (128 - width) as nat), shl120_u128(j as u128), 8))
    ensures u128run_table_ref(crc, data, s)
        == u128run_ref(shls_u128(poly, (128 - width) as nat), false, crc, s),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s2 = s.drop_last();
        assert(s2.len() + 1 == s.len());
        assert(s.drop_last() == s2);
        assert(s.last() == s[s2.len() as int]);
        assert(s == s2 + seq![s.last()]);
        lem_u128chain_equiv_n(data, poly, width, crc, s2);
        lem_u128step_equiv_n(data, poly, width);
        u128run_table_append_ref(crc, data, s2, s.last());
        u128run_append_ref(shls_u128(poly, (128 - width) as nat), false, crc, s2, s.last());
        assert(u128step_table_ref(u128run_table_ref(crc, data, s2), data, s.last())
            == u128step_none_ref(shls_u128(poly, (128 - width) as nat), false, u128run_table_ref(crc, data, s2), s.last()));
    }
}

} // verus!
