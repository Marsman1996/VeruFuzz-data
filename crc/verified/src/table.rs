//! verified/src/table.rs -- verus mirror of code/src/table.rs (pin 1894aa9).
//!
//! [Origin Rust: code/src/table.rs -- pub(crate) const fn crc8/16/32/64/128_table<L>]
//! Porting policy (incremental, minimal):
//!   - `const fn` -> `exec fn` (the const-generic L is kept), const dropped from the signature;
//!   - `requires 1 <= width <= W`: an implicit upstream precondition (the catalog guarantees width
//!     belongs to the family); otherwise the uN subtraction `W - width` is out of range (u8 underflow panic); this is the value contract of width;
//!   - the lane-0 fill loop writes its invariants in ensures shape (shls/shrs bridging equalities + a
//!     forall) (under loop isolation, derived equalities must enter the loop body via the invariant); L=0 (NoTable) is
//!     gated by `L > 0 ==>`; upstream new() likewise builds an empty table at L=0;
//!   - the lane k>=1 double loop: index safety + termination + the lane-0 forall preserved across
//!     the loops (writes happen only on the e>=1 rows); lane composition semantics left unmodeled (partial), carried by runtime re-verification;
//!   - `poly.reverse_bits()` replaced at the expression level by a local rev_W exec helper (revmW semantics);
//!   - `poly << (W - width)` machine-truncating left shift handled via the shift-amount bound (width <= W);
//!   - the forall items kept in invariants must keep their triggers available (j as T instantiates them explicitly).

use vstd::prelude::*;
use crate::model::*;
use super::util::*;
use super::crc8::rev8;
use super::crc16::rev16;
use super::crc32::rev32;
use super::crc64::rev64;
use super::crc128::rev128;

verus! {

broadcast use {
    lem_and1_u8, lem_and1_u16, lem_and1_u32, lem_and1_u64, lem_and1_u128,
    lem_shl1_u8, lem_shl1_u16, lem_shl1_u32, lem_shl1_u64, lem_shl1_u128,
    lem_shl8_u16, lem_shl24_u32, lem_shl56_u64, lem_shl120_u128,
    lem_shls_u8, lem_shls_u16, lem_shls_u32, lem_shls_u64, lem_shls_u128,
    lem_shrs_u8, lem_shrs_u16, lem_shrs_u32, lem_shrs_u64, lem_shrs_u128,
    lem_or_add_u8, lem_or_add_u16, lem_or_add_u32, lem_or_add_u64, lem_or_add_u128,
};

pub exec fn crc8_table<const L: usize>(width: u8, poly: u8, reflect: bool) -> (tbl: [[u8; 256]; L])
    requires
        1 <= width && width <= 8,
    ensures
        /* [verus note: the ensures is predicated on L>0 -- Table<0> (NoTable) has no lane; upstream new() likewise builds an empty table at L=0] */
        L > 0 ==> ((reflect == true  ==> forall |j: u8| tbl@[0][j as int] == crc8r_run(shrs_u8((revm8(poly)) as u8, (8u8 - width) as nat), j, 8)) && (reflect == false ==> forall |j: u8| tbl@[0][j as int] == crc8n_run(shls_u8(poly, (8u8 - width) as nat), j, 8))),
{
    let poly_adj = if reflect {
        let poly_v = rev8(poly);
        poly_v >> (8u8 - width)
    } else {
        poly << (8u8 - width)
    };
    proof {
        /* [verus note: shift dispatch bridges -- lem_shrs/lem_shls explicitly instantiated for s = 8u8 - width
         *  (< 8 guaranteed by the width precondition); the rev8 exec fact poly_v == revm8(poly) is carried in by the exec call's postcondition] */
        if reflect {
            lem_shrs_u8(revm8(poly), (8 - width) as u8);
        } else {
            lem_shls_u8(poly, (8 - width) as u8);
        }
    }
    assert(poly_adj == (if reflect { shrs_u8((revm8(poly)) as u8, (8u8 - width) as nat) } else { shls_u8(poly, (8u8 - width) as nat) }));
    let mut table = [[0u8; 256]; L];
    let mut i: usize = 0;
    while i < 256 && L > 0
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the poly_adj bridging equality and the lane-0 forall are written in
                 *  ensures shape into the invariant (otherwise the exec call's postcondition facts and derived equalities do not enter the loop body)] */
                poly_adj == (if reflect { shrs_u8((revm8(poly)) as u8, (8u8 - width) as nat) } else { shls_u8(poly, (8u8 - width) as nat) }),
                L > 0 ==> ((reflect == true  ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc8r_run(shrs_u8((revm8(poly)) as u8, (8u8 - width) as nat), j, 8)) && (reflect == false ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc8n_run(shls_u8(poly, (8u8 - width) as nat), j, 8))),
            decreases 256 - i,
    {
        table[0][i] = crc8(poly_adj, reflect, i as u8);
        i = i + 1;
    }
    if L > 1 {
        // [Origin Rust: lane k>=1 double loop -- only index safety and termination are kept (the semantics modeled as partial)]
        let mut i: usize = 0;
        while i < 256
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the if(L>1) fact and the lane-0 forall (writes happen only on the
                 *  e>=1 rows, so lane-0 content is preserved across both loops) are threaded in / preserved via the invariants] */
                L > 1,
                L > 0 ==> ((reflect == true ==> forall |j: u8| (j as int) < 256 ==> table@[0][j as int] == crc8r_run(shrs_u8(revm8(poly), (8 - width) as nat), j as u8, 8)) && (reflect == false ==> forall |j: u8| (j as int) < 256 ==> table@[0][j as int] == crc8n_run(shls_u8(poly, (8 - width) as nat), j, 8))),
            decreases 256 - i,
        {
            let mut e: usize = 1;
            while e < L
                invariant
                    1 <= e,
                    e <= L,
                    i < 256,
                    L > 0 ==> ((reflect == true ==> forall |j: u8| (j as int) < 256 ==> table@[0][j as int] == crc8r_run(shrs_u8(revm8(poly), (8 - width) as nat), j as u8, 8)) && (reflect == false ==> forall |j: u8| (j as int) < 256 ==> table@[0][j as int] == crc8n_run(shls_u8(poly, (8 - width) as nat), j, 8))),
                decreases L - e,
            {
                let one_lower = table[e - 1][i];
                assert((one_lower as int) < 256);
                table[e][i] = table[0][one_lower as usize];
                e = e + 1;
            }
            i = i + 1;
        }
    }
    table
}

/* -- u16 table generation -- */

/* [verus note: rlimit = the lane-0 chain unfolding (crc16r/n_run x 8 steps) exceeds the default 10s resource budget for a query -- only the resource ceiling is raised, no obligation is relaxed] */
#[verifier::rlimit(60)]
pub exec fn crc16_table<const L: usize>(width: u8, poly: u16, reflect: bool) -> (tbl: [[u16; 256]; L])
    requires
        1 <= width && width <= 16,
    ensures
        /* [verus note: the ensures is predicated on L>0 -- Table<0> (NoTable) has no lane; upstream new() likewise builds an empty table at L=0] */
        L > 0 ==> ((reflect == true  ==> forall |j: u8| tbl@[0][j as int] == crc16r_run(shrs_u16(revm16(poly), (16 - width) as nat), j as u16, 8)) && (reflect == false ==> forall |j: u8| tbl@[0][j as int] == crc16n_run(shls_u16(poly, (16 - width) as nat), shl8_u16(j as u16), 8))),
{
    let poly_adj = if reflect {
        let poly_v = rev16(poly);
        poly_v >> (16u8 - width)
    } else {
        poly << (16u8 - width)
    };
    assert(poly_adj == (if reflect { shrs_u16(revm16(poly), (16 - width) as nat) } else { shls_u16(poly, (16 - width) as nat) })) by {
        lem_shrs_u16(revm16(poly), (16 - width) as u16);
        lem_shls_u16(poly, (16 - width) as u16);
    };
    let mut table = [[0u16; 256]; L];
    let mut i: usize = 0;
    while i < 256 && L > 0
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the poly_adj bridging equality and the lane-0 forall are written in
                 *  ensures shape into the invariant (otherwise the exec call's postcondition facts and derived equalities do not enter the loop body)] */
                poly_adj == (if reflect { shrs_u16(revm16(poly), (16 - width) as nat) } else { shls_u16(poly, (16 - width) as nat) }),
                L > 0 ==> ((reflect == true  ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc16r_run(shrs_u16(revm16(poly), (16 - width) as nat), j as u16, 8)) && (reflect == false ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc16n_run(shls_u16(poly, (16 - width) as nat), shl8_u16(j as u16), 8))),
            decreases 256 - i,
    {
        table[0][i] = crc16(poly_adj, reflect, i as u16);
        i = i + 1;
    }
    if L > 1 {
        // [Origin Rust: lane k>=1 double loop -- only index safety and termination are kept (the semantics modeled as partial)]
        let mut i: usize = 0;
        while i < 256
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the if(L>1) fact and the lane-0 forall (writes happen only on the
                 *  e>=1 rows, so lane-0 content is preserved across both loops) are threaded in / preserved via the invariants] */
                L > 1,
                L > 0 ==> ((reflect == true ==> forall |j: u16| (j as int) < 256 ==> table@[0][j as int] == crc16r_run(shrs_u16(revm16(poly), (16 - width) as nat), j as u16, 8)) && (reflect == false ==> forall |j: u16| (j as int) < 256 ==> table@[0][j as int] == crc16n_run(shls_u16(poly, (16 - width) as nat), shl8_u16(j as u16), 8))),
            decreases 256 - i,
        {
            let mut e: usize = 1;
            while e < L
                invariant
                    1 <= e,
                    e <= L,
                    i < 256,
                    L > 0 ==> ((reflect == true ==> forall |j: u16| (j as int) < 256 ==> table@[0][j as int] == crc16r_run(shrs_u16(revm16(poly), (16 - width) as nat), j as u16, 8)) && (reflect == false ==> forall |j: u16| (j as int) < 256 ==> table@[0][j as int] == crc16n_run(shls_u16(poly, (16 - width) as nat), shl8_u16(j as u16), 8))),
                decreases L - e,
            {
                let one_lower = table[e - 1][i];
                /* [verus note: table lower bound (the vstd idx contract) -- the bv local assertion matches the indexing obligation verbatim in shape] */
                assert((one_lower & 0xff) < 256) by(bit_vector);
                if reflect {
                    table[e][i] = (one_lower >> 8) ^ table[0][(one_lower & 0xff) as usize];
                } else {
                    assert(((one_lower >> 8) & 0xff) < 256) by(bit_vector);
                    table[e][i] = (one_lower << 8) ^ table[0][((one_lower >> 8) & 0xff) as usize];
                }
                e = e + 1;
            }
            i = i + 1;
        }
    }
    table
}

/* -- u32 table generation -- */

/* [verus note: rlimit = the lane-0 chain unfolding (crc32r/n_run x 8 steps) exceeds the default 10s resource budget for a query -- only the resource ceiling is raised, no obligation is relaxed] */
#[verifier::rlimit(60)]
pub exec fn crc32_table<const L: usize>(width: u8, poly: u32, reflect: bool) -> (tbl: [[u32; 256]; L])
    requires
        1 <= width && width <= 32,
    ensures
        /* [verus note: the ensures is predicated on L>0 -- Table<0> (NoTable) has no lane; upstream new() likewise builds an empty table at L=0] */
        L > 0 ==> ((reflect == true  ==> forall |j: u8| tbl@[0][j as int] == crc32r_run(shrs_u32(revm32(poly), (32 - width) as nat), j as u32, 8)) && (reflect == false ==> forall |j: u8| tbl@[0][j as int] == crc32n_run(shls_u32(poly, (32 - width) as nat), shl24_u32(j as u32), 8))),
{
    let poly_adj = if reflect {
        let poly_v = rev32(poly);
        poly_v >> (32u8 - width)
    } else {
        poly << (32u8 - width)
    };
    assert(poly_adj == (if reflect { shrs_u32(revm32(poly), (32 - width) as nat) } else { shls_u32(poly, (32 - width) as nat) })) by {
        lem_shrs_u32(revm32(poly), (32 - width) as u32);
        lem_shls_u32(poly, (32 - width) as u32);
    };
    let mut table = [[0u32; 256]; L];
    let mut i: usize = 0;
    while i < 256 && L > 0
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the poly_adj bridging equality and the lane-0 forall are written in
                 *  ensures shape into the invariant (otherwise the exec call's postcondition facts and derived equalities do not enter the loop body)] */
                poly_adj == (if reflect { shrs_u32(revm32(poly), (32 - width) as nat) } else { shls_u32(poly, (32 - width) as nat) }),
                L > 0 ==> ((reflect == true  ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc32r_run(shrs_u32(revm32(poly), (32 - width) as nat), j as u32, 8)) && (reflect == false ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc32n_run(shls_u32(poly, (32 - width) as nat), shl24_u32(j as u32), 8))),
            decreases 256 - i,
    {
        table[0][i] = crc32(poly_adj, reflect, i as u32);
        i = i + 1;
    }
    if L > 1 {
        // [Origin Rust: lane k>=1 double loop -- only index safety and termination are kept (the semantics modeled as partial)]
        let mut i: usize = 0;
        while i < 256
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the if(L>1) fact and the lane-0 forall (writes happen only on the
                 *  e>=1 rows, so lane-0 content is preserved across both loops) are threaded in / preserved via the invariants] */
                L > 1,
                L > 0 ==> ((reflect == true ==> forall |j: u32| (j as int) < 256 ==> table@[0][j as int] == crc32r_run(shrs_u32(revm32(poly), (32 - width) as nat), j as u32, 8)) && (reflect == false ==> forall |j: u32| (j as int) < 256 ==> table@[0][j as int] == crc32n_run(shls_u32(poly, (32 - width) as nat), shl24_u32(j as u32), 8))),
            decreases 256 - i,
        {
            let mut e: usize = 1;
            while e < L
                invariant
                    1 <= e,
                    e <= L,
                    i < 256,
                    L > 0 ==> ((reflect == true ==> forall |j: u32| (j as int) < 256 ==> table@[0][j as int] == crc32r_run(shrs_u32(revm32(poly), (32 - width) as nat), j as u32, 8)) && (reflect == false ==> forall |j: u32| (j as int) < 256 ==> table@[0][j as int] == crc32n_run(shls_u32(poly, (32 - width) as nat), shl24_u32(j as u32), 8))),
                decreases L - e,
            {
                let one_lower = table[e - 1][i];
                /* [verus note: table lower bound (the vstd idx contract) -- the bv local assertion matches the indexing obligation verbatim in shape] */
                assert((one_lower & 0xff) < 256) by(bit_vector);
                if reflect {
                    table[e][i] = (one_lower >> 8) ^ table[0][(one_lower & 0xff) as usize];
                } else {
                    assert(((one_lower >> 24) & 0xff) < 256) by(bit_vector);
                    table[e][i] = (one_lower << 8) ^ table[0][((one_lower >> 24) & 0xff) as usize];
                }
                e = e + 1;
            }
            i = i + 1;
        }
    }
    table
}

/* -- u64 table generation -- */

/* [verus note: rlimit = the lane-0 chain unfolding (crc64r/n_run x 8 steps) exceeds the default 10s resource budget for a query -- only the resource ceiling is raised, no obligation is relaxed] */
#[verifier::rlimit(60)]
pub exec fn crc64_table<const L: usize>(width: u8, poly: u64, reflect: bool) -> (tbl: [[u64; 256]; L])
    requires
        1 <= width && width <= 64,
    ensures
        /* [verus note: the ensures is predicated on L>0 -- Table<0> (NoTable) has no lane; upstream new() likewise builds an empty table at L=0] */
        L > 0 ==> ((reflect == true  ==> forall |j: u8| tbl@[0][j as int] == crc64r_run(shrs_u64(revm64(poly), (64 - width) as nat), j as u64, 8)) && (reflect == false ==> forall |j: u8| tbl@[0][j as int] == crc64n_run(shls_u64(poly, (64 - width) as nat), shl56_u64(j as u64), 8))),
{
    let poly_adj = if reflect {
        let poly_v = rev64(poly);
        poly_v >> (64u8 - width)
    } else {
        poly << (64u8 - width)
    };
    assert(poly_adj == (if reflect { shrs_u64(revm64(poly), (64 - width) as nat) } else { shls_u64(poly, (64 - width) as nat) })) by {
        lem_shrs_u64(revm64(poly), (64 - width) as u64);
        lem_shls_u64(poly, (64 - width) as u64);
    };
    let mut table = [[0u64; 256]; L];
    let mut i: usize = 0;
    while i < 256 && L > 0
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the poly_adj bridging equality and the lane-0 forall are written in
                 *  ensures shape into the invariant (otherwise the exec call's postcondition facts and derived equalities do not enter the loop body)] */
                poly_adj == (if reflect { shrs_u64(revm64(poly), (64 - width) as nat) } else { shls_u64(poly, (64 - width) as nat) }),
                L > 0 ==> ((reflect == true  ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc64r_run(shrs_u64(revm64(poly), (64 - width) as nat), j as u64, 8)) && (reflect == false ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc64n_run(shls_u64(poly, (64 - width) as nat), shl56_u64(j as u64), 8))),
            decreases 256 - i,
    {
        table[0][i] = crc64(poly_adj, reflect, i as u64);
        i = i + 1;
    }
    if L > 1 {
        // [Origin Rust: lane k>=1 double loop -- only index safety and termination are kept (the semantics modeled as partial)]
        let mut i: usize = 0;
        while i < 256
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the if(L>1) fact and the lane-0 forall (writes happen only on the
                 *  e>=1 rows, so lane-0 content is preserved across both loops) are threaded in / preserved via the invariants] */
                L > 1,
                L > 0 ==> ((reflect == true ==> forall |j: u64| (j as int) < 256 ==> table@[0][j as int] == crc64r_run(shrs_u64(revm64(poly), (64 - width) as nat), j as u64, 8)) && (reflect == false ==> forall |j: u64| (j as int) < 256 ==> table@[0][j as int] == crc64n_run(shls_u64(poly, (64 - width) as nat), shl56_u64(j as u64), 8))),
            decreases 256 - i,
        {
            let mut e: usize = 1;
            while e < L
                invariant
                    1 <= e,
                    e <= L,
                    i < 256,
                    L > 0 ==> ((reflect == true ==> forall |j: u64| (j as int) < 256 ==> table@[0][j as int] == crc64r_run(shrs_u64(revm64(poly), (64 - width) as nat), j as u64, 8)) && (reflect == false ==> forall |j: u64| (j as int) < 256 ==> table@[0][j as int] == crc64n_run(shls_u64(poly, (64 - width) as nat), shl56_u64(j as u64), 8))),
                decreases L - e,
            {
                let one_lower = table[e - 1][i];
                /* [verus note: table lower bound (the vstd idx contract) -- the bv local assertion matches the indexing obligation verbatim in shape] */
                assert((one_lower & 0xff) < 256) by(bit_vector);
                if reflect {
                    table[e][i] = (one_lower >> 8) ^ table[0][(one_lower & 0xff) as usize];
                } else {
                    assert(((one_lower >> 56) & 0xff) < 256) by(bit_vector);
                    table[e][i] = (one_lower << 8) ^ table[0][((one_lower >> 56) & 0xff) as usize];
                }
                e = e + 1;
            }
            i = i + 1;
        }
    }
    table
}

/* -- u128 table generation -- */

/* [verus note: rlimit = the lane-0 chain unfolding (crc128r/n_run x 8 steps) exceeds the default 10s resource budget for a query -- only the resource ceiling is raised, no obligation is relaxed] */
#[verifier::rlimit(60)]
pub exec fn crc128_table<const L: usize>(width: u8, poly: u128, reflect: bool) -> (tbl: [[u128; 256]; L])
    requires
        1 <= width && width <= 128,
    ensures
        /* [verus note: the ensures is predicated on L>0 -- Table<0> (NoTable) has no lane; upstream new() likewise builds an empty table at L=0] */
        L > 0 ==> ((reflect == true  ==> forall |j: u8| tbl@[0][j as int] == crc128r_run(shrs_u128(revm128(poly), (128 - width) as nat), j as u128, 8)) && (reflect == false ==> forall |j: u8| tbl@[0][j as int] == crc128n_run(shls_u128(poly, (128 - width) as nat), shl120_u128(j as u128), 8))),
{
    let poly_adj = if reflect {
        let poly_v = rev128(poly);
        poly_v >> (128u8 - width)
    } else {
        poly << (128u8 - width)
    };
    assert(poly_adj == (if reflect { shrs_u128(revm128(poly), (128 - width) as nat) } else { shls_u128(poly, (128 - width) as nat) })) by {
        lem_shrs_u128(revm128(poly), (128 - width) as u128);
        lem_shls_u128(poly, (128 - width) as u128);
    };
    let mut table = [[0u128; 256]; L];
    let mut i: usize = 0;
    while i < 256 && L > 0
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the poly_adj bridging equality and the lane-0 forall are written in
                 *  ensures shape into the invariant (otherwise the exec call's postcondition facts and derived equalities do not enter the loop body)] */
                poly_adj == (if reflect { shrs_u128(revm128(poly), (128 - width) as nat) } else { shls_u128(poly, (128 - width) as nat) }),
                L > 0 ==> ((reflect == true  ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc128r_run(shrs_u128(revm128(poly), (128 - width) as nat), j as u128, 8)) && (reflect == false ==> forall |j: u8| (j as int) < i ==> table@[0][j as int] == crc128n_run(shls_u128(poly, (128 - width) as nat), shl120_u128(j as u128), 8))),
            decreases 256 - i,
    {
        table[0][i] = crc128(poly_adj, reflect, i as u128);
        i = i + 1;
    }
    if L > 1 {
        // [Origin Rust: lane k>=1 double loop -- only index safety and termination are kept (the semantics modeled as partial)]
        let mut i: usize = 0;
        while i < 256
            invariant
                i <= 256,
                /* [verus note: loop isolation -- the if(L>1) fact and the lane-0 forall (writes happen only on the
                 *  e>=1 rows, so lane-0 content is preserved across both loops) are threaded in / preserved via the invariants] */
                L > 1,
                L > 0 ==> ((reflect == true ==> forall |j: u128| (j as int) < 256 ==> table@[0][j as int] == crc128r_run(shrs_u128(revm128(poly), (128 - width) as nat), j as u128, 8)) && (reflect == false ==> forall |j: u128| (j as int) < 256 ==> table@[0][j as int] == crc128n_run(shls_u128(poly, (128 - width) as nat), shl120_u128(j as u128), 8))),
            decreases 256 - i,
        {
            let mut e: usize = 1;
            while e < L
                invariant
                    1 <= e,
                    e <= L,
                    i < 256,
                    L > 0 ==> ((reflect == true ==> forall |j: u128| (j as int) < 256 ==> table@[0][j as int] == crc128r_run(shrs_u128(revm128(poly), (128 - width) as nat), j as u128, 8)) && (reflect == false ==> forall |j: u128| (j as int) < 256 ==> table@[0][j as int] == crc128n_run(shls_u128(poly, (128 - width) as nat), shl120_u128(j as u128), 8))),
                decreases L - e,
            {
                let one_lower = table[e - 1][i];
                /* [verus note: table lower bound (the vstd idx contract) -- the bv local assertion matches the indexing obligation verbatim in shape] */
                assert((one_lower & 0xff) < 256) by(bit_vector);
                if reflect {
                    table[e][i] = (one_lower >> 8) ^ table[0][(one_lower & 0xff) as usize];
                } else {
                    assert(((one_lower >> 120) & 0xff) < 256) by(bit_vector);
                    table[e][i] = (one_lower << 8) ^ table[0][((one_lower >> 120) & 0xff) as usize];
                }
                e = e + 1;
            }
            i = i + 1;
        }
    }
    table
}

} // verus!
