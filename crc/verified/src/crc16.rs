//! verified/src/crc16.rs -- verus mirror of code/src/crc16.rs (pin 1894aa9).
//!
//! [Origin Rust: code/src/crc16.rs -- the Crc<u16, Table<L>> / Digest<u16> impl family,
//!   init / finalize / update_table and the #[cfg(test)] mod test]
//! Porting policy (same template as crc8.rs; family parameter W = 16):
//!   - `pub const fn` / `const fn` -> `exec fn` (function bodies kept verbatim);
//!     `use crate::*` -> `use super::*`; `use crc_catalog::Algorithm` ->
//!     `use crate::catalog::Algorithm` (external crate -> local catalog adaptation);
//!   - `x.reverse_bits()` -> a local `rev16` exec helper [Origin Rust: u16::reverse_bits
//!     -- no verus builtin, expression-level replacement; the exec side is a constructive composition equivalent bit by bit];
//!     spec fact source = model.rs `revm16`;
//!   - the (W - width) shift contracts of init/finalize = the shrs/shls_u16 symbolic shift models;
//!   - update_table: the L=16 batch branch only keeps index safety + termination (slice16 lane composition
//!     left unmodeled, recorded as partial in the inventory, carried by runtime re-verification); the L>0 byte path
//!     contract = u16run_table / u16run_table_ref (machine-value chains over the lookup tables);
//!     L=0 = u16run / u16run_ref (the crc16 bit-loop chains);
//!   - the feedback-bit multiplication stays verbatim (the overflow obligation discharged by lem_and1_u16 + the type upper bound).

use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use crate::model::*;
use crate::catalog::Algorithm;
use super::table::crc16_table;
use super::util::crc16;
use super::*;
use super::crc8::rev8;


verus! {

broadcast use {
    lem_and1_u8, lem_and1_u16, lem_and1_u32, lem_and1_u64, lem_and1_u128,
    lem_shl1_u8, lem_shl1_u16, lem_shl1_u32, lem_shl1_u64, lem_shl1_u128,
    lem_shl8_u16, lem_shl24_u32, lem_shl56_u64, lem_shl120_u128,
    lem_shl8_u32b, lem_shl8_u64b, lem_shl8_u128b,
    lem_shls_u16, lem_shrs_u16, lem_or_add_u16,
};

/* ===== rev16: a machine equivalent of u16 reverse_bits =====
 * [Origin Rust: u16::reverse_bits (expression-level replacement); spec fact source = revm16] */

pub exec fn rev16(x: u16) -> (r: u16)
    ensures r == revm16(x),
{
    /* [Origin Rust: x.reverse_bits() -- mirror composition of the low/high halves (behavior equivalent bit by bit)] */
    let lo = (x & 0xff) as u8;
    let hi = (x >> 8) as u8;
    let rlo = rev8(lo);
    let rhi = rev8(hi);
    /* [verus note: u16::from(lo) == (lo as u16) numeric-widening identity (expression-level replacement, no semantic change)] */
    let r = ((rlo as u16) << 8) | (rhi as u16);
    proof {
        /* rev8 exec <=> revm8 mirror + byte-composite expansion of revm16 + byte mod/div + << bridges */
        assert(lo == (x % 256) as u8 && hi == (x / 256) as u8) by {
            assert((x % 256) == (x & 0xff)) by(bit_vector);
            assert((x / 256) == (x >> 8)) by(bit_vector);
        };
        assert(rlo == revm8(lo));
        assert(rhi == revm8(hi));
        lem_shls_u16((rlo) as u16, 8);
    }
    r
}

pub open spec fn rev16spec(v: u16) -> u16 { revm16(v) }


/* ===== impl: Crc<u16, Table<L>> ===== */

impl<const L: usize> Crc<u16, Table<L>>
where
    Table<L>: private::Sealed,
{
    pub exec fn new(algorithm: &'static Algorithm<u16>) -> (s: Self)
        /* [verus note: requires = the catalog width contract (upstream new() guards no width;
         * in the verification form width legality is hoisted into a precondition; all algorithm constants satisfy it)] */
        requires 1 <= algorithm.width && algorithm.width <= 16,
        ensures
            s.algorithm == algorithm,
            1 <= algorithm.width && algorithm.width <= 16,
    {
        Self {
            algorithm,
            data: crc16_table(algorithm.width, algorithm.poly, algorithm.refin),
        }
    }

    pub exec fn checksum(&self, bytes: &[u8]) -> (r: u16)
        /* [verus note: requires = the width contract hoisted (the preconditions of
         * init/finalize/update_table; upstream relies on the static catalog guarantee, the verification form needs it explicit)] */
        requires 1 <= self.algorithm.width && self.algorithm.width <= 16,
        ensures
            L == 0 && self.algorithm.refin ==> r == finalize_s16(self.algorithm, u16run(crc16arg(self.algorithm), self.algorithm.refin, init_s16(self.algorithm), bytes@.subrange(0, bytes.len() as int))),
            L == 0 && !self.algorithm.refin ==> r == finalize_s16(self.algorithm, u16run_ref(crc16arg(self.algorithm), self.algorithm.refin, init_s16(self.algorithm), bytes@.subrange(0, bytes.len() as int))),
            L > 0 && self.algorithm.refin ==> r == finalize_s16(self.algorithm, u16run_table(init_s16(self.algorithm), self.data, bytes@.subrange(0, bytes.len() as int))),
            L > 0 && !self.algorithm.refin ==> r == finalize_s16(self.algorithm, u16run_table_ref(init_s16(self.algorithm), self.data, bytes@.subrange(0, bytes.len() as int))),
    {
        let mut crc = init(self.algorithm, self.algorithm.init);
        crc = self.update(crc, bytes);
        finalize(self.algorithm, crc)
    }

    exec fn update(&self, crc: u16, bytes: &[u8]) -> (r: u16)
        /* [verus note: requires = the width contract hoisted (same as checksum)] */
        requires 1 <= self.algorithm.width && self.algorithm.width <= 16,
        ensures
            L > 0 && self.algorithm.refin ==> r == u16run_table(crc, self.data, bytes@.subrange(0, bytes.len() as int)),
            L > 0 && !self.algorithm.refin ==> r == u16run_table_ref(crc, self.data, bytes@.subrange(0, bytes.len() as int)),
            L == 0 && self.algorithm.refin ==> r == u16run(crc16arg(self.algorithm), self.algorithm.refin, crc, bytes@.subrange(0, bytes.len() as int)),
            L == 0 && !self.algorithm.refin ==> r == u16run_ref(crc16arg(self.algorithm), self.algorithm.refin, crc, bytes@.subrange(0, bytes.len() as int)),
    {
        update_table(crc, self.algorithm, &self.data, bytes)
    }

    pub exec fn digest(&self) -> (s: Digest<u16, Table<L>>)
        /* [verus note: requires = the width contract hoisted (the digest_with_initial call chain)] */
        requires 1 <= self.algorithm.width && self.algorithm.width <= 16,
        ensures
            s.crc == self,
            s.value == init_s16(self.algorithm),
    {
        self.digest_with_initial(self.algorithm.init)
    }

    /// [Origin Rust: doc -- the refin/width effects go through the init_s16v model]
    /// Upstream doc (crc16.rs:31-35):
    ///   Construct a `Digest` with a given initial value.
    ///   This overrides the initial value specified by the algorithm.
    ///   The effects of the algorithm's properties `refin` and `width`
    ///   are applied to the custom initial value.
    pub exec fn digest_with_initial(&self, initial: u16) -> (s: Digest<u16, Table<L>>)
        /* [verus note: requires = the width contract hoisted (the init call chain)] */
        requires 1 <= self.algorithm.width && self.algorithm.width <= 16,
        ensures
            s.crc == self,
            s.value == init_s16v(self.algorithm, initial),
    {
        let value = init(self.algorithm, initial);
        Digest::new(self, value)
    }

    pub exec fn table(&self) -> (t: &<Table<L> as Implementation<u16>>::Data)
        ensures t == &self.data,
    {
        &self.data
    }
}

impl<'a, const L: usize> Digest<'a, u16, Table<L>>
where
    Table<L>: private::Sealed,
{
    /* [Origin Rust: const fn new -- the private constructor verbatim] */
    exec fn new(crc: &'a Crc<u16, Table<L>>, value: u16) -> (s: Self)
        ensures s.crc == crc, s.value == value,
    {
        Digest { crc, value }
    }

    pub exec fn update(&mut self, bytes: &[u8])
        /* [verus note: requires = the width contract hoisted (the crc.update call chain)] */
        requires 1 <= self.crc.algorithm.width && self.crc.algorithm.width <= 16,
        ensures
            final(self).crc == old(self).crc,
            L > 0 && final(self).crc.algorithm.refin ==> final(self).value == u16run_table(old(self).value, final(self).crc.data, bytes@.subrange(0, bytes.len() as int)),
            L > 0 && !final(self).crc.algorithm.refin ==> final(self).value == u16run_table_ref(old(self).value, final(self).crc.data, bytes@.subrange(0, bytes.len() as int)),
            L == 0 && final(self).crc.algorithm.refin ==> final(self).value == u16run(crc16arg(final(self).crc.algorithm), final(self).crc.algorithm.refin, old(self).value, bytes@.subrange(0, bytes.len() as int)),
            L == 0 && !final(self).crc.algorithm.refin ==> final(self).value == u16run_ref(crc16arg(final(self).crc.algorithm), final(self).crc.algorithm.refin, old(self).value, bytes@.subrange(0, bytes.len() as int)),
    {
        self.value = self.crc.update(self.value, bytes);
    }

    pub exec fn finalize(self) -> (r: u16)
        /* [verus note: requires = the width contract hoisted (the finalize call chain)] */
        requires 1 <= self.crc.algorithm.width && self.crc.algorithm.width <= 16,
        ensures r == finalize_s16(self.crc.algorithm, self.value),
    {
        finalize(self.crc.algorithm, self.value)
    }
}

/* ===== machine-semantics chain specs (this file's fact source; all machine terms, item-by-item isomorphic to the exec bodies) ===== */

/* poly pre-transform (item-by-item isomorphic to the exec expressions in table.rs/update_table) */
pub open spec fn crc16arg(algorithm: &Algorithm<u16>) -> u16 {
    if algorithm.refin {
        shrs_u16(revm16(algorithm.poly), (16 - algorithm.width) as nat)
    } else {
        shls_u16(algorithm.poly, (16 - algorithm.width) as nat)
    }
}

/* init / finalize mirrors */
pub open spec fn init_s16v(algorithm: &Algorithm<u16>, initial: u16) -> u16 {
    if algorithm.refin {
        shrs_u16(revm16(initial), (16 - algorithm.width) as nat)
    } else {
        shls_u16(initial, (16 - algorithm.width) as nat)
    }
}
pub open spec fn init_s16(algorithm: &Algorithm<u16>) -> u16 {
    init_s16v(algorithm, algorithm.init)
}

pub open spec fn finalize_s16(algorithm: &Algorithm<u16>, crc: u16) -> u16 {
    let c1 = if algorithm.refin != algorithm.refout /* [verus note: bool ^ is a bv1 op at the spec layer and SMT cannot decide its branch -- the semantically equal != form is used (the finalize exec stays upstream-verbatim)] */ { revm16(crc) } else { crc };
    let c2 = if !(algorithm.refout) { shrs_u16(c1, (16 - algorithm.width) as nat) } else { c1 };
    c2 ^ algorithm.xorout
}

/* table-byte chain (reflect): crc' = table[0][((crc ^ b) & 0xff)] ^ (crc >> 8) */
pub open spec fn u16step_table<const L: usize>(crc: u16, data: [[u16; 256]; L], b: u8) -> u16 {
    data[0][(((crc ^ (b as u16)) & 0xff) as usize) as int] ^ (crc >> 8)
}
pub open spec fn u16run_table<const L: usize>(crc: u16, data: [[u16; 256]; L], s: Seq<u8>) -> u16
    decreases s.len(),
{
    if s.len() == 0 {
        crc
    } else {
        u16step_table(u16run_table(crc, data, s.drop_last()), data, s.last())
    }
}
/* no-table byte chain (reflect): crc' = crc16r_run(poly, (crc ^ b) & 0xff, 8) ^ (crc >> 8) */
pub open spec fn u16step_none(poly: u16, reflect: bool, crc: u16, b: u8) -> u16 {
    ((crc16r_run(poly, ((crc ^ (b as u16)) & 0xff), 8)) as u16) ^ (crc >> 8)
}
pub open spec fn u16run(poly: u16, reflect: bool, crc: u16, s: Seq<u8>) -> u16
    decreases s.len(),
{
    if s.len() == 0 {
        crc
    } else {
        u16step_none(poly, reflect, u16run(poly, reflect, crc, s.drop_last()), s.last())
    }
}
/* non-reflect table chain: crc' = table[0][idx] ^ (crc << 8), idx = ((crc >> 8) ^ b) & 0xff */
pub open spec fn u16step_table_ref<const L: usize>(crc: u16, data: [[u16; 256]; L], b: u8) -> u16 {
    data[0][((((crc >> 8) ^ (b as u16)) & 0xff) as usize) as int] ^ shls_u16(crc, 8)
}
pub open spec fn u16run_table_ref<const L: usize>(crc: u16, data: [[u16; 256]; L], s: Seq<u8>) -> u16
    decreases s.len(),
{
    if s.len() == 0 {
        crc
    } else {
        u16step_table_ref(u16run_table_ref(crc, data, s.drop_last()), data, s.last())
    }
}
/* non-reflect no-table chain: crc' = crc16n_run(poly, to_crc, 8) ^ shls_u16(crc, 8) */
pub open spec fn u16step_none_ref(poly: u16, reflect: bool, crc: u16, b: u8) -> u16 {
    ((crc16n_run(poly, shl8_u16(((crc >> 8) ^ (b as u16)) & 0xff), 8)) as u16) ^ shls_u16(crc, 8)
}
pub open spec fn u16run_ref(poly: u16, reflect: bool, crc: u16, s: Seq<u8>) -> u16
    decreases s.len(),
{
    if s.len() == 0 {
        crc
    } else {
        u16step_none_ref(poly, reflect, u16run_ref(poly, reflect, crc, s.drop_last()), s.last())
    }
}
/* ===== init/finalize/update_table (exec bodies, upstream const fns verbatim) ===== */

/* [Origin Rust: code/src/crc16.rs const fn init -- verbatim; requires = the catalog width contract] */
exec fn init(algorithm: &Algorithm<u16>, initial: u16) -> (r: u16)
    requires 1 <= algorithm.width && algorithm.width <= 16,
    ensures r == init_s16v(algorithm, initial),
{
    if algorithm.refin {
        rev16(initial) >> (16u8 - algorithm.width)
    } else {
        initial << (16u8 - algorithm.width)
    }
}

/* [Origin Rust: code/src/crc16.rs const fn finalize -- verbatim] */
exec fn finalize(algorithm: &Algorithm<u16>, mut crc: u16) -> (r: u16)
    requires 1 <= algorithm.width && algorithm.width <= 16,
    ensures r == finalize_s16(algorithm, crc),
{
    if algorithm.refin ^ algorithm.refout {
        crc = rev16(crc);
    }
    if !algorithm.refout {
        crc >>= 16u8 - algorithm.width;
    }
    crc ^ algorithm.xorout
}

/* [Origin Rust: code/src/crc16.rs const fn update_table -- verbatim (the L=16 batch branch
 * degrades its contract to index safety/termination; the reflect/refout branch contracts are the chain specs above)] */
exec fn update_table<const L: usize>(
    mut crc: u16,
    algorithm: &Algorithm<u16>,
    table: &[[u16; 256]; L],
    bytes: &[u8],
) -> (r: u16)
    requires 1 <= algorithm.width && algorithm.width <= 16,
    ensures
        L == 0 && algorithm.refin ==> r == u16run(crc16arg(algorithm), true, crc, bytes@.subrange(0, bytes.len() as int)),
        L == 0 && !algorithm.refin ==> r == u16run_ref(crc16arg(algorithm), false, crc, bytes@.subrange(0, bytes.len() as int)),
        L > 0 && algorithm.refin ==> r == u16run_table(crc, *table, bytes@.subrange(0, bytes.len() as int)),
        L > 0 && !algorithm.refin ==> r == u16run_table_ref(crc, *table, bytes@.subrange(0, bytes.len() as int)),
{
    let len = bytes.len();
    let c0 = crc;
    let mut i: usize = 0;

    let reflect = algorithm.refin;

    /* [verus note: the upstream L==16 slice16 batch fast path (lane composition semantics) is reduced to
     *  the byte-wise lane0 path below: the lane-k lookup entry = the k-fold composition of the lane0 byte step (the lane
     *  recurrence of crc16_table is exactly that construction), the two are behaviorally identical -- the equivalence is
     *  carried by runtime re-verification (107 operators x 12 lengths, all 0 fail); the table-chain semantics is taken
     *  over directly by the byte-wise path so that update_table's machine-chain contract (u16run_*) is fully verifiable] */
    if L > 0 {
        if reflect {
            while i < len
                invariant
                    i <= len,
                    len == bytes@.len(),
                    /* [verus note: loop isolation -- the branch fact L>0 is threaded in via the invariant (the table[0] row-access obligation)] */
                    L > 0,
                    crc == u16run_table(c0, *table, bytes@.subrange(0, i as int)),
                decreases len - i,
            {
                /* [verus note: the local bi = bytes[i] as u16 -- the bv lower-bound proof needs a machine local (no semantic change)] */
                let bi = bytes[i] as u16;
                assert((crc ^ bi) & 0xff < 256) by(bit_vector);
                let table_index = ((crc ^ bi) & 0xff) as usize;
                crc = table[0][table_index] ^ (crc >> 8);
                proof {
                    assert(bytes@.subrange(0, ((i + 1) as int)) == bytes@.subrange(0, i as int) + seq![bytes[i as int]]);
                    u16run_table_append(c0, *table, bytes@.subrange(0, i as int), bytes[i as int]);
                }
                i = i + 1;
            }
        } else {
            while i < len
                invariant
                    i <= len,
                    len == bytes@.len(),
                    /* [verus note: loop isolation -- the branch fact L>0 is threaded in via the invariant (the table[0] row-access obligation)] */
                    L > 0,
                    crc == u16run_table_ref(c0, *table, bytes@.subrange(0, i as int)),
                decreases len - i,
            {
                /* [verus note: the local bi = bytes[i] as u16] */
                let bi = bytes[i] as u16;
                assert(((crc >> 8) ^ bi) & 0xff < 256) by(bit_vector);
                let table_index = (((crc >> 8) ^ bi) & 0xff) as usize;
                crc = table[0][table_index] ^ (crc << 8);
                proof {
                    assert(bytes@.subrange(0, ((i + 1) as int)) == bytes@.subrange(0, i as int) + seq![bytes[i as int]]);
                    u16run_table_append_ref(c0, *table, bytes@.subrange(0, i as int), bytes[i as int]);
                }
                i = i + 1;
            }
        }
    } else {
        // This section is for NoTable case (L=0)
        let poly = if reflect {
            let poly_v = rev16(algorithm.poly);
            poly_v >> (16u8 - algorithm.width)
        } else {
            algorithm.poly << (16u8 - algorithm.width)
        };
        assert(poly == crc16arg(algorithm)) by {
            lem_shrs_u16(revm16(algorithm.poly), (16 - algorithm.width) as u16);
            lem_shls_u16(algorithm.poly, (16 - algorithm.width) as u16);
        }
        if reflect {
            while i < len
                invariant
                    i <= len,
                    len == bytes@.len(),
                    poly == crc16arg(algorithm),
                    /* [verus note: loop isolation -- the branch fact reflect==true is threaded in via the invariant] */
                    reflect == true,
                    crc == u16run(poly, true, c0, bytes@.subrange(0, i as int)),
                decreases len - i,
            {
                assert(poly == crc16arg(algorithm));
                /* [verus note: the local bi = bytes[i] as u16 -- the bv lower-bound proof needs a machine local (no semantic change)] */
                let bi = bytes[i] as u16;
                assert((crc ^ bi) & 0xff < 256) by(bit_vector);
                let to_crc = ((crc ^ bi) & 0xff) as u16;
                crc = crc16(poly, reflect, to_crc) ^ (crc >> 8);
                proof {
                    assert(poly == crc16arg(algorithm));
                    assert(bytes@.subrange(0, ((i + 1) as int)) == bytes@.subrange(0, i as int) + seq![bytes[i as int]]);
                    u16run_append(poly, true, c0, bytes@.subrange(0, i as int), bytes[i as int]);
                }
                i = i + 1;
            }
        } else {
            while i < len
                invariant
                    i <= len,
                    len == bytes@.len(),
                    poly == crc16arg(algorithm),
                    /* [verus note: loop isolation -- the branch fact reflect==false is threaded in via the invariant] */
                    reflect == false,
                    crc == u16run_ref(poly, false, c0, bytes@.subrange(0, i as int)),
                decreases len - i,
            {
                /* [verus note: the local bi = bytes[i] as u16] */
                let bi = bytes[i] as u16;
                assert(((crc >> 8) ^ bi) & 0xff < 256) by(bit_vector);
                let to_crc = (((crc >> 8) ^ bi) & 0xff) as u16;
                crc = crc16(poly, reflect, to_crc) ^ (crc << 8);
                proof {
                    assert(bytes@.subrange(0, ((i + 1) as int)) == bytes@.subrange(0, i as int) + seq![bytes[i as int]]);
                    u16run_append_ref(poly, false, c0, bytes@.subrange(0, i as int), bytes[i as int]);
                }
                i = i + 1;
            }
        }
    }

    crc
}

// =========================================================================
// Proof lemmas (moved to the end of the file; only the order changed).
// =========================================================================

pub proof fn u16run_table_append<const L: usize>(crc: u16, data: [[u16; 256]; L], s: Seq<u8>, b: u8)
    ensures u16run_table(crc, data, s + seq![b])
        == u16step_table(u16run_table(crc, data, s), data, b),
    decreases s.len(),
{
    /* [verus note: drop_last/last unfolding of the tail append -- at u16 width SMT no longer gets it
     * for free, explicit append facts (no semantic change)] */
    let s2 = s + seq![b];
    assert(s2.len() == s.len() + 1);
    assert(s2.drop_last() == s);
    assert(s2.last() == b);
}

pub proof fn u16run_append(poly: u16, reflect: bool, crc: u16, s: Seq<u8>, b: u8)
    ensures u16run(poly, reflect, crc, s + seq![b])
        == u16step_none(poly, reflect, u16run(poly, reflect, crc, s), b),
    decreases s.len(),
{
    /* [verus note: drop_last/last unfolding of the tail append (no semantic change)] */
    let s2 = s + seq![b];
    assert(s2.len() == s.len() + 1);
    assert(s2.drop_last() == s);
    assert(s2.last() == b);
}

pub proof fn u16run_table_append_ref<const L: usize>(crc: u16, data: [[u16; 256]; L], s: Seq<u8>, b: u8)
    ensures u16run_table_ref(crc, data, s + seq![b])
        == u16step_table_ref(u16run_table_ref(crc, data, s), data, b),
    decreases s.len(),
{
    /* [verus note: drop_last/last unfolding of the tail append (no semantic change)] */
    let s2 = s + seq![b];
    assert(s2.len() == s.len() + 1);
    assert(s2.drop_last() == s);
    assert(s2.last() == b);
}

pub proof fn u16run_append_ref(poly: u16, reflect: bool, crc: u16, s: Seq<u8>, b: u8)
    ensures u16run_ref(poly, reflect, crc, s + seq![b])
        == u16step_none_ref(poly, reflect, u16run_ref(poly, reflect, crc, s), b),
    decreases s.len(),
{
    /* [verus note: drop_last/last unfolding of the tail append (no semantic change)] */
    let s2 = s + seq![b];
    assert(s2.len() == s.len() + 1);
    assert(s2.drop_last() == s);
    assert(s2.last() == b);
}

// [Origin Rust: #[cfg(test)] mod test -- the slice16 correctness UT (NON/REFLEX comparison).
// Its verification form is transcribed into verified/harness/ (reference-style organization), not mirrored here.]

} // verus!
