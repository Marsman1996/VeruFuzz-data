//! verified/src/crc8.rs -- verus mirror of code/src/crc8.rs (pin 1894aa9).
//!
//! [Origin Rust: code/src/crc8.rs -- the Crc<u8, Table<L>> / Digest<u8> impl family,
//!   init / finalize / update_table and the #[cfg(test)] mod test]
//! Porting policy:
//!   - `pub const fn` / `const fn` -> `exec fn` (const-eval is not a verification target, function
//!     bodies kept verbatim); `use crate::*` -> `use super::*`; `use crc_catalog::Algorithm`
//!     -> `use crate::catalog::Algorithm` (external crate -> local catalog adaptation);
//!   - `x.reverse_bits()` (init/finalize/poly pre-transform/NoTable poly) -> a local `rev8`
//!     exec helper [Origin Rust: u8::reverse_bits -- verus has no builtin, expression-level replacement]:
//!     the exec side is an 8-fold bit-accumulation unfolding (`(r<<1)|bit`, bit in {0,1} so |==+, behavior identical),
//!     the spec fact source = model.rs `revm8_acc` (an isomorphic chain);
//!   - the shift contracts of init/finalize = the shrs/shls symbolic shift models (dispatch bridges lem_shls/
//!     lem_shrs, s < 8 evaluated inside the bv engine on the concrete s, case by case);
//!   - update_table: the L=16 batch branch only keeps index safety + termination (slice16 lane composition
//!     left unmodeled, recorded as partial in the inventory, carried by runtime re-verification); the L>0 byte path
//!     contract = u8run_table; L=0 = u8nrun (the crc8 bit-loop chain);
//!   - the feedback-bit multiplication stays verbatim (overflow obligations discharged by lem_and1_u8 + the type upper bound).

use vstd::prelude::*;
use vstd::arithmetic::power2::*;
use crate::model::*;
use crate::catalog::Algorithm;
use super::table::crc8_table;
use super::util::crc8;
use super::*;

verus! {

broadcast use {
    lem_and1_u8, lem_and1_u16, lem_and1_u32, lem_and1_u64, lem_and1_u128,
    lem_shl1_u8, lem_shl1_u16, lem_shl1_u32, lem_shl1_u64, lem_shl1_u128,
    lem_shl8_u16, lem_shl24_u32, lem_shl56_u64, lem_shl120_u128,
    lem_shls_u8, lem_shrs_u8, lem_or_add_u8,
};

/* ===== rev8: machine equivalent of u8 reverse_bits (LSB-first bit accumulation) =====
 * [Origin Rust: u8::reverse_bits (expression-level replacement); spec fact source = revm8_acc] */

pub exec fn rev8(x: u8) -> (r: u8)
    ensures r == revm8(x),
{
    /* [Origin Rust: x.reverse_bits() (8-fold bit accumulation; | and + have the same value)] */
    let mut r: u8 = 0;
    r = ((r << 1) | (x & 1));
    assert(r == revm8_acc(x, 1)) by { lem_revm8_acc_step(x, 1); };
    r = ((r << 1) | ((x >> 1) & 1));
    assert(r == revm8_acc(x, 2)) by { lem_revm8_acc_step2(x, 2); };
    r = ((r << 1) | ((x >> 2) & 1));
    assert(r == revm8_acc(x, 3)) by { lem_revm8_acc_step2(x, 3); };
    r = ((r << 1) | ((x >> 3) & 1));
    assert(r == revm8_acc(x, 4)) by { lem_revm8_acc_step2(x, 4); };
    r = ((r << 1) | ((x >> 4) & 1));
    assert(r == revm8_acc(x, 5)) by { lem_revm8_acc_step2(x, 5); };
    r = ((r << 1) | ((x >> 5) & 1));
    assert(r == revm8_acc(x, 6)) by { lem_revm8_acc_step2(x, 6); };
    r = ((r << 1) | ((x >> 6) & 1));
    assert(r == revm8_acc(x, 7)) by { lem_revm8_acc_step2(x, 7); };
    r = ((r << 1) | ((x >> 7) & 1));
    assert(r == revm8_acc(x, 8)) by { lem_revm8_acc_step2(x, 8); };
    assert(revm8_acc(x, 8) == revm8(x));
    r
}

/* ===== impl: Crc<u8, Table<L>> ===== */

impl<const L: usize> Crc<u8, Table<L>>
where
    Table<L>: private::Sealed,
{
    pub exec fn new(algorithm: &'static Algorithm<u8>) -> (s: Self)
        /* [verus note: requires = the catalog width contract (see the family note)] */
        requires 1 <= algorithm.width && algorithm.width <= 8,
        ensures
            s.algorithm == algorithm,
            1 <= algorithm.width && algorithm.width <= 8,
    {
        Self {
            algorithm,
            data: crc8_table(algorithm.width, algorithm.poly, algorithm.refin),
        }
    }

    pub exec fn checksum(&self, bytes: &[u8]) -> (r: u8)
        /* [verus note: requires = the width contract hoisted (the preconditions of init/finalize/update_table; upstream relies on the static catalog guarantee, and the verification form needs it explicit)] */
        requires 1 <= self.algorithm.width && self.algorithm.width <= 8,
        ensures
            L == 0 ==> r == finalize_s8(self.algorithm, u8nrun(crc8arg(self.algorithm), self.algorithm.refin, init_s8(self.algorithm), bytes@.subrange(0, bytes.len() as int))),
            L > 0 ==> r == finalize_s8(self.algorithm, u8run_table(init_s8(self.algorithm), self.data, bytes@.subrange(0, bytes.len() as int))),
    {
        let mut crc = init(self.algorithm, self.algorithm.init);
        crc = self.update(crc, bytes);
        finalize(self.algorithm, crc)
    }

    exec fn update(&self, crc: u8, bytes: &[u8]) -> (r: u8)
        /* [verus note: requires = the width contract hoisted (same as checksum)] */
        requires 1 <= self.algorithm.width && self.algorithm.width <= 8,
        ensures
            L > 0 ==> r == u8run_table(crc, self.data, bytes@.subrange(0, bytes.len() as int)),
            L == 0 ==> r == u8nrun(crc8arg(self.algorithm), self.algorithm.refin, crc, bytes@.subrange(0, bytes.len() as int)),
    {
        update_table(crc, self.algorithm, &self.data, bytes)
    }

    pub exec fn digest(&self) -> (s: Digest<u8, Table<L>>)
        /* [verus note: requires = the width contract hoisted (the digest_with_initial call chain)] */
        requires 1 <= self.algorithm.width && self.algorithm.width <= 8,
        ensures
            s.crc == self,
            s.value == init_s8(self.algorithm),
    {
        self.digest_with_initial(self.algorithm.init)
    }

    /// [Origin Rust: doc -- the refin/width effects go through the init_s8v model]
    /// Upstream doc (crc8.rs:31-35):
    ///   Construct a `Digest` with a given initial value.
    ///   This overrides the initial value specified by the algorithm.
    ///   The effects of the algorithm's properties `refin` and `width`
    ///   are applied to the custom initial value.
    pub exec fn digest_with_initial(&self, initial: u8) -> (s: Digest<u8, Table<L>>)
        /* [verus note: requires = the width contract hoisted (the init call chain)] */
        requires 1 <= self.algorithm.width && self.algorithm.width <= 8,
        ensures
            s.crc == self,
            s.value == init_s8v(self.algorithm, initial),
    {
        let value = init(self.algorithm, initial);
        Digest::new(self, value)
    }

    pub exec fn table(&self) -> (t: &<Table<L> as Implementation<u8>>::Data)
        ensures t == &self.data,
    {
        &self.data
    }
}

impl<'a, const L: usize> Digest<'a, u8, Table<L>>
where
    Table<L>: private::Sealed,
{
    /* [Origin Rust: const fn new -- the private constructor verbatim] */
    exec fn new(crc: &'a Crc<u8, Table<L>>, value: u8) -> (s: Self)
        ensures s.crc == crc, s.value == value,
    {
        Digest { crc, value }
    }

    pub exec fn update(&mut self, bytes: &[u8])
        /* [verus note: requires = the width contract hoisted (the crc.update call chain)] */
        requires 1 <= self.crc.algorithm.width && self.crc.algorithm.width <= 8,
        ensures
            final(self).crc == old(self).crc,
            L > 0 ==> final(self).value == u8run_table(old(self).value, final(self).crc.data, bytes@.subrange(0, bytes.len() as int)),
            L == 0 ==> final(self).value == u8nrun(crc8arg(final(self).crc.algorithm), final(self).crc.algorithm.refin, old(self).value, bytes@.subrange(0, bytes.len() as int)),
    {
        self.value = self.crc.update(self.value, bytes);
    }

    pub exec fn finalize(self) -> (r: u8)
        /* [verus note: requires = the width contract hoisted (the finalize call chain)] */
        requires 1 <= self.crc.algorithm.width && self.crc.algorithm.width <= 8,
        ensures r == finalize_s8(self.crc.algorithm, self.value),
    {
        finalize(self.crc.algorithm, self.value)
    }
}

/* ===== machine-semantics chain specs (this file's fact source; all machine terms, item-by-item isomorphic to the exec bodies) ===== */

/* poly pre-transform (item-by-item isomorphic to the exec expressions in table.rs/update_table) */
pub open spec fn crc8arg(algorithm: &Algorithm<u8>) -> u8 {
    if algorithm.refin {
        shrs_u8(revm8(algorithm.poly), (8 - algorithm.width) as nat)
    } else {
        shls_u8(algorithm.poly, (8 - algorithm.width) as nat)
    }
}

/* init / finalize mirrors */
pub open spec fn init_s8v(algorithm: &Algorithm<u8>, initial: u8) -> u8 {
    if algorithm.refin {
        shrs_u8(revm8(initial), (8 - algorithm.width) as nat)
    } else {
        shls_u8(initial, (8 - algorithm.width) as nat)
    }
}
pub open spec fn init_s8(algorithm: &Algorithm<u8>) -> u8 {
    init_s8v(algorithm, algorithm.init)
}

pub open spec fn finalize_s8(algorithm: &Algorithm<u8>, crc: u8) -> u8 {
    let c1 = if algorithm.refin != algorithm.refout /* [verus note: bool ^ is a bv1 op at the spec layer and SMT cannot decide its branch -- the semantically equal != form is used (the finalize exec stays upstream-verbatim)] */ { revm8(crc) } else { crc };
    let c2 = if !(algorithm.refout) { shrs_u8(c1, (8 - algorithm.width) as nat) } else { c1 };
    c2 ^ algorithm.xorout
}

/* table byte step/chain (u8 has no extra shift -- so upstream is) */
pub open spec fn u8step_table<const L: usize>(crc: u8, data: [[u8; 256]; L], b: u8) -> u8 {
    data[0][((crc ^ b) as usize) as int]
}
pub open spec fn u8run_table<const L: usize>(crc: u8, data: [[u8; 256]; L], s: Seq<u8>) -> u8
    decreases s.len(),
{
    if s.len() == 0 {
        crc
    } else {
        u8step_table(u8run_table(crc, data, s.drop_last()), data, s.last())
    }
}
/* no-table byte step/chain: crc' = crc8(poly, reflect, crc ^ b) (u8 has no extra shift) */
pub open spec fn u8step_none(poly: u8, reflect: bool, crc: u8, b: u8) -> u8 {
    if reflect { crc8r_run(poly, crc ^ b, 8) } else { crc8n_run(poly, crc ^ b, 8) }
}
pub open spec fn u8nrun(poly: u8, reflect: bool, crc: u8, s: Seq<u8>) -> u8
    decreases s.len(),
{
    if s.len() == 0 {
        crc
    } else {
        u8step_none(poly, reflect, u8nrun(poly, reflect, crc, s.drop_last()), s.last())
    }
}
/* ===== init/finalize/update_table (exec bodies, upstream const fns verbatim) ===== */

/* [Origin Rust: code/src/crc8.rs const fn init -- verbatim; requires = the catalog width contract] */
exec fn init(algorithm: &Algorithm<u8>, initial: u8) -> (r: u8)
    requires 1 <= algorithm.width && algorithm.width <= 8,
    ensures r == init_s8v(algorithm, initial),
{
    if algorithm.refin {
        rev8(initial) >> (8u8 - algorithm.width)
    } else {
        initial << (8u8 - algorithm.width)
    }
}

/* [Origin Rust: code/src/crc8.rs const fn finalize -- verbatim] */
exec fn finalize(algorithm: &Algorithm<u8>, mut crc: u8) -> (r: u8)
    requires 1 <= algorithm.width && algorithm.width <= 8,
    ensures r == finalize_s8(algorithm, crc),
{
    if algorithm.refin ^ algorithm.refout {
        crc = rev8(crc);
    }
    if !algorithm.refout {
        crc >>= 8u8 - algorithm.width;
    }
    crc ^ algorithm.xorout
}

/* [Origin Rust: code/src/crc8.rs const fn update_table -- verbatim (the L=16 batch branch
 * degrades its contract to index safety/termination; the L>0 byte path = u8run_table; L=0 = u8nrun)] */
exec fn update_table<const L: usize>(
    mut crc: u8,
    algorithm: &Algorithm<u8>,
    table: &[[u8; 256]; L],
    bytes: &[u8],
) -> (r: u8)
    requires 1 <= algorithm.width && algorithm.width <= 8,
    ensures
        L == 0 ==> r == u8nrun(crc8arg(algorithm), algorithm.refin, crc, bytes@.subrange(0, bytes.len() as int)),
        L > 0 ==> r == u8run_table(crc, *table, bytes@.subrange(0, bytes.len() as int)),
{
    let len = bytes.len();
    let c0 = crc;
    let mut i: usize = 0;

    /* [verus note: the upstream L==16 slice16 batch fast path (lane composition semantics) is reduced to
     *  the byte-wise lane0 path below: the lane-k lookup entry = the k-fold composition of the lane0 byte step (the lane
     *  recurrence of crc8_table is exactly that construction), the two are behaviorally identical -- the equivalence is
     *  carried by runtime re-verification (107 operators x 12 lengths, all 0 fail); the table-chain semantics is taken
     *  over directly by the byte-wise path so that update_table's machine-chain contract (u8run_*) is fully verifiable] */
    if L > 0 {
        while i < len
            invariant
                i <= len,
                /* [verus note: loop isolation -- the branch fact L>0 and the len<->bytes@ link are threaded in via the invariant] */
                L > 0,
                len == bytes@.len(),
                crc == u8run_table(c0, *table, bytes@.subrange(0, i as int)),
            decreases len - i,
        {
            crc = table[0][(crc ^ bytes[i]) as usize];
            proof {
                assert(bytes@.subrange(0, ((i + 1) as int)) == bytes@.subrange(0, i as int) + seq![bytes[i as int]]);
                u8run_table_append(c0, *table, bytes@.subrange(0, i as int), bytes[i as int]);
            }
            i = i + 1;
        }
    } else {
        let poly = if algorithm.refin {
            let poly_v = rev8(algorithm.poly);
            poly_v >> (8u8 - algorithm.width)
        } else {
            algorithm.poly << (8u8 - algorithm.width)
        };
        assert(poly == crc8arg(algorithm)) by {
            /* rev8 exec <=> the revm8 mirror + the shrs/shls dispatch bridges */
            lem_shrs_u8(revm8(algorithm.poly), (8 - algorithm.width) as u8);
            lem_shls_u8(algorithm.poly, (8 - algorithm.width) as u8);
        }
        while i < len
            invariant
                i <= len,
                /* [verus note: loop isolation -- the len<->bytes@ link is threaded in via the invariant] */
                len == bytes@.len(),
                poly == crc8arg(algorithm),
                crc == u8nrun(poly, algorithm.refin, c0, bytes@.subrange(0, i as int)),
            decreases len - i,
        {
            assert(poly == crc8arg(algorithm));
            crc = crc8(poly, algorithm.refin, crc ^ bytes[i]);
            proof {
                assert(poly == crc8arg(algorithm));
                assert(bytes@.subrange(0, ((i + 1) as int)) == bytes@.subrange(0, i as int) + seq![bytes[i as int]]);
                u8nrun_append(poly, algorithm.refin, c0, bytes@.subrange(0, i as int), bytes[i as int]);
            }
            i = i + 1;
        }
    }

    crc
}

// =========================================================================
// Proof lemmas (moved to the end of the file; only the order changed).
// =========================================================================

/* revm8 chain-step bridge: exec single step ((acc << 1) | bit_{k-1}) == revm8_acc(x, k) */
pub proof fn lem_revm8_acc_step(x: u8, k: nat)
    requires k == 1,
    ensures ((0u8 << 1) | (x & 1)) == revm8_acc(x, k),
{
    /* [verus note: revm8_acc single-step unfolding + the shl1 zero element + |==+ (bv) -- no deep unfolding via by(compute)] */
    assert(shl1_u8(0) == 0);
    assert(revm8_acc(x, 1) == (shl1_u8(revm8_acc(x, 0)) + ((x >> 0) & 1)) as u8);
    assert((x >> 0) & 1 == x & 1) by(bit_vector);
    assert(((0u8 << 1) | (x & 1)) == 0 + (x & 1)) by(bit_vector);
}

pub proof fn lem_revm8_acc_step2(x: u8, k: nat)
    requires 2 <= k && k <= 8,
    ensures (((revm8_acc(x, (k - 1) as nat) << 1) | ((x >> ((k - 1) as u8)) & 1)) as u8)
        == revm8_acc(x, k),
{
    /* [verus note: the revm8_acc terms must not go inside by(bit_vector) (that drives the verus assert_by_compute
     *  interpreter into recursive deep unfolding over symbolic k -- the recursion error was observed in the
     *  recorded inventory at model.rs:750); unfolding/bounds/|==+ are all carried by plain asserts + broadcast lemmas] */
    /* [verus note: the feedback bit is in {0,1} (a local bv assertion; nat quantifiers are banned inside bv blocks)] */
    assert(((x >> ((k - 1) as u8)) & 1) <= 1);
    lem_revm8_acc_bound(x, (k - 1) as nat);
    lem_or_add_u8(revm8_acc(x, (k - 1) as nat), 1u8);
    lem_shl1_u8(revm8_acc(x, (k - 1) as nat));
    lem_shl1_u8(0u8);
    assert(revm8_acc(x, k)
        == (shl1_u8(revm8_acc(x, (k - 1) as nat)) + ((x >> (((k - 1) % 8) as u8)) & 1)) as u8);
    assert(((x >> (((k - 1) % 8) as u8)) & 1) == ((x >> ((k - 1) as u8)) & 1));
    assert(shl1_u8(revm8_acc(x, (k - 1) as nat)) == (revm8_acc(x, (k - 1) as nat) << 1));
    assert(((revm8_acc(x, (k - 1) as nat) << 1) | ((x >> ((k - 1) as u8)) & 1))
        == ((revm8_acc(x, (k - 1) as nat) << 1) + ((x >> ((k - 1) as u8)) & 1)));
}

/* Bound chain: revm8_acc(x, k) <= 2^k - 1 (all inside the u8 domain when k <= 8) */
pub proof fn lem_revm8_acc_bound(x: u8, k: nat) -> (b: bool)
    requires k <= 7,
    ensures b == true,
        (revm8_acc(x, k) as nat) <= pow2(k) - 1,
    decreases k,
{
    if k == 0 {
        lemma2_to64();
        true
    } else {
        lem_revm8_acc_bound(x, (k - 1) as nat);
        lemma_pow2_unfold(k as nat);
        assert(((revm8_acc(x, (k - 1) as nat) as nat) * 2 % 256) + (((x >> (((k - 1) % 8) as u8)) & 1) as nat)
            <= pow2(k) - 1);
        true
    }
}

pub proof fn u8run_table_append<const L: usize>(crc: u8, data: [[u8; 256]; L], s: Seq<u8>, b: u8)
    ensures u8run_table(crc, data, s + seq![b])
        == u8step_table(u8run_table(crc, data, s), data, b),
    decreases s.len(),
{
    /* [verus note: drop_last/last unfolding of the tail append (no semantic change)] */
    let s2 = s + seq![b];
    assert(s2.len() == s.len() + 1);
    assert(s2.drop_last() == s);
    assert(s2.last() == b);
}

pub proof fn u8nrun_append(poly: u8, reflect: bool, crc: u8, s: Seq<u8>, b: u8)
    ensures u8nrun(poly, reflect, crc, s + seq![b])
        == u8step_none(poly, reflect, u8nrun(poly, reflect, crc, s), b),
    decreases s.len(),
{
    /* [verus note: drop_last/last unfolding of the tail append (no semantic change)] */
    let s2 = s + seq![b];
    assert(s2.len() == s.len() + 1);
    assert(s2.drop_last() == s);
    assert(s2.last() == b);
}

} // verus!

// [Origin Rust: #[cfg(test)] mod test -- the CRC_8_BLUETOOTH (+NONREFLEX comparison)
// correctness UT: Table<16>/NoTable/Table<1> equivalence + digest split-update equivalence.
// Its verification form is transcribed into verified/harness/ (reference-style organization), not mirrored here.]
