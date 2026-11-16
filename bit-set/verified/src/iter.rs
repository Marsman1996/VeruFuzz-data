//! bit-set 0.11.1 iterator family (set/src/iter.rs) -- Verus translation.
//!
//! Shares the crate-root BitVec mount (../lib.rs; single source of
//! verified BitVec facts, B = u32) and mirrors upstream `mod iter` as a
//! sibling module. The generic `BlockIter<T>`/`TwoBitPositions` machinery
//! is materialized as one cursor struct: the generic tail becomes a
//! stream kind (0 = or / Union, 1 = and / Intersection, 2 = andnot /
//! Difference, 3 = xor / SymmetricDifference, 4 = own / Iter) over two
//! BlocksExec cursors (the bit-vec verified borrow cursor), the `merge`
//! fn pointer becomes the kind switch, and the Intersection `n`
//! countdown rides along as the budget field. `cleared` is the ghost
//! bookkeeping of the origin's LSB removal (`head & (head - 1)`): the
//! residual head equals the current block word masked down by the
//! already-yielded bits (cleared == 0 on a fresh block). The LSB
//! position comes off the u32 trailing-zeros axiom (the origin's
//! `B::count_ones(k)` over the low-bit prefix k reads exactly that
//! position).
//!
//! Domain note (recorded for the attribution pass): the cursor
//! family bounds both stream widths at 2^32-32 minus the head-slot
//! slack (nb <= 2^32-32-32 -- see bi_inv), a requires-side tightening
//! the origin does not have; it protects the usize head_offset/cap
//! arithmetic from the overflow face. Origin iter.rs has no such
//! bound; treat as a mirror-tightening when attributing.

use vstd::prelude::*;
use vstd::std_specs::bits::u32_trailing_zeros;

verus! {

use super::bitvec_lib::{
    BitVec, blocks_for_bits, blocks_inv, inv, trailing_zero, BlocksExec,
};
use super::set::{BitSet, bs_at, bs_inv};

// ---------------------------------------------------------------------------
// stream kind (the monomorphized merge faces of TwoBitPositions)
// ---------------------------------------------------------------------------

/// 0 = or (Union), 1 = and (Intersection), 2 = andnot (Difference),
/// 3 = xor (SymmetricDifference), 4 = own stream (Iter).
pub open spec fn kind_merged(kind: u8, aw: u32, bw: u32) -> u32 {
    if kind == 0u8 {
        aw | bw
    } else if kind == 1u8 {
        aw & bw
    } else if kind == 2u8 {
        aw & (4294967295u32 ^ bw)
    } else if kind == 3u8 {
        aw ^ bw
    } else {
        aw
    }
}

/// the padded stream word at block index i, over a Seq (the exhausted
/// side of TwoBitPositions::next pads zeros; exhaustion parks the cursor
/// at end == storage length, so "past the cursor" and "past the storage"
/// coincide).
pub open spec fn side_word_seq(aseq: Seq<u32>, i: usize) -> u32 {
    if (i as int) < aseq.len() { aseq[i as int] } else { 0u32 }
}

/// the padded stream word at block index i (the cursor-side wrapper).
pub open spec fn side_word(st: &BlocksExec, i: usize) -> u32 {
    side_word_seq(st.storage@, i)
}

/// the merged stream word at block index i (the Seq-level face the
/// proofs carry across cursor movement).
pub open spec fn word_at(kind: u8, aseq: Seq<u32>, bseq: Seq<u32>, i: usize) -> u32 {
    kind_merged(kind, side_word_seq(aseq, i), side_word_seq(bseq, i))
}

// ---------------------------------------------------------------------------
// the materialized iterator cursor
// ---------------------------------------------------------------------------

/// Origin Rust: struct BlockIter<T, B> { head, head_offset, tail } over
/// TwoBitPositions / Blocks (iter.rs:3-22, 182-206) -- one cursor over
/// two side streams plus the monomorphized merge kind; `cleared` is the
/// bits already yielded out of the current head block (0 on a fresh
/// pull); `n` is the Intersection countdown (usize::MAX for the
/// non-countdown kinds).
pub struct BiExec<'a> {
    pub kind: u8,
    pub a: BlocksExec<'a>,
    pub b: BlocksExec<'a>,
    pub head: u32,
    pub cleared: u32,
    pub head_offset: usize,
    pub head_block: usize,
    pub n: usize,
    pub nb_self: usize,
    pub nb_other: usize,
    pub ghost ly_plus: usize,
}

/// cursor well-formedness. The faces in order: both side cursors live
/// inside their storages with end == storage length (so cursor
/// exhaustion and zero padding coincide), the kind in range, the pos
/// pairing (each cursor sits one block past the head index once it
/// pulled the head, parked at its end otherwise -- the from_blocks
/// pre-pull convention), the offset/index pairing with the 2^32-64
/// universe bound, the stream-width bindings (the own kind shares one
/// stream, so its other width rides on the same end), and the head
/// face: the head is the merged padded word of the head block masked
/// down by the already-yielded bits (cleared == 0 on a fresh block
/// makes this the full word).
pub open spec fn bi_inv(be: &BiExec) -> bool {
    &&& blocks_inv(&be.a)
    &&& blocks_inv(&be.b)
    &&& be.kind <= 4u8
    &&& be.a.end == be.a.storage@.len()
    &&& be.b.end == be.b.storage@.len()
    &&& (be.a.pos as int)
        == (if (be.head_block as int) + 1 < (be.a.end as int) {
            (be.head_block as int) + 1
        } else {
            be.a.end as int
        })
    &&& (be.b.pos as int)
        == (if (be.head_block as int) + 1 < (be.b.end as int) {
            (be.head_block as int) + 1
        } else {
            be.b.end as int
        })
    &&& be.head_offset == be.head_block * 32
    &&& be.head_offset <= 4294967232usize
    &&& (be.kind == 4u8 ==> be.b.end == be.a.end)
    &&& be.nb_self <= 4294967232usize
    &&& be.nb_other <= 4294967232usize
    &&& (be.a.end as int) == blocks_for_bits(be.nb_self)
    &&& (be.kind != 4u8 ==> (be.b.end as int) == blocks_for_bits(be.nb_other))
    &&& (be.a.end == 0usize || be.nb_self % 32 == 0
        || be.a.storage@[(be.a.end - 1) as int] < (1u32 << (be.nb_self % 32)))
    &&& (be.kind == 4u8 || be.b.end == 0usize || be.nb_other % 32 == 0
        || be.b.storage@[(be.b.end - 1) as int] < (1u32 << (be.nb_other % 32)))
    &&& be.head == bi_word(be, be.head_block) & (4294967295u32 ^ be.cleared)
    &&& (be.ly_plus as int) <= (be.head_offset as int) + 32int
    &&& (forall|v: usize| (v as int) < (be.head_offset as int)
        && #[trigger] bi_at(be, v)
        ==> ((v as int) + 1int) <= (be.ly_plus as int))
    &&& (forall|j: u32| (j as int) < 32int
        ==> (#[trigger] (be.cleared & (1u32 << j)) != 0u32
            ==> (be.head_offset as int) + (j as int) < (be.ly_plus as int)))
    &&& (forall|j: u32| (j as int) < 32int
        ==> (#[trigger] (bi_word(be, be.head_block) & (1u32 << j)) != 0u32
            && (be.head_offset as int) + (j as int) < (be.ly_plus as int)
            ==> (be.cleared & (1u32 << j)) != 0u32))
}

/// the merged padded stream word at block index i.
pub open spec fn bi_word(be: &BiExec, i: usize) -> u32 {
    word_at(be.kind, be.a.storage@, be.b.storage@, i)
}

/// the virtual universe width (the union/andnot/xor kinds pad out to the
/// longer side; the own kind stays at the self universe; the and kind's
/// countdown is bounded by the min -- the wider face keeps bit-level
/// well-foundedness below the min).
pub open spec fn bi_nb(be: &BiExec) -> usize {
    if be.kind == 4u8 {
        be.nb_self
    } else if be.kind == 1u8 {
        if be.nb_self < be.nb_other { be.nb_self } else { be.nb_other }
    } else {
        if be.nb_self < be.nb_other { be.nb_other } else { be.nb_self }
    }
}

/// the iterator's element face: the merged padded word's bit at j.
pub open spec fn bi_at(be: &BiExec, j: usize) -> bool {
    j < bi_nb(be)
        && (bi_word(be, (j / 32) as usize) & (1u32 << (j % 32))) != 0u32
}

/// the state-free element face over pinned stream values (the same bit
/// the bi_at face reads, spelled without the struct so exhaustion facts
/// frozen before a cursor mutation stay matchable after it).
pub open spec fn bi_face_at(kind: u8, aseq: Seq<u32>, bseq: Seq<u32>, v: usize) -> bool {
    (word_at(kind, aseq, bseq, (v / 32) as usize) & (1u32 << (v % 32))) != 0u32
}

// ---------------------------------------------------------------------------
// the width lemma: a set bit inside a padded stream sits below the width
// ---------------------------------------------------------------------------

/// a set bit of a padded block stream lies below the stream width: the
/// block index is inside the storage, so the tail-padding face bounds
/// the bit position of the last block, and earlier blocks are plainly
/// below the width. This is the per-stream half of the bi_at width face.
pub proof fn lemma_stream_bit_below(
    storage: Seq<u32>,
    nb: usize,
    k: usize,
    tz: u32,
)
    requires
        storage.len() == (blocks_for_bits(nb) as int),
        nb % 32 == 0 || storage[(blocks_for_bits(nb) - 1) as int]
            < (1u32 << (nb % 32)),
        k < storage.len(),
        (storage[k as int] & (1u32 << tz)) != 0u32,
        tz < 32u32,
    ensures
        (k as int) * 32 + (tz as int) < nb,
{
    let e = nb % 32;
    if k < blocks_for_bits(nb) - 1 {
        assert(blocks_for_bits(nb)
            == ((nb as int) / 32 + (if (nb as int) % 32 > 0 { 1int } else { 0int }))
                as usize);
        if e > 0 {
            assert((blocks_for_bits(nb) as int) == (nb as int) / 32 + 1);
        } else {
            assert((blocks_for_bits(nb) as int) == (nb as int) / 32);
        }
        assert(((nb as int) / 32) * 32 <= (nb as int));
        assert((blocks_for_bits(nb) as int - 1) * 32 <= (nb as int));
        assert((tz as int) <= 31);
        assert((k as int) * 32 + 31 < (blocks_for_bits(nb) as int) * 32);
        assert((blocks_for_bits(nb) as int) * 32 - 32
            == (blocks_for_bits(nb) as int - 1) * 32);
        assert((k as int) * 32 + 31
            < (blocks_for_bits(nb) as int - 1) * 32 + 1);
        assert((k as int) * 32 + 31 <= (blocks_for_bits(nb) as int - 1) * 32);
        assert((k as int) * 32 + (tz as int) < (nb as int));
    } else {
        assert(k == blocks_for_bits(nb) - 1);
        if e == 0 {
            assert(blocks_for_bits(nb)
                == ((nb as int) / 32 + (if (nb as int) % 32 > 0 { 1int } else {
                    0int
                })) as usize);
            assert((blocks_for_bits(nb) as int) == (nb as int) / 32);
            assert(((nb as int) / 32) * 32 == (nb as int) - ((nb as int) % 32));
            assert(((nb as int) % 32) == 0int);
            assert((k as int) * 32 + (tz as int) <= ((nb as int) / 32) * 32);
            assert((k as int) * 32 + (tz as int) <= (nb as int));
        } else {
            // the tail block is below 2^e, so a set bit of it sits in the
            // low e positions: tz < e, and the position ends below nb.
            let wtail: u32 = storage[k as int];
            assert(wtail < (1u32 << e));
            assert((1u32 << tz) <= wtail) by (bit_vector)
                requires (wtail & (1u32 << tz)) != 0u32
                    && (tz as u32) < 32u32;
            assert((1u32 << tz) < (1u32 << e)) by (bit_vector)
                requires (1u32 << tz) <= wtail
                    && wtail < (1u32 << e)
                    && (tz as u32) < 32u32 && (e as u32) < 32u32;
            assert((tz as u32) < (e as u32)) by (bit_vector)
                requires (1u32 << tz) < (1u32 << e)
                    && (tz as u32) < 32u32 && (e as u32) < 32u32;
            assert((tz as int) < e);
            assert((storage.len() as int)
                == (nb as int) / 32 + (if (nb as int) % 32 > 0 { 1int } else { 0int }));
            assert((storage.len() as int) == (nb as int) / 32 + 1);
            assert((k as int) * 32 <= (storage.len() as int) * 32 - 32);
            assert((nb as int) - e == ((nb as int) / 32) * 32);
            assert((k as int) * 32 + (tz as int)
                < (k as int) * 32 + e);
            assert((k as int) * 32 + (tz as int) < (nb as int));
        }
    }
}

// ---------------------------------------------------------------------------
// the constructors (the five Iterator entries of impl BitSet)
// ---------------------------------------------------------------------------

impl<'a> BiExec<'a> {

    /// Origin Rust: BlockIter::from_blocks(mut blocks: T) { let h =
    /// blocks.next().unwrap_or(B::zero()); BlockIter { tail: blocks,
    /// head: h, head_offset: 0 } } (iter.rs:14-21) -- the shared
    /// pre-pull: the head carries the first merged block, each side
    /// cursor sits one block past the head index (parked at its end
    /// once exhausted). Both side cursors pull unconditionally (the
    /// own kind reads only the a side, but its b cursor must track the
    /// same block grid for the pos pairing; both sides borrow the same
    /// storage in that kind).
    pub exec fn from_blocks(
        kind: u8,
        mut a: BlocksExec<'a>,
        mut b: BlocksExec<'a>,
        nb_self: usize,
        nb_other: usize,
        n: usize,
    ) -> (r: BiExec<'a>)
        requires
            blocks_inv(&a),
            blocks_inv(&b),
            kind <= 4u8,
            a.pos == 0usize,
            b.pos == 0usize,
            a.end == a.storage@.len(),
            b.end == b.storage@.len(),
            (a.end as int) == blocks_for_bits(nb_self),
            kind == 4u8 ==> b.end == a.end,
            kind != 4u8 ==> (b.end as int) == blocks_for_bits(nb_other),
            nb_self % 32 == 0 || a.storage@[(a.end - 1) as int]
                < (1u32 << (nb_self % 32)),
            kind == 4u8 || nb_other % 32 == 0
                || b.storage@[(b.end - 1) as int] < (1u32 << (nb_other % 32)),
            nb_self <= 4294967232usize,
            nb_other <= 4294967232usize,
        ensures
            bi_inv(&r),
            r.kind == kind,
            r.head_offset == 0usize,
            r.head_block == 0usize,
            r.n == n,
            r.nb_self == nb_self,
            r.nb_other == nb_other,
            r.ly_plus == 0usize,
            r.a.storage == a.storage,
            r.b.storage == b.storage,
    {
        let mut ha: u32 = 0u32;
        let mut hbw: u32 = 0u32;
        if a.pos < a.end {
            let pa = a.next();
            ha = match pa {
                Some(w) => w,
                None => 0u32,
            };
        }
        if b.pos < b.end {
            let pb = b.next();
            hbw = match pb {
                Some(w) => w,
                None => 0u32,
            };
        }
        let head = match kind {
            0u8 => ha | hbw,
            1u8 => ha & hbw,
            2u8 => ha & (4294967295u32 ^ hbw),
            3u8 => ha ^ hbw,
            _ => ha,
        };
        let mut r = BiExec {
            kind: kind,
            a: a,
            b: b,
            head: head,
            cleared: 0u32,
            head_offset: 0usize,
            head_block: 0usize,
            n: n,
            nb_self: nb_self,
            nb_other: nb_other,
            ly_plus: 0,
        };
        proof {
            // the pre-pull pairing: one block consumed per live side
            if r.a.end > 0usize {
                assert(r.a.pos == 1usize);
                assert(ha == r.a.storage@[0]);
            } else {
                assert(r.a.pos == 0usize);
                assert(ha == 0u32);
            }
            if r.b.end > 0usize {
                assert(r.b.pos == 1usize);
                assert(hbw == r.b.storage@[0]);
            } else {
                assert(r.b.pos == 0usize);
                assert(hbw == 0u32);
            }
            assert((r.a.pos as int)
                == (if (r.a.end as int) <= 1int {
                    (r.a.end as int)
                } else {
                    1int
                }));
            assert((r.b.pos as int)
                == (if (r.b.end as int) <= 1int {
                    (r.b.end as int)
                } else {
                    1int
                }));
            assert(side_word(&r.a, 0usize) == ha);
            assert(side_word(&r.b, 0usize) == hbw);
            let aw2 = side_word(&r.a, 0usize);
            let bw2 = side_word(&r.b, 0usize);
            if kind == 0u8 {
                assert(aw2 | bw2 == head);
            } else if kind == 1u8 {
                assert(aw2 & bw2 == head);
            } else if kind == 2u8 {
                assert(aw2 & (4294967295u32 ^ bw2) == head);
            } else if kind == 3u8 {
                assert(aw2 ^ bw2 == head);
            } else {
                assert(aw2 == head);
            }
            assert(bi_word(&r, 0usize) == head);
            assert(r.head_block == 0usize);
            assert(bi_word(&r, r.head_block) == head);
            assert(r.cleared == 0u32);
            let h2: u32 = head;
            let c2: u32 = r.cleared;
            assert(h2 == (h2 & (4294967295u32 ^ c2))) by (bit_vector)
                requires c2 == 0u32;
            assert(head == (head & (4294967295u32 ^ r.cleared)));
            // the fresh cursor's yield-log rows: ly_plus == 0 with a fresh
            // head at offset 0 makes every one of them vacuous
            assert(r.ly_plus == 0usize);
            assert((r.ly_plus as int) <= (r.head_offset as int) + 32int);
            assert forall|v: usize| ((v as int) < (r.head_offset as int))
                && bi_at(&r, v)
                implies (((v as int) + 1int) <= (r.ly_plus as int)) by { }
            assert forall|j: u32| (j as int) < 32int
                implies (((r.cleared & (1u32 << j)) != 0u32)
                    ==> ((r.head_offset as int) + (j as int)
                        < (r.ly_plus as int))) by {
                let cz: u32 = r.cleared;
                if (cz & (1u32 << j)) != 0u32 {
                    assert((0u32 & (1u32 << j)) == 0u32) by (bit_vector);
                    assert(false);
                }
            }
            assert forall|j: u32| (j as int) < 32int
                implies (((bi_word(&r, r.head_block) & (1u32 << j)) != 0u32)
                    && ((r.head_offset as int) + (j as int)
                        < (r.ly_plus as int)))
                    ==> ((r.cleared & (1u32 << j)) != 0u32) by { }
        }
        r
    }

    /// Origin Rust: pub fn union<'a>(&'a self, other: &'a Self) -> Union
    ///     (iter.rs:45-55) -- Iterator over each usize stored in `self`
    ///     union `other`.
    /// Upstream doc (iter.rs:26-27):
    ///   Iterator over each usize stored in `self` union `other`.
    ///   See [`union_with`] for an efficient in-place version.
    /// Upstream doc (iter.rs:29-41) examples: from_bytes([0b01101000])
    /// union from_bytes([0b10100000]) prints 0, 1, 2, 4.
    /// (batch H2 signature fix: the batch-C pass had mounted both side
    /// cursors on the single argument's stream, which reads as the own
    /// stream twice -- the origin walks self's stream against other's;
    /// the mirror now takes both bit vectors, like its three siblings)
    pub exec fn bi_union(self_bv: &'a BitVec, other_bv: &'a BitVec) -> (r: BiExec<'a>)
        requires
            inv(self_bv),
            inv(other_bv),
            self_bv.nbits <= 4294967232usize,
            other_bv.nbits <= 4294967232usize,
        ensures
            bi_inv(&r),
            r.kind == 0u8,
            r.head_offset == 0usize,
            r.head_block == 0usize,
            r.n == 4294967295usize,
            r.ly_plus == 0usize,
            r.nb_self == self_bv.nbits,
            r.nb_other == other_bv.nbits,
            r.a.storage@ == self_bv.storage@,
            r.b.storage@ == other_bv.storage@,
    {
        let nb_self = self_bv.nbits;
        let nb_other = other_bv.nbits;
        proof {
            assert(trailing_zero(self_bv));
            assert(trailing_zero(other_bv));
        }
        let bl_a = self_bv.blocks();
        let bl_b = other_bv.blocks();
        proof {
            assert(bl_a.end == self_bv.storage@.len());
            assert(bl_b.end == other_bv.storage@.len());
            assert(self_bv.storage@.len() == blocks_for_bits(nb_self));
            assert(other_bv.storage@.len() == blocks_for_bits(nb_other));
            assert((bl_a.end as int) == blocks_for_bits(nb_self));
            assert((bl_b.end as int) == blocks_for_bits(nb_other));
            assert(bl_a.storage@ == self_bv.storage@);
            assert(bl_b.storage@ == other_bv.storage@);
        }
        Self::from_blocks(0u8, bl_a, bl_b, nb_self, nb_other, 4294967295usize)
    }

    /// Origin Rust: pub fn intersection<'a>(...) -> Intersection
    ///     (iter.rs:76-90) -- Iterator over each usize stored in `self`
    ///     intersect `other`, with the min-universe countdown n.
    /// Upstream doc (iter.rs:57-58):
    ///   Iterator over each usize stored in `self` intersect `other`.
    /// Upstream doc (iter.rs:60-72) examples: from_bytes([0b01101000])
    /// intersection from_bytes([0b10100000]) prints 2.
    pub exec fn bi_intersection(self_bv: &'a BitVec, other_bv: &'a BitVec) -> (r: BiExec<'a>)
        requires
            inv(self_bv),
            inv(other_bv),
            self_bv.nbits <= 4294967232usize,
            other_bv.nbits <= 4294967232usize,
        ensures
            bi_inv(&r),
            r.kind == 1u8,
            r.head_offset == 0usize,
            r.head_block == 0usize,
            r.n == (if self_bv.nbits < other_bv.nbits {
                self_bv.nbits
            } else {
                other_bv.nbits
            }),
            r.ly_plus == 0usize,
            r.nb_self == self_bv.nbits,
            r.nb_other == other_bv.nbits,
            r.a.storage@ == self_bv.storage@,
            r.b.storage@ == other_bv.storage@,
    {
        let nb_self = self_bv.nbits;
        let nb_other = other_bv.nbits;
        proof {
            assert(trailing_zero(self_bv));
            assert(trailing_zero(other_bv));
        }
        let bl_a = self_bv.blocks();
        let bl_b = other_bv.blocks();
        proof {
            assert(bl_a.end == self_bv.storage@.len());
            assert(bl_b.end == other_bv.storage@.len());
            assert(self_bv.storage@.len() == blocks_for_bits(nb_self));
            assert(other_bv.storage@.len() == blocks_for_bits(nb_other));
            assert((bl_a.end as int) == blocks_for_bits(nb_self));
            assert((bl_b.end as int) == blocks_for_bits(nb_other));
            assert(bl_a.storage@ == self_bv.storage@);
            assert(bl_b.storage@ == other_bv.storage@);
        }
        Self::from_blocks(
            1u8,
            bl_a,
            bl_b,
            nb_self,
            nb_other,
            if nb_self < nb_other { nb_self } else { nb_other },
        )
    }

    /// Origin Rust: pub fn difference<'a>(&'a self, other: &'a Self)
    ///     (iter.rs:118-128) -- the setminus face.
    /// Upstream doc (iter.rs:92-93):
    ///   Iterator over each usize stored in the `self` setminus `other`.
    /// Upstream doc (iter.rs:95-114) examples: from_bytes([0b01101000])
    /// difference from_bytes([0b10100000]) prints 1, 4 (and the reverse
    /// prints 0).
    pub exec fn bi_difference(self_bv: &'a BitVec, other_bv: &'a BitVec) -> (r: BiExec<'a>)
        requires
            inv(self_bv),
            inv(other_bv),
            self_bv.nbits <= 4294967232usize,
            other_bv.nbits <= 4294967232usize,
        ensures
            bi_inv(&r),
            r.kind == 2u8,
            r.head_offset == 0usize,
            r.head_block == 0usize,
            r.n == 4294967295usize,
            r.ly_plus == 0usize,
            r.nb_self == self_bv.nbits,
            r.nb_other == other_bv.nbits,
            r.a.storage@ == self_bv.storage@,
            r.b.storage@ == other_bv.storage@,
    {
        let nb_self = self_bv.nbits;
        let nb_other = other_bv.nbits;
        proof {
            assert(trailing_zero(self_bv));
            assert(trailing_zero(other_bv));
        }
        let bl_a = self_bv.blocks();
        let bl_b = other_bv.blocks();
        proof {
            assert(bl_a.end == self_bv.storage@.len());
            assert(bl_b.end == other_bv.storage@.len());
            assert(self_bv.storage@.len() == blocks_for_bits(nb_self));
            assert(other_bv.storage@.len() == blocks_for_bits(nb_other));
            assert((bl_a.end as int) == blocks_for_bits(nb_self));
            assert((bl_b.end as int) == blocks_for_bits(nb_other));
            assert(bl_a.storage@ == self_bv.storage@);
            assert(bl_b.storage@ == other_bv.storage@);
        }
        Self::from_blocks(2u8, bl_a, bl_b, nb_self, nb_other, 4294967295usize)
    }

    /// Origin Rust: pub fn symmetric_difference<'a>(...)
    ///     (iter.rs:149-159).
    /// Upstream doc (iter.rs:130-131):
    ///   Iterator over each usize stored in the symmetric difference of
    ///   `self` and `other`.
    /// Upstream doc (iter.rs:133-145) examples: prints 0, 1, 4.
    pub exec fn bi_symmetric_difference(
        self_bv: &'a BitVec,
        other_bv: &'a BitVec,
    ) -> (r: BiExec<'a>)
        requires
            inv(self_bv),
            inv(other_bv),
            self_bv.nbits <= 4294967232usize,
            other_bv.nbits <= 4294967232usize,
        ensures
            bi_inv(&r),
            r.kind == 3u8,
            r.head_offset == 0usize,
            r.head_block == 0usize,
            r.n == 4294967295usize,
            r.ly_plus == 0usize,
            r.nb_self == self_bv.nbits,
            r.nb_other == other_bv.nbits,
            r.a.storage@ == self_bv.storage@,
            r.b.storage@ == other_bv.storage@,
    {
        let nb_self = self_bv.nbits;
        let nb_other = other_bv.nbits;
        proof {
            assert(trailing_zero(self_bv));
            assert(trailing_zero(other_bv));
        }
        let bl_a = self_bv.blocks();
        let bl_b = other_bv.blocks();
        proof {
            assert(bl_a.end == self_bv.storage@.len());
            assert(bl_b.end == other_bv.storage@.len());
            assert(self_bv.storage@.len() == blocks_for_bits(nb_self));
            assert(other_bv.storage@.len() == blocks_for_bits(nb_other));
            assert((bl_a.end as int) == blocks_for_bits(nb_self));
            assert((bl_b.end as int) == blocks_for_bits(nb_other));
            assert(bl_a.storage@ == self_bv.storage@);
            assert(bl_b.storage@ == other_bv.storage@);
        }
        Self::from_blocks(3u8, bl_a, bl_b, nb_self, nb_other, 4294967295usize)
    }

    /// Origin Rust: pub fn iter(&self) -> Iter(BlockIter::from_blocks(
    ///     self.bit_vec.blocks())) (iter.rs:176-178).
    /// Upstream doc (iter.rs:161-162):
    ///   Iterator over each usize stored in the `BitSet`.
    /// Upstream doc (iter.rs:164-174) examples: from_bytes([0b01001010])
    /// prints 1, 4, 6.
    pub exec fn bi_iter(self_bv: &'a BitVec) -> (r: BiExec<'a>)
        requires
            inv(self_bv),
            self_bv.nbits <= 4294967232usize,
        ensures
            bi_inv(&r),
            r.kind == 4u8,
            r.head_offset == 0usize,
            r.head_block == 0usize,
            r.n == 4294967295usize,
            r.ly_plus == 0usize,
            r.nb_self == self_bv.nbits,
            r.a.storage@ == self_bv.storage@,
            r.b.storage@ == self_bv.storage@,
    {
        let nb_self = self_bv.nbits;
        proof {
            assert(trailing_zero(self_bv));
        }
        let bl_a = self_bv.blocks();
        let bl_b = self_bv.blocks();
        proof {
            assert(bl_a.end == self_bv.storage@.len());
            assert(bl_b.end == self_bv.storage@.len());
            assert(bl_b.end == bl_a.end);
            assert(self_bv.storage@.len() == blocks_for_bits(nb_self));
            assert((bl_a.end as int) == blocks_for_bits(nb_self));
            assert(bl_a.storage@ == self_bv.storage@);
        }
        Self::from_blocks(4u8, bl_a, bl_b, nb_self, 0usize, 4294967295usize)
    }
}

// ---------------------------------------------------------------------------
// the walk kernel (BlockIter::next, iter.rs:214-232)
// ---------------------------------------------------------------------------

impl<'a> BiExec<'a> {

    /// Origin Rust: fn next(&mut self) -> Option<Self::Item>
    ///     (iter.rs:214-232; TwoBitPositions::next iter.rs:250-257 pairs
    ///     the side cursors with the exhausted-side zero arm, BlockIter
    ///     skips the zero heads)
    /// Upstream comment (iter.rs:223-231) -- the LSB isolation comment:
    ///   from the current block, isolate the LSB and subtract 1, ...
    ///   update block, removing the LSB ... return offset + (index of LSB)
    pub exec fn bi_next(&mut self) -> (r: Option<usize>)
        requires
            bi_inv(old(self)),
        ensures
            bi_inv(final(self)),
            final(self).kind == old(self).kind,
            final(self).nb_self == old(self).nb_self,
            final(self).nb_other == old(self).nb_other,
            final(self).n == old(self).n,
            final(self).a.storage == old(self).a.storage,
            final(self).b.storage == old(self).b.storage,
            final(self).ly_plus
                == (if r.is_Some() { (r.unwrap() + 1) as usize } else { old(self).ly_plus }),
            // the yield face: each yielded element is a member that sits
            // strictly at-or-above the yield log (the log counts the last
            // yield plus one; 0 means nothing yielded yet), with no member
            // between the logged yield and this one (the walk is the
            // ascending enumeration of the merged stream's members)
            r.is_Some() ==> (old(self).ly_plus as int) <= (r.unwrap() as int),
            r.is_Some() ==> bi_at(old(self), r.unwrap()),
            r.is_Some() ==> forall|v: usize|
                (old(self).ly_plus as int) <= (v as int)
                && (v as int) < (r.unwrap() as int)
                ==> !bi_at(old(self), v),
            // the exhaustion face: a None step means no member remains
            // at-or-above the logged yield
            r.is_None() ==> forall|v: usize|
                (old(self).ly_plus as int) <= (v as int)
                ==> !bi_at(old(self), v),
    {
        let ghost old_kind = self.kind;
        let ghost old_nb_self = self.nb_self;
        let ghost old_nb_other = self.nb_other;
        let ghost old_st_a = self.a.storage;
        let ghost old_st_b = self.b.storage;
        let ghost aseq: Seq<u32> = old_st_a@;
        let ghost nbv: usize = bi_nb(self);
        let ghost bseq: Seq<u32> = old_st_b@;
        proof {
            // the entry snapshots are literally the old(self) field values
            assert(old_st_a == old(self).a.storage);
            assert(old_st_b == old(self).b.storage);
        }
        while self.head == 0u32
            invariant
                bi_inv(self),
                self.kind == old_kind,
                self.nb_self == old_nb_self,
                self.nb_other == old_nb_other,
                bi_nb(self) == nbv,
                self.ly_plus == old(self).ly_plus,
                self.a.storage == old(self).a.storage,
                self.b.storage == old(self).b.storage,
                self.a.storage == old_st_a,
                self.b.storage == old_st_b,
                self.a.storage@ == aseq,
                self.b.storage@ == bseq,
            decreases ((self.a.end as int) - (self.a.pos as int))
                + ((self.b.end as int) - (self.b.pos as int)),
        {
            let new_hb = self.head_block + 1;
            let ghost old_pa: usize = self.a.pos;
            let ghost old_pb: usize = self.b.pos;
            let ghost old_hb: usize = self.head_block;
            // freeze the exhausted old head block while the state still
            // carries it (head == 0 under the loop guard): every set word
            // bit is parked in cleared, and the state-free element face
            // below the old head offset stays clear above the last yield
            let ghost gp_word: u32 = bi_word(self, old_hb);
            let ghost gp_cleared: u32 = self.cleared;
            let ghost gp_ho: usize = self.head_offset;
            proof {
                assert(self.head == 0u32);
                assert(self.head == gp_word & (4294967295u32 ^ gp_cleared));
                lemma_ex_word_parked(gp_word, gp_cleared);
                // the doorstep parking map, quoted in self form so the
                // invariant's face fires at the ground terms
                assert forall|j3: u32| (j3 as int) < 32int
                    implies (((self.cleared & (1u32 << j3)) != 0u32)
                        ==> ((self.head_offset as int) + (j3 as int)
                            < (self.ly_plus as int))) by { }
                // the pre-head exhaustion face, frozen over the pinned
                // stream values (bi_face_at mentions no struct field, so
                // the fact survives the head/head_block writes)
                assert forall|vv: usize| ((self.ly_plus as int) <= (vv as int))
                    && (vv as int) < (gp_ho as int)
                    implies ((vv < nbv) ==> #[trigger] bi_face_at(old_kind, aseq, bseq, vv) == false) by {
                    if ((self.ly_plus as int) <= (vv as int))
                        && (vv as int) < (gp_ho as int) {
                        assert(bi_at(self, vv) == false);
                        assert(bi_nb(self) == nbv);
                        assert(bi_word(self, (vv / 32) as usize)
                            == word_at(old_kind, aseq, bseq, (vv / 32) as usize));
                        if vv < nbv {
                            assert(bi_face_at(old_kind, aseq, bseq, vv)
                                == bi_at(self, vv));
                            assert(bi_face_at(old_kind, aseq, bseq, vv) == false);
                        }
                    }
                }
                // the exhausted word's above-yield face, frozen the same way
                assert((gp_ho as int) == 32 * (old_hb as int));
                assert forall|vv: usize| ((self.ly_plus as int) <= (vv as int))
                    && (gp_ho as int) <= (vv as int)
                    && (vv as int) < (gp_ho as int) + 32
                    implies ((vv < nbv) ==> #[trigger] bi_face_at(old_kind, aseq, bseq, vv) == false) by {
                    if ((self.ly_plus as int) <= (vv as int))
                        && (gp_ho as int) <= (vv as int)
                        && (vv as int) < (gp_ho as int) + 32 {
                        let j4: u32 = ((vv as int) - (gp_ho as int)) as u32;
                        assert(((vv as int) / 32) == (old_hb as int)) by (nonlinear_arith)
                            requires (gp_ho as int) <= (vv as int)
                                && (vv as int) < (gp_ho as int) + 32
                                && (gp_ho as int) == 32 * (old_hb as int);
                        assert(vv / 32 == old_hb);
                        assert((vv as int) == (gp_ho as int) + (j4 as int));
                        assert((vv % 32) as u32 == j4);
                        // the parking map of the exhausted word
                        assert((gp_word & (1u32 << j4)) != 0u32
                            ==> (gp_cleared & (1u32 << j4)) != 0u32);
                        assert((gp_cleared & (1u32 << j4)) != 0u32
                            ==> ((self.head_offset as int) + (j4 as int)
                                < (self.ly_plus as int)));
                        assert(bi_nb(self) == nbv);
                        assert(bi_word(self, (vv / 32) as usize) == gp_word);
                        assert(bi_at(self, vv) == ((vv < nbv)
                            && ((gp_word & (1u32 << j4)) != 0u32)));
                        if (gp_word & (1u32 << j4)) != 0u32 {
                            // parked: sits at-or-below the logged yield, which
                            // contradicts vv at-or-above the log
                            assert((self.head_offset as int) + (j4 as int)
                                < (self.ly_plus as int));
                            assert((gp_ho as int) + (j4 as int) == (vv as int));
                            assert(false);
                        }
                    }
                }
            }
            assert((old_pa as int)
                == (if ((old_hb as int) + 1) < (self.a.end as int) {
                    ((old_hb as int) + 1) as int
                } else {
                    (self.a.end as int)
                }));
            assert((old_pb as int)
                == (if ((old_hb as int) + 1) < (self.b.end as int) {
                    ((old_hb as int) + 1) as int
                } else {
                    (self.b.end as int)
                }));
            let wa = self.a.next();
            let wb = self.b.next();
            if wa matches Some(_) || wb matches Some(_) {
                let aw: u32 = match wa {
                    Some(w) => w,
                    None => 0u32,
                };
                let bwd: u32 = match wb {
                    Some(w) => w,
                    None => 0u32,
                };
                self.head = match self.kind {
                    0u8 => aw | bwd,
                    1u8 => aw & bwd,
                    2u8 => aw & (4294967295u32 ^ bwd),
                    3u8 => aw ^ bwd,
                    _ => aw,
                };
                self.cleared = 0u32;
                proof {
                    // bridge the pulled values onto the padded side_word
                    // faces of the new head block
                    assert(self.a.end == self.a.storage@.len());
                    assert(self.b.end == self.b.storage@.len());
                    if wa matches Some(_) {
                        assert((self.a.pos as int) == (old_pa as int) + 1int);
                        assert((old_pa as int) < (self.a.end as int));
                        assert(((old_hb as int) + 1) < (self.a.end as int)) by {
                            if !(((old_hb as int) + 1) < (self.a.end as int)) {
                                assert((old_pa as int) == (self.a.end as int));
                                assert(false);
                            }
                        }
                        assert((old_pa as int) == (old_hb as int) + 1);
                        assert((new_hb as int) == (old_pa as int));
                        assert(self.a.storage@[(new_hb as int)] == aw);
                        assert(side_word(&self.a, new_hb) == aw);
                    } else {
                        assert((self.a.end as int) == (old_pa as int));
                        assert((self.a.pos as int) == (self.a.end as int));
                        assert((new_hb as int) >= (self.a.end as int));
                        assert(side_word(&self.a, new_hb) == 0u32);
                    }
                    if wb matches Some(_) {
                        assert((self.b.pos as int) == (old_pb as int) + 1int);
                        assert((old_pb as int) < (self.b.end as int));
                        assert(((old_hb as int) + 1) < (self.b.end as int)) by {
                            if !(((old_hb as int) + 1) < (self.b.end as int)) {
                                assert((old_pb as int) == (self.b.end as int));
                                assert(false);
                            }
                        }
                        assert((old_pb as int) == (old_hb as int) + 1);
                        assert((new_hb as int) == (old_pb as int));
                        assert(self.b.storage@[(new_hb as int)] == bwd);
                        assert(side_word(&self.b, new_hb) == bwd);
                    } else {
                        assert((self.b.end as int) == (old_pb as int));
                        assert((self.b.pos as int) == (self.b.end as int));
                        assert((new_hb as int) >= (self.b.end as int));
                        assert(side_word(&self.b, new_hb) == 0u32);
                    }
                    // the index/offset bound faces of the pull
                    assert(blocks_for_bits(self.nb_self)
                        == (((self.nb_self as int) / 32)
                            + (if (self.nb_self as int) % 32 > 0int {
                                1int
                            } else {
                                0int
                            })) as usize);
                    assert(blocks_for_bits(self.nb_other)
                        == (((self.nb_other as int) / 32)
                            + (if (self.nb_other as int) % 32 > 0int {
                                1int
                            } else {
                                0int
                            })) as usize);
                    assert((self.nb_self as int) <= 134217726 * 32);
                    assert((self.nb_other as int) <= 134217726 * 32);
                    if wa matches Some(_) {
                        assert((new_hb as int) < (blocks_for_bits(self.nb_self) as int)) by {
                            assert((new_hb as int) < (self.a.end as int));
                            assert((self.a.end as int)
                                == (blocks_for_bits(self.nb_self) as int));
                        }
                    }
                    if wb matches Some(_) {
                        assert((new_hb as int) < 134217727) by {
                            assert((new_hb as int) < (self.b.end as int));
                            assert((blocks_for_bits(self.nb_self) as int) <= 134217727);
                            assert((blocks_for_bits(self.nb_other) as int) <= 134217727);
                            if self.kind == 4u8 {
                                assert(self.b.end == self.a.end);
                                assert((self.a.end as int)
                                    == (blocks_for_bits(self.nb_self) as int));
                            }
                            if !(self.kind == 4u8) {
                                assert((self.b.end as int)
                                    == (blocks_for_bits(self.nb_other) as int));
                            }
                        }
                    }
                    assert((new_hb as int) < (blocks_for_bits(self.nb_self) as int)
                        || (new_hb as int) < (blocks_for_bits(self.nb_other) as int)) by {
                        if wa matches Some(_) {
                            assert((new_hb as int)
                                < (blocks_for_bits(self.nb_self) as int));
                        } else {
                            // the a side is exhausted: the b side carried the pull
                            assert(self.kind != 4u8) by {
                                if self.kind == 4u8 {
                                    assert(self.b.end == self.a.end);
                                    assert((old_pb as int)
                                        == (if ((old_hb as int) + 1) < (self.b.end as int) {
                                            ((old_hb as int) + 1) as int
                                        } else {
                                            (self.b.end as int)
                                        }));
                                    assert(wb matches None);
                                    assert(false);
                                }
                            }
                            assert((new_hb as int)
                                < (blocks_for_bits(self.nb_other) as int));
                        }
                    }
                    assert((new_hb as int) * 32 <= 4294967232);
                    assert(bi_word(self, new_hb) == self.head) by {
                        let sw2 = side_word(&self.a, new_hb);
                        let ow2 = side_word(&self.b, new_hb);
                        if self.kind == 0u8 {
                            assert(kind_merged(self.kind, sw2, ow2) == sw2 | ow2);
                        } else if self.kind == 1u8 {
                            assert(kind_merged(self.kind, sw2, ow2) == sw2 & ow2);
                        } else if self.kind == 2u8 {
                            assert(kind_merged(self.kind, sw2, ow2)
                                == sw2 & (4294967295u32 ^ ow2));
                        } else if self.kind == 3u8 {
                            assert(kind_merged(self.kind, sw2, ow2) == sw2 ^ ow2);
                        } else {
                            assert(kind_merged(self.kind, sw2, ow2) == sw2);
                        }
                    }
                }
                self.head_block = new_hb;
                self.head_offset = self.head_offset + 32;
                proof {
                    // the head face at the fresh block: cleared resets to 0,
                    // so the head is exactly the merged word
                    let hg: u32 = self.head;
                    let c2: u32 = self.cleared;
                    let ghost g = bi_word(self, self.head_block);
                    assert(c2 == 0u32);
                    assert(g == hg);
                    assert(hg == g & (4294967295u32 ^ c2)) by (bit_vector)
                        requires g == hg && c2 == 0u32;
                    assert(self.head == bi_word(self, self.head_block)
                        & (4294967295u32 ^ self.cleared));
                    assert(self.head_offset == self.head_block * 32);
                    // the pre-head face of the advanced cursor: the two
                    // frozen range faces splice into (last_yield, head_offset)
                    assert(self.head_offset == gp_ho + 32);
                    // row bisection
                    assert((self.ly_plus as int) <= (self.head_offset as int) + 32int);
                    assert forall|j: u32| (j as int) < 32int
                        implies (#[trigger] (self.cleared & (1u32 << j)) != 0u32
                            ==> (self.head_offset as int) + (j as int)
                                < (self.ly_plus as int)) by {
                        let cz: u32 = self.cleared;
                        if (cz & (1u32 << j)) != 0u32 {
                            assert((0u32 & (1u32 << j)) == 0u32) by (bit_vector);
                            assert(false);
                        }
                    }
                    assert forall|j: u32| (j as int) < 32int
                        implies ((#[trigger] (bi_word(self, self.head_block) & (1u32 << j)) != 0u32)
                            && ((self.head_offset as int) + (j as int)
                                < (self.ly_plus as int))
                            ==> ((self.cleared & (1u32 << j)) != 0u32)) by { }
                    assert forall|v2: usize| ((self.ly_plus as int) <= (v2 as int))
                        && (v2 as int) < (self.head_offset as int)
                        implies (bi_at(self, v2) == false) by {
                        assert(bi_nb(self) == nbv);
                        assert(bi_word(self, (v2 / 32) as usize)
                            == word_at(old_kind, aseq, bseq, (v2 / 32) as usize));
                        assert(bi_at(self, v2) == ((v2 < nbv)
                            && bi_face_at(old_kind, aseq, bseq, v2)));
                        if (v2 < nbv) {
                            assert(bi_face_at(old_kind, aseq, bseq, v2) == false);
                        }
                    }
                }
            } else {
                // both side cursors exhausted: upstream returns None. The
                // exhaustion face: above the last yield the merged stream
                // holds no member (the walked-past blocks yielded all of
                // theirs, the exhausted head block parks all of its word
                // bits, and both exhausted cursors sit at their ends, so
                // every further merged word is zero padding)
                proof {
                    let ghost lp1: usize = self.ly_plus;
                    let ho1: usize = self.head_offset;
                    let hb1: usize = self.head_block;
                    assert(self.head == 0u32);
                    assert(self.head_offset == self.head_block * 32);
                    assert((ho1 as int) == 32 * (hb1 as int));
                    // the exhausted side cursors sit at their ends
                    assert(self.a.pos == self.a.end);
                    assert(self.b.pos == self.b.end);
                    assert(bi_nb(old(self)) == bi_nb(self));
                    assert(old(self).ly_plus == lp1);
                    assert forall|v: usize| (lp1 as int) <= (v as int)
                        implies (bi_at(old(self), v) == false) by {
                        if (v as int) < (ho1 as int) {
                            // the walked-past region: the invariant's face
                            // (a member below the walked offset is logged)
                            assert(bi_at(self, v) ==> (((v as int) + 1int)
                                <= (self.ly_plus as int)));
                            assert(lp1 as int <= (v as int));
                            assert(bi_at(self, v) == false);
                            assert(bi_at(old(self), v) == bi_at(self, v));
                        } else if (v as int) < (ho1 as int) + 32 {
                            // the exhausted head block
                            assert(((v as int) / 32) == (hb1 as int)) by (nonlinear_arith)
                                requires (ho1 as int) <= (v as int)
                                    && (v as int) < (ho1 as int) + 32
                                    && (ho1 as int) == 32 * (hb1 as int);
                            assert(v / 32 == hb1);
                            let w1: u32 = bi_word(self, hb1);
                            let c1: u32 = self.cleared;
                            assert(bi_word(self, (v / 32) as usize) == w1);
                            assert(bi_word(old(self), (v / 32) as usize) == w1);
                            if (w1 & (1u32 << (v % 32))) != 0u32 {
                                // the word bit is parked; the invariant parks
                                // it at-or-below the last yield
                                let h1: u32 = self.head;
                                assert((c1 & (1u32 << (v % 32))) != 0u32) by (bit_vector)
                                    requires h1 == 0u32
                                        && h1 == w1 & (4294967295u32 ^ c1)
                                        && (w1 & (1u32 << (v % 32))) != 0u32;
                                assert((self.cleared & (1u32 << (v % 32))) != 0u32);
                                assert((self.head_offset as int) + ((v % 32) as int)
                                    < (self.ly_plus as int));
                                assert((ho1 as int) + ((v % 32) as int) == (v as int));
                                assert(false);
                            } else {
                                assert(bi_at(self, v) == false);
                                assert(bi_at(old(self), v) == bi_at(self, v));
                            }
                        } else {
                            // beyond the head block: zero padding on both
                            // sides, so the merged word is zero under any
                            // kind
                            let k1: usize = (v / 32) as usize;
                            assert(((v as int) / 32) >= (hb1 as int) + 1) by (nonlinear_arith)
                                requires (v as int) >= (ho1 as int) + 32
                                    && (ho1 as int) == 32 * (hb1 as int);
                            assert((k1 as int) == ((v as int) / 32));
                            assert((k1 as int) >= (self.a.end as int));
                            assert((k1 as int) >= (self.b.end as int));
                            assert((k1 as int) >= (self.a.storage@.len() as int));
                            assert((k1 as int) >= (self.b.storage@.len() as int));
                            let sw1: u32 = side_word_seq(aseq, k1);
                            let ow1: u32 = side_word_seq(bseq, k1);
                            assert(sw1 == 0u32);
                            assert(ow1 == 0u32);
                            assert(word_at(old_kind, aseq, bseq, k1)
                                == kind_merged(old_kind, sw1, ow1));
                            let swz: u32 = sw1;
                            let owz: u32 = ow1;
                            if old_kind == 0u8 {
                                assert(kind_merged(old_kind, swz, owz) == swz | owz);
                                assert((swz | owz) == 0u32) by (bit_vector)
                                    requires swz == 0u32 && owz == 0u32;
                            } else if old_kind == 1u8 {
                                assert(kind_merged(old_kind, swz, owz) == swz & owz);
                                assert((swz & owz) == 0u32) by (bit_vector)
                                    requires swz == 0u32 && owz == 0u32;
                            } else if old_kind == 2u8 {
                                assert(kind_merged(old_kind, swz, owz)
                                    == swz & (4294967295u32 ^ owz));
                                assert((swz & (4294967295u32 ^ owz)) == 0u32) by (bit_vector)
                                    requires swz == 0u32;
                            } else if old_kind == 3u8 {
                                assert(kind_merged(old_kind, swz, owz) == swz ^ owz);
                                assert((swz ^ owz) == 0u32) by (bit_vector)
                                    requires swz == 0u32 && owz == 0u32;
                            } else {
                                assert(kind_merged(old_kind, swz, owz) == swz);
                                assert(swz == 0u32);
                            }
                            assert(kind_merged(old_kind, sw1, ow1) == 0u32);
                            assert(word_at(old_kind, aseq, bseq, k1) == 0u32);
                            let zword: u32 = word_at(old_kind, aseq, bseq, k1);
                            assert((zword & (1u32 << (v % 32))) == 0u32) by (bit_vector)
                                requires zword == 0u32;
                            assert(bi_word(old(self), k1) == word_at(old_kind, aseq, bseq, k1));
                            assert(bi_at(old(self), v) == false);
                        }
                    }
                    // the element face reads only the pinned storages
                    assert(self.a.storage == old(self).a.storage);
                    assert(self.b.storage == old(self).b.storage);
                }
                return None;
            }
        }
        // the walk exit: the negated guard gives a nonzero residual head
        // (direct LSB read; origin: B::count_ones(k) over the low-bit
        // prefix k, which is exactly the trailing-zero position)
        let c0: u32 = self.cleared;
        let hb: usize = self.head_block;
        let ho: usize = self.head_offset;
        let tz = self.head.trailing_zeros();
        let full: u32 = self.head;
        proof {
            let w: u32 = full;
            assert(w != 0u32);
            broadcast use vstd::std_specs::bits::axiom_u32_trailing_zeros;
            assert(u32_trailing_zeros(w) < 32u32);
            assert(tz == (u32_trailing_zeros(w) as usize));
            assert((w >> (tz as u32)) & 1u32 == 1u32);
            assert((tz as u32) < 32u32);
            assert(tz < 32usize);
            assert(full == bi_word(self, hb) & (4294967295u32 ^ c0));
            assert((full & (1u32 << (tz as u32))) != 0u32) by (bit_vector)
                requires (tz as u32) < 32u32
                    && ((full >> (tz as u32)) & 1u32) == 1u32;
        }
        // the yield face (checked pre-write, while the invariant's parking
        // faces still ride the current state): the yielded position sits
        // strictly above the last yield, and no member remains strictly
        // between the two
        let ghost L0: int = ((self.ly_plus as int) - 1int);
        let ghost wcur: u32 = bi_word(self, hb);
        proof {
            // the yielded word bit is set and clean of the parking map
            assert((wcur & (1u32 << (tz as u32))) != 0u32) by (bit_vector)
                requires full == wcur & (4294967295u32 ^ c0)
                    && (full & (1u32 << (tz as u32))) != 0u32;
            assert((c0 & (1u32 << (tz as u32))) == 0u32) by (bit_vector)
                requires full == wcur & (4294967295u32 ^ c0)
                    && (full & (1u32 << (tz as u32))) != 0u32;
            assert(L0 < (ho as int) + (tz as int)) by {
                if L0 >= (ho as int) + (tz as int) {
                    // a word bit at-or-below the logged yield sits in the
                    // parking map -- contradiction with the clean bit
                    assert(((ho as int) + (tz as int)) < (self.ly_plus as int));
                    assert((bi_word(self, self.head_block) & (1u32 << (tz as u32))) != 0u32);
                    assert((self.head_offset as int) + (tz as int)
                        < (self.ly_plus as int));
                    assert((self.cleared & (1u32 << (tz as u32))) != 0u32);
                    assert(false);
                }
            }
            // nothing sits strictly between the logged yield and this one
            assert forall|q2: usize| (self.ly_plus as int) <= (q2 as int)
                && (q2 as int) < (ho as int) + (tz as int)
                implies (bi_at(old(self), q2) == false) by {
                assert(bi_nb(old(self)) == bi_nb(self));
                assert(bi_at(old(self), q2) == ((q2 < bi_nb(self))
                    && bi_face_at(old_kind, aseq, bseq, q2)));
                if (q2 as int) < (ho as int) {
                    // the pre-head region: the invariant's face (a member
                    // below the walked offset is already logged)
                    assert(bi_at(self, q2) ==> (((q2 as int) + 1int)
                        <= (self.ly_plus as int)));
                    assert(self.ly_plus == old(self).ly_plus);
                    assert(bi_at(self, q2) == false);
                } else {
                    // inside the head block below the yielded position
                    assert(bi_at(self, q2) == ((q2 < bi_nb(self))
                        && bi_face_at(old_kind, aseq, bseq, q2)));
                    assert((ho as int) == 32 * (hb as int));
                    assert(((q2 as int) / 32) == (hb as int)) by (nonlinear_arith)
                        requires (ho as int) <= (q2 as int)
                            && (q2 as int) < (ho as int) + 32
                            && (ho as int) == 32 * (hb as int);
                    assert(q2 / 32 == hb);
                    assert(((q2 as int) - (ho as int)) < (tz as int));
                    assert((q2 % 32) < 32);
                    if (wcur & (1u32 << (q2 % 32))) != 0u32 {
                        if (c0 & (1u32 << (q2 % 32))) != 0u32 {
                            // parked: sits at-or-below the last yield
                            assert((self.cleared & (1u32 << (q2 % 32))) != 0u32);
                            assert((self.head_offset as int) + ((q2 % 32) as int)
                                < (self.ly_plus as int));
                            assert((ho as int) + ((q2 % 32) as int) == (q2 as int));
                            assert(false);
                        } else {
                            // a live word bit strictly below the yielded one
                            // contradicts the head's trailing-zero minimality
                            let j2: u32 = (q2 % 32) as u32;
                            assert((full & (1u32 << j2)) != 0u32) by (bit_vector)
                                requires full == wcur & (4294967295u32 ^ c0)
                                    && (wcur & (1u32 << j2)) != 0u32
                                    && ((c0 & (1u32 << j2)) == 0u32);
                            assert(((q2 as int) - (ho as int)) < (tz as int));
                            assert((j2 as int) == ((q2 as int) - (ho as int)));
                            assert((j2 as int) < (tz as int));
                            assert(((full >> j2) & 1u32) == 0u32);
                            assert(((full >> j2) & 1u32) == 1u32) by (bit_vector)
                                requires ((full & (1u32 << j2)) != 0u32);
                            assert(false);
                        }
                    }
                }
            }
        }
        // update block, removing the bit (origin: head & (head - one);
        // the mirror clears the trailing-zero bit directly -- the same
        // yielded LSB, recorded as a removal-face note in batch-C notes)
        self.head = full & (4294967295u32 ^ (1u32 << (tz as u32)));
        self.cleared = c0 | (1u32 << (tz as u32));
        proof {
            let wt: u32 = self.head;
            let ghost word = bi_word(self, hb);
            assert(wt == word & (4294967295u32 ^ (c0 | (1u32 << (tz as u32)))))
                by (bit_vector)
                requires wt == (full & (4294967295u32 ^ (1u32 << (tz as u32))))
                    && full == word & (4294967295u32 ^ c0);
            assert(wt == bi_word(self, hb)
                & (4294967295u32 ^ (c0 | (1u32 << (tz as u32)))));
            assert(self.kind == old_kind);
            assert(self.nb_self == old_nb_self);
            assert(self.nb_other == old_nb_other);
            assert(self.a.storage == old_st_a);
            assert(self.b.storage == old_st_b);
            assert(self.a.storage@ == aseq);
            assert(self.b.storage@ == bseq);
            assert(bi_word(self, hb) == word_at(old_kind, aseq, bseq, hb));
        }
        let v = ho + tz as usize;
        proof {
            let ghost bitm: u32 = 1u32 << (tz as u32);
            let ghost k: usize = (v / 32) as usize;
            assert(ho == hb * 32);
            assert((v as int) == (hb as int) * 32 + (tz as int));
            assert((v as int) / 32 == (hb as int) && (v as int) % 32 == (tz as int))
                by (nonlinear_arith)
                requires 0 <= (tz as int) && (tz as int) < 32
                    && (v as int) == (hb as int) * 32 + (tz as int);
            assert(k == hb);
            assert((v % 32) == tz as usize);
            assert(1u32 << (v % 32) == bitm);
            // word congruence: kind and both storages never move
            assert(old(self).a.storage == old_st_a);
            assert(old(self).b.storage == old_st_b);
            assert(old(self).kind == old_kind);
            assert(old(self).nb_self == old_nb_self);
            assert(old(self).nb_other == old_nb_other);
            assert(old(self).a.storage@ == aseq);
            assert(old(self).b.storage@ == bseq);
            assert(bi_word(old(self), k) == bi_word(self, hb)) by {
                assert(k == hb);
                assert(side_word(&old(self).a, k) == side_word(&self.a, hb));
                assert(side_word(&old(self).b, k) == side_word(&self.b, hb));
            }
            // the bit face: the yielded bit is live in the merged word
            let ghost word = bi_word(old(self), k);
            assert(bi_word(self, hb) == word);
            assert(full == word & (4294967295u32 ^ c0));
            assert((full & bitm) != 0u32);
            assert((word & bitm) != 0u32) by (bit_vector)
                requires full == word & (4294967295u32 ^ c0) && (full & bitm) != 0u32;
            let ghost sa = side_word(&self.a, hb);
            let ghost sb = side_word(&self.b, hb);
            assert(word == kind_merged(old_kind, sa, sb));
            assert((sa & bitm) != 0u32 || (sb & bitm) != 0u32) by {
                if old_kind == 1u8 {
                    assert(word == sa & sb);
                    assert((sa & sb & bitm) != 0u32) by (bit_vector)
                        requires (word & bitm) != 0u32 && word == sa & sb;
                    assert((sa & bitm) != 0u32 && (sb & bitm) != 0u32)
                        by (bit_vector)
                        requires (sa & sb & bitm) != 0u32;
                } else if old_kind == 2u8 {
                    assert(word == sa & (4294967295u32 ^ sb));
                    assert((sa & bitm) != 0u32) by (bit_vector)
                        requires (word & bitm) != 0u32
                            && word == sa & (4294967295u32 ^ sb);
                } else if old_kind == 0u8 {
                    assert(word == sa | sb);
                    assert((sa & bitm) != 0u32 || (sb & bitm) != 0u32)
                        by (bit_vector)
                        requires (word & bitm) != 0u32 && word == sa | sb;
                } else if old_kind == 3u8 {
                    assert(word == sa ^ sb);
                    assert((sa & bitm) != 0u32 || (sb & bitm) != 0u32)
                        by (bit_vector)
                        requires (word & bitm) != 0u32 && word == sa ^ sb;
                } else {
                    assert(word == sa);
                    assert((sa & bitm) != 0u32) by (bit_vector)
                        requires (word & bitm) != 0u32 && word == sa;
                }
            }
            // the width face: the live bit sits below the stream widths
            if old_kind == 4u8 {
                assert(bi_nb(old(self)) == old_nb_self);
                assert(sa == side_word_seq(aseq, hb));
                assert(word == sa);
                assert((sa & bitm) != 0u32 && sa != 0u32) by (bit_vector)
                    requires (word & bitm) != 0u32 && word == sa;
                assert((hb as int) < aseq.len()) by {
                    if !((hb as int) < aseq.len()) {
                        assert(sa == 0u32);
                        assert(false);
                    }
                }
                assert(aseq[(hb as int)] == sa);
                assert((aseq[(hb as int)] & (1u32 << (tz as u32))) != 0u32);
                assert(aseq.len() == (blocks_for_bits(old_nb_self) as int)) by {
                    assert((self.a.end as int) == blocks_for_bits(self.nb_self));
                    assert(self.a.end == self.a.storage@.len());
                }
                lemma_stream_bit_below(aseq, old_nb_self, hb, tz as u32);
                assert((v as int) < old_nb_self);
                assert((v as int) < (bi_nb(old(self)) as int));
            } else if old_kind == 1u8 {
                assert(((bi_nb(old(self))) as int)
                    == (if old_nb_self < old_nb_other {
                        old_nb_self as int
                    } else {
                        old_nb_other as int
                    }));
                assert(((sa & sb) & bitm) != 0u32) by (bit_vector)
                    requires word == sa & sb && (word & bitm) != 0u32;
                assert((sa & bitm) != 0u32 && (sb & bitm) != 0u32
                    && sa != 0u32 && sb != 0u32) by (bit_vector)
                    requires ((sa & sb) & bitm) != 0u32;
                assert(sa == side_word_seq(aseq, hb));
                assert(sb == side_word_seq(bseq, hb));
                assert((hb as int) < aseq.len()) by {
                    if !((hb as int) < aseq.len()) {
                        assert(sa == 0u32);
                        assert((sa & (1u32 << (tz as u32))) == 0u32) by (bit_vector)
                            requires sa == 0u32 && (tz as u32) < 32u32;
                        assert(false);
                    }
                }
                assert((hb as int) < bseq.len()) by {
                    if !((hb as int) < bseq.len()) {
                        assert(sb == 0u32);
                        assert((sb & (1u32 << (tz as u32))) == 0u32) by (bit_vector)
                            requires sb == 0u32 && (tz as u32) < 32u32;
                        assert(false);
                    }
                }
                assert((aseq[(hb as int)] & (1u32 << (tz as u32))) != 0u32);
                assert((bseq[(hb as int)] & (1u32 << (tz as u32))) != 0u32);
                assert(aseq.len() == (blocks_for_bits(old_nb_self) as int));
                assert(bseq.len() == (blocks_for_bits(old_nb_other) as int));
                lemma_stream_bit_below(aseq, old_nb_self, hb, tz as u32);
                lemma_stream_bit_below(bseq, old_nb_other, hb, tz as u32);
                assert((v as int) < old_nb_self);
                assert((v as int) < old_nb_other);
                assert((v as int) < (bi_nb(old(self)) as int));
            } else {
                assert((bi_nb(old(self)) as int)
                    == (if old_nb_self < old_nb_other {
                        old_nb_other as int
                    } else {
                        old_nb_self as int
                    }));
                assert(sb == side_word_seq(bseq, hb));
                if (sa & bitm) != 0u32 {
                    assert(sa != 0u32) by (bit_vector)
                        requires (sa & bitm) != 0u32;
                    assert((hb as int) < aseq.len()) by {
                        if !((hb as int) < aseq.len()) {
                            assert(sa == 0u32);
                            assert((sa & (1u32 << (tz as u32))) == 0u32) by (bit_vector)
                                requires sa == 0u32 && (tz as u32) < 32u32;
                            assert(false);
                        }
                    }
                    assert((aseq[(hb as int)] & (1u32 << (tz as u32))) != 0u32);
                    assert(aseq.len() == (blocks_for_bits(old_nb_self) as int));
                    lemma_stream_bit_below(aseq, old_nb_self, hb, tz as u32);
                    assert((v as int) < old_nb_self);
                } else {
                    assert(sb != 0u32) by (bit_vector)
                        requires (sb & bitm) != 0u32;
                    assert((hb as int) < bseq.len()) by {
                        if !((hb as int) < bseq.len()) {
                            assert(sb == 0u32);
                            assert((sb & (1u32 << (tz as u32))) == 0u32) by (bit_vector)
                                requires sb == 0u32 && (tz as u32) < 32u32;
                            assert(false);
                        }
                    }
                    assert((bseq[(hb as int)] & (1u32 << (tz as u32))) != 0u32);
                    assert(bseq.len() == (blocks_for_bits(old_nb_other) as int));
                    lemma_stream_bit_below(bseq, old_nb_other, hb, tz as u32);
                    assert((v as int) < old_nb_other);
                }
                assert((v as int) < (bi_nb(old(self)) as int));
            }
            // the element face itself
            assert(v < (bi_nb(old(self)) as usize));
            assert((bi_word(old(self), k) & (1u32 << (v % 32))) != 0u32);
            assert(bi_at(old(self), v));
        }
        // the last-yield log rides the fresh yield; the post-yield parking
        // map faces follow (the parked bits all sit at-or-below the fresh
        // yield, and every word bit at-or-below it is parked)
        proof {
            self.ly_plus = ((v + 1) as usize);
        }
        proof {
            assert(self.ly_plus == (v + 1usize));
            assert((self.head_offset as int) == (ho as int));
            assert((self.ly_plus as int) == ((ho as int) + (tz as int) + 1int));
            assert((v as int) == (ho as int) + (tz as int));
            let ghost wpost: u32 = bi_word(self, self.head_block);
            assert(wpost == wcur);
            assert forall|j2: u32| (j2 as int) < 32int
                implies (((self.cleared & (1u32 << j2)) != 0u32)
                    ==> ((self.head_offset as int) + (j2 as int)
                        < (self.ly_plus as int))) by {
                let cz2: u32 = self.cleared;
                assert(cz2 == (c0 | (1u32 << (tz as u32))));
                if ((cz2 & (1u32 << j2)) != 0u32) {
                    if (c0 & (1u32 << j2)) != 0u32 {
                        // an old parked bit: the pre-state parking map bounds
                        // it strictly below the fresh yield
                        assert((self.head_offset as int) + (j2 as int) <= L0);
                    } else {
                        // only the fresh yield's own bit can carry the position
                        assert(j2 == (tz as u32)) by (bit_vector)
                            requires (((c0 | (1u32 << (tz as u32))) & (1u32 << j2)) != 0u32)
                                && ((c0 & (1u32 << j2)) == 0u32)
                                && ((tz as u32) < 32u32)
                                && ((j2 as int) < 32int);
                        assert((self.head_offset as int) + (j2 as int)
                            == ((self.ly_plus as int) - 1int));
                    }
                }
            }
            assert forall|j2: u32| (j2 as int) < 32int
                implies ((((bi_word(self, self.head_block) & (1u32 << j2)) != 0u32)
                    && ((self.head_offset as int) + (j2 as int)
                        < (self.ly_plus as int)))
                    ==> ((self.cleared & (1u32 << j2)) != 0u32)) by {
                let cz3: u32 = self.cleared;
                assert(cz3 == (c0 | (1u32 << (tz as u32))));
                if (((bi_word(self, self.head_block) & (1u32 << j2)) != 0u32)
                    && ((self.head_offset as int) + (j2 as int)
                        < (self.ly_plus as int))) {
                    if (c0 & (1u32 << j2)) != 0u32 {
                        assert((cz3 & (1u32 << j2)) != 0u32) by (bit_vector)
                            requires (c0 & (1u32 << j2)) != 0u32
                                && cz3 == (c0 | (1u32 << (tz as u32)))
                                && (j2 as u32) < 32u32;
                    } else if j2 == (tz as u32) {
                        assert((cz3 & (1u32 << j2)) != 0u32) by (bit_vector)
                            requires cz3 == (c0 | (1u32 << j2))
                                && (j2 as u32) < 32u32;
                    } else {
                        // a live word bit strictly below the fresh yield would
                        // have sat in the head, contradicting its
                        // trailing-zero minimality at the walk exit
                        assert((j2 as int) < (tz as int));
                        let bmj: u32 = 1u32 << j2;
                        assert((wpost & bmj) != 0u32);
                        assert((wcur & bmj) != 0u32);
                        assert((c0 & bmj) == 0u32);
                        lemma_andnot_bit_live(wcur, c0, bmj);
                        assert((full & bmj) != 0u32);
                        assert(u32_trailing_zeros(full) == (tz as u32));
                        assert(((full >> j2) & 1u32) == 0u32);
                        lemma_shift_bit_live(full, j2);
                        assert(false);
                    }
                }
            }
        }
        Some(v)
    }
}

// ===========================================================================
// the exhaustion machinery (batch C extension): the value-level parking
// face of one exhausted head block
// ===========================================================================

/// a live bit survives the and-not mask: w's bit is live in w & ~c.
pub proof fn lemma_andnot_bit_live(w: u32, c: u32, m: u32)
    requires
        (w & m) != 0u32,
        (c & m) == 0u32,
    ensures
        ((w & (4294967295u32 ^ c)) & m) != 0u32,
{
    assert(((w & (4294967295u32 ^ c)) & m) != 0u32) by (bit_vector)
        requires (w & m) != 0u32 && (c & m) == 0u32;
}

/// the set bit of a word reads as the 1 at its shift position.
pub proof fn lemma_shift_bit_live(w: u32, j: u32)
    requires
        (w & (1u32 << j)) != 0u32,
        j < 32u32,
    ensures
        ((w >> j) & 1u32) == 1u32,
{
    assert(((w >> j) & 1u32) == 1u32) by (bit_vector)
        requires (w & (1u32 << j)) != 0u32 && j < 32u32;
}

/// an exhausted word (masked to zero) has every set bit parked: the
/// value-level half of the exhaustion face of one head block.
pub proof fn lemma_ex_word_parked(w: u32, c: u32)
    requires
        w & (4294967295u32 ^ c) == 0u32,
    ensures
        forall|j: u32| (j as int) < 32int
            ==> ((#[trigger] (w & (1u32 << j)) != 0u32) ==> (c & (1u32 << j)) != 0u32),
{
    assert forall|j: u32| (j as int) < 32int
        ==> ((w & (1u32 << j)) != 0u32 ==> (c & (1u32 << j)) != 0u32) by {
        if (w & (1u32 << j)) != 0u32 {
            assert((c & (1u32 << j)) != 0u32) by (bit_vector)
                requires (w & (4294967295u32 ^ c)) == 0u32
                    && (w & (1u32 << j)) != 0u32;
        }
    }
}

} // verus!
