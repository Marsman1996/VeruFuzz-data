//! harness: inline-UT witnesses for src/ascii_set.rs
//! Mirrors the 4 inline `#[test]`s of upstream ascii_set.rs:172-213 (U15-U18).
//! Reference-style organization: `#[path]` includes verified/src/lib.rs (which contains the ascii_set module),
//! without copying its spec; the verification fact source stays single in src (the membership-face
//! theorems of add/remove/union/complement are all verified in the module-level lemma_*_membership of src).
//! The trait shells of ops::Add / ops::Not (ascii_set.rs:86-100) are each a 1-line delegation
//! (union/complement); verus does not verify std trait impls directly -- the delegated exec
//! semantics is witnessed here via the contract face of union/complement (ascii_set.rs ledger item 3).
//! UT assertion shapes: add_op/union use assert_eq! (structural equality -> element-wise
//! mask exec asserts, converted via the array_view bridge lemmas); not_op/complement use contains
//! asserts (point-wise instantiation of k values; the EMPTY membership face goes through src's lemma_empty_members).
fn main() {}

#[path = "../src/lib.rs"]
mod percent_encoding;

use percent_encoding::*;

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

broadcast use vstd::seq::group_seq_lemmas;

/* ============================================================
 * Value-face lemmas (0x41=65 -> chunk2 bit 1; 0x42=66 -> chunk2 bit 2)
 * ============================================================ */

/* ---------- U15 add_op (ascii_set.rs:176-182) ----------
 * assert_eq!(left + right, expected): `+` is a 1-line delegation to union. */
exec fn ut_add_op()
{
    let left = AsciiSet::EMPTY.add(0x41);
    let right = AsciiSet::EMPTY.add(0x42);
    let expected = AsciiSet::EMPTY.add(0x41).add(0x42);
    /* Origin Rust: let u = left + right; (== left.union(right)) */
    let u = left.union(right);
    proof {
        assert(AsciiSet::EMPTY.mask@ == seq![0u32, 0u32, 0u32, 0u32]);
        reveal(add_bit_spec);
        lemma_val_left(left.mask@);
        lemma_val_right(right.mask@);
        lemma_val_expected(expected.mask@);
        lemma_val_union(u.mask@, left.mask@, right.mask@);
        // array_view bridge: exec array element <-> Seq index
        assert(u.mask@.index(0) == u.mask[0]);
        assert(expected.mask@.index(0) == expected.mask[0]);
    }
    // Structural semantics of assert_eq!(left + right, expected): mask equal element-wise
    assert(u.mask[0] == expected.mask[0]);
    assert(u.mask[1] == expected.mask[1]);
    assert(u.mask[2] == expected.mask[2]);
    assert(u.mask[3] == expected.mask[3]);
    // Value-face records (0x41/0x42 both in chunk2; the three chunk2 values are 2/4/6)
    assert(expected.mask[2] == 6u32);
}

/* ---------- U16 not_op (ascii_set.rs:184-190) ----------
 * let not_set = !set: `!` is a 1-line delegation to complement;
 * asserting the membership duality of set and its negation. */
exec fn ut_not_op()
{
    let set = AsciiSet::EMPTY.add(0x41).add(0x42);
    /* Origin Rust: let not_set = !set; (== set.complement()) */
    let not_set = set.complement();
    let c1 = not_set.contains(0x41);
    let c2 = set.contains(0x41);
    let c3 = set.contains(0x43);
    let c4 = not_set.contains(0x43);
    proof {
        assert(AsciiSet::EMPTY.mask@ == seq![0u32, 0u32, 0u32, 0u32]);
        lemma_empty_members(AsciiSet::EMPTY.mask@);
        reveal(bit_at);
    }
    assert(c2);
    assert(!c3);
    assert(!c1);
    assert(c4);
}

/* ---------- U17 union (ascii_set.rs:194-201) ----------
 * Const-context usability is the upstream test intent; the mirror uses a same-semantics exec chain (ledger item 4). */
exec fn ut_union()
{
    let a = AsciiSet::EMPTY.add(0x41);
    let b = AsciiSet::EMPTY.add(0x42);
    let union_ab = a.union(b);
    let expected = AsciiSet::EMPTY.add(0x41).add(0x42);
    proof {
        assert(AsciiSet::EMPTY.mask@ == seq![0u32, 0u32, 0u32, 0u32]);
        reveal(add_bit_spec);
        lemma_val_left(a.mask@);
        lemma_val_right(b.mask@);
        lemma_val_expected(expected.mask@);
        lemma_val_union(union_ab.mask@, a.mask@, b.mask@);
        assert(union_ab.mask@.index(0) == union_ab.mask[0]);
        assert(expected.mask@.index(0) == expected.mask[0]);
    }
    assert(union_ab.mask[0] == expected.mask[0]);
    assert(union_ab.mask[1] == expected.mask[1]);
    assert(union_ab.mask[2] == expected.mask[2]);
    assert(union_ab.mask[3] == expected.mask[3]);
    assert(expected.mask[2] == 6u32);
}

/* ---------- U18 complement (ascii_set.rs:204-212) ----------
 * const BOTH = EMPTY.add(A).add(B); COMPLEMENT = BOTH.complement();
 * asserts !contains(A), !contains(B), contains(C) */
exec fn ut_complement()
{
    let both = AsciiSet::EMPTY.add(0x41).add(0x42);
    let comp = both.complement();
    let c1 = comp.contains(0x41);
    let c2 = comp.contains(0x42);
    let c3 = comp.contains(0x43);
    let s1 = both.contains(0x41);
    let s2 = both.contains(0x42);
    let s3 = both.contains(0x43);
    proof {
        assert(AsciiSet::EMPTY.mask@ == seq![0u32, 0u32, 0u32, 0u32]);
        lemma_empty_members(AsciiSet::EMPTY.mask@);
        reveal(bit_at);
    }
    assert(s1);
    assert(s2);
    assert(!s3);
    assert(!c1);
    assert(!c2);
    assert(c3);
}


// =========================================================================
// Proof lemmas -- the standalone value-face proof fns live at the end of
// the file so the UT witnesses read directly; the proof {} blocks inside
// the exec witnesses stay in place.
// measured: all five verification panels identical before and after the move.
proof fn lemma_val_left(l: Seq<u32>)
    requires
        l == add_bit_spec(seq![0u32, 0u32, 0u32, 0u32], 0x41),
    ensures
        l[0] == 0u32,
        l[1] == 0u32,
        l[2] == (1u32 << 1),
        l[3] == 0u32,
{
    reveal(add_bit_spec);
    assert((0x41 as int) / 32 == 2);
    assert((0x41 as int) % 32 == 1);
    assert((seq![0u32, 0u32, 0u32, 0u32])[2] == 0u32);
    assert(l[2] == (0u32 | (1u32 << 1)));
    assert((0u32 | (1u32 << 1)) == (1u32 << 1)) by (bit_vector)
        requires
            1 < 32u32,
    ;
}


proof fn lemma_val_right(r: Seq<u32>)
    requires
        r == add_bit_spec(seq![0u32, 0u32, 0u32, 0u32], 0x42),
    ensures
        r[0] == 0u32,
        r[1] == 0u32,
        r[2] == (1u32 << 2),
        r[3] == 0u32,
{
    reveal(add_bit_spec);
    assert((0x42 as int) / 32 == 2);
    assert((0x42 as int) % 32 == 2);
    assert((seq![0u32, 0u32, 0u32, 0u32])[2] == 0u32);
    assert(r[2] == (0u32 | (1u32 << 2)));
    assert((0u32 | (1u32 << 2)) == (1u32 << 2)) by (bit_vector)
        requires
            2 < 32u32,
    ;
}


proof fn lemma_val_expected(e: Seq<u32>)
    requires
        e == add_bit_spec(add_bit_spec(seq![0u32, 0u32, 0u32, 0u32], 0x41), 0x42),
    ensures
        e[0] == 0u32,
        e[1] == 0u32,
        e[2] == 6u32,
        e[3] == 0u32,
{
    reveal(add_bit_spec);
    assert((0x41 as int) / 32 == 2);
    assert((0x41 as int) % 32 == 1);
    assert((0x42 as int) / 32 == 2);
    assert((0x42 as int) % 32 == 2);
    assert((seq![0u32, 0u32, 0u32, 0u32])[2] == 0u32);
    let inner = add_bit_spec(seq![0u32, 0u32, 0u32, 0u32], 0x41);
    assert(inner[2] == (0u32 | (1u32 << 1)));
    assert((0u32 | (1u32 << 1)) == (1u32 << 1)) by (bit_vector)
        requires
            1 < 32u32,
    ;
    assert(inner[2] == (1u32 << 1));
    assert(e[2] == ((1u32 << 1) | (1u32 << 2)));
    assert(((1u32 << 1) | (1u32 << 2)) == 6u32) by (bit_vector)
        requires
            1 < 32u32,
            2 < 32u32,
    ;
}


proof fn lemma_val_union(u: Seq<u32>, l: Seq<u32>, r: Seq<u32>)
    requires
        forall|j: int| #![trigger u[j]] 0 <= j < 4 ==> u[j] == (l[j] | r[j]),
        l[0] == 0u32,
        r[0] == 0u32,
        l[1] == 0u32,
        r[1] == 0u32,
        l[2] == (1u32 << 1),
        r[2] == (1u32 << 2),
        l[3] == 0u32,
        r[3] == 0u32,
    ensures
        u[0] == 0u32,
        u[1] == 0u32,
        u[2] == 6u32,
        u[3] == 0u32,
{
    assert(u[0] == (l[0] | r[0]));
    assert(u[1] == (l[1] | r[1]));
    assert((0u32 | 0u32) == 0u32) by (bit_vector);
    assert(u[2] == (l[2] | r[2]));
    assert(u[3] == (l[3] | r[3]));
    assert(((1u32 << 1) | (1u32 << 2)) == 6u32) by (bit_vector)
        requires
            1 < 32u32,
            2 < 32u32,
    ;
}


}
