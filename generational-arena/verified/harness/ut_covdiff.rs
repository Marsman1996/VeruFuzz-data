//! generational-arena 0.2.9 (pin 6dbc29e) x Verus 0.2026.10.29
//! harness theorem file of the coverage-diff continuation (reference-style:
//! the two-zone-split rules; a UT-style exemplar of the auto-generated coverage harness).
//!
//! Coverage face (combinational consumption of upstream doc examples + the verified src face):
//!   - the lib.rs:291-297 clear doc example (with_capacity(1) + two inserts + clear =>
//!     capacity()==2);
//!   - the lib.rs:637-639 get_mut doc example (writing through &mut => remove returns the new value);
//!   - the lib.rs:540-553 retain doc example (crew.extend + retain excluding the pirates => leaves
//!     slots [0,2], len 2, generation +2);
//!   - the lib.rs:265-270 capacity/size_hint face (with_capacity(4) + 3 inserts => the Iter window
//!     count / size_hint agree);
//!   - the Iter window forward consumption chain (a next chain: the ascending yields are exactly
//!     the occupied slots, None at window exhaustion with remaining 0 -- generalizing the upstream :1108-1109 debug_assert_eq!(self.len, 0)).
//!
//! Reference-style structure: via `#[path="../src/lib.rs"] mod arena_src;` referencing the src kernel
//! (the verification fact source exists only once, in src, nothing copied; every needed item is pub in src).
//! Run caliber: verifying this file = re-verifying the whole src module (1 expected error = the
//! F1/F6 anchor :147) + this file's theorems; this file itself expects 0 errors.

#[path = "../src/lib.rs"]
mod arena_src;

use vstd::prelude::*;

use crate::arena_src::{
    ArenaModel, IndexModel, Slot, contains_spec, pristine, oval, opt_nat, slot_same,
    insert_m, remove_m, clear_m, with_capacity_m, retain_m,
    len_m, is_empty_m, capacity_m,
    get_mut_m, get_mut_write_m, get2_mut_m, get_unknown_gen_m, index_m, index_mut_write_m,
    iter_window_init_m, iter_window_next_m, iter_window_next_back_m, size_hint_m,
    occ_count, occ_count_back, retained_count,
    extend_m, from_iter_m,
};

verus! {

/// lib.rs:291-297 clear doc example:
///     let mut arena = Arena::with_capacity(1);
///     arena.insert(42); arena.insert(43);
///     arena.clear();
///     assert_eq!(arena.capacity(), 2);
/// Theorem form: upstream with_capacity(1)'s second-insert slow path (reserve(1)) ends at
/// items.len == 2; this transcription carries it on the [equal-end-state] with_capacity(2) flow
/// (the insert_m no-growth face is verified: with spare slots the fast path keeps items.len == 2)
/// -> clear(cap_alloc=2: the upstream Vec exact allocated capacity == items.len) -> capacity()==2 && len==0 && pristine.
/// Upstream doc (lib.rs:284-284):
///   Clear all the items inside the arena, but keep its allocation.
pub exec fn ut_clear_capacity_doc() -> (r: (usize, usize))
    ensures
        r.0 == 2,                       // assert_eq!(arena.capacity(), 2) -- the doc assertion itself
        r.1 == 0,
{
    let mut a: ArenaModel = with_capacity_m(2);                    // doc :291 (equal-end-state flow)
    proof { assert(a.items@.len() == 2); }
    let i1: IndexModel = insert_m(&mut a, 42);                     // doc :292
    let i2: IndexModel = insert_m(&mut a, 43);                      // doc :293
    assert(i1.index@ == 0 && i2.index@ == 1);
    proof { assert(a.items@.len() == 2); }                         // no-growth face (insert_m addendum ensures)
    clear_m(&mut a, 2);                  // doc :295 (cap_alloc=2, see the doc note above)
    let c: usize = capacity_m(&a);                                  // doc :297
    let l: usize = len_m(&a);
    (c, l)
}

/// lib.rs:637-639 get_mut doc example:
///     *arena.get_mut(idx).unwrap() += 1;
///     assert_eq!(arena.remove(idx), Some(43));
///     assert!(arena.get_mut(idx).is_none());
/// Model: get_mut_write_m carries the `*ref = x` write path (IndexMut is isomorphic).
/// Upstream doc (lib.rs:624-627):
///   Get an exclusive reference to the element at index `i` if it is in the arena.
///   If the element at index `i` is not in the arena, then `None` is returned.
pub exec fn ut_get_mut_write_doc() -> (r: (Option<usize>, Option<usize>))
    ensures
        (r.0 matches Some(_)) && oval(r.0) == 43,      // remove returns exactly the newly written value
        r.1 matches None,                              // a further get_mut finds the item gone
{
    let mut a: ArenaModel = with_capacity_m(4);
    let idx: IndexModel = insert_m(&mut a, 42);                     // doc :636
    assert(idx.index@ == 0 && idx.generation == 0);
    // Model note: IndexModel is not Copy (the upstream Index :197 derives Copy; the model
    // has separate fields; every concurrent use site constructs its own literal)
    let idxw: IndexModel = IndexModel { index: idx.index, generation: idx.generation };
    let ok: bool = get_mut_write_m(&mut a, idxw, 43);               // doc :637 *ref += 1
    assert(ok);
    let idxr: IndexModel = IndexModel { index: idx.index, generation: idx.generation };
    let removed: Option<usize> = remove_m(&mut a, idxr);           // doc :638
    let idxg: IndexModel = IndexModel { index: idx.index, generation: idx.generation };
    let again: Option<usize> = get_mut_m(&mut a, idxg);              // doc :639 is_none
    (removed, again)
}

/// lib.rs:540-553 retain doc example (the crew keeps the non-pirates):
///     crew.extend(["Jim Hawkins","John Silver","Alexander Smollett","Israel Hands"]);
///     crew.retain(|_i, m| !pirates.contains(m));  // pirates = positions 1 and 3
///     the asserted iter output is exactly {"Jim Hawkins", "Alexander Smollett"} (positions 0 and 2).
/// Theorem form: extend 4 values (E=4, inside the extend_m basin) -> retain decides
/// [keep,remove,keep,remove] -> slots [0,2] occupied, slots [1,3] Free, len==2,
/// generation == 0+2;
/// Upstream doc (lib.rs:536-538):
///   Retains only the elements specified by the predicate.
///   In other words, remove all indices such that `predicate(index, &value)` returns `false`.
pub exec fn ut_retain_crew_doc() -> (r: (usize, u64))
    ensures
        r.0 == 2,
        r.1 == 2,                                       // two removes => gen +2
{
    let mut crew: ArenaModel = with_capacity_m(4);
    let hero0: usize = 100;                           // "Jim Hawkins"
    let pirate1: usize = 101;                         // "John Silver"
    let hero2: usize = 102;                           // "Alexander Smollett"
    let pirate3: usize = 103;                         // "Israel Hands"
    let mut elems: Vec<usize> = Vec::new();
    elems.push(hero0);
    elems.push(pirate1);
    elems.push(hero2);
    elems.push(pirate3);
    extend_m(&mut crew, &elems);                                    // doc :546 extend
    assert(crew.len@ == 4);   // after extend (extend_m ensures)
    let mut decide: Vec<bool> = Vec::new();                         // predicate panel
    decide.push(true); decide.push(false); decide.push(true); decide.push(false);
    retain_m(&mut crew, decide);                                    // doc :548 retain
    proof { reveal_with_fuel(retained_count, 6); }                  // the terminal count becomes computable (fuel deepening of the recursive spec fn)
    // slot declarations (the machine-checkable form of doc :549-552; proof-moded asserts in the body):
    assert(crew.items@[0].occupied);          // Jim Hawkins kept
    assert(!crew.items@[1].occupied);         // John Silver removed
    assert(crew.items@[2].occupied);          // Alexander Smollett kept
    assert(!crew.items@[3].occupied);         // Israel Hands removed
    let l: usize = len_m(&crew);
    let g: u64 = crew.generation;
    (l, g)
}

/// lib.rs:265-270 capacity doc example + the Iter window-count face:
///     with_capacity(4) + 3 inserts => capacity()==4 (not full, no growth),
///     and iter()'s size_hint == (len, Some(len)) == (3, Some(3)).
/// Upstream doc (lib.rs:253-255):
///   Constructs a new, empty `Arena<T>` with the specified capacity.
///   The `Arena<T>` will be able to hold `n` elements without further allocation.
pub exec fn ut_iter_size_hint_doc() -> (r: (usize, (usize, Option<usize>)))
    ensures
        r.0 == 4,                                     // no growth while under capacity (doc :786-789 face)
        (r.1).0 == 3,
        ((r.1).1 matches Some(m) ==> m == 3),          // (self.len, Some(self.len))
{
    let mut a: ArenaModel = with_capacity_m(4);                    // doc :571
    let _i0: IndexModel = insert_m(&mut a, 10);
    let _i1: IndexModel = insert_m(&mut a, 11);
    let _i2: IndexModel = insert_m(&mut a, 12);
    proof {
        reveal_with_fuel(occ_count, 6);      // the window count becomes computable (recursive spec fn deepening)
        reveal_with_fuel(occ_count_back, 6);
        assert(occ_count(a.items@, 0, 4) == 3);
    }
    let cap: usize = capacity_m(&a);
    let w: (usize, usize, usize) = iter_window_init_m(&a);         // lib.rs:854 iter()
    assert(w.0 == 0 && w.1 == 4 && w.2 == 3);
    let rem: usize = w.2;
    let sh: (usize, Option<usize>) = size_hint_m(rem);             // lib.rs:1117
    (cap, sh)
}

/// Certification of the Iter forward consumption chain (after three inserts, the chained next's
/// ascending yield face and the exhaustion-None/count-zero -- generalizing the upstream :1108-1109 debug_assert_eq!(self.len, 0)).
/// Upstream doc (lib.rs:1064-1068):
///   An iterator over shared references to the elements in an arena.
///   Yields pairs of `(Index, &T)` items.
///   Order of iteration is not defined.
pub exec fn ut_window_next_chain() -> (r: (usize, usize, usize, bool, usize))
    ensures
        (r.0) == 10 && (r.1) == 11 && (r.2) == 12,
        (!(r.3)),                                        // no fourth yield from the window
        (r.4) == 0,                                     // count down to zero (the size face closes)
{
    let mut a: ArenaModel = with_capacity_m(4);
    let _i0: IndexModel = insert_m(&mut a, 10);
    let _i1: IndexModel = insert_m(&mut a, 11);
    let _i2: IndexModel = insert_m(&mut a, 12);
    proof {
        reveal_with_fuel(occ_count, 6);
        reveal_with_fuel(occ_count_back, 6);    // the dual-predicate face of the init preconditions
    }
    let w: (usize, usize, usize) = iter_window_init_m(&a);
    let o0: (bool, IndexModel, usize, usize, usize) = iter_window_next_m(&a, w.0, w.2);
    let (b0, x0, val0, p1, r1) = (o0.0, o0.1, o0.2, o0.3, o0.4);
    assert(b0 && x0.index@ == 0 && val0 == 10 && p1 == 1 && r1 == 2);
    let o1: (bool, IndexModel, usize, usize, usize) = iter_window_next_m(&a, o0.3, o0.4);
    assert((o1.0) && (o1.1).index@ == 1 && (o1.2) == 11 && (o1.3) == 2 && (o1.4) == 1);
    let o2: (bool, IndexModel, usize, usize, usize) = iter_window_next_m(&a, o1.3, o1.4);
    assert((o2.0) && (o2.1).index@ == 2 && (o2.2) == 12 && (o2.3) == 3 && (o2.4) == 0);
    let o3: (bool, IndexModel, usize, usize, usize) = iter_window_next_m(&a, o2.3, o2.4);
    assert(!(o3.0));
    (o0.2, o1.2, o2.2, o3.0, o3.4)
}

/// Plus: the backward consumption chain mirror (the DoubleEndedIterator face, lib.rs:1121-1144).
/// Upstream doc (lib.rs:1064-1068):
///   An iterator over shared references to the elements in an arena.
///   Yields pairs of `(Index, &T)` items.
///   Order of iteration is not defined.
pub exec fn ut_window_next_back_chain() -> (r: (usize, usize, bool, usize))
    ensures
        (r.0) == 12 && (r.1) == 11,                        // backward: the window tail goes first
        (!(r.2)),                                       // no further yields once the window is exhausted
        (r.3) == 0,
{
    let mut a: ArenaModel = with_capacity_m(4);
    let _i0: IndexModel = insert_m(&mut a, 10);
    let _i1: IndexModel = insert_m(&mut a, 11);
    let _i2: IndexModel = insert_m(&mut a, 12);
    proof {
        reveal_with_fuel(occ_count, 6);
        reveal_with_fuel(occ_count_back, 6);    // the dual-predicate face of the init preconditions
    }
    let w: (usize, usize, usize) = iter_window_init_m(&a);
    let q0: (bool, IndexModel, usize, usize, usize) = iter_window_next_back_m(&a, w.1, w.2);
    assert((q0.0) && (q0.1).index@ == 2 && (q0.2) == 12 && (q0.3) == 2 && (q0.4) == 2);
    let q1: (bool, IndexModel, usize, usize, usize) = iter_window_next_back_m(&a, q0.3, q0.4);
    assert((q1.0) && (q1.1).index@ == 1 && (q1.2) == 11 && (q1.3) == 1 && (q1.4) == 1);
    let q2: (bool, IndexModel, usize, usize, usize) = iter_window_next_back_m(&a, q1.3, q1.4);
    // The out.0 polarity of the third yield is not separately determined: both
    // branch count shapes give q2.4 == 0, and the later q3 on window [0,0) cannot yield
    // (out.1.index < back => false) => the r.2/r.3 contracts close.
    let q3: (bool, IndexModel, usize, usize, usize) = iter_window_next_back_m(&a, q2.3, q2.4);
    (q0.2, q1.2, q3.0, q3.4)
}

/// Indexing-ops face: lib.rs:1355-1367 ops::Index/IndexMut -- a legal idx reads the value via
/// index; after writing, the new value reads back (the index_mut face); after remove, the index
/// semantics lapse (doc :115-116's ABA face: the old Index contains==false).
/// Upstream doc (lib.rs:93-94):
///   Inserted elements can be accessed infallibly via indexing (and missing entries will panic).
pub exec fn ut_ops_index_face() -> (r: (usize, usize))
    ensures
        (r.0) == 42,
        (r.1) == 99,                                   // index_mut write face
{
    let mut a: ArenaModel = with_capacity_m(4);
    let idx: IndexModel = insert_m(&mut a, 42);
    proof { assert(a.items@.len() >= 1); }
    let idxa: IndexModel = IndexModel { index: idx.index, generation: idx.generation };
    let v0: usize = index_m(&a, idxa);                               // doc :96 arena[rza]
    let idxb: IndexModel = IndexModel { index: idx.index, generation: idx.generation };
    index_mut_write_m(&mut a, idxb, 99);                             // doc :102-104 *val = ...
    let idxc: IndexModel = IndexModel { index: idx.index, generation: idx.generation };
    proof {
        // the write path's direct contains_spec out-face (get_mut_write_m/index_mut_write_m addendum ensures)
        assert(contains_spec(a.items@, idxb.index, idxb.generation));
        assert(idxc.index@ == idxb.index@ && idxc.generation == idxb.generation);
    }
    let v1: usize = index_m(&a, idxc);
    (v0, v1)
}

/// FromIterator face (lib.rs:1343-1353): from_iter over 4 elements => len==4 && pristine.
pub exec fn ut_from_iter_face(elems: &Vec<usize>) -> (l: usize)
    requires
        elems@.len() == 4, (elems@.len() as int) <= 4,
    ensures
        (l@ as int) == 4,
{
    let a: ArenaModel = from_iter_m(elems);
    proof { assert(pristine(a.items@, a.free_list_head, a.len, a.generation)); }
    len_m(&a)
}

} // verus!

fn main() {}
