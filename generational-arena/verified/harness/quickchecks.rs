//! generational-arena 0.2.9 (pin 6dbc29e) x Verus 0.2026.10.29
//! quickcheck Q1/Q2 property harness (reference-style: the two-zone-split rules).
//!
//! Attribution criterion: this file is a "test/property transcription" -- the
//! Q1/Q2 arbitrary-length synthetic drivers of upstream tests/quickchecks.rs.
//!
//! Reference-style structure: via `#[path="../src/lib.rs"] mod arena_src;` this file references
//! the Part B flat Slot model L0 kernel of verified/src/lib.rs (the verification fact source
//! exists only once, in src, nothing copied; the needed ArenaModel/IndexModel/insert_m/remove_m
//! and spec predicates are all pub in src, no visibility adjustments).
//!
//! Run caliber: verifying this file = re-verifying the whole referenced src module (incl.
//! its expected 1 error = the F1/F6 anchor, the lib.rs:406 transcript line :147, see the src
//! file header; the obligations match a standalone src run) + this file's 2 qc drivers.
//!
//! This file's own theorems expect (`--multiple-errors 100`): **0 errors**; the obligation
//! face (requires/ensures/invariant clause contents) not weakened. Three machine proofs:
//!   1. **invariant carrying**: in this verus build (0.2026.10.29) the loop-body query
//!      context holds only invariant clauses -- a function's requires ground facts do not
//!      reach the loop body directly (straight-line / condition-length / ghost-let rewrites
//!      lose reach equally); the needed requires facts must be carried into the loop as invariant clauses;
//!   2. **explicit trigger**: for this forall-requires the auto trigger cannot instantiate
//!      (ground instantiation also fails); `#![trigger arena.items@[j]]` opens both the ground
//!      and the assert-forall forms in one stroke; the forall clauses inside the invariants
//!      need the annotation likewise;
//!   3. **addition chains + assert forall ... implies ... by**: in this build int-domain
//!      binomial product unfolding is blocked (the 2*(2x+4) shape does not unfold); binomial
//!      unfoldings go through additions instead; inside `assert forall` bodies `==>` carries
//!      no premise context, so `implies` is required.
//!
// ---------- qc properties ----------

#[path = "../src/lib.rs"]
mod arena_src;

use vstd::prelude::*;

use crate::arena_src::{
    ArenaModel, IndexModel, Slot, contains_spec, pristine, oval,
    insert_m, remove_m, opt_nat, slot_same,
};

verus! {

/// qc Q1 `always_contains_inserted_elements` (quickchecks.rs:9-15):
/// after inserting arbitrary elems one by one, every returned index stays contained and
/// the value reads back. Input restricted to the `Arena::new()` shape (pristine && len==0
/// && initial capacity <= 4 -- the upstream quickcheck's starting point Arena::new() =
/// with_capacity(4), lib.rs:230/249-250). The proof uses a positional abstraction: the
/// k-th insert lands in slot k and the generation stays constantly g0 (insert does not
/// bump generation), so slot j has value == elems[j] and ids_out@[t] == {index: t, generation: g0} -- maintained each round by the invariant.
pub exec fn qc_always_contains_inserted_elements(
    arena: &mut ArenaModel,
    elems: &Vec<usize>,
) -> (ids_out: Vec<IndexModel>)
    requires
        pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
        arena.len@ == 0,
        arena.items@.len() <= 4,
        4 * elems@.len() + 8 <= usize::MAX,
    ensures
        ids_out@.len() == elems@.len(),
        forall |t| 0 <= t < elems@.len() ==>
            ids_out@[t].index@ == t
            && ids_out@[t].generation == old(arena).generation@,
        forall |t| 0 <= t < elems@.len() ==>
            contains_spec(final(arena).items@, ids_out@[t].index, ids_out@[t].generation)
            && final(arena).items@[ids_out@[t].index@ as int].value@ == elems@[t],
{
    let ghost mut g0: u64 = 0;
    proof {
        g0 = arena.generation@;
    }
    let mut ids: Vec<IndexModel> = Vec::new();
    let mut k: usize = 0;
    while k < elems.len()
        invariant
            k <= elems@.len(),
            ids@.len() == k,
            arena.len@ == k,
            pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
            arena.items@.len() <= 2 * arena.len@ + 4,
            arena.generation@ == g0,
            // positional shape: slot j in [0, k): value == elems[j]
            forall |j| 0 <= j < arena.len@ ==> arena.items@[j].value@ == elems@[j],
            // recorded id positional shape: ids@.index == position, generation == g0
            forall |t| #![trigger ids@[t]] 0 <= t < ids@.len() ==> ids@[t].index@ == t && ids@[t].generation == g0,
            // requires-carry clause (requires ground facts don't reach the loop body)
            4 * elems@.len() + 8 <= usize::MAX,
        decreases elems@.len() - k,
    {
        proof {
            // addition-chain derivation (this build blocks binomial product unfolding; constants
            // are rewritten as term sums; the 2*x == x+x linear restatement works)
            assert(arena.len@ <= elems@.len());                      // len==k<=elems.len (invariant)
            assert(arena.items@.len() + arena.items@.len() <= 4 * elems@.len() + 8);   // carried clause + invariant, addition restatement
            assert(4 * elems@.len() + 8 <= usize::MAX);               // carried clause, original shape
            assert(arena.items@.len() + arena.items@.len() <= usize::MAX);
            assert(2 * arena.items@.len() == arena.items@.len() + arena.items@.len()); // (m1)
            assert(2 * arena.items@.len() <= usize::MAX);             // insert_m precondition
            assert(arena.items@.len() < usize::MAX);
        }
        let idx: IndexModel = insert_m(arena, elems[k]);
        assert(idx.index@ == k@);           // the landing fact under the insert precondition (r.index == old.len == k)
        ids.push(idx);
        k += 1;
    }
    // tail bridge: prove first in CURRENT wording (final(...) is just an alias for the out-param)
    assert(k@ == elems@.len());
    assert(ids@.len() == k@);
    assert(arena.len@ == k@);
    assert(forall |t| 0 <= t < elems@.len() ==>
        contains_spec(arena.items@, ids@[t].index, ids@[t].generation)
        && arena.items@[ids@[t].index@ as int].value@ == elems@[t]);
    ids
}

// ---------- qc Q2 ----------
/// qc Q2 `never_contains_deleted_elements` (quickchecks.rs:17-26), the second-half deletion loop:
/// the first half's (insert n items and record indices) spec shape is given by Q1's ensures --
/// here its positional shape is required directly (ids@[t] == {index: t, generation: g0},
/// slot j: occupied && generation g0 && value == elems[j]).
/// Every per-idx remove returns Some (`unwrap` does not panic, and the value is exactly the
/// inserted one -- Q2's `arena.remove(i).unwrap()` expectation); after deleting all, forall t: !contains.
pub exec fn qc_never_contains_deleted_elements(
    arena: &mut ArenaModel,
    elems: &Vec<usize>,
    ids: &Vec<IndexModel>,
    gen0: u64,
)
    requires
        ids@.len() == elems@.len(),
        arena.len@ == ids@.len(),
        gen0 == arena.generation@,
        ids@.len() <= arena.items@.len(),
        forall |t| #![trigger ids@[t]] 0 <= t < ids@.len() ==> ids@[t].index@ == t && ids@[t].generation == gen0,
        forall |j| #![trigger arena.items@[j]] 0 <= j < ids@.len() ==>
            arena.items@[j].occupied && arena.items@[j].generation == gen0 && arena.items@[j].value@ == elems@[j],
        arena.generation@ + ids@.len() <= u64::MAX,
    ensures
        final(arena).len@ == 0,
        final(arena).generation@ == old(arena).generation@ + ids@.len(),
        final(arena).items@.len() == old(arena).items@.len(),
        forall |t| 0 <= t < ids@.len() ==>
            !contains_spec(final(arena).items@, ids@[t].index, ids@[t].generation),
{
    let ghost mut items_len0: int = 0;
    proof {
        items_len0 = arena.items@.len() as int;
    }
    proof {
        assert(arena.generation@ == gen0);
    }
    let mut k: usize = 0;
    proof {
        // pre-loop segment facts established by force (a restatement opened up by the explicit
        // trigger, entering the main query context for direct entry-check instantiation)
        assert(forall |j: int| 0 <= j < ids@.len() ==>
            arena.items@[j].occupied
            && arena.items@[j].generation == gen0
            && arena.items@[j].value@ == elems@[j]);
    }
    while k < ids.len()
        invariant
            k <= ids@.len(),
            arena.len@ == ids@.len() - k@,
            arena.items@.len() == items_len0,
            arena.generation@ == gen0 + k@,
            // positional shape: slots [0, k) already deleted-empty, slots [k, n) still occupied@gen0/value-matched
            // (forall clause with explicit trigger: the auto trigger cannot instantiate)
            forall |j| #![trigger arena.items@[j]] 0 <= j < k@ ==> !arena.items@[j].occupied,
            forall |j| #![trigger arena.items@[j]] k@ <= j < ids@.len() ==>
                arena.items@[j].occupied && arena.items@[j].generation == gen0 && arena.items@[j].value@ == elems@[j],
            // ids read-only (an & reference); the requires positional properties carry over
            forall |t| #![trigger ids@[t]] 0 <= t < ids@.len() ==> ids@[t].index@ == t && ids@[t].generation == gen0,
            // requires-carry clause (requires ground facts don't reach the loop body)
            ids@.len() <= arena.items@.len(),
            gen0 + ids@.len() <= u64::MAX,
        decreases ids@.len() - k,
    {
        let idx_val: IndexModel = IndexModel { index: k, generation: gen0 };
        proof {
            assert(k@ < ids@.len() <= arena.items@.len());   // slot k in bounds
            assert(contains_spec(arena.items@, idx_val.index, idx_val.generation));
            assert(arena.generation@ < u64::MAX);             // gen0 + k < gen0 + ids.len <= MAX
            assert(arena.len@ > 0);
        }
        // ghost snapshot (the pre-remove state: the frame basis for segment maintenance)
        let ghost pre_items: Seq<Slot> = arena.items@;
        let v: Option<usize> = remove_m(arena, idx_val);
        proof {
            // remove returns Some and the value is exactly elems[k] (Q2's unwrap and value-read-back expectation)
            assert(v matches Some(_));
            assert(oval(v) == pre_items[k@ as int].value@);
            // frame instantiation -- carried-clause semantics (assert forall ... implies ... by; the body's ==> carries
            // no premise context, implies is required; inside by, j is concrete,
            // so the remove frame and the old-segment triggers hit naturally)
            assert forall |j: int| k@ + 1 <= j < ids@.len() implies
                arena.items@[j].occupied
                && arena.items@[j].generation == gen0
                && arena.items@[j].value@ == elems@[j]
            by {
                let sj_new = arena.items@[j];
                let sj_pre = pre_items[j];
            }
            // [0, k+1) deleted-empty (: frame order + this round's slot k direct post-remove property)
            assert forall |j: int| 0 <= j < k@ + 1 implies
                !arena.items@[j].occupied
            by {
                if j == k@ {
                    assert(!arena.items@[j].occupied);
                } else {
                    let sj_new = arena.items@[j];
                    let sj_pre = pre_items[j];
                    assert(!sj_pre.occupied);
                }
            }
        }
        k += 1;
    }
    // tail bridge: prove first in CURRENT wording (final(...) is an alias for the out-param)
    assert(k@ == ids@.len());
    assert(arena.len@ == 0);
    assert(forall |t| 0 <= t < ids@.len() ==> !contains_spec(arena.items@, ids@[t].index, ids@[t].generation));
}
} // verus!

fn main() {}
