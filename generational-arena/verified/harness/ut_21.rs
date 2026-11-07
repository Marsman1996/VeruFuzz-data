//! generational-arena 0.2.9 (pin 6dbc29e) x Verus 0.2026.10.29
//! UT#21 (tests.rs:228-258 drain) key-assertion harness (reference-style: the
//! two-zone-split coordination rules).
//!
//! Attribution criterion: this file is a "test/property transcription" -- the theorem
//! shapes of upstream tests.rs UT#21 drain assertions (4) and (5) (insert after drain
//! takes the guarded slow path and allocates normally / repeated drain of an empty arena does not bump the generation).
//!
//! Reference-style structure: via `#[path="../src/lib.rs"] mod arena_src;` this file references
//! the Part B flat Slot model L0 kernel of verified/src/lib.rs (the verification fact source
//! exists only once, in src, nothing copied; the needed ArenaModel/insert_m/reserve_m/drain_m
//! and spec predicates are all pub in src, no visibility adjustments).
//!
//! Run caliber: verifying this file = re-verifying the whole referenced src module (incl. its
//! expected 1 error = the F1/F6 anchor, the lib.rs:406 transcript line :147, see the src file
//! header; the obligations match a standalone src run) + this file's 2 UT#21 theorems. This
//! file's own theorems expect **0 errors**.

#[path = "../src/lib.rs"]
mod arena_src;

use vstd::prelude::*;

use crate::arena_src::{
    ArenaModel, IndexModel, contains_spec, pristine,
    insert_m, reserve_m, drain_m,
};

verus! {

// ---------- UT#21 key assertions ----------

/// UT drain (tests.rs:228-258) key assertion (4) (:242-247), theorem form:
/// pristine nonempty arena -> drain (items empty / len 0 / gen +1, head None) ->
/// the insert takes the guarded slow path and allocates normally; the new index lands in
/// slot 0 with generation == old + 1 (i.e. the generation-face difference of idx_3 != idx_1).
pub exec fn ut21_drain_then_insert_works(arena: &mut ArenaModel) -> (r: IndexModel)
    requires
        pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
        arena.len@ > 0,
        2 * arena.items@.len() <= usize::MAX,
        arena.items@.len() < usize::MAX,
    ensures
        final(arena).len@ == 1,
        r.generation@ == old(arena).generation@ + 1,
        r.index@ == 0,
        contains_spec(final(arena).items@, r.index, r.generation),
{
    drain_m(arena);
    // after drain: items empty, head None, len 0 = the empty branch of pristine;
    // the insert takes the guarded slow path (lib.rs:468: capacity()==0 => reserve(1)).
    insert_m(arena, 0usize)
}

/// UT drain assertion (5) (tests.rs:250-257): an empty arena (built via with_capacity(1))
/// drained repeatedly never bumps the generation -- 3 times in a row, the final generation stays 0.
pub exec fn ut21_empty_drains_keep_generation_zero() -> (g: u64)
    ensures
        g@ == 0,
{
    // Origin Rust (lib.rs:272-282) with_capacity: empty items + reserve(n)
    let mut arena: ArenaModel = ArenaModel { items: Vec::new(), generation: 0, free_list_head: None, len: 0 };
    reserve_m(&mut arena, 1);
    let mut k: usize = 0;
    while k < 3
        invariant
            k <= 3,
            arena.len@ == 0,
            arena.generation@ == 0,
        decreases 3 - k,
    {
        drain_m(&mut arena);
        k += 1;
    }
    arena.generation
}

} // verus!

fn main() {}
