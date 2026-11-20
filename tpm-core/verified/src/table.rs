//! tpm-core 0.1.4 context/session slot table (src/table.rs) --
//! Verus translation.
//!
//! Upstream face: the three-state ctx slot enum and the two fixed
//! 3-slot arrays with their query/free/intern/lookup methods
//! (src/table.rs:1-105). Re-erected here: resolve's exact spec twin
//! (a pure function over the table view, so two calls on the same
//! table provably agree -- the fact map_command_handles' two-phase
//! validate/rewrite pass rides on), lookup/intern roundtrips back
//! into resolve (the vhandle they report re-resolves to the same
//! physical handle at the same slot), and the set_*/clear_session
//! mutators' pointwise preservation of every other slot.
//!
//! Upstream `iter().position(...)` / `.find(...)` / `.contains(...)`
//! iterator chains are lowered to canonical index-walk loops with
//! the same first-match early return; Origin notes mark each site.
//! Slot equality tests (`slot == CtxSlot::Live(p)`) are lowered to
//! match-based predicates (see the handle.rs toolchain note).

use vstd::prelude::*;

verus! {

use super::handle::{
    is_transient_exec, slot_of_exec, spec_is_transient, spec_is_transient_val, spec_slot_of,
    spec_vhandle_of, vhandle_of_exec, SLOTS,
};

// ------------------------------------------------------------------
// Slot state (table.rs:3-12)
// ------------------------------------------------------------------

/// Origin Rust: /// Slot state in the context table.
/// #[derive(Clone, Copy, PartialEq, Eq)]
/// pub enum CtxSlot {
///     /// Free slot.
///     Empty,
///     /// Object contents have been saved to the backup buffer; there is no matching handle on the chip.
///     Saved,
///     /// The slot holds an active physical handle.
///     Live(u32),
/// } (table.rs:3-12; the derives carry no Verus twin -- slot
/// comparisons are lowered to the match predicates below)
pub enum CtxSlot {
    /// Free slot.
    Empty,
    /// Object contents have been saved to the backup buffer; there is no matching handle on the chip.
    Saved,
    /// The slot holds an active physical handle.
    Live(u32),
}

/// Match-based Live(p) test (the spec-level image of
/// `slot == CtxSlot::Live(p)`).
pub open spec fn spec_slot_is_live(s: CtxSlot, p: u32) -> bool {
    match s {
        CtxSlot::Live(q) => q == p,
        CtxSlot::Saved => false,
        CtxSlot::Empty => false,
    }
}

/// Int-valued Live test over wire word values (the response-side
/// rewrite faces speak in wire words; no int->u32 casts anywhere).
pub open spec fn spec_slot_live_word(s: CtxSlot, p: int) -> bool {
    match s {
        CtxSlot::Live(q) => q as int == p,
        CtxSlot::Saved => false,
        CtxSlot::Empty => false,
    }
}

/// Match-based Empty test.
pub open spec fn spec_slot_is_empty(s: CtxSlot) -> bool {
    match s {
        CtxSlot::Empty => true,
        CtxSlot::Saved => false,
        CtxSlot::Live(_) => false,
    }
}

/// Match-based Saved test.
pub open spec fn spec_slot_is_saved(s: CtxSlot) -> bool {
    match s {
        CtxSlot::Saved => true,
        CtxSlot::Empty => false,
        CtxSlot::Live(_) => false,
    }
}

// ------------------------------------------------------------------
// Table view (table.rs:13-18)
// ------------------------------------------------------------------

/// Origin Rust: #[derive(Clone, Copy)]
/// pub struct SpaceTable {
///     ctx: [CtxSlot; SLOTS],
///     /// `0` means an empty slot.
///     sessions: [u32; SLOTS],
/// } (table.rs:13-18; both fields are private upstream; the twin
/// opens them to pub with Origin notes because the public contracts
/// of the query and rewrite layers talk about the slot contents
/// directly -- runtime face unchanged, visibility only)
pub struct SpaceTable {
    pub ctx: [CtxSlot; SLOTS],
    /// `0` means an empty slot.
    pub sessions: [u32; SLOTS],
}

/// The resolve spec twin: a pure function on the table view, so the
/// two passes of rewrite.rs's handle mapping (validate, then
/// rewrite) provably consult the same resolution. Two exec calls
/// are not definitionally equal; consulting this twin is the only
/// route to that fact.
/// The word value is carried as int (wire-decoded words are ints
/// upstream of this twin); every caller-side u32 (whose word value
/// is already in range) passes `v as int`.
pub open spec fn spec_resolve(t: &SpaceTable, v: int) -> Option<u32> {
    if spec_is_transient_val(v) {
        let i = spec_slot_of(v as int);
        if 0 <= i < SLOTS as int {
            match t.ctx@.index(i) {
                CtxSlot::Live(p) => Option::Some(p),
                CtxSlot::Saved => Option::None,
                CtxSlot::Empty => Option::None,
            }
        } else {
            Option::None
        }
    } else {
        Option::None
    }
}

/// Spelled-out copy of a table (upstream derives Clone, Copy on
/// SpaceTable at table.rs:13-14; this build has no derive support,
/// so the copy re-materializes both arrays element-wise with exact
/// view faces -- module.rs's begin/commit ride it).
pub(crate) exec fn clone_of_space_table(t: &SpaceTable) -> (r: SpaceTable)
    ensures
        r.ctx@ == t.ctx@,
        r.sessions@ == t.sessions@,
{
    // each slot read is copied by re-materializing through the
    // match arms (no derives in this build)
    let c0 = match t.ctx[0] {
        CtxSlot::Empty => CtxSlot::Empty,
        CtxSlot::Saved => CtxSlot::Saved,
        CtxSlot::Live(u) => CtxSlot::Live(u),
    };
    let c1 = match t.ctx[1] {
        CtxSlot::Empty => CtxSlot::Empty,
        CtxSlot::Saved => CtxSlot::Saved,
        CtxSlot::Live(u) => CtxSlot::Live(u),
    };
    let c2 = match t.ctx[2] {
        CtxSlot::Empty => CtxSlot::Empty,
        CtxSlot::Saved => CtxSlot::Saved,
        CtxSlot::Live(u) => CtxSlot::Live(u),
    };
    let u0 = t.sessions[0];
    let u1 = t.sessions[1];
    let u2 = t.sessions[2];
    SpaceTable {
        ctx: [c0, c1, c2],
        sessions: [u0, u1, u2],
    }
}

/// The resolved value of a transient word, as a total function: 0
/// when the word does not resolve. The two-pass command mapper
/// (rewrite.rs) carries `spec_resolve == Some(spec_resolved)` as a
/// plain universal fact, eliminating the existential from loop
/// invariants.
pub open spec fn spec_resolved(t: &SpaceTable, v: int) -> u32 {
    match spec_resolve(t, v) {
        Option::Some(p) => p,
        Option::None => 0,
    }
}

impl SpaceTable {
    /// Origin Rust: pub fn new() -> Self {
    ///     SpaceTable { ctx: [CtxSlot::Empty; SLOTS], sessions: [0u32; SLOTS] }
    /// } (table.rs:19-26 plus the Default impl at table.rs:28-32;
    /// the const array literals are spelled out for the fixed
    /// SLOTS width)
    pub exec fn new() -> (t: SpaceTable)
        ensures
            forall|k: int|
                0 <= k < SLOTS as int ==> spec_slot_is_empty(t.ctx@.index(k)),
            forall|k: int| 0 <= k < SLOTS as int ==> t.sessions@.index(k) == 0,
    {
        SpaceTable {
            ctx: [CtxSlot::Empty, CtxSlot::Empty, CtxSlot::Empty],
            sessions: [0u32, 0u32, 0u32],
        }
    }
}

impl Default for SpaceTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SpaceTable {
    // --------------------------------------------------------------
    // Slot mutators (table.rs:34-51)
    // --------------------------------------------------------------

    /// Origin Rust: /// Mark the slot as empty or saved. These two states do not carry a handle and never violate the
    /// /// invariant.
    /// pub fn set_slot_free(&mut self, i: usize, saved: bool) {
    ///     self.ctx[i] = if saved { CtxSlot::Saved } else { CtxSlot::Empty };
    /// } (table.rs:34-43; upstream indexes ctx[i] with no bound
    /// check -- the twin carries i < SLOTS as the requires; the
    /// panic face is recorded at the suspect row S-T5-2)
    pub exec fn set_slot_free(&mut self, i: usize, saved: bool)
        requires
            (i as int) < SLOTS as int,
        ensures
            if saved {
                spec_slot_is_saved(final(self).ctx@.index(i as int))
            } else {
                spec_slot_is_empty(final(self).ctx@.index(i as int))
            },
            forall|j: int|
                0 <= j < SLOTS as int && j != (i as int)
                    ==> final(self).ctx@.index(j) == old(self).ctx@.index(j),
            final(self).sessions@ == old(self).sessions@,
    {
        self.ctx[i] = if saved {
            CtxSlot::Saved
        } else {
            CtxSlot::Empty
        };
    }

    /// Origin Rust: /// Mark the slot as live. Requires the handle to be valid and not already registered.
    /// ///
    /// /// "Not already registered" is a precondition rather than a runtime check: the call sites (`intern`,
    /// /// load path) already inspected the table once, and checking again would be wasted work. The injective
    /// /// property is carried by this precondition without introducing any trust assumption.
    /// pub fn set_slot_live(&mut self, i: usize, p: u32) {
    ///     self.ctx[i] = CtxSlot::Live(p);
    /// } (table.rs:44-51; the doc's injectivity is caller
    /// discipline -- no runtime check enforces it; the twin records
    /// it in the doc contract, the i bound is as above)
    pub exec fn set_slot_live(&mut self, i: usize, p: u32)
        requires
            (i as int) < SLOTS as int,
        ensures
            spec_slot_is_live(final(self).ctx@.index(i as int), p),
            forall|j: int|
                0 <= j < SLOTS as int && j != (i as int)
                    ==> final(self).ctx@.index(j) == old(self).ctx@.index(j),
            final(self).sessions@ == old(self).sessions@,
    {
        self.ctx[i] = CtxSlot::Live(p);
    }

    // --------------------------------------------------------------
    // Queries (table.rs:52-104)
    // --------------------------------------------------------------

    /// Origin Rust: /// Virtual handle -> physical handle.
    /// /// (doc summary of the upstream comment "Virtual handle -> physical handle.")
    /// pub fn resolve(&self, v: u32) -> Option<u32> {
    ///     if !is_transient_exec(v) { return None; }
    ///     let i = slot_of_exec(v);
    ///     if i >= SLOTS { return None; }
    ///     match self.ctx[i] { CtxSlot::Live(p) => Some(p), _ => None }
    /// } (table.rs:52-65; total, no input bounds; the exact spec
    /// twin makes resolve functional in the table state)
    pub exec fn resolve(&self, v: u32) -> (r: Option<u32>)
        ensures
            r == spec_resolve(self, v as int),
    {
        if !is_transient_exec(v) {
            return Option::None;
        }
        let i = slot_of_exec(v);
        if i >= SLOTS {
            return Option::None;
        }
        match self.ctx[i] {
            CtxSlot::Live(p) => Option::Some(p),
            CtxSlot::Saved => Option::None,
            CtxSlot::Empty => Option::None,
        }
    }

    /// Origin Rust: /// Physical handle -> virtual handle, query-only and no allocation.
    /// pub fn lookup(&self, p: u32) -> Option<u32> {
    ///     self.ctx.iter().position(|&slot| slot == CtxSlot::Live(p)).map(vhandle_of_exec)
    /// } (table.rs:66-71; lowered to the first-match index walk; the
    /// None face is total: no slot at all is Live(p))
    pub exec fn lookup(&self, p: u32) -> (r: Option<u32>)
        ensures
            match r {
                Option::Some(v) =>
                    spec_slot_of(v as int) < SLOTS as int
                        && spec_is_transient(v)
                        && (v as int) == spec_vhandle_of(spec_slot_of(v as int))
                        && spec_slot_is_live(
                            self.ctx@.index(spec_slot_of(v as int)),
                            p,
                        ),
                Option::None =>
                    forall|k: int|
                        0 <= k < SLOTS as int
                            ==> !spec_slot_is_live(self.ctx@.index(k), p),
            },
    {
        let mut i: usize = 0;
        while i < SLOTS
            invariant
                (i as int) <= SLOTS as int,
                forall|k: int|
                    0 <= k < (i as int)
                        ==> !spec_slot_is_live(self.ctx@.index(k), p),
            decreases
                SLOTS as int - (i as int),
        {
            match self.ctx[i] {
                CtxSlot::Live(q) => {
                    if q == p {
                        return Option::Some(vhandle_of_exec(i));
                    }
                }
                CtxSlot::Saved => {}
                CtxSlot::Empty => {}
            }
            i = i + 1;
        }
        Option::None
    }

    /// Origin Rust: /// Allocate an empty slot for a physical handle and return the corresponding virtual handle.
    /// ///
    /// /// Returns `None` when the table is full; in that case the caller is obligated to release the physical
    /// /// handle on the chip, or it will continue to occupy chip resources and can never be referenced again.
    /// pub fn intern(&mut self, p: u32) -> Option<u32> {
    ///     let i = self.ctx.iter().position(|&slot| slot == CtxSlot::Empty)?;
    ///     self.set_slot_live(i, p);
    ///     Some(vhandle_of_exec(i))
    /// } (table.rs:72-81; lowered to the index walk; the None arm
    /// carries the doc's caller release obligation in the comment
    /// only -- the rewrite.rs caller face packages it as the
    /// OutOfSlots data)
    pub exec fn intern(&mut self, p: u32) -> (r: Option<u32>)
        ensures
            match r {
                Option::Some(v) =>
                    spec_is_transient(v)
                        && (v as int)
                            == spec_vhandle_of(spec_slot_of(v as int))
                        && spec_slot_of(v as int) < SLOTS as int
                        && spec_slot_is_live(
                            final(self).ctx@.index(spec_slot_of(v as int)),
                            p,
                        )
                        && (forall|j: int|
                            0 <= j < SLOTS as int
                                && j != spec_slot_of(v as int)
                            ==> final(self).ctx@.index(j)
                                == old(self).ctx@.index(j))
                        && final(self).sessions@ == old(self).sessions@,
                Option::None =>
                    final(self).ctx@ == old(self).ctx@
                        && final(self).sessions@ == old(self).sessions@
                        && forall|k: int|
                            0 <= k < SLOTS as int
                                ==> !spec_slot_is_empty(old(self).ctx@.index(k)),
            },
    {
        let mut i: usize = 0;
        while i < SLOTS
            invariant
                (i as int) <= SLOTS as int,
                forall|k: int|
                    0 <= k < (i as int)
                        ==> !spec_slot_is_empty(self.ctx@.index(k)),
                self.ctx@ == old(self).ctx@,
                self.sessions@ == old(self).sessions@,
            decreases
                SLOTS as int - (i as int),
        {
            match self.ctx[i] {
                CtxSlot::Empty => {
                    self.set_slot_live(i, p);
                    return Option::Some(vhandle_of_exec(i));
                }
                CtxSlot::Saved => {}
                CtxSlot::Live(_) => {}
            }
            i = i + 1;
        }
        Option::None
    }

    /// Origin Rust: /// Register a session handle. Returns `false` when the table is full; the caller also has the release
    /// /// obligation in that case.
    /// pub fn add_session(&mut self, h: u32) -> bool {
    ///     match self.sessions.iter_mut().find(|slot| **slot == 0) {
    ///         Some(slot) => { *slot = h; true } None => false }
    /// } (table.rs:82-92; lowered to the index walk)
    pub exec fn add_session(&mut self, h: u32) -> (r: bool)
        ensures
            if r {
                exists|i: int|
                    0 <= i < SLOTS as int
                        && old(self).sessions@.index(i) == 0
                        && final(self).sessions@.index(i) == h
                        && forall|j: int|
                            0 <= j < SLOTS as int && j != i
                                ==> final(self).sessions@.index(j)
                                    == old(self).sessions@.index(j)
            } else {
                final(self).sessions@ == old(self).sessions@
                    && forall|k: int|
                        0 <= k < SLOTS as int
                            ==> old(self).sessions@.index(k) != 0
            },
            final(self).ctx@ == old(self).ctx@,
    {
        let mut i: usize = 0;
        while i < SLOTS
            invariant
                (i as int) <= SLOTS as int,
                forall|k: int|
                    0 <= k < (i as int) ==> self.sessions@.index(k) != 0,
                self.sessions@ == old(self).sessions@,
                self.ctx@ == old(self).ctx@,
            decreases
                SLOTS as int - (i as int),
        {
            if self.sessions[i] == 0 {
                self.sessions[i] = h;
                return true;
            }
            i = i + 1;
        }
        false
    }

    /// Origin Rust: pub fn has_session_exec(&self, h: u32) -> bool {
    ///     self.sessions.contains(&h)
    /// } (table.rs:93-94; lowered to the index walk; the face is
    /// the exact membership quantifier)
    pub exec fn has_session_exec(&self, h: u32) -> (r: bool)
        ensures
            r == (exists|k: int|
                0 <= k < SLOTS as int && self.sessions@.index(k) == h),
    {
        let mut i: usize = 0;
        while i < SLOTS
            invariant
                (i as int) <= SLOTS as int,
                forall|k: int|
                    0 <= k < (i as int) ==> self.sessions@.index(k) != h,
            decreases
                SLOTS as int - (i as int),
        {
            if self.sessions[i] == h {
                assert(self.sessions@.index(i as int) == h);
                return true;
            }
            i = i + 1;
        }
        false
    }

    /// Origin Rust: pub fn session_at(&self, i: usize) -> u32 { self.sessions[i] }
    /// (table.rs:95-97; i bound as above, suspect row S-T5-2)
    pub exec fn session_at(&self, i: usize) -> (r: u32)
        requires
            (i as int) < SLOTS as int,
        ensures
            r == self.sessions@.index(i as int),
    {
        self.sessions[i]
    }

    /// Origin Rust: pub fn clear_session(&mut self, i: usize) { self.sessions[i] = 0 }
    /// (table.rs:98-100; i bound as above)
    pub exec fn clear_session(&mut self, i: usize)
        requires
            (i as int) < SLOTS as int,
        ensures
            final(self).sessions@.index(i as int) == 0,
            forall|j: int|
                0 <= j < SLOTS as int && j != (i as int)
                    ==> final(self).sessions@.index(j) == old(self).sessions@.index(j),
            final(self).ctx@ == old(self).ctx@,
    {
        self.sessions[i] = 0;
    }

    /// Origin Rust: pub fn slot_at(&self, i: usize) -> CtxSlot { self.ctx[i] }
    /// (table.rs:101-104; i bound as above)
    pub exec fn slot_at(&self, i: usize) -> (r: CtxSlot)
        requires
            (i as int) < SLOTS as int,
        ensures
            r == self.ctx@.index(i as int),
    {
        // upstream derives Copy on CtxSlot; this verus build has no
        // derive support, so the slot value is re-materialized by
        // the match arms (same value, no move)
        match self.ctx[i] {
            CtxSlot::Empty => CtxSlot::Empty,
            CtxSlot::Saved => CtxSlot::Saved,
            CtxSlot::Live(u) => CtxSlot::Live(u),
        }
    }
}

} // verus!
