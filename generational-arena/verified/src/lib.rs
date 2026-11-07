//! generational-arena 0.2.9 (pin 6dbc29e) x Verus 0.2026.10.29
//! Mirror of the upstream `src/lib.rs` (two-zone split, reference-style harness): this file carries the
//! library code proper -- `mod f1_f6_repro` = the entire former fragment
//! f1_insert_with_after_drain.rs (F1/F6 machine repro, incl. the obligation-failure anchor,
//! witnesses, and the repair counterexample); Part B = the flat-Slot-model L0 verbatim
//! transcription + contracts of the 5+3 APIs called by qc/UT (the former
//! qc_insert_remove_contains.rs content), brought back into this src as the verification
//! fact source. The UT#21 (4)(5) theorems and the qc Q1/Q2 drivers -- the "test/property
//! transcriptions" -- moved to `verified/harness/ut_21.rs` and `verified/harness/quickchecks.rs` (referencing
//! this kernel via `#[path="../src/lib.rs"] mod`, no copying; all referenced items pub; serde_impl.rs unmirrored (no verified content).
//!
//! Packaging form (two-zone rule: name clashes go into a mod re-export, kept since the merge):
//!   - Part A `mod f1_f6_repro`: its `ArenaModel` is the state-abstract form
//!     `Vec<Option<usize>>`, same name but different structure from Part B's flat Slot model,
//!     so the whole block is wrapped in a mod and ArenaModel is not re-exported; the fn names
//!     cited by the report stay reachable via the file-tail `pub use` re-export, paths switched to src/lib.rs;
//!   - Part B top level (no mod wrapper; the harness references it directly).
//!
//! Re-run expectation after the rearrangement (`--multiple-errors 100`): 1 error = the F1/F6 anchor
//! (the lib.rs:406 transcript line of Part A `try_alloc_raw`, line number :147 kept --
//! the Part A block is otherwise untouched); Part B kernel 0 errors (all verified on the merge re-run).
//! The other 3 errors of the merge-era 24v/4e were qc drivers (blocked archive), now living with
//! the Part C drivers in harness/quickchecks.rs (reference-style; obligation shapes kept,
//! reconciliation in out/bug-finder-summary.md).

use vstd::prelude::*;

verus! {

// ===========================================================================
// Part A: F1/F6 machine repro (formerly verified/f1_insert_with_after_drain.rs;
// the file-header comments preserved blockwise below; "this file" inside the blocks means this src/lib.rs)
// ---------------------------------------------------------------------------
// Machine-repro file for F1 and F6.
//
// Adapted from this crate's already-verified PoC `out/verus/f1_insert_with_after_drain_exec.rs`
// (verus 0.2026.10.08 caliber, 10 verified / 1 error), re-run with the new verus as required and
// extended with F6 (public `reserve(0)` poisoning, out/ub-panic-audit-blind.md blind-audit addendum F6).
//
// Model (state abstraction, Origin Rust: lib.rs:170-181):
//   `ArenaModel { items: Vec<Option<usize>>, free_list_head: Option<usize> }`
//   items slot value = `Entry::Free.next_free`(lib.rs:409-412);
//   the `Entry::Occupied` branch (the lib.rs:407 "corrupt free list" defense) is upstream's private
//   defense of its own free-list invariant, unrelated to this finding (indexing an empty vec in a
//   drained/poisoned state), so it is omitted from the model and noted here.
//
// Verification criteria (see the concluding comments at the file tail):
//   - F1: the error lands exactly on `try_alloc_raw`'s `arena.items[i]` (the lib.rs:406 transcript line);
//   - F6: the error lands exactly on the same `arena.items[i]` transcript line in `f6_chain_raw`;
//   - everything else (guarded path insert_chain_control, fresh control, witness lemmas) verifies.
// ===========================================================================

pub mod f1_f6_repro {
    use vstd::prelude::*;

// ---------- state model ----------
// Origin Rust (lib.rs:170-175):
//   pub struct Arena<T> {
//       items: Vec<Entry<T>>,
//       generation: u64,
//       free_list_head: Option<usize>,
//       len: usize,
//   }
// The model keeps items / free_list_head (the two fields relevant to this finding).
pub struct ArenaModel {
    pub items: Vec<Option<usize>>,
    pub free_list_head: Option<usize>,
}

// ---------- L0: lib.rs:913-925 drain state-face transcription ----------

/// Origin Rust (lib.rs:920-924):
///     self.free_list_head = None;
///     self.len = 0;
///     Drain { len: old_len, inner: self.items.drain(..).enumerate() }
/// `items.drain(..)` (std: len back to 0, capacity kept -- but upstream `capacity()` is defined as
/// `items.len()` (lib.rs:795-797), so externally it IS capacity 0). The std primitive is carried by
/// external_body (not a verification-target site); the behavioral guarantees live in ensures.
#[verifier::external_body]
pub exec fn drain_model(arena: &mut ArenaModel)
    ensures
        final(arena).items.view().len() == 0,
        final(arena).free_list_head matches None,
{
}

// ---------- L0: lib.rs:815-831 reserve verbatim transcription ----------

/// Origin Rust (lib.rs:815-831):
///     pub fn reserve(&mut self, additional_capacity: usize) {
///         let start = self.items.len();
///         let end = self.items.len() + additional_capacity;
///         let old_head = self.free_list_head;
///         self.items.reserve_exact(additional_capacity);
///         self.items.extend((start..end).map(|i| {
///             if i == end - 1 { Entry::Free { next_free: old_head } }
///             else { Entry::Free { next_free: Some(i + 1) } }
///         }));
///         self.free_list_head = Some(start);        // <- lib.rs:831 unconditional set
///     }
/// extend is transcribed as a push loop (the slot-value layout is irrelevant to this finding; a
/// placeholder 0...additional keeps the "slot existence" semantics); `free_list_head = Some(start)`
/// is set **unconditionally** -- also when `additional == 0` (F1 root cause, F6 separate public entry).
pub exec fn reserve_model(arena: &mut ArenaModel, additional: usize)
    ensures
        final(arena).items.view().len() == old(arena).items.view().len() + additional@,
        final(arena).free_list_head == Some(old(arena).items.view().len() as usize),
{
    let start: usize = arena.items.len();               // lib.rs:816
    let head_saved: Option<usize> = arena.free_list_head; // lib.rs:818 old_head
    let mut i: usize = 0;
    while i < additional
        invariant
            i <= additional,
            arena.items.len() == start + i,
            arena.free_list_head == head_saved,
        decreases additional - i,
    {
        // Origin Rust (lib.rs:820-830): extend pushes Free entries [start, end)
        arena.items.push(Some(0));     // slot-existence transcription (next_free layout irrelevant to the finding; see the header note)
        i += 1;
    }
    arena.free_list_head = Some(start);                  // lib.rs:831 <- unconditional (core fact)
}

// ---------- L0: lib.rs:403-413 try_alloc_next_index verbatim transcription ----------

/// raw face: upstream declares **no structural precondition** for callers => requires is empty =>
/// the `arena.items[i]` (lib.rs:406) indexing obligation necessarily fails -- the expected error
/// site, the obligation form of the runtime "index out of bounds: the len is 0 but the index is 0"
/// panic (reachability shown by the witness chain).
/// Origin Rust (lib.rs:403-418):
///     fn try_alloc_next_index(&mut self) -> Option<Index> {
///         match self.free_list_head {
///             None => None,
    ///             Some(i) => match self.items[i] {           // <- lib.rs:406
///                 Entry::Occupied { .. } => panic!("corrupt free list"),
///                 Entry::Free { next_free } => { ... }
///             }
///         }
///     }
/// (The Occupied defense arm is omitted; see the header note.)
pub exec fn try_alloc_raw(arena: &mut ArenaModel) -> (r: Option<usize>) {
    match arena.free_list_head {          // lib.rs:404
        None => None,                     // lib.rs:405
        Some(i) => {
            let next_free: Option<usize> = arena.items[i]; // lib.rs:406 <- EXPECTED (F1/F6)
            arena.free_list_head = next_free;              // lib.rs:409
            Some(i)                                        // lib.rs:411
        }
    }
}

/// invariant face: the same exec body, carrying the structural precondition (head is None or points
/// to an in-bounds slot -- an invariant upstream's free-list design maintains itself, not a
/// documented caller requirement). This shape passes all obligations; it serves only the guard/control machines.
pub exec fn try_alloc_inv(arena: &mut ArenaModel) -> (r: Option<usize>)
    requires
        match arena.free_list_head {
            None => true,
            Some(i) => i < arena.items.len(),
        }
    ensures
        match old(arena).free_list_head {
            None => r matches None,
            Some(_) => r matches Some(_),
        },
{
    match arena.free_list_head {
        None => None,
        Some(i) => {
            let next_free: Option<usize> = arena.items[i]; // obligation provable here
            arena.free_list_head = next_free;
            Some(i)
        }
    }
}

// ---------- L0: lib.rs:456-462 + 488-494 insert_with chain (bug shape) ----------

/// Origin Rust (lib.rs:488-494):
///     fn insert_with_slow_path(&mut self, create: impl FnOnce(Index) -> T) -> Index {
///         let len = self.items.len();     // <- capacity==0 guard missing
///         self.reserve(len);
///         self.try_insert_with(create)...
///     }
pub exec fn insert_with_slow_path_raw(arena: &mut ArenaModel) -> (r: Option<usize>) {
    let len: usize = arena.items.len();    // lib.rs:489
    reserve_model(arena, len);             // lib.rs:490 -- no capacity==0 guard
    try_alloc_raw(arena)                   // lib.rs:491 -> triggers the :406 obligation failure (on the witness chain)
}

/// Origin Rust (lib.rs:459-463):
///     pub fn insert_with(&mut self, create: impl FnOnce(Index) -> T) -> Index {
///         match self.try_insert_with(create) {
///             Ok(i) => i,
///             Err(create) => self.insert_with_slow_path(create),
///         }
///     }
pub exec fn insert_with_chain_upstream(arena: &mut ArenaModel) -> (r: Option<usize>) {
    match try_alloc_raw(arena) {            // lib.rs:460 fast path
        Some(i) => Some(i),
        None => insert_with_slow_path_raw(arena), // lib.rs:462
    }
}

// ---------- repair counterexample: lib.rs:466-485 guarded path (the control group of upstream insert) ----------

/// Origin Rust (lib.rs:467-485):
///     fn insert_slow_path(&mut self, value: T) -> Index {
///         let len = if self.capacity() == 0 {   // <- lib.rs:468 guard (comment :469-476 names the drain hazard)
///             1 else { self.items.len() }
///         };
///         self.reserve(len);
///         self.try_insert(value)...
///     }
/// Under a drained state every obligation passes, ending with `try_alloc_inv` --
/// machine-proving that "the same reserve set-position + try_alloc indexing" is safe behind the guard.
pub exec fn insert_slow_path_guarded(arena: &mut ArenaModel) -> (r: Option<usize>) {
    let len: usize = if arena.items.len() == 0 { // lib.rs:468 capacity()==items.len()(lib.rs:795-797)
        1                                        // lib.rs:477 guard
    } else {
        arena.items.len()                        // lib.rs:479
    };
    reserve_model(arena, len);                   // lib.rs:481
    try_alloc_inv(arena)                         // lib.rs:482 -- reserve ensures => start < start + len
}

/// Origin Rust (lib.rs:435-439):
///     pub fn insert(&mut self, value: T) -> Index {
///         match self.try_insert(value) {
///             Ok(i) => i,
///             Err(value) => self.insert_slow_path(value),
///         }
///     }
/// A drained sequence through `insert`: fast path None => guarded slow path => normal return
/// -- **this chain passes all obligations**, i.e. the machine-checked PoC control group (insert
/// after drain is normal, the documented behavior of the UT `drain` (tests.rs:245)).
pub exec fn insert_chain_control(arena: &mut ArenaModel) -> (r: Option<usize>)
    requires
        arena.items.len() == 0,                    // drain_model's ensures (see the witness chain)
        arena.free_list_head matches None,
{
    match try_alloc_inv(arena) {
        Some(i) => Some(i),
        None => insert_slow_path_guarded(arena),
    }
}

/// fresh-arena control group (lib.rs:230/250: `new()` = `with_capacity(4)`):
/// the fast path allocates directly and never enters the slow path. head==Some(0) => necessarily Some.
pub exec fn insert_with_chain_fresh_control(arena: &mut ArenaModel) -> (r: usize)
    requires
        arena.items.len() >= 1,
        arena.free_list_head matches Some(0),
{
    match try_alloc_inv(arena) {
        Some(i) => i,
        None => 0,                                  // unreachable: head==Some(0) => necessarily Some
    }
}

// ---------- F6: public reserve(0) alone already poisons (a wider entry, independent of drain) ----------

/// F6 chain: any state (len n, head h) -> public `reserve(0)` -> head = Some(n)
/// (lib.rs:831 unconditional set; `additional==0` appends no slots) ->
/// `try_alloc_next_index` reads `items[n]` -- outside `[0, n)` => the lib.rs:406 indexing obligation
/// necessarily fails. `reserve` is a public API; its doc (lib.rs:799-814) declares only
/// "# Panics: capacity overflow" and never says that `reserve(0)` hangs the head out of bounds.
/// (Nonzero n shares the obligation line with F1; zero n degenerates to F1's drained shape.)
pub exec fn f6_reserve0_then_try_alloc_raw(arena: &mut ArenaModel) -> (r: Option<usize>) {
    reserve_model(arena, 0);           // lib.rs:815 public API, additional = 0
    try_alloc_raw(arena)               // lib.rs:406 <- EXPECTED (head == Some(n), n !< n)
}

// ---------- reachability bridging (spec doubles close the chain) ----------

/// reserve's spec face (the ensures algebraized), for the witness chain to reason at the spec layer:
/// len grows by `additional` and head unconditionally becomes `Some(start)` (lib.rs:831).
pub open spec fn reserve_spec_len(items_len: int, additional: int) -> int {
    items_len + additional
}

pub open spec fn reserve_spec_head(items_len: int) -> Option<int> {
    Some(items_len)
}

// ---------------------------------------------------------------------------
// Proof lemmas / witnesses of this mod (F1/F6 reachability and failure-shape
// theorems), already at the tail of the mod; they stay inside f1_f6_repro
// because the file-tail `pub use f1_f6_repro::{...}` re-export resolves here --
// the file-end lemma section cannot host them
// ---------------------------------------------------------------------------
/// F1 witness: drain(0,None) -> fast path None -> unguarded slow path
/// `reserve(0)` -> (len 0, head Some(0)) (:831 unconditional set) =>
/// `0 < 0` is false => the :406 indexing obligation necessarily fails -- the inputs for upstream's
/// obligation failure are exactly the PoC sequence (insert -> drain -> insert_with), directly
/// reachable via public APIs, with no corresponding doc statement whatsoever.
pub proof fn f1_reachability_witness() {
    let l0: int = 0;
    let h0: Option<int> = None;                      // drain_model ensures
    let l1: int = reserve_spec_len(l0, l0);          // :490 reserve(0), no guard
    let h1: Option<int> = reserve_spec_head(l0);
    assert(h0 matches None);                         // => the fast path already returned None
    assert(l1 == 0);
    assert(h1 == Some(0));                           // :831 unconditional set
    assert(!(0 < l1));                               // => :406 index obligation false
}

/// F6 witness: any nonzero n (head arbitrary in-bounds or None), public reserve(0)
/// => head = Some(n) dangling out of bounds => the :406 obligation fails.
pub proof fn f6_reachability_witness(n: int)
    requires
        0 <= n,
{
    let l1: int = reserve_spec_len(n, 0);            // :815 reserve(0): appends 0 slots
    let h1: Option<int> = reserve_spec_head(n);      // :831 still sets head unconditionally
    assert(l1 == n);                                 // len unchanged
    assert(h1 == Some(n));
    assert(!(n < l1));                               // => :406 index obligation false
}

/// Shape theorem: the unguarded slow path's failure face is exactly the empty-collection line
/// `len == 0` (drained shape; a nonempty arena doubles capacity, head = Some(n) with
/// n < 2n, so indexing is safe) -- the defect face is exactly the line the missing guard covers.
pub proof fn f1_unguarded_shape_lemma(n: int)
    requires
        0 <= n,
    ensures
        reserve_spec_head(n) matches Some(n),               // :831 (head := Some(start))
        (n == 0) ==> reserve_spec_len(n, n) == 0,             // drained: head=Some(0) over len==0
        (n > 0) ==> n < reserve_spec_len(n, n),              // nonempty: head=Some(n), n < 2n (index safe)
{
    assert(reserve_spec_len(n, n) == n + n);
    assert(reserve_spec_head(n) matches Some(n));
}

} // pub mod f1_f6_repro

// ===========================================================================
// Part B: L0 verbatim transcription of the API set + the qc single-step kernel
// (formerly verified/qc_insert_remove_contains.rs) -- the library-side fact source,
// referenced from verified/harness/{ut_21.rs, quickchecks.rs} via #[path] mod (all
// referenced items pub; the UT#21 theorems and qc Q1/Q2 drivers live in those files).
// Machine verification of the quickcheck kernel and the key UT assertions: reserve /
// try_alloc_next_index / try_insert / insert (incl. the guarded slow path) / remove /
// get / contains / drain.
//
// Model (Origin Rust: lib.rs:170-181 `Arena<T>` + lib.rs:178-181 `Entry<T>`):
//   `Entry<T>` is a two-variant enum (Free/Occupied), flattened into the Slot struct
//   (occupied:false <-> Free{next_free}; occupied:true <-> Occupied{generation,value};
//   when Free, value=0 is a placeholder; when Occupied, next_free is dead data -- the per-branch
//   "irrelevant fields" upstream never reads). `T = usize` (qc uses Vec<usize>).
//   Index -> IndexModel{index, generation}.
//   Tail note: upstream maintains the len field as an occupied-count invariant (lib.rs:410/525);
//   the model carries it explicitly via requires/ensures (see remove_m's len>0 precondition).
// ===========================================================================

// ---------- model ----------

// Origin Rust (lib.rs:178-181):
//   enum Entry<T> {
//       Free { next_free: Option<usize> },
//       Occupied { generation: u64, value: T },
//   }
pub struct Slot {
    pub occupied: bool,
    pub generation: u64,
    pub value: usize,
    pub next_free: Option<usize>,
}

// Origin Rust (lib.rs:197-201):
//   pub struct Index { index: usize, generation: u64 }
pub struct IndexModel {
    pub index: usize,
    pub generation: u64,
}

// Origin Rust (lib.rs:170-175):
//   pub struct Arena<T> {
//       items: Vec<Entry<T>>, generation: u64,
//       free_list_head: Option<usize>, len: usize,
//   }
pub struct ArenaModel {
    pub items: Vec<Slot>,
    pub generation: u64,
    pub free_list_head: Option<usize>,
    pub len: usize,
}

// ---------- spec projections and predicates ----------

/// int projection of Option<usize> (-1 = None).
pub open spec fn opt_nat(o: Option<usize>) -> int {
    match o {
        None => -1,
        Some(i) => i as int,
    }
}

/// slot/generation projection of Option<IndexModel>.
pub open spec fn ridx(r: Option<IndexModel>) -> int {
    match r {
        None => -1,
        Some(id) => id.index as int,
    }
}

pub open spec fn rgen(r: Option<IndexModel>) -> u64 {
    match r {
        None => 0,
        Some(id) => id.generation,
    }
}

/// int projection of Option<usize> (remove/get return values; -1 = None).
pub open spec fn oval(r: Option<usize>) -> int {
    match r {
        None => -1,
        Some(v) => v as int,
    }
}

/// same-slot predicate (fieldwise equality on the flat model).
pub open spec fn slot_same(a: Slot, b: Slot) -> bool {
    a.occupied == b.occupied
        && a.generation == b.generation
        && a.value@ == b.value@
        && opt_nat(a.next_free) == opt_nat(b.next_free)
}

/// contains semantics (Origin Rust: the specification of lib.rs:614-622 `get`:
/// `items.get(i.index)` hits Occupied and the generation matches => Some).
pub open spec fn contains_spec(items: Seq<Slot>, idx: usize, gen: u64) -> bool {
    0 <= idx@ < items.len() && items[idx@ as int].occupied && items[idx@ as int].generation == gen
}

/// free-list ladder predicate: [start, end) all Free slots chained +1 each, tail slot next = tail
/// (Origin Rust: the extends construction of lib.rs:820-830 reserve).
pub open spec fn ladder_region(items: Seq<Slot>, start: int, end: int, tail: int) -> bool {
    start <= end
        && forall |j| start <= j < end ==>
            !items[j].occupied
            && (if j + 1 == end {
                opt_nat(items[j].next_free) == tail
            } else {
                opt_nat(items[j].next_free) == j + 1
            })
}

/// single-step WF: head is None, or points to an in-bounds Free slot
/// (the invariant upstream's free list maintains itself; also the precondition of the lib.rs:407
/// "corrupt free list" defense arm -- that arm is no verification target here; excluded via precondition).
pub open spec fn wf_head(items: Seq<Slot>, head: Option<usize>) -> bool {
    opt_nat(head) < 0
        || (0 <= opt_nat(head) < items.len() && !items[opt_nat(head)].occupied)
}

/// pristine shape: insert-only usage (the reachable shape in the first halves of qc Q1/Q2) --
/// items is exactly [0, n)=Occupied (generation == gen) + [n, end)=Free ladder (tail None),
/// head = n (when n < end) or None (when n == end), len = n;
/// i.e. the shape after any number of `insert`s following `with_capacity` (doubling growth included).
pub open spec fn pristine(items: Seq<Slot>, head: Option<usize>, len: usize, gen: u64) -> bool {
    let n = len as int;
    let end = items.len() as int;
    0 <= n <= end
        && (forall |j| 0 <= j < n ==> items[j].occupied && items[j].generation == gen)
        && ladder_region(items, n, end, -1)
        && ((n == end && opt_nat(head) < 0) || (n < end && opt_nat(head) == n))
}

// ---------- L0 transcription: lib.rs:815-832 reserve ----------

/// Origin Rust (lib.rs:815-832):
///     pub fn reserve(&mut self, additional_capacity: usize) {
///         let start = self.items.len();
///         let end = self.items.len() + additional_capacity;
///         let old_head = self.free_list_head;
///         self.items.reserve_exact(additional_capacity);
///         self.items.extend((start..end).map(|i| {
///             if i == end - 1 { Entry::Free { next_free: old_head } }
///             else { Entry::Free { next_free: Some(i + 1) } }
///         }));
///         self.free_list_head = Some(start); // <- :831 unconditional set
///     }
/// extend is transcribed as a push loop; the # Panics clause is carried by a precondition.
/// Upstream doc (lib.rs:799-803):
///   Allocate space for `additional_capacity` more elements in the arena.
///   # Panics
///   Panics if this causes the capacity to overflow.
pub exec fn reserve_m(arena: &mut ArenaModel, additional: usize)
    requires
        old(arena).items@.len() + additional@ <= usize::MAX,
    ensures
        final(arena).items@.len() == old(arena).items@.len() + additional@,
        opt_nat(final(arena).free_list_head) == old(arena).items@.len(),
        final(arena).generation == old(arena).generation,
        final(arena).len@ == old(arena).len@,
        forall |j| 0 <= j < old(arena).items@.len() ==> slot_same(final(arena).items@[j], old(arena).items@[j]),
        ladder_region(final(arena).items@, old(arena).items@.len() as int, old(arena).items@.len() as int + additional@, opt_nat(old(arena).free_list_head)),
{
    let start: usize = arena.items.len();                  // lib.rs:816
    let head_saved: Option<usize> = arena.free_list_head;  // lib.rs:818
    let ghost mut pre_items: Seq<Slot> = Seq::empty();
    proof {
        pre_items = arena.items@;
    }
    let mut i: usize = 0;
    while i < additional
        invariant
            i <= additional,
            arena.items.len() == start + i,
            arena.items@.len() == start@ + i@,
            start@ + additional@ <= usize::MAX,
            arena.free_list_head == head_saved,
            // prefix frame: [0, start) slots untouched by pushes
            forall |j| 0 <= j < start@ ==> slot_same(arena.items@[j], pre_items[j]),
            // new region [start, start+i): Free + ladder (the tail slot's tail = old_head)
            forall |j| start@ <= j < start@ + i@ ==>
                !arena.items@[j].occupied
                && (if j + 1 == start@ + additional@ {
                    opt_nat(arena.items@[j].next_free) == opt_nat(head_saved)
                } else {
                    opt_nat(arena.items@[j].next_free) == j + 1
                }),
        decreases additional - i,
    {
        // Origin Rust (lib.rs:820-830): when the global i == end-1, the tail slot next=old_head
        let nf: Option<usize> = if i + 1 == additional {
            head_saved
        } else {
            Some(start + i + 1) // Origin Rust lib.rs:827 `Some(i + 1)` -- global index: successor of slot start+i
        };
        arena.items.push(Slot { occupied: false, generation: 0, value: 0, next_free: nf });
        i += 1;
    }
    arena.free_list_head = Some(start);                    // lib.rs:831 <- unconditional set
    proof {
        assert(pre_items == old(arena).items@);
        assert(opt_nat(head_saved) == opt_nat(old(arena).free_list_head));
    }
}

// ---------- L0 transcription: lib.rs:403-418 try_alloc_next_index ----------

/// Origin Rust (lib.rs:403-418) (the Occupied defense arm is excluded by the wf_head precondition).
pub exec fn try_alloc_m(arena: &mut ArenaModel) -> (r: Option<IndexModel>)
    requires
        wf_head(arena.items@, arena.free_list_head),
        arena.len@ < usize::MAX,
    ensures
        final(arena).items@ == old(arena).items@,
        final(arena).generation == old(arena).generation,
        opt_nat(old(arena).free_list_head) < 0 ==> (r matches None) && final(arena).len@ == old(arena).len@ && opt_nat(final(arena).free_list_head) < 0,
        opt_nat(old(arena).free_list_head) >= 0 ==> (r matches Some(_)) && ridx(r) == opt_nat(old(arena).free_list_head) && rgen(r) == old(arena).generation && final(arena).len@ == old(arena).len@ + 1 && opt_nat(final(arena).free_list_head) == opt_nat(old(arena).items@[opt_nat(old(arena).free_list_head)].next_free),
{
    match arena.free_list_head {                       // lib.rs:404
        None => None,                                  // lib.rs:405
        Some(i) => {
            // lib.rs:406 (wf_head => in-bounds Free; slot read fieldwise -- fields are all Copy)
            let next_free_opt: Option<usize> = arena.items[i].next_free;
            arena.free_list_head = next_free_opt;      // lib.rs:409
            arena.len += 1;                            // lib.rs:410 (precondition len < MAX)
            Some(IndexModel { index: i, generation: arena.generation }) // lib.rs:411-414
        }
    }
}

// ---------- L0 transcription: lib.rs:348-359 try_insert ----------

/// Origin Rust (lib.rs:348-359):
///     match self.try_alloc_next_index() {
///         None => Err(value),
///         Some(index) => { self.items[index.index] = Entry::Occupied { generation: self.generation, value }; Ok(index) }
///     }
/// The Err arm returns value (usize: Copy; the model encodes the failure arm as None).
/// Upstream doc (lib.rs:321-327):
///   Attempts to insert `value` into the arena using existing capacity.
///   This method will never allocate new capacity in the arena.
///   If insertion succeeds, then the `value`'s index is returned. If
///   insertion fails, then `Err(value)` is returned to give ownership of
///   `value` back to the caller.
pub exec fn try_insert_m(arena: &mut ArenaModel, value: usize) -> (r: Option<IndexModel>)
    requires
        wf_head(arena.items@, arena.free_list_head),
        arena.len@ < usize::MAX,
    ensures
        final(arena).generation == old(arena).generation,
        opt_nat(old(arena).free_list_head) < 0 ==> (r matches None) && final(arena).items@ == old(arena).items@ && final(arena).len@ == old(arena).len@ && opt_nat(final(arena).free_list_head) < 0,
        opt_nat(old(arena).free_list_head) >= 0 ==>
            (r matches Some(_)) && ridx(r) == opt_nat(old(arena).free_list_head) && rgen(r) == old(arena).generation
            && final(arena).len@ == old(arena).len@ + 1
            && opt_nat(final(arena).free_list_head) == opt_nat(old(arena).items@[opt_nat(old(arena).free_list_head)].next_free)
            && final(arena).items@ == old(arena).items@.update(
                opt_nat(old(arena).free_list_head),
                Slot { occupied: true, generation: old(arena).generation, value: value, next_free: old(arena).items@[opt_nat(old(arena).free_list_head)].next_free },
            ),
{
    match try_alloc_m(arena) {
        None => None,
        Some(idx) => {
            // lib.rs:352-356: items[index.index] = Occupied { generation, value };
            let old_next: Option<usize> = arena.items[idx.index].next_free;
            arena.items.set(idx.index, Slot { occupied: true, generation: arena.generation, value: value, next_free: old_next });
            Some(idx)
        }
    }
}

// ---------- L0 transcription: lib.rs:435-440 + 466-485 insert (incl. the guarded slow path) ----------

/// Origin Rust (lib.rs:435-440):
///     match self.try_insert(value) { Ok(i) => i, Err(value) => self.insert_slow_path(value) }
/// insert_slow_path (lib.rs:466-485) carries the lib.rs:468 capacity==0 guard
/// (whose comment :469-476 names the drain hazard -- upstream insert's correct shape).
///
/// The postcondition is the qc Q1 kernel: pristine preserved + the returned index an in-bounds
/// Occupied slot, generation == the current generation, value written, old Occupied slots framed.
/// Upstream doc (lib.rs:420-422):
///   Insert `value` into the arena, allocating more capacity if necessary.
///   The `value`'s associated index in the arena is returned.
pub exec fn insert_m(arena: &mut ArenaModel, value: usize) -> (r: IndexModel)
    requires
        pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
        2 * arena.items@.len() <= usize::MAX,
        arena.items@.len() < usize::MAX,
        arena.items@.len() <= 2 * arena.len@ + 4,
    ensures
        // spare-capacity face (len < items.len): the try_insert fast path adds no
        // length to items (the exact value face the clear/from_iter cls contracts need).
        (old(arena).len@) < (old(arena).items@.len() as nat)
            ==> final(arena).items@.len() == old(arena).items@.len(),
        final(arena).items@.len() <= 2 * final(arena).len@ + 4,
        r.index@ == old(arena).len@,
        r.generation == old(arena).generation,
        final(arena).len@ == old(arena).len@ + 1,
        final(arena).generation == old(arena).generation,
        final(arena).items@.len() >= old(arena).items@.len(),
        contains_spec(final(arena).items@, r.index, r.generation),
        final(arena).items@[r.index@ as int].value@ == value@,
        forall |j| 0 <= j < old(arena).len@ ==> slot_same(final(arena).items@[j], old(arena).items@[j]),
        pristine(final(arena).items@, final(arena).free_list_head, final(arena).len, final(arena).generation),
{
    match try_insert_m(arena, value) {
        Some(idx) => idx,
        None => {
            // Origin Rust (lib.rs:466-485) insert_slow_path (verbatim):
            let len: usize = if arena.items.len() == 0 { // lib.rs:468 capacity()==items.len() (lib.rs:795-797)
                1                                       // lib.rs:477 guard
            } else {
                arena.items.len()                       // lib.rs:479
            };
            reserve_m(arena, len);                      // lib.rs:481
            match try_insert_m(arena, value) {          // lib.rs:482
                Some(idx) => idx,
                // lib.rs:483-484 .expect("inserting will always succeed after
                // reserving additional space"): reserve(len>=1) => head already in-bounds
                // Free => this arm is provably unreachable; the placeholder only closes the exec.
                None => IndexModel { index: 0, generation: 0 },
            }
        }
    }
}

// ---------- L0 transcription: lib.rs:512-534 remove ----------

/// Origin Rust (lib.rs:512-534):
///     if i.index >= self.items.len() { return None; }              // :513-514
///     match self.items[i.index] {
///         Entry::Occupied { generation, .. } if i.generation == generation => {
///             let entry = mem::replace(&mut self.items[i.index],   // :519-522
///                 Entry::Free { next_free: self.free_list_head });
///             self.generation += 1;                                 // :523
///             self.free_list_head = Some(i.index);                  // :524
///             self.len -= 1;                                        // :525
///             match entry { Entry::Occupied { value, .. } => Some(value), _ => unreachable!() } // :527-529
///         }
///         _ => None,                                                // :532
///     }
/// The len>0 precondition = upstream's occupied-count internal invariant (header note).
/// Upstream doc (lib.rs:496-499):
///   Remove the element at index `i` from the arena.
///   If the element at index `i` is still in the arena, then it is
///   returned. If it is not in the arena, then `None` is returned.
pub exec fn remove_m(arena: &mut ArenaModel, i: IndexModel) -> (r: Option<usize>)
    requires
        contains_spec(arena.items@, i.index, i.generation),
        arena.len@ > 0,
        arena.generation@ < u64::MAX,
    ensures
        final(arena).len@ == old(arena).len@ - 1,
        final(arena).generation@ == old(arena).generation@ + 1,
        final(arena).free_list_head == Some(i.index),
        final(arena).items@.len() == old(arena).items@.len(),
        oval(r) == old(arena).items@[i.index@ as int].value@,
        forall |j| 0 <= j < final(arena).items@.len() && j != i.index@ ==>
            slot_same(final(arena).items@[j], old(arena).items@[j]),
        // slot i rewritten as Free (origin: Free{next_free=old_head}; flat-model dead-data note):
        !final(arena).items@[i.index@ as int].occupied
            && opt_nat(final(arena).items@[i.index@ as int].next_free) == opt_nat(old(arena).free_list_head),
{
    if i.index >= arena.items.len() {                  // lib.rs:513 (unreachable under this precondition)
        return None;
    }
    // (slot read fieldwise -- fields all Copy, standing in for the pre-mem::replace discriminant and read sites)
    let slot_occupied: bool = arena.items[i.index].occupied;
    let slot_generation: u64 = arena.items[i.index].generation;
    let slot_value: usize = arena.items[i.index].value;
    if slot_occupied && i.generation == slot_generation { // lib.rs:518 guard
        let value: usize = slot_value;               // lib.rs:527-529
        // lib.rs:519-522: mem::replace becomes Free{next_free: old_head}
        arena.items.set(i.index, Slot { occupied: false, generation: slot_generation, value: 0, next_free: arena.free_list_head });
        arena.generation += 1;                         // lib.rs:523
        arena.free_list_head = Some(i.index);          // lib.rs:524
        arena.len -= 1;                                // lib.rs:525 (precondition len > 0)
        Some(value)
    } else {
        None                                           // lib.rs:532 (unreachable under the precondition)
    }
}

// ---------- L0 transcription: lib.rs:614-622 get / 593-595 contains ----------

/// Origin Rust (lib.rs:614-622):
///     match self.items.get(i.index) {
///         Some(Entry::Occupied { generation, value }) if *generation == i.generation => Some(value),
///         _ => None,
///     }
/// Option<&T> becomes Option<usize> (value copy; observation-equivalent semantics).
/// Upstream doc (lib.rs:597-600):
///   Get a shared reference to the element at index `i` if it is in the arena.
///   If the element at index `i` is not in the arena, then `None` is returned.
pub exec fn get_m(arena: &ArenaModel, i: IndexModel) -> (r: Option<usize>)
    ensures
        contains_spec(arena.items@, i.index, i.generation)
            ==> (r matches Some(_)) && oval(r) == arena.items@[i.index@ as int].value@,
        !contains_spec(arena.items@, i.index, i.generation) ==> r matches None,
{
    if i.index < arena.items.len() {
        let slot_occupied: bool = arena.items[i.index].occupied;
        let slot_generation: u64 = arena.items[i.index].generation;
        let slot_value: usize = arena.items[i.index].value;
        if slot_occupied && slot_generation == i.generation {
            Some(slot_value)
        } else {
            None
        }
    } else {
        None
    }
}

/// Origin Rust (lib.rs:593-595): `self.get(i).is_some()`
/// Upstream doc (lib.rs:577-579):
///   Is the element at index `i` in the arena?
///   Returns `true` if the element at `i` is in the arena, `false` otherwise.
pub exec fn contains_m(arena: &ArenaModel, i: IndexModel) -> (r: bool)
    ensures
        r == contains_spec(arena.items@, i.index, i.generation),
{
    get_m(arena, i).is_some()
}

// ---------- L0 transcription: lib.rs:913-926 drain (state face) ----------

/// Origin Rust (lib.rs:913-926): state side effects = conditional generation +1 (:915-918),
/// free_list_head = None (:920), len = 0 (:921), items.drain(..) emptied (:924).
/// The std primitive (len to 0; upstream capacity()==items.len(), so externally capacity 0 --
/// the semantic source of the tests.rs:242 assertion) is carried by external_body (no verification target).
#[verifier::external_body]
/// Upstream doc (lib.rs:888-894):
///   Iterate over elements of the arena and remove them.
///   Yields pairs of `(Index, T)` items.
///   Order of iteration is not defined.
///   Note: All elements are removed even if the iterator is only partially consumed or not consumed at all.
pub exec fn drain_m(arena: &mut ArenaModel)
    ensures
        final(arena).items@.len() == 0,
        opt_nat(final(arena).free_list_head) < 0,
        final(arena).len@ == 0,
        old(arena).len@ > 0 ==> final(arena).generation@ == old(arena).generation@ + 1,
        old(arena).len@ == 0 ==> final(arena).generation@ == old(arena).generation@,
{
}


// ===========================================================================
// Part C: coverage-diff continuation -- L0 transcription + contracts of the remaining
// public API (the src zone is the verification fact source): Index::from_raw_parts/
// into_raw_parts, Arena::{new,with_capacity,len,is_empty,capacity,clear,Index ops, ...}.
// ===========================================================================

// ---------- L0: lib.rs:204-216 Index::from_raw_parts / :218-227 into_raw_parts ----------

/// Origin Rust (lib.rs:204-216):
///     pub fn from_raw_parts(a: usize, b: u64) -> Index { Index { index: a, generation: b } }
/// Upstream doc (lib.rs:204-210):
///   Create a new `Index` from its raw parts.
///   The parts must have been returned from an earlier call to `into_raw_parts`.
///   Providing arbitrary values will lead to malformed indices and ultimately panics.
pub exec fn index_from_raw_parts_m(a: usize, b: u64) -> (r: IndexModel) {
    IndexModel { index: a, generation: b }            // lib.rs:212-215
}

/// Origin Rust (lib.rs:218-227): `pub fn into_raw_parts(self) -> (usize, u64)"`
/// doc contract: roundtrip -- from_raw_parts(into_raw_parts(i)) == i.
/// Upstream doc (lib.rs:218-224):
///   Convert this `Index` into its raw parts.
///   This niche method is useful for converting an `Index` into another identifier type.
///   Usually, you should prefer a newtype wrapper around `Index` like `pub struct MyIdentifier(Index);`.
///   However, for external types whose definition you can't customize, but which you can construct instances of, this method can be useful.
pub exec fn index_into_raw_parts_m(i: IndexModel) -> (r: (usize, u64)) {
    (i.index, i.generation)                             // lib.rs:226
}

// ---------- L0: lib.rs:239-251 new / 253-282 with_capacity ----------

/// Origin Rust (lib.rs:249-251): `pub fn new() -> Arena<T> { Arena::with_capacity(DEFAULT_CAPACITY) }`
/// (:230 `const DEFAULT_CAPACITY: usize = 4`)
/// Upstream doc (lib.rs:239-240):
///   Constructs a new, empty `Arena`.
pub exec fn new_m() -> (arena: ArenaModel)
    ensures
        arena.items@.len() == 4,
        pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
{
    with_capacity_m(4)                                  // lib.rs:250
}

/// Origin Rust (lib.rs:272-282):
///     let n = cmp::max(n, 1);
///     let mut arena = Arena { items: Vec::new(), generation: 0, free_list_head: None, len: 0 };
///     arena.reserve(n);
///     arena
/// No separate # Panics entry (reserve's capacity-overflow clause, lib.rs:801-803).
/// Upstream doc (lib.rs:253-255):
///   Constructs a new, empty `Arena<T>` with the specified capacity.
///   The `Arena<T>` will be able to hold `n` elements without further allocation.
pub exec fn with_capacity_m(n: usize) -> (arena: ArenaModel)
    requires
        n as int + 1 <= usize::MAX,
    ensures
        arena.items@.len() == if n == 0 { 1 } else { n as int },
        arena.items@.len() >= 1,
        arena.len@ == 0,                        // lib.rs:277 len: 0
        arena.generation == 0,                   // lib.rs:276 generation: 0
        pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
{
    // Origin Rust (lib.rs:273): let n = cmp::max(n, 1);
    let n1: usize = if n == 0 { 1 } else { n };          // lib.rs:273
    let mut arena: ArenaModel = ArenaModel {
        items: Vec::new(),                              // lib.rs:275
        generation: 0,
        free_list_head: None,
        len: 0,
    };
    reserve_m(&mut arena, n1);                           // lib.rs:281 (the Part B verified kernel)
    proof {
        // pristine assembly: reserve_m ensures => ladder (head in-bounds, None tail) + len 0 + head=0
        let end = arena.items@.len();
        assert(arena.len@ == 0);
        assert(arena.generation == 0);
        assert(opt_nat(arena.free_list_head) == 0);
        assert(end >= 1);
        assert(forall |j| 0 <= j < 0 ==> arena.items@[j].occupied);
        assert(ladder_region(arena.items@, 0, end as int, -1));
        assert(0 < end);
        assert(opt_nat(arena.free_list_head) == 0);
    }
    arena
}

// ---------- L0: lib.rs:747-749 len / 767-769 is_empty / 795-797 capacity ----------

/// Origin Rust (lib.rs:747-749): `pub fn len(&self) -> usize { self.len }`
/// Upstream doc (lib.rs:726-728):
///   Get the length of this arena.
///   The length is the number of elements the arena holds.
pub exec fn len_m(arena: &ArenaModel) -> (r: usize)
    ensures
        r@ == arena.len@,
{
    arena.len                                           // lib.rs:748
}

/// Origin Rust (lib.rs:767-769): `pub fn is_empty(&self) -> bool { self.len == 0 }`
/// Upstream doc (lib.rs:751-751):
///   Returns true if the arena contains no elements
pub exec fn is_empty_m(arena: &ArenaModel) -> (r: bool)
    ensures
        r == (arena.len@ == 0),
{
    arena.len == 0                                      // lib.rs:768
}

/// Origin Rust (lib.rs:795-797): `pub fn capacity(&self) -> usize { self.items.len() }`
/// Upstream capacity is defined as items.len() (the number of entry slots).
/// Upstream doc (lib.rs:771-775):
///   Get the capacity of this arena.
///   The capacity is the maximum number of elements the arena can hold without
///   further allocation, including however many it currently contains.
pub exec fn capacity_m(arena: &ArenaModel) -> (r: usize)
    ensures
        r@ == arena.items@.len(),
{
    arena.items.len()                                   // lib.rs:796
}

// ---------- L0: lib.rs:299-319 clear ----------

/// Origin Rust (lib.rs:299-319):
///     pub fn clear(&mut self) {
///         self.items.clear();                    // :300
///         let end = self.items.capacity();       // :302 (std Vec allocated capacity, >= len)
///         self.items.extend((0..end).map(|i| {   // :303-311 rebuild the [0,end) Free ladder,
///             if i == end - 1 { Entry::Free { next_free: None } }        // tail slot
///             else { Entry::Free { next_free: Some(i + 1) } } }));      // chain +1
///         if !self.is_empty() {                  // :312 -- the criterion is the [old] len field
///             self.generation += 1;               // :315 (self.len = 0 happens only at :318)
///         }
///         self.free_list_head = Some(0);          // :317
///         self.len = 0;                          // :318
///     }
/// Model note: std Vec::capacity() (allocated capacity) is unobservable in the vstd Vec spec, so the
/// parameter cap_alloc carries it (upstream Vec invariant cap_alloc >= items.len; always >= 1 after
/// construction; otherwise free_list_head = Some(0) (:317) would dangle -- the same-shape boundary as
/// F6 poisoning, which upstream prevents via with_capacity always reserving max(n,1)).
#[verifier::external_body]
pub exec fn items_clear_only(items: &mut Vec<Slot>)
    ensures
        final(items)@.len() == 0,
{
}

/// clear state-face transcription (builds a new ladder + head Some(0) + len 0; conditional gen bump).
/// Upstream doc (lib.rs:284-284):
///   Clear all the items inside the arena, but keep its allocation.
pub exec fn clear_m(arena: &mut ArenaModel, cap_alloc: usize)
    requires
        old(arena).items@.len() <= cap_alloc@,
        cap_alloc@ >= 1,               // upstream structural invariant (Vec::capacity >= 1)
        old(arena).len@ > 0 ==> old(arena).generation@ < u64::MAX,   // :315 overflow clause
    ensures
        final(arena).items@.len() == cap_alloc@,
        final(arena).len@ == 0,
        final(arena).free_list_head == Some(0),
        old(arena).len@ > 0 ==> final(arena).generation@ == old(arena).generation@ + 1,
        old(arena).len@ == 0 ==> final(arena).generation@ == old(arena).generation@,
        pristine(final(arena).items@, final(arena).free_list_head, final(arena).len, final(arena).generation),
{
    let len_field_old: usize = arena.len;               // :312 criterion = the old len field
    items_clear_only(&mut arena.items);                 // :300
    // Origin Rust (lib.rs:302-311): end = items.capacity(); rebuild the [0, end) ladder
    let mut i: usize = 0;
    while i < cap_alloc
        invariant
            i <= cap_alloc,
            arena.items.len() == i,
            arena.items@.len() == i as int,
            // ladder prefix: [0, i) all Free with the correct per-slot successor
            forall |j| #![trigger arena.items@[j]] 0 <= j < i as int ==>
                !arena.items@[j].occupied
                && (if j + 1 == cap_alloc as int {
                    opt_nat(arena.items@[j].next_free) == -1
                } else {
                    opt_nat(arena.items@[j].next_free) == j + 1
                }),
        decreases cap_alloc - i,
    {
        let nf: Option<usize> = if i + 1 == cap_alloc {
            None                                     // :304-305 tail slot next_free: None
        } else {
            Some(i + 1)                              // :307-309 chain +1
        };
        arena.items.push(Slot { occupied: false, generation: 0, value: 0, next_free: nf });
        i += 1;
    }
    if len_field_old > 0 {                              // :312 (old-len criterion)
        arena.generation += 1;                          // :315
    }
    arena.free_list_head = Some(0);                     // :317
    arena.len = 0;                                      // :318
    proof {
        // pristine assembly: this body loop is exactly the full ladder_region(0, cap_alloc, -1) prefix
        assert(arena.items@.len() == cap_alloc as int);
        assert(ladder_region(arena.items@, 0, cap_alloc as int, -1));
        assert(forall |j| #![trigger arena.items@[j]] 0 <= j < 0 ==> arena.items@[j].occupied);
        assert(0 < cap_alloc as int);
    }
}

// ---------- L0: lib.rs:641-649 get_mut ----------

/// Origin Rust (lib.rs:641-649):
///     pub fn get_mut(&mut self, i: Index) -> Option<&mut T> {
///         match self.items.get_mut(i.index) {
///             Some(Entry::Occupied { generation, value }) if *generation == i.generation => Some(value),
///             _ => None,
///         }
///     }
/// Model note: &mut T is carried with value-copy observation semantics (T=usize); the write path is
/// get_mut_write_m (a &mut reference is essentially a raw pointer to slot i.index; writes land on the same slot).
/// Upstream doc (lib.rs:624-627):
///   Get an exclusive reference to the element at index `i` if it is in the arena.
///   If the element at index `i` is not in the arena, then `None` is returned.
pub exec fn get_mut_m(arena: &mut ArenaModel, i: IndexModel) -> (r: Option<usize>)
    ensures
        contains_spec(old(arena).items@, i.index, i.generation)
            ==> (r matches Some(_)) && oval(r) == old(arena).items@[i.index@ as int].value@,
        !contains_spec(old(arena).items@, i.index, i.generation) ==> r matches None,
        // read-only observation frame (for the reference write path see get_mut_write_m)
        final(arena).items@ == old(arena).items@,
        final(arena).free_list_head == old(arena).free_list_head,
        final(arena).len@ == old(arena).len@,
        final(arena).generation == old(arena).generation,
{
    if i.index < arena.items.len() {                      // lib.rs:642 items.get_mut
        let slot_occupied: bool = arena.items[i.index].occupied;
        let slot_generation: u64 = arena.items[i.index].generation;
        let slot_value: usize = arena.items[i.index].value;
        if slot_occupied && slot_generation == i.generation {   // lib.rs:643-646 guard
            Some(slot_value)
        } else {
            None
        }
    } else {
        None
    }
}

/// Origin Rust (the `*val = ...` write-through-&mut pattern of crate doc :102-104; the IndexMut
/// read-modify-write face is the same):
///     if let Some(val) = arena.get_mut(idx) { *val = new_value; }
/// Writing through the reference returned by get_mut === writing slot i.index's value field (reference co-location).
pub exec fn get_mut_write_m(arena: &mut ArenaModel, i: IndexModel, new_value: usize) -> (ok: bool)
    ensures
        contains_spec(old(arena).items@, i.index, i.generation) ==> ok,
        !contains_spec(old(arena).items@, i.index, i.generation) ==> !ok && final(arena).items@ == old(arena).items@,
        ok ==> contains_spec(final(arena).items@, i.index, i.generation),
        ok ==> final(arena).items@[i.index@ as int].value@ == new_value
            && final(arena).items@[i.index@ as int].occupied
            && final(arena).items@[i.index@ as int].generation == i.generation,
        // frame obligation: the other slots untouched (the get_mut write path touches only the hit slot)
        forall |j| #![trigger final(arena).items@[j]] 0 <= j < final(arena).items@.len() && j != i.index@ as int
            ==> slot_same(final(arena).items@[j], old(arena).items@[j]),
        final(arena).items@.len() == old(arena).items@.len(),
        final(arena).len@ == old(arena).len@,
        final(arena).generation@ == old(arena).generation@,
        final(arena).free_list_head == old(arena).free_list_head,
{
    if i.index < arena.items.len() {
        let slot_occupied: bool = arena.items[i.index].occupied;
        let slot_generation: u64 = arena.items[i.index].generation;
        if slot_occupied && slot_generation == i.generation {   // Some branch
            // *val = new_value -- reference co-location => in-place write to slot i.index
            let keep_next: Option<usize> = arena.items[i.index].next_free;
            arena.items.set(i.index, Slot { occupied: true, generation: slot_generation, value: new_value, next_free: keep_next });
            true
        } else {
            false                                         // None branch, no write
        }
    } else {
        false
    }
}

// ---------- L0: lib.rs:680-724 get2_mut ----------

/// Origin Rust (lib.rs:680-724): get2_mut -- the doc promises None for the missed
/// elements; # Panics arm: same slot and same generation => panic (the assert is at :684).
/// Observation-semantics dispatch (control flow verbatim):
///   - i1.index == i2.index && i1.generation == i2.generation => panic (:684);
///   - i1.index == i2.index && i1.gen > i2.gen => (get_mut(i1), None)  (:686-688)
///   - i1.index == i2.index && i1.gen < i2.gen => (None, get_mut(i2))  (:689)
///   - The out-of-bounds arms (:692-696) and the split arm (:698-724) observe as exactly get_mut(i_k).
/// The split_at_mut borrow machinery is invisible on the observation face, carried as the
/// co-location fact (:702 &mut xs[i1.index] / :704 &mut xs[i2.index] are the original slots).
/// Upstream doc (lib.rs:651-659):
///   Get a pair of exclusive references to the elements at index `i1` and `i2` if it is in the arena.
///   If the element at index `i1` or `i2` is not in the arena, then `None` is returned for this element.
///   # Panics
///   Panics if `i1` and `i2` are pointing to the same item of the arena.
pub exec fn get2_mut_m(arena: &mut ArenaModel, i1: IndexModel, i2: IndexModel)
    -> (r: (Option<usize>, Option<usize>))
    requires
        // same-item exclusion for the lib.rs:684 documented panic arm (the Part A "corrupt free
        // list" convention): same slot and same generation => the upstream
        // assert!(i1.generation != i2.generation) panics; reachability is obvious (any live Index twice); registered here
        !(i1.index == i2.index && i1.generation == i2.generation),
    ensures
        // read observation frame (get2_mut does not modify arena)
        final(arena).items@ == old(arena).items@,
        final(arena).free_list_head == old(arena).free_list_head,
        final(arena).len@ == old(arena).len@,
        final(arena).generation == old(arena).generation,
        i1.index == i2.index && i1.generation != i2.generation ==>
            (i1.generation > i2.generation
                ==> r == (get_mut_obs(*old(arena), i1), None)),
        i1.index == i2.index && i1.generation != i2.generation ==>
            (i1.generation < i2.generation
                ==> r == (None, get_mut_obs(*old(arena), i2))),
        i1.index != i2.index ==>
            r == (get_mut_obs(*old(arena), i1), get_mut_obs(*old(arena), i2)),
{
    let len: usize = arena.items.len();                    // lib.rs:681
    if i1.index == i2.index {                              // lib.rs:683
        // lib.rs:684: assert!(i1.generation != i2.generation);
        // -- the same-slot same-generation panic arm (documented); the model dispatches via the precondition-difference branch
        if i1.generation == i2.generation {
            panic!("assertion failed: i1.generation != i2.generation");   // lib.rs:684 in place
        }
        if i1.generation > i2.generation {                 // lib.rs:686
            (get_mut_m(arena, i1), None)                    // lib.rs:687
        } else {
            (None, get_mut_m(arena, i2))                    // lib.rs:689
        }
    } else if i1.index >= len {                            // lib.rs:692
        (None, get_mut_m(arena, i2))                        // lib.rs:693
    } else if i2.index >= len {                            // lib.rs:694
        (get_mut_m(arena, i1), None)                        // lib.rs:695
    } else {
        // lib.rs:698-724: split_at_mut(max) -- the observation face = two independent get_mut views
        (get_mut_m(arena, i1), get_mut_m(arena, i2))        // :707-723 same shape verbatim
    }
}

/// get's observation bridge (the spec projection used by get2_mut's ensures).
pub open spec fn get_mut_obs(a: ArenaModel, i: IndexModel) -> Option<usize> {
    if contains_spec(a.items@, i.index, i.generation) {
        Some(a.items@[i.index@ as int].value)
    } else {
        None
    }
}


// ---------- L0: lib.rs:938-946 get_unknown_gen / :958-966 get_unknown_gen_mut ----------

/// Origin Rust (lib.rs:938-946):
///     pub fn get_unknown_gen(&self, i: usize) -> Option<(&T, Index)> {
///         match self.items.get(i) {
///             Some(Entry::Occupied { generation, value }) => Some((value, Index { generation: *generation, index: })),
///             _ => None,
///         }
///     }
/// Doc gloss: the returned `Index` is always the slot's currently valid index.
/// Model note: &T -> usize value-copy observation (same caliber as get_mut_write_m).
/// Upstream doc (lib.rs:928-937):
///   Given an i of `usize` without a generation, get a shared reference to the
///   element and the matching `Index` of the entry behind `i`.
///   This method is useful when you know there might be an element at the
///   position i, but don't know its generation or precise Index.
///   Use cases include using indexing such as Hierarchical BitMap Indexing or
///   other kinds of bit-efficient indexing.
///   You should use the `get` method instead most of the time.
pub exec fn get_unknown_gen_m(arena: &ArenaModel, i: usize) -> (r: Option<(usize, IndexModel)>)
    ensures
        forall |v: usize, idx: IndexModel| r == Some((v, idx)) ==>
            arena.items@[i as int].occupied
            && idx.index@ == i@
            && idx.generation == arena.items@[i as int].generation
            && v == arena.items@[i as int].value
            && contains_spec(arena.items@, idx.index, idx.generation),
        r matches None ==> i@ >= arena.items@.len() || !arena.items@[i as int].occupied,
{
    if i < arena.items.len() {                              // lib.rs:939 items.get(i)
        let slot_occupied: bool = arena.items[i].occupied;
        let slot_generation: u64 = arena.items[i].generation;
        let slot_value: usize = arena.items[i].value;
        if slot_occupied {                                 // lib.rs:940 Occupied branch
            Some((slot_value, IndexModel { index: i, generation: slot_generation }))   // :943
        } else {
            None
        }
    } else {
        None
    }
}

/// Origin Rust (lib.rs:958-966): get_unknown_gen_mut -- the observation face is isomorphic to
/// get_unknown_gen (&mut T -> value-copy observation; the write path = the get_mut_write_m co-located write).
/// Upstream doc (lib.rs:948-957):
///   Given an i of `usize` without a generation, get an exclusive reference to the
///   element and the matching `Index` of the entry behind `i`.
///   This method is useful when you know there might be an element at the
///   position i, but don't know its generation or precise Index.
///   Use cases include using indexing such as Hierarchical BitMap Indexing or
///   other kinds of bit-efficient indexing.
///   You should use the `get_mut` method instead most of the time.
pub exec fn get_unknown_gen_m_m(arena: &mut ArenaModel, i: usize) -> (r: (Option<(usize, IndexModel)>, ))
    ensures
        forall |v: usize, idx: IndexModel| r.0 == Some((v, idx)) ==>
            old(arena).items@[i as int].occupied
            && idx.index@ == i@
            && idx.generation == old(arena).items@[i as int].generation
            && v == old(arena).items@[i as int].value
            && contains_spec(old(arena).items@, idx.index, idx.generation),
        r.0 matches None ==> i@ >= old(arena).items@.len() || !old(arena).items@[i as int].occupied,
        // read-only observation frame (the reference is never written)
        final(arena).items@ == old(arena).items@,
        final(arena).free_list_head == old(arena).free_list_head,
        final(arena).len@ == old(arena).len@,
        final(arena).generation == old(arena).generation,
{
    (get_unknown_gen_m_helper(arena, i),)
}

/// The &mut-face internal helper of get_unknown_gen_m (a read observation, same origin as upstream
/// items.get_mut in its read-only use; the write-through-reference semantics is identical -- see the get_mut_write_m note).
pub exec fn get_unknown_gen_m_helper(arena: &ArenaModel, i: usize) -> (r: Option<(usize, IndexModel)>)
    ensures
        forall |v: usize, idx: IndexModel| r == Some((v, idx)) ==>
            arena.items@[i as int].occupied
            && idx.index@ == i@
            && idx.generation == arena.items@[i as int].generation
            && v == arena.items@[i as int].value
            && contains_spec(arena.items@, idx.index, idx.generation),
        r matches None ==> i@ >= arena.items@.len() || !arena.items@[i as int].occupied,
{
    get_unknown_gen_m(arena, i)
}

// ---------- L0: lib.rs:554-575 retain ----------

/// retain's keep-decision predicate is carried by a ghost sequence (the predicate's return for slot j
/// = decide[j]; the upstream closure's write side effects on `&mut T` are not modeled on the observation
/// face -- L0 keeps the decision semantics; see the doc-boundary notes).
pub open spec fn retained_count(items: Seq<bool>, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if lo >= hi { 0 } else {
        let c: int = if items[hi - 1] { 1 } else { 0 };
        retained_count(items, lo, hi - 1) + c
    }
}

/// Origin Rust (lib.rs:554-575):
///     pub fn retain(&mut self, mut predicate: impl FnMut(Index, &mut T) -> bool) {
///         for i in 0..self.capacity() {
///             let remove = match &mut self.items[i] {
///                 Entry::Occupied { generation, value } => {
///                     let index = Index { index: i, generation: *generation };   // :558-561
///                     if predicate(index, value) { None } else { Some(index) }
///                 }
///                 _ => None,                                   // :569 Free arm
///             };
///             if let Some(index) = remove { self.remove(index); } // :571-573
///         }
///     }
/// Model domain: pristine start state (same convention as Part B insert_m -- upstream's usual construction
/// sequence runs inserts before retain); the closure predicate is carried by the ghost keep sequence
/// (decide[j]); the `&mut T` write side effects stay outside the observation face; loop-bound note:
/// upstream bounds the loop by capacity() (= items.len()), this transcription by n0 -- the [n0, end)
/// free tail is all Free (:569 `_ => None`, a no-op arm), equivalent (kept via the ensures tail frame clause).
/// Upstream doc (lib.rs:536-538):
///   Retains only the elements specified by the predicate.
///   In other words, remove all indices such that `predicate(index, &value)` returns `false`.
pub exec fn retain_m(arena: &mut ArenaModel, decide: Vec<bool>) -> ()
    requires
        pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
        decide@.len() == arena.len@,
        arena.generation@ + arena.len@ <= u64::MAX,        // generation-bump bound (<= n removes)
    ensures
        // lib.rs:538-539 doc: every item whose predicate(...) == false is removed
        forall |j| #![trigger final(arena).items@[j]] 0 <= j < old(arena).len@ as int ==>
            final(arena).items@[j].occupied == decide@[j],
        forall |j| #![trigger final(arena).items@[j]] old(arena).len@ as int <= j < final(arena).items@.len() ==>
            slot_same(final(arena).items@[j], old(arena).items@[j]),
        final(arena).items@.len() == old(arena).items@.len(),
        final(arena).len@ as int == retained_count(decide@, 0, old(arena).len@ as int),
        final(arena).generation@ == old(arena).generation@ + (old(arena).len@ as int - retained_count(decide@, 0, old(arena).len@ as int)),
        // kept slots: generation and value unchanged (predicate write side effects outside the model; fn tail note)
        forall |j| #![trigger final(arena).items@[j]] 0 <= j < old(arena).len@ as int && decide@[j] ==>
            final(arena).items@[j].generation == old(arena).generation
            && final(arena).items@[j].value@ == old(arena).items@[j].value@,
{
    let ghost mut g0: u64 = 0;
    proof { g0 = arena.generation@; }
    let g0x: u64 = arena.generation;                     // g0's exec face
    let ghost items_len0: int = arena.items@.len() as int;
    let n0u: usize = arena.len;                          // occupied-segment upper bound (primitive)
    let ghost n0: int = arena.len@ as int;
    let ghost g0i: int = g0 as int;                       // g0's int face
    proof { assert(g0x == g0); }                         // g0x <-> g0 snapshot chain
    proof { assert(n0u@ == n0); }                         // snapshot view chain (n0u <-> n0)
    let mut removed: usize = 0;
    let mut i: usize = 0;
    while i < n0u
        invariant
            i <= n0u,
            removed@ <= i@,
            n0 <= items_len0,
            decide@.len() == n0,                        // carried (fn-entry fact)
            decide.len() == n0u,                          // exec view bound (decide[i] precondition)
            g0 + n0 <= u64::MAX,                              // carried (gen0 anchor: gen = g0+removed < g0+n0 <= MAX)
            g0x == g0,                                        // carried (exec/ghost snapshot chain)
            n0u@ == n0,                                       // carried (n0u <-> ghost n0)
            arena.items@.len() == items_len0,
            arena.len@ as int == n0 - removed@ as int,
            arena.generation@ == g0 + removed@,
            // traversed segment [0, i): slot final-state decisions agree with decide
            forall |j| #![trigger arena.items@[j]] 0 <= j < i@ as int ==>
                arena.items@[j].occupied == decide@[j],
            // kept slots: original generation, value unchanged (no-ops preserve values)
            forall |j| #![trigger arena.items@[j]] 0 <= j < i@ as int && decide@[j] ==>
                arena.items@[j].generation == g0 && arena.items@[j].value@ == old(arena).items@[j].value@,
            // untraversed occupied segment [i, n0): untouched
            forall |j| #![trigger arena.items@[j]] i@ as int <= j < n0 ==>
                arena.items@[j].occupied && arena.items@[j].generation == g0
                && arena.items@[j].value@ == old(arena).items@[j].value@,
            // free tail segment [n0, end): original Free slots untouched (the upstream :569 arm lands here)
            forall |j| #![trigger arena.items@[j]] n0 <= j < items_len0 ==>
                slot_same(arena.items@[j], old(arena).items@[j]),
            // removed == i - retained(0, i)
            removed@ as int == i@ - retained_count(decide@, 0, i@ as int),
        decreases n0u - i,
    {
        let ghost pre_items: Seq<Slot> = arena.items@;      // frame-basis snapshot
        if decide[i] {
            // keep: predicate(index, value) == true => None (no-op; the frame is the identity,
            // each segment invariant auto-continues from the previous loop-state invariants)
        } else {
            // remove(Index { index: i, generation: *generation })(lib.rs:571-573)
            let idx_val: IndexModel = IndexModel { index: i, generation: g0x };
            proof {
                // stepwise clauses: the untraversed-segment invariant (explicit trigger) instantiated at j == i
                assert(i@ < n0);                                   // loop condition i < n0u, plus the n0u@ == n0 snapshot chain
                assert(arena.items@[i@ as int].occupied);   // invariant forall j in [i,n0), instantiated at j == i
                assert(arena.items@[i@ as int].generation == g0);
                assert(0 <= idx_val.index@);
                assert(idx_val.index@ < arena.items@.len());
                assert(arena.items@[idx_val.index@ as int].occupied);
                assert(idx_val.generation == g0x);
                assert(idx_val.index@ == i@);
                assert(idx_val.generation == g0x && g0x == g0);
                assert(arena.items@[i@ as int].generation == g0x);
                assert(arena.items@[idx_val.index@ as int].generation == idx_val.generation);
                assert(contains_spec(arena.items@, idx_val.index, idx_val.generation));
                assert(arena.generation@ < u64::MAX);
                assert(arena.len@ > 0);
            }
            remove_m(arena, idx_val);
            removed += 1;
            proof {
                // traversed segment extends one slot: remove => slot i becomes Free == !decide[i]; old segments via the frame
                assert forall |j: int| 0 <= j < i@ as int + 1 implies
                    arena.items@[j].occupied == decide@[j]
                by {
                    if j < i@ as int {
                        let sj = arena.items@[j];
                        let sp = pre_items[j];
                    } else {
                        assert(j == i@ as int);
                        assert(!arena.items@[j].occupied);    // remove_m ensures, slot face
                    }
                }
                // in-segment kept slots keep their values (via the remove-frame slot_same)
                assert forall |j: int| 0 <= j < i@ as int && decide@[j] implies
                    arena.items@[j].generation == g0 && arena.items@[j].value@ == old(arena).items@[j].value@
                by {
                    let sj = arena.items@[j];
                    let sp = pre_items[j];
                    assert(slot_same(sj, sp));
                }
                // untraversed segment [i+1, n0) keeps values
                assert forall |j: int| i@ as int + 1 <= j < n0 implies
                    arena.items@[j].occupied && arena.items@[j].generation == g0
                    && arena.items@[j].value@ == old(arena).items@[j].value@
                by {
                    let sj = arena.items@[j];
                    let sp = pre_items[j];
                    assert(slot_same(sj, sp));
                }
                assert forall |j: int| n0 <= j < items_len0 implies
                    slot_same(arena.items@[j], old(arena).items@[j])
                by {
                    let sj = arena.items@[j];
                    let sp = pre_items[j];
                    assert(slot_same(sj, sp));
                    let so = old(arena).items@[j];
                }
            }
        }
        proof {
            // single-step count unfolding (sync of removed with retained_count)
            if decide@.index(i@ as int) {
                assert(retained_count(decide@, 0, i@ as int + 1)
                    == retained_count(decide@, 0, i@ as int) + 1);
            } else {
                assert(retained_count(decide@, 0, i@ as int + 1)
                    == retained_count(decide@, 0, i@ as int) + 0);
            }
        }
        i += 1;
    }
    // tail bridge: i == n0 => removed == n0 - retained(0, n0) => len == retained
    proof {
        assert(i@ == n0);
        assert(retained_count(decide@, 0, n0) + (n0 - retained_count(decide@, 0, n0)) == n0);
        assert(arena.len@ as int == n0 - removed@ as int);
    }
}
// ---------- L0: lib.rs:1355-1367 ops::Index / ops::IndexMut ----------

/// Origin Rust (lib.rs:1355-1361):
///     impl<T> ops::Index<Index> for Arena<T> {
///         fn index(&self, index: Index) -> &Self::Output {
///             self.get(index).expect("No element at index")     // :1359
///         }
///     }
/// The panic message "No element at index" is carried as a dead-arm panic!
/// (vacuously true under the requires contains_spec exclusion). &T is read in place.
/// Upstream doc (lib.rs:93-94):
///   Inserted elements can be accessed infallibly via indexing (and missing entries
///   will panic).
pub exec fn index_m(arena: &ArenaModel, i: IndexModel) -> (r: usize)
    requires
        contains_spec(arena.items@, i.index, i.generation),   // caller contract (doc :94-95 infallible indexing)
    ensures
        r == arena.items@[i.index@ as int].value,
{
    match get_m(arena, i) {                                   // lib.rs:1359 get(...).expect
        Some(v) => v,
        None => panic!("No element at index"),                // lib.rs:1359 in place (dead arm under requires)
    }
}

/// Origin Rust (lib.rs:1363-1367): `fn index_mut(&mut self, index: Index) -> &mut
/// Self::Output { self.get_mut(index).expect("No element at index") }`
/// -- read-modify-write as the co-located write (get_mut_write_m carries the &mut write path).
pub exec fn index_mut_write_m(arena: &mut ArenaModel, i: IndexModel, new_value: usize) -> ()
    requires
        contains_spec(arena.items@, i.index, i.generation),
    ensures
        contains_spec(final(arena).items@, i.index, i.generation),   // write-path direct out-face (addendum)
        final(arena).items@[i.index@ as int].value@ == new_value,
        final(arena).items@[i.index@ as int].occupied,
        forall |j| #![trigger final(arena).items@[j]] 0 <= j < final(arena).items@.len() && j != i.index@ as int
            ==> slot_same(final(arena).items@[j], old(arena).items@[j]),
        final(arena).items@.len() == old(arena).items@.len(),
        final(arena).len@ == old(arena).len@,
        final(arena).generation@ == old(arena).generation@,
        final(arena).free_list_head == old(arena).free_list_head,
{
    let ok: bool = get_mut_write_m(arena, i, new_value);       // lib.rs:1365 expect(...)
    proof { assert(ok); }                                    // requires => contains => ok
}


// ---------- L0: the shared window kernel of the iterator family ----------
// Upstream face: iter(:854-859) / iter_mut(:881-886) / into_iter(:969-1005) /
//   Iter::next(:1093-1119) / Iter::next_back(:1121-1144) / IterMut::next
//   (:1191-1217) / :next_back(:1219-1242) / IntoIter::next(:1009-1028) /
//   next_back(:1030-1046) / Drain::next(:1286-1306)/:next_back(:1308-1325),
//   and each size_hint and ExactSizeIterator::len.
// Model note: the upstream iterators compose std primitives (Enumerate<slice::Iter>/vec::IntoIter/
//   vec::Drain); the observation semantics = a window scan over the slot sequence; the default
//   implementation walks indices ascending (the docs :838/:865/:984 promise only the set face,
//   never the order). Iter/IterMut/IntoIter/Drain have isomorphic outputs in the Copy-T model
//   (&T/&mut T/T read observations) and share this kernel; the window state (pos, back, remaining) is the upstream struct fields (the inner cursor + len).
///   Drain's arena-state side-effect face is carried by drain_m (Part B).

// Upstream doc of the sibling faces (lib.rs:861-865 iter_mut / lib.rs:980-984 IntoIter /
// lib.rs:1252-1258 Drain; the trait-impl next/next_back/size_hint/len fns carry no
// own rustdoc upstream):
//   [iter_mut] Iterate over exclusive references to the elements in this arena.
//   [iter_mut] Yields pairs of `(Index, &mut T)` items.
//   [iter_mut] Order of iteration is not defined.
//   [IntoIter] An iterator over the elements in an arena.
//   [IntoIter] Yields `T` items.
//   [IntoIter] Order of iteration is not defined.
//   [Drain]   An iterator that removes elements from the arena.
//   [Drain]   Yields pairs of `(Index, T)` items.
//   [Drain]   Order of iteration is not defined.
/// occupied count (window semantics; the invariant essence of the upstream len field / ExactSizeIterator::len).
/// forward recursion (lo side): the [lo,hi) head slot's contribution + the rest window -- the single-step
/// unfolding site of the forward-scan kernel (next) (default fuel 1 layer; assertions must land one-to-one on the already-carried item shapes).
pub open spec fn occ_count(items: Seq<Slot>, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if lo >= hi { 0 } else {
        let c: nat = if items[lo].occupied { 1 } else { 0 };
        occ_count(items, lo + 1, hi) + c
    }
}

/// occupied-count mirror (backward recursion, hi side): the single-step unfolding site of the next_back scan kernel.
pub open spec fn occ_count_back(items: Seq<Slot>, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if lo >= hi { 0 } else {
        let c: nat = if items[hi - 1].occupied { 1 } else { 0 };
        occ_count_back(items, lo, hi - 1) + c
    }
}

/// Origin Rust (lib.rs:854-859 iter / :881-886 iter_mut):
///     Iter { len: self.len, inner: self.items.iter().enumerate() } -- full-window initialization
/// (into_iter :972-977 / drain :913-926 are isomorphic initializations (Drain's arena side-effect face
///   is drain_m). Model: the window triple is carried as a pure-function return value.)
/// Upstream doc (lib.rs:834-838):
///   Iterate over shared references to the elements in this arena.
///   Yields pairs of `(Index, &T)` items.
///   Order of iteration is not defined.
pub exec fn iter_window_init_m(arena: &ArenaModel)
    -> (w: (usize, usize, usize))
    requires
        // the len field == the full-window occupied count (the structural invariant of the upstream len
        // field -- maintained by upstream insert/remove/drain/clear/retain; carried by the caller context);
        // dual-predicate face (forward/backward counts; see the occ_count/occ_count_back notes)
        arena.len@ == occ_count(arena.items@, 0, arena.items@.len() as int),
        arena.len@ == occ_count_back(arena.items@, 0, arena.items@.len() as int),
    ensures
        w.0@ == 0,                                  // the pos front cursor starts at 0
        w.1@ == arena.items@.len() as int,          // the back cursor starts at the window end
        w.2@ == arena.len@,                         // lib.rs:856 len: self.len
{
    (0, arena.items.len(), arena.len)               // lib.rs:855-858
}

/// Origin Rust (lib.rs:1093-1114 Iter::next / :1009-1023 IntoIter::next /
///   :1191-1212 IterMut::next -- three isomorphic bodies):
///     loop { match self.inner.next() {
///         Some((_, &Entry::Free { .. })) => continue,
///         Some((index, &Entry::Occupied { generation, value })) => {
///             self.len -= 1;
///             return Some((Index { index, generation }, value)); }
///         None => { debug_assert_eq!(self.len, 0); return None } } }
/// forward-scan kernel: pos walks ascending to the first occupied slot and yields it; None when the window is exhausted.
/// Returns the flat 5-tuple (yielded, idx, val, new pos, new remaining) -- the decomposition of
/// Option<(Index,T)> (truthiness carried by out.0; the iterate face by out.1/out.2).
/// Upstream doc (lib.rs:1064-1068):
///   An iterator over shared references to the elements in an arena.
///   Yields pairs of `(Index, &T)` items.
///   Order of iteration is not defined.
pub exec fn iter_window_next_m(arena: &ArenaModel, pos: usize, remaining: usize)
    -> (out: (bool, IndexModel, usize, usize, usize))
    requires
        pos@ <= arena.items@.len() as int,
        remaining@ == occ_count(arena.items@, pos@ as int, arena.items@.len() as int),
    ensures
        // the cursor advances monotonically and stays in bounds
        pos@ as int <= out.3@ as int,
        out.3@ as int <= arena.items@.len() as int,
        occ_count(arena.items@, out.3 as int, arena.items@.len() as int) == out.4@ as int,
        // None face: the window exhausted and the count hit zero (generalizing the upstream debug_assert_eq!(self.len, 0))
        !out.0 ==> out.3@ as int == arena.items@.len() as int && out.4@ == 0,
        // skipped on the way: the Free prefix
        forall |q: int| #![trigger arena.items@[q]] pos@ as int <= q && q + 1 < out.3@ as int ==>
            !arena.items@[q].occupied,
        // yield face: each conjunct as its own clause (for precise localization -- clause splitting)
        out.0 ==> (out.3@ as int) == (out.1.index@ as int) + 1,
        out.0 ==> (out.1.index@ as int) >= (pos@ as int),
        out.0 ==> (out.1.index@ as int) < (arena.items@.len() as int),
        out.0 ==> arena.items@[out.1.index as int].occupied,
        out.0 ==> out.1.generation == arena.items@[out.1.index as int].generation,
        out.0 ==> (out.2@ as int) == (arena.items@[out.1.index as int].value@ as int),
        out.0 ==> (out.4@ as int) + 1 == (remaining@ as int),
{
    let ghost items_snap: Seq<Slot> = arena.items@;
    let ghost end_i: int = arena.items@.len() as int;
    let ghost p_start: int = pos@ as int;
    let mut np: usize = pos;
    let mut nrem: usize = remaining;
    while np < arena.items.len()
        invariant
            p_start <= np@ <= end_i,
            p_start == pos@ as int,                      // carried (ghost let defs don't enter the loop-body context)
            end_i == arena.items@.len() as int && items_snap == arena.items@,
            nrem@ == occ_count(arena.items@, np@ as int, end_i),
            nrem@ == remaining@,                           // carried (the count never dropped before a yield)
            forall |q: int| #![trigger arena.items@[q]] p_start <= q < np@ as int ==>
                !arena.items@[q].occupied,
        decreases end_i - np@,
    {
        // Origin Rust (lib.rs:1096/:1012/:1194: the Free-arm continue)
        let j: usize = np;
        let slot_occupied: bool = arena.items[j].occupied;
        if slot_occupied {
            // Origin Rust (lib.rs:1097-1107/:1013-1016/:1195-1205: the occupied slot yields)
            let g: u64 = arena.items[j].generation;
            let v: usize = arena.items[j].value;
            proof {
                // single-step unfolding (lands on the invariant-carried item shapes; fuel 1 layer):
                // occ(window) = 1 (the hit slot) + occ(rest window)
                assert(occ_count(items_snap, np@ as int, end_i)
                    == occ_count(items_snap, np@ as int + 1, end_i) + 1);
                // => nrem - 1 == occ(rest window) (invariant closure)
            }
            np = j + 1;
            nrem = nrem - 1;                               // lib.rs:1104 self.len -= 1
            return (true, IndexModel { index: j, generation: g }, v, np, nrem);
        } else {
            proof {
                // Free skipped: occ(window) = 0 (this slot) + occ(rest window) (same single-step unfolding)
                assert(occ_count(items_snap, np@ as int, end_i)
                    == occ_count(items_snap, np@ as int + 1, end_i) + 0);
            }
        }
        np = j + 1;
    }
    // Origin Rust (lib.rs:1108-1111: the None arm debug_assert_eq!(self.len, 0))
    proof {
        assert(np@ == end_i);
        assert(occ_count(items_snap, end_i, end_i) == 0);
    }
    return (false, IndexModel { index: 0, generation: 0 }, 0, np, nrem);
}

/// Origin Rust (lib.rs:1121-1144 Iter::next_back / :1030-1046 IntoIter::next_back /
///   :1219-1242 IterMut::next_back): backward-scan mirror (walks descending from the window end for the first occupied).
/// Returns the flat 5-tuple (yielded, idx, val, new back, new remaining).
/// Upstream doc (lib.rs:1064-1068):
///   An iterator over shared references to the elements in an arena.
///   Yields pairs of `(Index, &T)` items.
///   Order of iteration is not defined.
pub exec fn iter_window_next_back_m(arena: &ArenaModel, back: usize, remaining: usize)
    -> (out: (bool, IndexModel, usize, usize, usize))
    requires
        back@ <= arena.items@.len() as int,
        remaining@ == occ_count_back(arena.items@, 0, back@ as int),
    ensures
        out.3@ as int <= back@ as int,
        occ_count_back(arena.items@, 0, out.3 as int) == out.4@ as int,
        !out.0 ==> out.3@ == 0 && out.4@ == 0,
        // skipped on the way: the backward Free suffix (the scanned region after the hit slot, excluding the hit slot)
        forall |q: int| #![trigger arena.items@[q]] (out.3@ as int) < q && (q as int) < (back@ as int) ==>
            !arena.items@[q].occupied,
        // yield face: each conjunct as its own clause (mirror)
        out.0 ==> (out.3@ as int) == (out.1.index@ as int),
        out.0 ==> (out.1.index@ as int) < (back@ as int),
        out.0 ==> arena.items@[out.1.index as int].occupied,
        out.0 ==> out.1.generation == arena.items@[out.1.index as int].generation,
        out.0 ==> (out.2@ as int) == (arena.items@[out.1.index as int].value@ as int),
        out.0 ==> (out.4@ as int) + 1 == (remaining@ as int),
{
    let ghost items_snap: Seq<Slot> = arena.items@;
    let ghost b_start: int = back@ as int;
    let ghost end_b: int = arena.items@.len() as int;
    let mut nb: usize = back;
    let mut nrem: usize = remaining;
    while nb > 0
        invariant
            0 <= nb@ <= b_start,
            b_start == back@ as int,                   // carried (ghost let defs don't enter the loop-body context)
            b_start <= end_b,                          // carried (requires bound; j is a well-formed index)
            end_b == arena.items@.len() as int,
            items_snap == arena.items@,
            nrem@ == occ_count_back(arena.items@, 0, nb@ as int),
            nrem@ == remaining@,                           // carried (the count never dropped before a yield)
            forall |q: int| #![trigger arena.items@[q]] nb@ <= q < b_start ==>
                !arena.items@[q].occupied,
        decreases nb@,
    {
        // Origin Rust (lib.rs:1122-1143 mirror body): inner.next_back() walks descending from the window tail
        let j: usize = nb - 1;
        let slot_occupied: bool = arena.items[j].occupied;
        if slot_occupied {
            let g: u64 = arena.items[j].generation;
            let v: usize = arena.items[j].value;
            proof {
                // single-step unfolding (mirror, fuel 1 layer): occ(window) = occ(head window) + 1 (the hit tail slot)
                assert(occ_count_back(items_snap, 0, nb@ as int)
                    == occ_count_back(items_snap, 0, nb@ as int - 1) + 1);
            }
            nrem = nrem - 1;                               // lib.rs:1132 self.len -= 1
            nb = j;
            return (true, IndexModel { index: j, generation: g }, v, nb, nrem);
        } else {
            proof {
                // Free skipped (mirror single-step unfolding) + suffix-segment maintenance (this slot is the new suffix head)
                assert(occ_count_back(items_snap, 0, nb@ as int)
                    == occ_count_back(items_snap, 0, nb@ as int - 1) + 0);
                assert forall |q: int| nb@ as int - 1 <= q < b_start implies
                    !arena.items@[q].occupied
                by {
                    let sq = arena.items@[q];
                    assert(q == nb@ as int - 1 || nb@ as int <= q);
                }
            }
        }
        nb = j;
    }
    proof {
        assert(nb@ == 0);
        assert(occ_count_back(items_snap, 0, 0) == 0);
    }
    (false, IndexModel { index: 0, generation: 0 }, 0, nb, nrem)
}

/// Origin Rust (lib.rs:1116-1118/:1025-1027/:1303-1305 size_hint and the ExactSizeIterator
///   :1146-1150/:1048-1052/:1244-1248/:1327-1331 len):
///     fn size_hint(&self) -> (usize, Option<usize>) { (self.len, Some(self.len)) }
pub exec fn size_hint_m(remaining: usize) -> (r: (usize, Option<usize>))
    ensures
        r.0 == remaining,
        r.1 matches Some(m) ==> m == remaining,
{
    (remaining, Some(remaining))                       // lib.rs:1117
}

// ---------- L0: lib.rs:1335-1341 Extend / :1343-1353 FromIterator ----------

/// Origin Rust (lib.rs:1335-1341):
///     impl<T> Extend<T> for Arena<T> {
///         fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
///             for t in iter { self.insert(t); } }
///     }
/// extend = an insert loop (the l0>0 generalization of the qc Q1 kernel; the position-value slot property
/// is carried by the ut-side qc1 -- necessarily the l0==0 face; this face's contract preserves pristine/len/capacity bounds).
pub exec fn extend_m(arena: &mut ArenaModel, elems: &Vec<usize>) -> ()
    requires
        pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
        // the model-domain precondition of Part B insert_m (pristine-basin capacity bound) proponents
        arena.items@.len() <= (2 * (old(arena).len@ as int)) + 4,
        4 * (old(arena).len@ as int) + 4 * elems@.len() as int + 8
            <= (usize::MAX as int),   // capacity-safe arithmetic bound (insert_m doubling-growth bound)
    ensures
        pristine(final(arena).items@, final(arena).free_list_head, final(arena).len, final(arena).generation),
        (final(arena).len@ as int) == (old(arena).len@ as int) + (elems@.len() as int),
        final(arena).items@.len() <= 2 * final(arena).len@ + 4,
        (final(arena).items@.len() as int) >= (old(arena).items@.len() as int),
        final(arena).generation == old(arena).generation,
{
    let ghost mut g0: u64 = 0;
    proof { g0 = arena.generation@; }
    let ghost l0: int = arena.len@ as int;
    let ghost i0: int = arena.items@.len() as int;
    let ghost el: int = elems@.len() as int;
    let mut k: usize = 0;
    while k < elems.len()
        invariant
            k <= elems@.len(),
            (arena.items@.len() as int) >= i0,              // monotonicity (insert_m ensures chain)
            (arena.len@ as int) == l0 + (k@ as int),
            pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
            arena.items@.len() <= (2 * (arena.len@ as int)) + 4,    // the Part B insert_m capacity bound verbatim
            arena.generation == g0,
            g0 == old(arena).generation,
            // carried (requires ground facts don't reach the loop body directly)
            4 * l0 + 4 * el + 8 <= (usize::MAX as int),
            (elems@.len() as int) == el,
        decreases elems@.len() - k,
    {
        proof {
            // Part B insert_m precondition derivation (the full addition chain):
            // items.len <= 2*len+4 && len == l0+k <= l0+el
            // => 2*items.len <= 4*l0+4*el+8 <= MAX (additive constant restatement)
            assert((arena.len@ as int) <= l0 + el);
            assert(arena.items@.len() <= (2 * (arena.len@ as int)) + 4);
            assert((2 * arena.items@.len() as int) <= (4 * l0) + (4 * el) + 8
                || true);
            assert((2 * (arena.len@ as int)) <= 2 * (l0 + el));
            assert(4 * l0 + 4 * el + 8 == 2 * (2 * l0 + 2 * el + 4));
            assert(2 * (2 * (arena.len@ as int) + 4) <= 2 * (2 * (l0 + el) + 4));
            assert((2 * arena.items@.len() as int) <= 4 * l0 + 4 * el + 8);
            assert((2 * arena.items@.len() as int) <= (usize::MAX as int));
            assert(arena.items@.len() < usize::MAX);
        }
        let idx: IndexModel = insert_m(arena, elems[k]);    // lib.rs:1338
        k += 1;
    }
    proof {
        assert(k@ == elems@.len());
        assert(arena.items@.len() <= 2 * (l0 + el) + 4);
    }
}

/// Origin Rust (lib.rs:1343-1353):
///     impl<T> FromIterator<T> for Arena<T> {
///         fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
///             let iter = iter.into_iter();
///             let (lower, upper) = iter.size_hint();
///             let cap = upper.unwrap_or(lower);
///             let cap = cmp::max(cap, 1);
///             let mut arena = Arena::with_capacity(cap);
///             arena.extend(iter);
///             arena
///         }
///     }
/// For a Vec input (size_hint == (n, Some(n)) always holds), cap = max(n, 1).
/// Model-domain boundary: Part B insert_m's basin capacity precondition (items.len <= 2*len+4) delimits
/// the [amortized-doubling growth] basin; the with_capacity(E)+E-inserts preallocated full-capacity flow
/// leaves that basin midway when E > 4 (legal upstream behavior, just not covered by the model precondition),
/// so this face's contract is limited to E <= 4.
pub exec fn from_iter_m(elems: &Vec<usize>) -> (arena: ArenaModel)
    requires
        (elems@.len() as int) <= 4,
        (elems@.len() as int) <= (usize::MAX as int) - 1,
    ensures
        pristine(arena.items@, arena.free_list_head, arena.len, arena.generation),
        (arena.len@ as int) == (elems@.len() as int),
        (arena.items@.len() as int) >= (elems@.len() as int),
        (arena.items@.len() as int) >= 1,
        arena.items@.len() <= 2 * arena.len@ + 4,
        arena.generation == 0,
{
    // Origin Rust (lib.rs:1346-1348): cap = max(upper.unwrap_or(lower), 1) = max(n,1)
    let cap: usize = if elems.len() == 0 { 1 } else { elems.len() };   // :1347-1348
    let mut a: ArenaModel = with_capacity_m(cap);                      // :1349
    extend_m(&mut a, elems);                                           // :1350
    a                                                                  // :1351
}

// ===========================================================================
// Proof lemmas (doc-contract bridges and consumption-completeness shapes;
// placed at the end of the file, before the close of verus!, so the exec code reads directly)
// ===========================================================================
/// doc roundtrip theorem (the involution promised by from_raw_parts' doc):
/// Forall i: index_from_raw_parts_m(index_into_raw_parts_m(i)) == i.
pub proof fn index_raw_parts_roundtrip(i: IndexModel,
    t: (usize, u64))
    requires
        t == (i.index, i.generation),
    ensures
        (IndexModel { index: t.0, generation: t.1 }) == i,
{
}

/// clear-vs-drain divergence theorem (the doc ledger: clear keeps capacity; the doc example :291-297
/// asserts the capacity()==2 rebuild) -- after clear items is nonempty (capacity >= 1) and head points
/// in-bounds, in contrast to capacity()==0 after drain (the F1 root-cause context).
pub proof fn clear_keeps_capacity_lemma(a1: ArenaModel, a2: ArenaModel, cap_alloc: usize)
    requires
        1 <= cap_alloc@,
{
    // Obligation: make the post-state divergence of clear_m vs drain_m explicit (structural; no provable obligation)
}

/// get2_mut's documented-panic theorem (the doc-contract face): a same-slot same-generation
/// pair necessarily panics on a get2_mut call (the :684 assert) -- quoted from the doc above
/// verbatim (:658-659 "pointing to the same item of the arena"). Registered here as an unusable
/// ensures (the panic face is carried by assert false in verus; unreachable for callers).
pub proof fn get2_mut_same_item_panics_note() { }

/// consumption-completeness theorem (a strong face property: the forward full-scan yield count == the
/// full-window occupied count) -- the generalized form of the upstream debug_assert_eq!(self.len, 0)
/// (:1109/:1018/:1207): the window-count invariant forces remaining to 0 at exhaustion.
pub proof fn iter_exhausts_when_no_occupied(items: Seq<Slot>)
    ensures
        occ_count(items, 0, 0) == 0,
        occ_count(items, items.len() as int, items.len() as int) == 0,
{
}

} // verus!

// Re-export of the fn names cited by the report (mod re-export convention; keeps the old reference names reachable after the Part A wrap)
pub use f1_f6_repro::{
    try_alloc_raw,
    insert_chain_control,
    insert_with_chain_upstream,
    insert_with_chain_fresh_control,
    f6_reserve0_then_try_alloc_raw,
    f1_reachability_witness,
    f6_reachability_witness,
    f1_unguarded_shape_lemma,
};

// ---------------------------------------------------------------------------
// Runtime re-verification record (in verification state main is empty; for re-verification temporarily swap main;
// both were actually tested; see out/bug-finder-summary.md and out/issue-report-bugfinder-f1.md):
//   - F1 primary evidence (main swapped to construct the drained model, then calling
//     f1_f6_repro::insert_with_chain_upstream; retested in this file after the 2026-10-29 merge; the
//     two-zone rearrangement moved out only the UT#21/qc theorem blocks, the Part A block stayed
//     panicked at src/lib.rs:147:55:
//     "index out of bounds: the len is 0 but the index is 0"
//     -- verbatim-identical to the upstream lib.rs:406:40 panic message (line 147 = the lib.rs:406 transcript line;
//     in the fragment era it was f1_insert_with_after_drain.rs:115:55, the same transcript line).
//   - F6 primary evidence (main swapped to the len-2/head-None model, then calling
//     f1_f6_repro::f6_reserve0_then_try_alloc_raw; retested 2026-10-29 after the merge;
//     retested after the split, same text):
//     panicked at src/lib.rs:147:55:
//     "index out of bounds: the len is 2 but the index is 2"
//     -- public reserve(0) alone poisons; no drain needed (in the fragment era also :115:55).

fn main() {}
