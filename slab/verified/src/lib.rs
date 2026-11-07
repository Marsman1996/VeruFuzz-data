//! slab 0.4.12 x Verus -- verified driver
//! Upstream tokio-rs/slab @ 7d1d8ab0 (src/lib.rs line numbers cited per
//! annotation; inventory in DB/out/harness-inventory.md).
//!
//! Transcription targets (the harness-called API set, <= 5):
//!   * get2_mut    (lib.rs:764-813) -- the F1 site, no UT coverage (recorded
//!     in the inventory)
//!   * insert/insert_at (lib.rs:1030-1036, 1092-1105)
//!   * retain      (lib.rs:1214-1228; the predicate concretized per tests/slab.rs:222-249)
//!
//! Form (following the F1 two-copy discipline):
//!   1. verbatim transcription of the upstream exec (doc contracts as
//!      requires/ensures); a Verus obligation failing exactly at a panic
//!      site is the bug-reproduction anchor;
//!   2. repair counter-proof get2_mut_fixed: the same code plus the guard means
//!      all obligations pass;
//!   3. key UT assertions transcribed into exec/proof witnesses.
//!
//! Lossy abstractions (none sits at a panic site; see each annotation):
//!   * the private Entry/Slab representations transcribed as EntryExec/
//!     SlabExec (fields one-to-one); derive(Clone) and friends that take no
//!     part in control flow are dropped.
//!   * the usize capacity bound is abstracted as entries.len() <
//!     usize::MAX@ - 1 in the invariant, plus the insert precondition
//!     entries.len() < usize::MAX@ - 2 (covering the capacity-overflow tier
//!     the insert # Panics of lib.rs:1018-1020 declares: that tier is a
//!     documented, legitimate panic/abort, outside this pipeline's scope).
//!   * the vacant-chain internal invariant (implicit upstream) is captured
//!     by the recursive chain_ok spec; its two update lemmas are admitted
//!     (pure structural facts, disclosed by them); the obligations at the
//!     verified target sites (get2_mut's split_at_mut, remove's invalid-key,
//!     loop index bounds) never touch assume/admit/external_body.
//!   * for i in 0..len loops rewritten as while (Verus does not support that for form).
//!
//! Crate attrs: the allocator_api feature is needed only for the signature of
//! assume_specification<Vec::capacity> (the same dependency vstd own Vec specs have).

#![feature(allocator_api)]

use vstd::prelude::*;
use vstd::seq::Seq;
use std::alloc::Allocator; // needed by the assume_specification<Vec::capacity> signature

verus! {

// =====================================================================
// std external spec injection (the kverus-fix "Missing Standard-Library
// Specifications" branch, minimal sound spec): Vec::capacity has no vstd
// spec while the batch-2 capacity/reserve/reserve_exact need its lower
// bound. Per the std Vec invariant capacity >= len (rustdoc:
// "capacity ... at least equal to len"):
//   ensures cap@ >= vec@.len()
// trusted-boundary disclosure in out/harness-inventory.md.
// =====================================================================
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::capacity ](vec: &Vec<T, A>) -> (cap: usize)
    ensures
        cap@ >= vec@.len(),
;

// vstd covers only Vec::reserve; reserve_exact is the same shape but absent
// from vstd; injected with the minimal sound spec identical to the vstd
// Vec::reserve (an allocator-layer operation; the entries view is unchanged).
pub assume_specification<T, A: Allocator>[ Vec::<T, A>::reserve_exact ](
    vec: &mut Vec<T, A>,
    additional: usize,
)
    ensures
        final(vec)@ == old(vec)@,
;

// =====================================================================
// representation-layer transcription (the private types of src/lib.rs)
// =====================================================================

/// Origin Rust (lib.rs:269-273):
///   #[derive(Clone)]
///   enum Entry<T> { Vacant(usize), Occupied(T) }
/// derive(Clone) is irrelevant to the control flow under proof; dropped.
pub exec enum EntryExec<T> {
    Vacant(usize),
    Occupied(T),
}

/// Origin Rust (lib.rs:144-154):
///   pub struct Slab<T> {
///       entries: Vec<Entry<T>>,   // Chunk of memory
///       len: usize,               // Number of Filled elements
///       next: usize,              // Offset of the next available slot
///   }
pub exec struct SlabExec<T> {
    // Chunk of memory
    pub entries: Vec<EntryExec<T>>,
    // Number of Filled elements currently in the slab
    pub len: usize,
    // Offset of the next available slot in the slab. Set to the slab's
    // capacity when the slab is full.
    pub next: usize,
}

// =====================================================================
// spec model (occupancy / vacant chain / internal invariant)
// =====================================================================

/// Whether the entry is a vacant slot: the Entry::Vacant discrimination.
/// Machine-type level.
pub open spec fn is_vacant<T>(e: EntryExec<T>) -> bool {
    e matches EntryExec::Vacant(_)
}

/// The chain pointer of a vacant slot (the Vacant payload); the Occupied
/// branch's value is meaningless (every use site is guarded by it).
pub open spec fn vacant_link<T>(e: EntryExec<T>) -> int {
    match e {
        EntryExec::Vacant(next) => next as int,
        EntryExec::Occupied(_) => 0int,
    }
}

/// Whether es[i] is occupied: the key's "associated value" semantics (the rustdoc associated value).
pub open spec fn occ_at<T>(es: Seq<EntryExec<T>>, i: int) -> bool {
    0 <= i < es.len() && es[i] matches EntryExec::Occupied(_)
}

/// Occupancy count: the number of Occupied slots among the first n; the spec image of s.len.
pub open spec fn occ_cnt<T>(es: Seq<EntryExec<T>>) -> int {
    occ_cnt_prefix(es, es.len() as int)
}

pub open spec fn occ_cnt_prefix<T>(es: Seq<EntryExec<T>>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0int
    } else {
        (if es[n - 1] matches EntryExec::Occupied(_) { 1int } else { 0int })
            + occ_cnt_prefix(es, n - 1)
    }
}

/// The vacant chain, starting from cur, reaches the end marker (= es.len())
/// within budget steps. Abstraction of the upstream implicit invariant (the
/// module doc "stack of vacant slots using a linked list", lib.rs:110-118).
pub open spec fn chain_ok<T>(es: Seq<EntryExec<T>>, cur: int, budget: int) -> bool
    decreases budget
{
    if cur == es.len() {
        true
    } else if budget <= 0 {
        false
    } else {
        0 <= cur < es.len()
        && (es[cur] matches EntryExec::Vacant(_))
        && 0 <= vacant_link(es[cur]) <= es.len()
        && chain_ok(es, vacant_link(es[cur]), budget - 1)
    }
}

/// Slab internal invariant: the machinization of the module doc at
/// lib.rs:1017 ("stack of vacant slots / next is the next available slot").
/// The budget = the number of vacant slots (guaranteeing an acyclic,
/// terminating chain). Also carries the capacity bound (usize overflow
/// protection; see the lossy-abstraction note in the file header).
pub open spec fn slab_inv<T>(s: &SlabExec<T>) -> bool {
    occ_cnt(s.entries@) == s.len@
    && s.len@ <= s.entries@.len()
    && 0 <= s.next@ <= s.entries@.len()
    && s.entries@.len() < usize::MAX@ - 1
    && chain_ok(s.entries@, s.next as int, s.entries@.len() - s.len as int)
}

// =====================================================================
// Counting: only the occ_bump delta spec lives here (the occ_cnt_prefix
// structural proof lemmas moved to the tail of the file).
// =====================================================================


/// Base layer: the occupancy-count delta of a slot update.
pub open spec fn occ_bump<T>(e0: EntryExec<T>, e1: EntryExec<T>) -> int {
    (if e1 matches EntryExec::Occupied(_) { 1int } else { 0int })
        - (if e0 matches EntryExec::Occupied(_) { 1int } else { 0int })
}



/// The predicate `*x % 2 == 0` of tests/slab.rs:230 (the concretized retain instance).
pub open spec fn even_keep(e: EntryExec<u64>) -> bool {
    match e {
        EntryExec::Occupied(v) => v % 2 == 0,
        EntryExec::Vacant(_) => false,
    }
}

/// Occupied slots failing the predicate (to be dropped by retain).
pub open spec fn odd_occ(e: EntryExec<u64>) -> bool {
    match e {
        EntryExec::Occupied(v) => v % 2 == 1,
        EntryExec::Vacant(_) => false,
    }
}

/// The number of slots to be dropped among the first n (retain's exact count).
pub open spec fn drop_cnt_prefix(es: Seq<EntryExec<u64>>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0int
    } else {
        (if odd_occ(es[n - 1]) { 1int } else { 0int }) + drop_cnt_prefix(es, n - 1)
    }
}


// =====================================================================
// API transcription + doc contracts
// =====================================================================


impl<T> SlabExec<T> {
    /// Upstream doc (lib.rs:276-286):
    ///   Construct a new, empty `Slab`.
    ///   The function does not allocate and the returned slab will have no
    ///   capacity until `insert` is called or capacity is explicitly reserved.
    pub exec fn new() -> (s: SlabExec<T>)
        ensures
            slab_inv(&s),
            s.entries@ == Seq::<EntryExec<T>>::empty(),
            s.len == 0,
            s.next == 0,
    {
        // Origin Rust (lib.rs:288-292):
        //   Self { entries: Vec::new(), next: 0, len: 0 }
        SlabExec { entries: Vec::new(), next: 0, len: 0 }
    }

    // -------------------------------------------------------------
    // insert / insert_at (lib.rs:1030-1036, 1092-1105)
    // -------------------------------------------------------------

    /// Origin Rust (lib.rs:1092-1105, private fn insert_at):
    ///   self.len += 1;
    ///   if key == self.entries.len() {
    ///       self.entries.push(Entry::Occupied(val));
    ///       self.next = key + 1;
    ///   } else {
    ///       self.next = match self.entries.get(key) {
    ///           Some(&Entry::Vacant(next)) => next,
    ///           _ => unreachable!(),
    ///       };
    ///       self.entries[key] = Entry::Occupied(val);
    ///   }
    /// get(key) has no vstd spec, rewritten as a bounded-index match (same
    /// semantics while in bounds and the slot is vacant; the unreachable!
    /// semantics is preserved).
    exec fn insert_at(&mut self, key: usize, val: T)
        requires
            slab_inv(self),
            key@ == self.next@,
            self.entries@.len() < usize::MAX@ - 2,
        ensures
            slab_inv(&*final(self)),
            final(self).len@ == old(self).len@ + 1,
            final(self).entries@[key as int] == EntryExec::Occupied(val),
            // each path's own precise post-state
            key@ == old(self).entries@.len() ==> (
                final(self).entries@ == old(self).entries@.push(EntryExec::Occupied(val))
                && final(self).next@ == old(self).entries@.len() + 1
            ),
            key@ < old(self).entries@.len() ==> (
                final(self).entries@ == old(self).entries@.update(key as int, EntryExec::Occupied(val))
                && final(self).next@ == vacant_link(old(self).entries@.index(key as int))
            ),
    {
        // ghost captures (mirroring old(self) in the contract; used only
        // for the invariant-maintenance bookkeeping proof)
        let ghost pre_es = self.entries@;
        let ghost pre_len = self.len@;
        let ghost pre_budget = pre_es.len() - pre_len;
        self.len += 1; // lib.rs:1093
        if key == self.entries.len() { // lib.rs:1095
            self.entries.push(EntryExec::Occupied(val)); // lib.rs:1096
            self.next = key + 1; // lib.rs:1097
            proof {
                // Vec::push spec: self.entries@ == pre_es.push(Occ(val)),
                // key+1 == the post-push length => next' is the end marker;
                // the chain head terminates there.
                occ_cnt_push(pre_es, EntryExec::Occupied(val));
                chain_end_marker(self.entries@, pre_budget);
            }
        } else {
            self.next = match self.entries[key] {
                EntryExec::Vacant(next) => next,
                _ => unreachable!(), // lib.rs:1101 verbatim (unreachable under the invariant)
            };
            self.entries[key] = EntryExec::Occupied(val); // lib.rs:1103
            proof {
                // vacant branch: slot key was the chain head Vacant(link)
                // (from unfolding the chain_ok precondition); once re-occupied,
                // the chain continues well-formed along link, budget - 1.
                chain_head_bound(pre_es, key as int, pre_budget);
                chain_consume_head(pre_es, key as int, pre_budget, EntryExec::Occupied(val));
                occ_cnt_update(pre_es, key as int, EntryExec::Occupied(val));
            }
        }
    }

    // -------------------------------------------------------------
    // get2_mut -- the F1 site (lib.rs:764-813): comments and the doc contract
    // kept in full
    // -------------------------------------------------------------

    /// Return two mutable references to the values associated with the two
    /// given keys simultaneously. (lib.rs:764-765)
    ///
    /// If any one of the given keys is not associated with a value, then
    /// `None` is returned. (lib.rs:767-768)
    ///
    /// # Panics (lib.rs:773-775 verbatim)
    ///
    /// This function will panic if `key1` and `key2` are the same.
    ///
    /// === transcription note ===
    /// This function carries no precondition (faithful to the signature and the
    /// rustdoc: used as documented, the only panic condition is key1 == key2).
    /// Verification reading:
    ///   * an obligation failing at the assert line = reproduction of the
    ///     documented panic (key1==key2) (class 2), working as documented;
    ///   * an obligation failing at a split_at_mut line = **F1 (class 1)**:
    ///     with either key strictly greater than entries.len(), the mid > len
    ///     panic fires while the doc promises those keys "not associated with
    ///     a value -> None" -- contradicting the doc promise (doc/panic-audit-
    ///     classification.md line 3; out/issue-report.md; out/issue-report-formal.md).
    /// Upstream doc (lib.rs:764-790):
    ///   Return two mutable references to the values associated with the two
    ///   given keys simultaneously.
    ///   If any one of the given keys is not associated with a value, then `None`
    ///   is returned.
    ///   This function can be used to get two mutable references out of one slab,
    ///   so that you can manipulate both of them at the same time, eg. swap them.
    ///   # Panics
    ///   This function will panic if `key1` and `key2` are the same.
    pub exec fn get2_mut(&mut self, key1: usize, key2: usize)
        -> (ret: Option<(&mut T, &mut T)>)
        ensures
            // the lib.rs:767-768 None promise (an out-of-bounds key is never associated)
            (key1@ >= old(self).entries@.len() || key2@ >= old(self).entries@.len())
                ==> ret matches None,
            // contrapositive: Some => both keys in bounds (associated values)
            ret matches Some(_)
                ==> (key1@ < old(self).entries@.len() && key2@ < old(self).entries@.len()),
            final(self).len == old(self).len,
            final(self).next == old(self).next,
            final(self).entries@.len() == old(self).entries@.len(),
    {
        assert!(key1 != key2); // lib.rs:792 (the upstream assert!, the documented panic site)

        // Origin Rust (lib.rs:794-804):
        //   let (entry1, entry2);
        //   if key1 > key2 {
        //       let (slice1, slice2) = self.entries.split_at_mut(key1);
        //       entry1 = slice2.get_mut(0);
        //       entry2 = slice1.get_mut(key2);
        //   } else {
        //       let (slice1, slice2) = self.entries.split_at_mut(key2);
        //       entry1 = slice1.get_mut(key1);
        //       entry2 = slice2.get_mut(0);
        //   }
        // Verus does not support the deferred-initialization halves; rewritten
        // as branch-local tuple extraction (equivalent).
        let (entry1, entry2) = if key1 > key2 {
            let (slice1, slice2) = self.entries.split_at_mut(key1); // lib.rs:797 <-- F1 site a
            (slice2.get_mut(0), slice1.get_mut(key2))               // lib.rs:798-799
        } else {
            let (slice1, slice2) = self.entries.split_at_mut(key2); // lib.rs:801 <-- F1 site b
            (slice1.get_mut(key1), slice2.get_mut(0))               // lib.rs:802-803
        };

        // Origin Rust (lib.rs:806-812):
        //   match (entry1, entry2) {
        //       (Some(&mut Entry::Occupied(ref mut val1)),
        //        Some(&mut Entry::Occupied(ref mut val2))) => Some((val1, val2)),
        //       _ => None,
        //   }
        match (entry1, entry2) {
            (Some(&mut EntryExec::Occupied(ref mut val1)),
             Some(&mut EntryExec::Occupied(ref mut val2))) => Some((val1, val2)),
            _ => None,
        }
    }

    /// get2_mut's repair counter-proof (the issue-report.md Fix Code draft:
    /// honor the None promise first for out-of-bounds keys). Everything else
    /// is field-for-field identical.
    /// requires key1 != key2 is exactly the sole condition the # Panics documents;
    /// with the guard adding the boundary branch F1 lacks, the split precondition
    /// becomes provable (mid = max(key1, key2) < len) and all obligations pass
    /// => the guard restores exactly the doc promise.
    pub exec fn get2_mut_fixed(&mut self, key1: usize, key2: usize)
        -> (ret: Option<(&mut T, &mut T)>)
        requires
            key1@ != key2@, // the sole condition the lib.rs:773-775 # Panics declares
        ensures
            (key1@ >= old(self).entries@.len() || key2@ >= old(self).entries@.len())
                ==> ret matches None,
            ret matches Some(_)
                ==> (key1@ < old(self).entries@.len() && key2@ < old(self).entries@.len()),
            final(self).len == old(self).len,
            final(self).next == old(self).next,
    {
        assert!(key1 != key2); // lib.rs:792
        if key1 >= self.entries.len() || key2 >= self.entries.len() {
            return None; // FIX: honor the None promise first; an out-of-bounds key must not panic
        }
        let (entry1, entry2) = if key1 > key2 {
            let (slice1, slice2) = self.entries.split_at_mut(key1); // lib.rs:797 (after the guard)
            (slice2.get_mut(0), slice1.get_mut(key2))
        } else {
            let (slice1, slice2) = self.entries.split_at_mut(key2); // lib.rs:801 (after the guard)
            (slice1.get_mut(key1), slice2.get_mut(0))
        };
        match (entry1, entry2) {
            (Some(&mut EntryExec::Occupied(ref mut val1)),
             Some(&mut EntryExec::Occupied(ref mut val2))) => Some((val1, val2)),
            _ => None,
        }
    }

    // -------------------------------------------------------------
    // insert (lib.rs:1012-1036, doc quoted verbatim)
    // -------------------------------------------------------------

    /// (Model note: this tier is a documented, legitimate panic, absorbed by the
    /// invariant's capacity bound; see the file header.)
    /// Upstream doc (lib.rs:1012-1029):
    ///   Insert a value in the slab, returning key assigned to the value.
    ///   The returned key can later be used to retrieve or remove the value using indexed
    ///   lookup and `remove`. Additional capacity is allocated if needed. See
    ///   [Capacity and reallocation](index.html#capacity-and-reallocation).
    ///   # Panics
    ///   Panics if the new storage in the vector exceeds `isize::MAX` bytes.
    pub exec fn insert(&mut self, val: T) -> (ret_key: usize)
        requires
            slab_inv(self),
            // capacity-bound tier (spare slack; covering the isize::MAX-byte overflow
            // the lib.rs:1018-1020 # Panics declares; model in the file header)
            self.entries@.len() < usize::MAX@ - 2,
        ensures
            slab_inv(&*final(self)),
            final(self).len@ == old(self).len@ + 1,
            ret_key@ == old(self).next@, // lib.rs:1031 key = self.next
            final(self).entries@[ret_key as int] == EntryExec::Occupied(val),
            // the vacant-reuse path does not grow; the append path +1
            old(self).next@ < old(self).entries@.len()
                ==> final(self).entries@.len() == old(self).entries@.len(),
            old(self).next@ == old(self).entries@.len() ==> (
                final(self).entries@.len() == old(self).entries@.len() + 1
                && final(self).next@ == old(self).entries@.len() + 1
            ),
    {
        // Origin Rust (lib.rs:1031-1035):
        //   let key = self.next;
        //   self.insert_at(key, val);
        //   key
        let key = self.next;
        self.insert_at(key, val);
        key
    }

    // -------------------------------------------------------------
    // try_remove / remove (lib.rs:1107-1144, 1146-1169)
    // -------------------------------------------------------------

    /// Origin Rust (lib.rs:1124-1144) -- the body uses `entries.get_mut(key)` +
    /// `core::mem::replace(entry, Entry::Vacant(self.next))`; neither has a usable
    /// vstd spec, so both are rewritten equivalently as "bounded index +
    /// core::mem::swap (which vstd has a spec for)": after the swap the local
    /// slot holds the old entry and the indexed slot is set to Vacant(old self.next)
    /// -- matching the value semantics of mem::replace.
    /// Upstream doc (lib.rs:1107-1123):
    ///   Tries to remove the value associated with the given key,
    ///   returning the value if the key existed.
    ///   The key is then released and may be associated with future stored
    ///   values.
    pub exec fn try_remove(&mut self, key: usize) -> (ret: Option<T>)
        requires
            slab_inv(self),
        ensures
            slab_inv(&*final(self)),
            // key associated <=> returns Some (lib.rs:1108, "if the key existed")
            occ_at(old(self).entries@, key as int) == (ret matches Some(_)),
            ret matches Some(v)
                ==> old(self).entries@[key as int] == EntryExec::Occupied(v),
            occ_at(old(self).entries@, key as int) ==> (
                final(self).entries@
                    == old(self).entries@.update(key as int, EntryExec::Vacant(old(self).next as usize))
                && final(self).next == key // lib.rs:1139 self.next = key
                && final(self).len@ == old(self).len@ - 1
            ),
            !occ_at(old(self).entries@, key as int) ==> (
                final(self).entries@ == old(self).entries@
                && final(self).next == old(self).next
                && final(self).len@ == old(self).len@
            ),
    {
        let ghost pre_es = self.entries@;
        let ghost pre_len = self.len@;
        let ghost pre_next = self.next@;
        let ghost pre_budget = pre_es.len() - pre_len;
        // lib.rs:1125-1126: if let Some(entry) = self.entries.get_mut(key)
        //                  if let Entry::Occupied(_) = entry
        if key < self.entries.len() && self.entries[key] matches EntryExec::Occupied(_) {
            proof {
                // len == occ_cnt(pre_es) >= 1 (slot key occupied) => len-1 does not underflow
                occ_cnt_ge_at(pre_es, key as int);
            }
            let mut slot = EntryExec::Vacant(self.next); // lib.rs:1133, the second argument of replace
            core::mem::swap(&mut self.entries[key], &mut slot);
            self.len -= 1; // lib.rs:1138
            self.next = key; // lib.rs:1139
            proof {
                chain_insert_head(pre_es, key as int, pre_next as int, pre_budget);
                occ_cnt_update(pre_es, key as int, EntryExec::Vacant(pre_next as usize));
            }
            // lib.rs:1140: return val.into();
            if let EntryExec::Occupied(val) = slot {
                return Some(val);
            }
        }
        None // lib.rs:1143
    }

    /// (transcription: this # Panics is contractualized as requires occ_at; a
    /// violation is the call-site obligation failure -- the
    /// documented-panic reproduction.)
    /// Upstream doc (lib.rs:1146-1165):
    ///   Remove and return the value associated with the given key.
    ///   The key is then released and may be associated with future stored
    ///   values.
    ///   # Panics
    ///   Panics if `key` is not associated with a value.
    pub exec fn remove(&mut self, key: usize) -> (ret: T)
        requires
            slab_inv(self),
            occ_at(self.entries@, key as int),
        ensures
            slab_inv(&*final(self)),
            final(self).entries@
                == old(self).entries@.update(key as int, EntryExec::Vacant(old(self).next as usize)),
            final(self).next == key,
            final(self).len@ == old(self).len@ - 1,
            old(self).entries@[key as int] == EntryExec::Occupied(ret),
    {
        /* Origin Rust (lib.rs:1168):
             self.try_remove(key).expect("invalid key")
           Option::expect has no vstd spec, rewritten equivalently as an explicit
           match; the None arm is unreachable under the requires (an encoding that keeps the documented-panic semantics).*/
        match self.try_remove(key) {
            Some(v) => v,
            None => panic!("invalid key"), // the expect panic of lib.rs:1168
        }
    }

    // =============================================================
    // difference-verification batch 1: the simple read-only / lookup family
    //   (2026-10-30 batch)
    //   len(lib.rs:635-637)/is_empty(:651-653)/contains(:1186-1188)/
    //   vacant_key(:1058-1060)/get(:733-738)/get_mut(:757-762)
    // =============================================================

    /// Upstream doc (lib.rs:621-634):
    ///   Return the number of stored values.
    pub exec fn len(&self) -> (ret: usize)
        ensures
            ret@ == self.len@,
    {
        self.len // lib.rs:637
    }

    /// Upstream doc (lib.rs:639-650):
    ///   Return `true` if there are no values stored in the slab.
    pub exec fn is_empty(&self) -> (ret: bool)
        ensures
            ret == (self.len@ == 0),
    {
        self.len == 0 // lib.rs:652
    }

    /// Origin Rust (lib.rs:1187):
    ///   matches!(self.entries.get(key), Some(&Entry::Occupied(_)))
    /// Vec::get has no usable vstd spec, rewritten as "bounds check + direct
    /// index" (same semantics).
    /// Upstream doc (lib.rs:1171-1185):
    ///   Return `true` if a value is associated with the given key.
    pub exec fn contains(&self, key: usize) -> (ret: bool)
        ensures
            ret == occ_at(self.entries@, key as int),
    {
        if key < self.entries.len() {
            match &self.entries[key] {
                EntryExec::Occupied(_) => true,
                _ => false,
            }
        } else {
            false
        }
    }

    /// Upstream doc (lib.rs:1038-1057):
    ///   Returns the key of the next vacant entry.
    ///   This function returns the key of the vacant entry which  will be used
    ///   for the next insertion. This is equivalent to
    ///   `slab.vacant_entry().key()`, but it doesn't require mutable access.
    pub exec fn vacant_key(&self) -> (ret: usize)
        ensures
            ret@ == self.next@, // the next insert's key is exactly self.next (see insert: ret_key == old.next)
    {
        self.next // lib.rs:1059
    }

    /// Origin Rust (lib.rs:733-738):
    ///   match self.entries.get(key) {
    ///       Some(Entry::Occupied(val)) => Some(val),
    ///       _ => None,
    ///   }
    /// Vec::get has no usable vstd spec, rewritten as "bounds check + direct
    /// index" (same semantics -- the upstream get(key) returns None exactly
    /// when out of bounds, and branches by discrimination when in bounds).
    /// Upstream doc (lib.rs:718-732):
    ///   Return a reference to the value associated with the given key.
    ///   If the given key is not associated with a value, then `None` is
    ///   returned.
    pub exec fn get(&self, key: usize) -> (ret: Option<&T>)
        ensures
            // Some <=> the key is in bounds and occupied (the machinization of
            // "associated with a value"; occ_at already includes the bounds)
            (ret matches Some(_)) == occ_at(self.entries@, key as int),
            ret matches Some(_) ==> self.entries@.index(key as int) matches EntryExec::Occupied(_),
    {
        if key < self.entries.len() {
            match &self.entries[key] {
                EntryExec::Occupied(val) => Some(val), // lib.rs:735
                _ => None,                             // lib.rs:736
            }
        } else {
            None // get(key) out of bounds -> None (matching the upstream _ => None)
        }
    }

    /// Origin Rust (lib.rs:757-762):
    ///   match self.entries.get_mut(key) {
    ///       Some(&mut Entry::Occupied(ref mut val)) => Some(val),
    ///       _ => None,
    ///   }
    /// Same as get: bounds check + direct index, an equivalent rewrite. Spec note
    /// (the classification-3 revision): an API returning `&mut T` lets the caller
    /// mutate through the reference anyway, so the entries sequence staying
    /// unchanged is **not** part of get_mut's contract face (the upstream makes
    /// no such promise either, and the IndexMut spec does not hand it over for
    /// free); the contract anchors are the unchanged len/next and the
    /// associated-value binding -- entries content changes are left to the caller.
    /// Upstream doc (lib.rs:740-756):
    ///   Return a mutable reference to the value associated with the given key.
    ///   If the given key is not associated with a value, then `None` is
    ///   returned.
    pub exec fn get_mut(&mut self, key: usize) -> (ret: Option<&mut T>)
        ensures
            final(self).len == old(self).len,
            final(self).next == old(self).next,
            final(self).entries@.len() == old(self).entries@.len(),
            (ret matches Some(_)) == occ_at(old(self).entries@, key as int),
            ret matches Some(_)
                ==> old(self).entries@.index(key as int) matches EntryExec::Occupied(_),
    {
        if key < self.entries.len() {
            match &mut self.entries[key] {
                EntryExec::Occupied(val) => Some(val), // lib.rs:759
                _ => None,                             // lib.rs:760
            }
        } else {
            None
        }
    }

    // =============================================================
    // difference-verification batch 2: the capacity-state family (2026-10-30 batch)
    //   with_capacity(lib.rs:322-328)/capacity(:339-341)/clear(:615-619)/
    //   reserve(:369-375)/reserve_exact(:403-409)/Default(:175-179)
    // =============================================================

    /// (the .capacity value lives in the Vec allocation layer, where vstd has no
    /// Vec::capacity spec to carry its value -- see the assume_specification
    /// injected in this file; the "exactly" tier is left unasserted).
    /// Upstream doc (lib.rs:295-321):
    ///   Construct a new, empty `Slab` with the specified capacity.
    ///   The returned slab will be able to store exactly `capacity` without
    ///   reallocating. If `capacity` is 0, the slab will not allocate.
    ///   It is important to note that this function does not specify the *length*
    ///   of the returned slab, but only the capacity. For an explanation of the
    ///   difference between length and capacity, see [Capacity and
    ///   reallocation](index.html#capacity-and-reallocation).
    pub exec fn with_capacity(capacity: usize) -> (s: SlabExec<T>)
        ensures
            slab_inv(&s),
            s.entries@ == Seq::<EntryExec<T>>::empty(), // len()/capacity() carry no value -- see the note above
            s.len == 0,                                 // lib.rs:312 doc example
            s.next == 0,
    {
        // Origin Rust (lib.rs:322-328):
        //   Slab { entries: Vec::with_capacity(capacity), next: 0, len: 0 }
        SlabExec { entries: Vec::with_capacity(capacity), next: 0, len: 0 }
    }

    /// (lib.rs:330) Vec::capacity has no vstd spec; the minimal sound external
    /// spec below is injected (the std Vec invariant capacity >= len; the
    /// stronger exact capacity value -- meaningful only to avoid reallocation
    /// -- is not asserted, delegating that tier to the allocation layer).
    /// Upstream doc (lib.rs:330-338):
    ///   Return the number of values the slab can store without reallocating.
    pub exec fn capacity(&self) -> (ret: usize)
        ensures
            ret@ >= self.entries@.len(), // the Vec invariant -> the lower bound of the slab obligation
    {
        self.entries.capacity() // lib.rs:340
    }

    /// Upstream doc (lib.rs:600-614):
    ///   Clear the slab of all values.
    pub exec fn clear(&mut self)
        ensures
            slab_inv(&*final(self)),
            final(self).entries@ == Seq::<EntryExec<T>>::empty(),
            final(self).len == 0,   // lib.rs:613 doc-example assertion
            final(self).next == 0,
            forall|k: int| !occ_at(final(self).entries@, k), // every key disassociated
    {
        // Origin Rust (lib.rs:615-619):
        //   self.entries.clear();
        //   self.len = 0;
        //   self.next = 0;
        self.entries.clear(); // lib.rs:616 (vstd spec: entries@ == empty)
        self.len = 0;         // lib.rs:617
        self.next = 0;        // lib.rs:618
        proof {
            // chain_ok(empty, 0, 0): cur == es.len() -> true; occ_cnt(empty) == 0 == len
            let ghost es: Seq<EntryExec<T>> = Seq::empty();
            assert(occ_cnt_prefix(es, 0int) == 0int);
            assert(occ_cnt(es) == 0int);
            assert(chain_ok(es, 0int, 0int));
        }
    }

    /// (Model note: a documented, legitimate panic tier, absorbed contractually
    /// by the requires capacity bound as in insert; see the file header.)
    ///
    /// This function's real obligation surface: neither of the two usize
    /// subtractions may underflow:
    ///   * `self.capacity() - self.len` (invariant: len <= entries.len() <= cap), and
    ///   * `additional - (self.entries.len() - self.len)`
    ///     (taking the reserve branch => cap - len < additional; cap >=
    ///     entries.len() => entries.len() - len < additional => the difference
    ///     is positive).
    /// Both are discharged by slab_inv + the injected capacity lower bound --
    /// the upstream has no overflow face there, in robustness terms.
    /// Upstream doc (lib.rs:343-368):
    ///   Reserve capacity for at least `additional` more values to be stored
    ///   without allocating.
    ///   `reserve` does nothing if the slab already has sufficient capacity for
    ///   `additional` more values. If more capacity is required, a new segment of
    ///   memory will be allocated and all existing values will be copied into it.
    ///   As such, if the slab is already very large, a call to `reserve` can end
    ///   up being expensive.
    ///   The slab may reserve more than `additional` extra space in order to
    ///   avoid frequent reallocations. Use `reserve_exact` instead to guarantee
    ///   that only the requested space is allocated.
    ///   # Panics
    ///   Panics if the new capacity exceeds `isize::MAX` bytes.
    pub exec fn reserve(&mut self, additional: usize)
        requires
            slab_inv(self),
            // capacity-overflow tier (the isize::MAX bytes the # Panics declares), modeled
            self.entries@.len() + additional@ < usize::MAX@,
        ensures
            slab_inv(&*final(self)),
            final(self).entries@ == old(self).entries@,
            final(self).len == old(self).len,
            final(self).next == old(self).next,
    {
        // Origin Rust (lib.rs:369-375) -- line-by-line faithful:
        //   if self.capacity() - self.len >= additional { return; }
        //   let need_add = additional - (self.entries.len() - self.len);
        //   self.entries.reserve(need_add);
        if self.capacity() - self.len >= additional { // lib.rs:370
            return; // lib.rs:371
        }
        let need_add = additional - (self.entries.len() - self.len); // lib.rs:373
        self.entries.reserve(need_add); // lib.rs:374 (vstd spec: entries@ unchanged)
    }

    /// The obligation surface equals reserve's (the same ropework subtrace).
    /// Upstream doc (lib.rs:377-402):
    ///   Reserve the minimum capacity required to store exactly `additional`
    ///   more values.
    ///   `reserve_exact` does nothing if the slab already has sufficient capacity
    ///   for `additional` more values. If more capacity is required, a new segment
    ///   of memory will be allocated and all existing values will be copied into
    ///   it.  As such, if the slab is already very large, a call to `reserve` can
    ///   end up being expensive.
    ///   Note that the allocator may give the slab more space than it requests.
    ///   Therefore capacity can not be relied upon to be precisely minimal.
    ///   Prefer `reserve` if future insertions are expected.
    ///   # Panics
    ///   Panics if the new capacity exceeds `isize::MAX` bytes.
    pub exec fn reserve_exact(&mut self, additional: usize)
        requires
            slab_inv(self),
            self.entries@.len() + additional@ < usize::MAX@,
        ensures
            slab_inv(&*final(self)),
            final(self).entries@ == old(self).entries@,
            final(self).len == old(self).len,
            final(self).next == old(self).next,
    {
        // Origin Rust (lib.rs:403-409) -- line-by-line faithful:
        //   if self.capacity() - self.len >= additional { return; }
        //   let need_add = additional - (self.entries.len() - self.len);
        //   self.entries.reserve_exact(need_add);
        if self.capacity() - self.len >= additional { // lib.rs:404
            return; // lib.rs:405
        }
        let need_add = additional - (self.entries.len() - self.len); // lib.rs:407
        self.entries.reserve_exact(need_add); // lib.rs:408
    }

    // =============================================================
    // difference-verification batch 3 (cont): iterator factories (the
    // one-entry-per-name mapping of the Enumerate-cursor model for the upstream
    // Iter/IterMut/IntoIter; see the batch-3 file notes)
    // =============================================================

    // BLOCKED (batch 4): vacant_entry_insert (= VacantEntry::insert,
    //   lib.rs:1445-1452) -- the composite borrow chain of lending out an
    //   'a mut and then mutating through insert_at failed repeatedly in Verus
    //   (tying the insert_at postcondition to the IndexMut return borrow;
    //   same-shape insert rewrites / pruned asserts / block reshuffles were all
    //   tried); recorded in the batch-4 section of out/harness-inventory.md.
    //   Its full verifiable obligation surface is carried by combinations of
    //   already-verified units: insert_at / insert (the core insert
    //   obligations) and index_mut_exec (the slot readout borrow); the
    //   harness combination anchor is
    //   verified/harness/cover_batch4_vacant_entry_index.rs.

    // -------------------------------------------------------------
    // ops::Index / ops::IndexMut (lib.rs:1268-1288) -- the "invalid key" panic
    //   is the same documented tier as remove (the general Rust Index/IndexMut
    //   trait convention: an invalid index panics; the upstream verbatim is
    //   panic!("invalid key")). Transcription: contractualized as requires +
    //   a faithful panic branch.
    // -------------------------------------------------------------

    /// Origin Rust (lib.rs:1268-1278):
    ///   impl<T> ops::Index<usize> for Slab<T> {
    ///       fn index(&self, key: usize) -> &T {
    ///           match self.entries.get(key) {
    ///               Some(Entry::Occupied(v)) => v,
    ///               _ => panic!("invalid key"),
    ///           }
    ///       }
    ///   }
    pub exec fn index_exec(&self, key: usize) -> (ret: &T)
        requires
            occ_at(self.entries@, key as int), // the "invalid key" panic, contractualized
        ensures
            self.entries@.index(key as int) == EntryExec::Occupied(*ret),
    {
        if key < self.entries.len() {
            match &self.entries[key] {
                EntryExec::Occupied(v) => v,         // lib.rs:1274
                _ => panic!("invalid key"),           // lib.rs:1275
            }
        } else {
            panic!("invalid key") // lib.rs:1275 (an out-of-range get => None => the same panic)
        }
    }

    /// Origin Rust (lib.rs:679-684):
    ///   Iter { entries: self.entries.iter().enumerate(), len: self.len }
    /// transcribed as IterExec (the Enumerate cursor materialized as pos=0; len copied).
    /// Upstream doc (lib.rs:655-678):
    ///   Return an iterator over the slab.
    ///   This function should generally be **avoided** as it is not efficient.
    ///   Iterators must iterate over every slot in the slab even if it is
    ///   vacant. As such, a slab with a capacity of 1 million but only one
    ///   stored value must still iterate the million slots.
    pub exec fn iter(&self) -> (ret: IterExec<T>)
        requires
            slab_inv(self),
        ensures
            iter_inv(&ret),
            ret.pos == 0,               // enumerate starts at 0
            ret.slab == self,
            ret.len@ == self.len@,      // the ExactSize initial value
    {
        IterExec { slab: self, pos: 0, len: self.len } // lib.rs:681-683
    }

}

// BLOCKED (batch 3): iter_mut()/IterMut::next -- the Verus restriction on
// 'a mut self-referential structures (E0499/E0502/E0503); recorded in
// out/harness-inventory.md; no placeholder injected.

// =====================================================================
// difference-verification batch 3: the iterator family (2026-11-03 batch):
//   iter (lib.rs:679), the get-side Iter + Iter::next (:1529), size_hint (:1541),
//   len (:1561); iter_mut (:711) + IterMut::next (:1573);
//   IntoIterator(:1294)+IntoIter::next(:1485)/size_hint(:1497)
//
// Lossy-abstraction disclosure: the upstream Iter/IterMut/IntoIter ride on
// Enumerate<slice::Iter / SliceIterMut / vec::IntoIter> compounds -- none of
// the three std iterator layers has a vstd spec, so a verbatim transcription
// is unverifiable. Equivalent transcription via the explicit "slab reference +
// pos + len" index model:
//   * semantic fidelity: next() scans forward from pos, skips Vacant, returns
//     (key, &v | &mut v) on Occupied with len -= 1, and None on exhaustion --
//     in one-to-one correspondence with the Enumerate version (pos is the
//     enumerate cursor; len the remaining ExactSizeIterator count);
//   * the counting invariant is maintained with suffix_occ (the number of
//     Occupied within [pos, len)), and the underflow obligation of len -= 1 is
//     discharged by "current slot Occupied => suffix >= 1" -- that obligation is
//     exactly the transcription carrier of the upstream
//     debug_assert_eq!(self.len, 0) / self.len -= 1.
// =====================================================================

/// The Occupied count within [lo, es.len()) (the machinization of the remaining iteration count).
pub open spec fn suffix_occ<T>(es: Seq<EntryExec<T>>, lo: int) -> int {
    occ_cnt_prefix(es, es.len() as int) - occ_cnt_prefix(es, lo)
}


/// IterExec structural invariant (iterator well-formedness).
pub open spec fn iter_inv<'a, T>(it: &IterExec<'a, T>) -> bool {
    it.pos@ <= it.slab.entries@.len()
        && it.len@ == suffix_occ(it.slab.entries@, it.pos as int)
        && it.slab.entries@.len() < usize::MAX@ - 1
}

/// Origin Rust (lib.rs:243-246):
///   pub struct Iter<'a, T> {
///       entries: iter::Enumerate<slice::Iter<'a, Entry<T>>>,
///       len: usize,
///   }
/// Enumerate/Iter has no vstd spec, carried by the equivalent "slab reference
/// + pos cursor (the enumerate counterpart) + len (the ExactSize count)" model
/// -- pos == the enumerate cursor.
pub struct IterExec<'a, T> {
    pub slab: &'a SlabExec<T>,
    pub pos: usize,
    pub len: usize,
}

impl<'a, T> IterExec<'a, T> {
    /// Origin Rust (lib.rs:1541-1543):fn size_hint(&self) -> (self.len, Some(self.len))
    pub exec fn size_hint(&self) -> (ret: (usize, Option<usize>))
        ensures
            ret.0@ == self.len@,
            ret.1 matches Some(h) ==> h@ == self.len@,
    {
        (self.len, Some(self.len)) // lib.rs:1542
    }

    /// Origin Rust (lib.rs:1560-1563 ExactSizeIterator):
    ///   fn len(&self) -> usize { self.len }
    pub exec fn iter_len(&self) -> (ret: usize)
        ensures
            ret@ == self.len@,
    {
        self.len // lib.rs:1562
    }

    /// Origin Rust (lib.rs:1529-1538):
    ///   for (key, entry) in &mut self.entries {
    ///       if let Entry::Occupied(ref v) = *entry {
    ///           self.len -= 1;
    ///           return Some((key, v));
    ///       }
    ///   }
    ///   debug_assert_eq!(self.len, 0);
    ///   None
    /// transcription: for->while is carried by the explicit enumerate cursor pos;
    /// the key obligations are `self.len -= 1` not underflowing (a hit slot is
    /// Occupied => the remaining count >= 1) and debug_assert_eq!(self.len, 0)
    /// (machinized through iter_inv at exhaustion).
    pub exec fn next(&mut self) -> (ret: Option<(usize, &'a T)>)
        requires
            iter_inv(&*old(self)),
        ensures
            iter_inv(&*final(self)),
            final(self).pos@ >= old(self).pos@, // cursor monotone
            // Some: the hit key with its associated value; pos == k+1; len-1
            ret matches Some((k, v)) ==> (
                old(self).pos@ <= k@ < old(self).slab.entries@.len()
                && old(self).slab.entries@.index(k as int) == EntryExec::Occupied(*v)
                && final(self).pos@ == k@ + 1
                && final(self).len@ == old(self).len@ - 1
            ),
            // None: exhausted (pos at the end, len exactly 0 -- the debug_assert
            // obligation, machinized)
            ret matches None ==> (
                final(self).pos@ == old(self).slab.entries@.len()
                && final(self).len@ == old(self).len@ == 0int // exhausted, nothing consumed
            ),
    {
        // on entry self == old(self): pre_es is old(self).slab.entries@ (&slab
        // is read-only, unchanged throughout -- the match holds a shared borrow)
        let ghost pre_es = self.slab.entries@;
        while self.pos < self.slab.entries.len()
            invariant
                iter_inv(&*self),
                self.pos@ >= old(self).pos@,
                self.len@ == old(self).len@, // the loop only moves the cursor, never the count
                self.slab.entries@ == pre_es,
                pre_es == old(self).slab.entries@,
                forall|j: int| #![trigger pre_es.index(j)]
                    old(self).pos@ <= j < self.pos@
                        ==> pre_es.index(j) matches EntryExec::Vacant(_),
            decreases self.slab.entries@.len() - self.pos@,
        {
            match &self.slab.entries[self.pos] {
                EntryExec::Occupied(v) => {
                    proof {
                        let ghost es = pre_es;
                        let ghost lo = self.pos;
                        suffix_step_occupied(es, lo as int);
                        // hit => suffix(es,lo) = suffix(es,lo+1)+1 >= 1 => len >= 1
                        assert(occ_cnt_prefix(es, (lo + 1) as int)
                            == occ_cnt_prefix(es, lo as int) + 1);
                        occ_monotone(es, (lo + 1) as int, es.len() as int);
                        assert(es.index(lo as int) matches EntryExec::Occupied(_));
                        // len == suffix(es,lo): overall >= prefix(lo)+1 - prefix(lo) >= 1
                        // len == suffix(es,lo) => len >= 1: len -= 1 does not underflow
                    }
                    let k = self.pos; // the current enumerate key
                    self.len -= 1; // lib.rs:1532
                    self.pos += 1; // enumerate.next() consumes 1 slot
                    return Some((k, v)); // lib.rs:1533
                }
                EntryExec::Vacant(_) => {
                    proof {
                        let ghost es = self.slab.entries@;
                        let ghost lo = self.pos;
                        suffix_skip_vacant(es, lo as int);
                    }
                    self.pos += 1; // enumeration continues (skip vacant)
                }
            }
        }
        // loop exit: pos == es.len() => iter_inv => len == suffix(es, pos) == 0
        None // lib.rs:1537
    }
}



/// Origin Rust (lib.rs:237-240):
///   pub struct IntoIter<T> {
///       entries: iter::Enumerate<vec::IntoIter<Entry<T>>>,
///       len: usize,
///   }
/// vec::IntoIter/Enumerate has no vstd spec, carried by the equivalent "owned
/// Vec + pos cursor" model; next's consuming readout is implemented over the
/// core::mem::swap vstd spec (the occupied slot is swapped for a dummy Vacant,
/// matching the per-item-invalidation semantics of vec::IntoIter).
pub struct IntoIterExec<T> {
    pub entries: Vec<EntryExec<T>>,
    pub pos: usize,
    pub len: usize,
}

pub open spec fn into_iter_inv<T>(it: &IntoIterExec<T>) -> bool {
    it.pos@ <= it.entries@.len()
        && it.len@ == suffix_occ(it.entries@, it.pos as int)
        && it.entries@.len() < usize::MAX@ - 1
}

/// IntoIter::next's readout primitive: swap the entry at position lo with the
/// dummy, handing the caller the owned value and invalidating the slot (the
/// vec::IntoIter per-item-invalidation counterpart). The mem::swap + IndexMut
/// update relation failed repeatedly as direct asserts inside the loop body,
/// so it is factored into a statement-level-spec, loop-free helper (the same
/// shape as try_remove's success chain).
pub exec fn swap_take_dummy<T>(es: &mut Vec<EntryExec<T>>, lo: usize)
    -> (ret: EntryExec<T>)
    requires
        lo@ < es@.len(),
    ensures
        final(es)@ == old(es)@.update(lo as int, EntryExec::Vacant(0usize)),
        ret == old(es)@.index(lo as int),
{
    let mut dummy = EntryExec::Vacant(0usize); // the invalidation sentinel
    core::mem::swap(&mut es[lo], &mut dummy);
    dummy
}

/// Origin Rust (lib.rs:1290-1299):
///   impl<T> IntoIterator for Slab<T> {
///       fn into_iter(self) -> IntoIter<T> {
///           IntoIter { entries: self.entries.into_iter().enumerate(), len: self.len }
///       }
///   }
/// transcription: the into_iter().enumerate() cursor materialized as pos=0; the Vec handover (self.entries moved).
pub exec fn into_iter_exec<T>(s: SlabExec<T>) -> (ret: IntoIterExec<T>)
    requires
        slab_inv(&s),
    ensures
        into_iter_inv(&ret),
        ret.entries@ == s.entries@, // into_iter keeps the contents; the cursor starts at 0
        ret.pos == 0,
        ret.len@ == s.len@,
{
    IntoIterExec { entries: s.entries, pos: 0, len: s.len } // lib.rs:1295-1298
}

impl<T> IntoIterExec<T> {
    /// Origin Rust (lib.rs:1497-1499):fn size_hint = (len, Some(len))
    pub exec fn size_hint(&self) -> (ret: (usize, Option<usize>))
        ensures
            ret.0@ == self.len@,
            ret.1 matches Some(h) ==> h@ == self.len@,
    {
        (self.len, Some(self.len)) // lib.rs:1498
    }

    /// Origin Rust (lib.rs:1516-1519 ExactSizeIterator::len)
    pub exec fn iter_len(&self) -> (ret: usize)
        ensures
            ret@ == self.len@,
    {
        self.len // lib.rs:1518
    }

    /// Origin Rust (lib.rs:1485-1494):
    ///   for (key, entry) in &mut self.entries {
    ///       if let Entry::Occupied(v) = entry { self.len -= 1; return Some((key, v)); }
    ///   }
    ///   debug_assert_eq!(self.len, 0);
    ///   None
    /// consuming-readout transcription: Occupied(v) swapped out with the dummy
    /// Vacant (the vec::IntoIter post-iteration invalidation counterpart -- the
    /// upstream core readout pattern `match entry` moves the value).
    #[verifier::loop_isolation(false)]
    pub exec fn next(&mut self) -> (ret: Option<(usize, T)>)
        requires
            into_iter_inv(&*old(self)),
        ensures
            into_iter_inv(&*final(self)),
            final(self).pos@ >= old(self).pos@,
            final(self).entries@.len() == old(self).entries@.len(),
            ret matches Some((k, _)) ==> (
                old(self).pos@ <= k@ < old(self).entries@.len()
                && (final(self).entries@.index(k as int) matches EntryExec::Vacant(_)) // consumed / invalidated
                && final(self).pos@ == k@ + 1
                && final(self).len@ == old(self).len@ - 1
            ),
            ret matches None ==> (
                final(self).pos@ == old(self).entries@.len()
                && final(self).len@ == old(self).len@ == 0int
            ),
    {
        let ghost pre_es = self.entries@; // == old(self).entries@ (at fn entry)
        while self.pos < self.entries.len()
            invariant
                into_iter_inv(&*self),
                self.pos@ >= old(self).pos@,
                self.len@ == old(self).len@,
                self.entries@.len() == pre_es.len(),
                pre_es.len() == old(self).entries@.len(),
                // the unscanned-segment frame (the swap touched only consumed slots;
                // next may re-enter mid-way)
                forall|j: int| #![trigger pre_es.index(j)]
                    self.pos@ <= j < pre_es.len()
                        ==> self.entries@.index(j) == pre_es.index(j),
            decreases self.entries@.len() - self.pos@,
        {
            // the discrimination is captured as a pure value first (the match's
            // pattern facts do not outlive the borrow scope; carried across
            // the swap by spec-mode evaluation)
            let ghost occ_here = pre_es.index(self.pos as int) matches EntryExec::Occupied(_);
            let ghost lo: int = self.pos as int;
            match &self.entries[self.pos] {
                EntryExec::Occupied(_) => {
                    proof {
                        assert(occ_here);
                        assert(self.entries@.index(lo) == pre_es.index(lo));
                        suffix_step_occupied(pre_es, lo);
                        // len == suffix(pre_es,lo) => >= 1: len -= 1 does not underflow
                        occ_monotone(pre_es, lo + 1, pre_es.len() as int);
                    }
                    let k = self.pos;
                    proof {
                        // len == suffix(cur,lo) on a hit => >= 1: len -= 1 does not underflow
                        let ghost cur = self.entries@;
                        assert(cur.index(lo) == pre_es.index(lo));
                        suffix_step_occupied(cur, lo);
                        occ_monotone(cur, lo + 1, cur.len() as int);
                    }
                    let ghost es0 = self.entries@; // the pre-swap base (the iteration-entry frame)
                    let out = swap_take_dummy(&mut self.entries, self.pos);
                    proof {
                        // helper contract: entries@ == es0.update(lo, Vacant(0)), and
                        // out == es0[lo] == pre_es[lo] -> the Occupied discrimination carries
                        assert(self.entries@ == es0.update(lo, EntryExec::Vacant(0usize)));
                        assert(self.entries@.index(lo) matches EntryExec::Vacant(_));
                        assert(out matches EntryExec::Occupied(_));
                        // swap-out bookkeeping (base es0; the invariant's
                        // len == suffix(es0,lo) is the current frame):
                        //   occ_cnt(es.upd) == occ_cnt(es0)-1 (occ_cnt_update)
                        //   occ_prefix(es.upd, lo+1) == occ_prefix(es0, lo) (upd_vacant_step)
                        // => suffix(es.upd, lo+1) == suffix(es0, lo) - 1
                        occ_cnt_update(es0, lo, EntryExec::Vacant(0usize));
                        upd_vacant_step(es0, lo);
                        assert(suffix_occ(self.entries@, lo + 1)
                            == suffix_occ(es0, lo) - 1);
                        // unscanned-segment frame maintenance (the update touches only lo; es0 inherits pre_es through the invariant)
                        assert forall|j: int| lo + 1 <= j < pre_es.len()
                            implies self.entries@.index(j) == pre_es.index(j) by {
                            vstd::seq::lemma_seq_update_different(es0, lo, j, EntryExec::Vacant(0usize));
                        };
                    }
                    self.len -= 1; // lib.rs:1488
                    self.pos += 1;
                    if let EntryExec::Occupied(v) = out {
                        return Some((k, v)); // lib.rs:1489
                    }
                    // out is proven Occupied; the fall-through is structurally unreachable
                }
                EntryExec::Vacant(_) => {
                    proof {
                        assert(!occ_here);
                        suffix_skip_vacant(pre_es, lo);
                    }
                    self.pos += 1;
                }
            }
        }
        None // lib.rs:1493
    }
}

impl SlabExec<u64> {
    // -------------------------------------------------------------
    // retain (lib.rs:1190-1228; the predicate concretized per tests/slab.rs:222-231)
    // -------------------------------------------------------------

    /// Concretization note (a lossy abstraction): the closure parameter of the
    /// upstream `retain<F: FnMut(usize, &mut T) -> bool>` is not supported at
    /// Verus's exec layer, so it is inlined with the tests/slab.rs:228-231
    /// predicate `|key, x| *x % 2 == 0` (T fixed to u64). All panic sites (the
    /// index bounds of self.entries[i]; the documented invalid-key
    /// precondition of self.remove(i)) keep their real obligations.
    /// Upstream doc (lib.rs:1190-1213):
    ///   Retain only the elements specified by the predicate.
    ///   In other words, remove all elements `e` such that `f(usize, &mut e)`
    ///   returns false. This method operates in place and preserves the key
    ///   associated with the retained values.
    pub exec fn retain_even(&mut self)
        requires
            slab_inv(self),
        ensures
            slab_inv(&*final(self)),
            final(self).entries@.len() == old(self).entries@.len(),
            // exact count: the len decrease is exactly the number of dropped slots
            final(self).len@ == old(self).len@ - drop_cnt_prefix(
                old(self).entries@, old(self).entries@.len() as int),
            // key preservation (rustdoc: "preserves the key associated with the
            // retained values")
            forall|j: int|
                0 <= j < old(self).entries@.len() && even_keep(old(self).entries@.index(j))
                ==> final(self).entries@.index(j) == old(self).entries@.index(j),
            // occupied slots failing the predicate are dropped (turned Vacant)
            forall|j: int|
                0 <= j < old(self).entries@.len() && odd_occ(old(self).entries@.index(j))
                ==> final(self).entries@.index(j) matches EntryExec::Vacant(_),
    {
        /* Origin Rust (lib.rs:1218-1227):
             for i in 0..self.entries.len() {
                 let keep = match self.entries[i] {
                     Entry::Occupied(ref mut v) => f(i, v),
                     _ => true,
                 };
                 if !keep { self.remove(i); }
             }
           for->while (Verus does not support that for form); f inlined as *v % 2 == 0.*/
        let ghost pre_es = self.entries@;
        let ghost pre_len = self.len@;
        let mut i: usize = 0;
        while i < self.entries.len()
            invariant
                i <= self.entries.len(),
                slab_inv(self),
                self.entries@.len() == pre_es.len(),
                self.len@ == pre_len - drop_cnt_prefix(pre_es, i as int),
                forall|j: int| 0 <= j < i && even_keep(pre_es.index(j))
                    ==> self.entries@.index(j) == pre_es.index(j),
                forall|j: int| 0 <= j < i && odd_occ(pre_es.index(j))
                    ==> self.entries@.index(j) matches EntryExec::Vacant(_),
                forall|j: int| i <= j < pre_es.len()
                    ==> self.entries@.index(j) == pre_es.index(j),
            decreases self.entries@.len() - i @,
        {
            let keep: bool = match self.entries[i] {
                EntryExec::Occupied(v) => v % 2 == 0, // tests/slab.rs:230 (u64 is Copy; taking the value suffices)
                _ => true, // lib.rs:1221
            };
            if !keep {
                let ghost iter_es = self.entries@;
                let ghost iter_next = self.next@;
                self.remove(i); // lib.rs:1225
                proof {
                    // remove(i) changes exactly slot i; the suffix frame (the proven helper)
                    suffix_update_frame(iter_es, i as int, iter_next as int,
                        i as int + 1, pre_es.len() as int);
                    assert(self.entries@ == iter_es.update(i as int,
                        EntryExec::Vacant(iter_next as usize)));
                }
            }
            i += 1;
        }
    }
}

// =====================================================================
// difference-verification batch 2 (cont): Default for SlabExec<T> (upstream lib.rs:175-179)
// Origin Rust:
//   impl<T> Default for Slab<T> {
//       fn default() -> Self { Slab::new() }
//   }
// Semantic fidelity: default() == new().
// =====================================================================
impl<T> Default for SlabExec<T> {
    fn default() -> (s: Self)
        ensures
            slab_inv(&s),
            s.entries@ == Seq::<EntryExec<T>>::empty(),
            s.len == 0,
            s.next == 0,
    {
        SlabExec::new() // lib.rs:177 Slab::new()
    }
}


// =====================================================================
// obligation-anchor witnesses and reachability proofs: after the two-zone
// split this section keeps only the library-side obligation anchors (double-
// delete doc anchor, repair counter-example, F1 reachability witness); the UT
// transcription lives in harness/ut_slab.rs.
// =====================================================================

/// witness: tests/slab.rs:105-110 (double_remove_panics, the # Panics documented tier).
/// The call-site obligation failure (remove's occ_at precondition unsatisfied)
/// = the obligation-ized reproduction of remove's documented "Panics if `key` is
/// not associated with a value" -- read as class 2 (documented, working as
/// intended). **This function expects exactly one error, at the remove call.**
pub exec fn witness_double_remove_docpanic() -> u64 {
    let mut s = SlabExec::<u64>::new();
    let key = s.insert(123); // UT:107
    let _ = s.remove(key); // UT:108
    s.remove(key) // UT:109 <-- EXPECTED ERROR (the # Panics tier)
}

/// witness (control): the boundary key == entries.len() returns None normally (F1's
/// control group; immediate from the fixed version's contract -- the upstream
/// version, called the same way, does not panic either, since mid == len satisfies
/// the split precondition; that fact was tested empirically in the "normal"
/// branch of out/f1_runtime_repro.rs and the panic-audit PoC control).
pub exec fn witness_boundary_none_fixed() -> (ok: bool)
    ensures ok,
{
    let mut v: Vec<EntryExec<u64>> = Vec::new();
    v.push(EntryExec::Occupied(7));
    v.push(EntryExec::Occupied(9));
    let mut s = SlabExec { entries: v, len: 2, next: 2 };
    let out = s.get2_mut_fixed(2, 0);
    assert(out matches None); // key2 = 0 is a live key, but key1 = len => the documented None
    true
}


// =====================================================================
// difference-verification batch 4: the VacantEntry family + Index/IndexMut
//   (2026-11-03 batch): vacant_entry (lib.rs:1085-1090), VacantEntry::key
//   (:1475-1477), VacantEntry::insert (:1445-1452), Index (:1268-1278),
//   IndexMut (:1280-1288).
// =====================================================================

/// Origin Rust (lib.rs:230-234):
///   #[derive(Debug)]
///   pub struct VacantEntry<'a, T> {
///       slab: &'a mut Slab<T>,
///       key: usize,
///   }
/// derive(Debug) is irrelevant to control flow; dropped.
pub struct VacantEntryExec<'a, T> {
    pub slab: &'a mut SlabExec<T>,
    pub key: usize,
}

// BLOCKED note (2026-11-03, batch 4): VacantEntry::insert's by-value self form
// (self.slab an 'a-mut field, returning an 'a mut) belongs to the same Verus
// borrow-restriction family as this batch's IterMut -- reliably recorded in
// the batch-4 section of out/harness-inventory.md. All of the upstream
// method's verifiable semantics are carried by SlabExec::vacant_entry_insert
// below, in the equivalent "mut slab + key" parameter form (no body-side
// difference from lending out the mut).

impl<'a, T> VacantEntryExec<'a, T> {
    /// Origin Rust (lib.rs:1475-1477):fn key(&self) -> usize { self.key }
    /// Upstream doc (lib.rs:1454-1474):
    ///   Return the key associated with this entry.
    ///   A value stored in this entry will be associated with this key.
    pub exec fn key(&self) -> (ret: usize)
        ensures
            ret@ == self.key@,
    {
        self.key // lib.rs:1477
    }
}

impl<T> SlabExec<T> {
    /// Origin Rust (lib.rs:1085-1090):
    ///   VacantEntry { key: self.next, slab: self }
    /// Upstream doc (lib.rs:1062-1084):
    ///   Return a handle to a vacant entry allowing for further manipulation.
    ///   This function is useful when creating values that must contain their
    ///   slab key. The returned `VacantEntry` reserves a slot in the slab and is
    ///   able to query the associated key.
    pub exec fn vacant_entry(&mut self) -> (ret: VacantEntryExec<T>)
        requires
            slab_inv(self),
        ensures
            ret.key@ == old(self).next@, // lib.rs:1087 key: self.next
            // ret.slab holding this slab is statically guaranteed by the exclusivity
            // of the &mut return type; a field-by-field comparison would add
            // disambiguation obligations to the &mut lend in Verus, so it is not written.
    {
        let key = self.next; // take the field value first (borrow separation; the same semantics as upstream)
        VacantEntryExec { slab: self, key } // lib.rs:1086-1089
    }

    /// Origin Rust (lib.rs:1280-1288):
    ///   impl<T> ops::IndexMut<usize> for Slab<T> {
    ///       fn index_mut(&mut self, key: usize) -> &mut T {
    ///           match self.entries.get_mut(key) {
    ///               Some(&mut Entry::Occupied(ref mut v)) => v,
    ///               _ => panic!("invalid key"),
    ///           }
    ///       }
    ///   }
    /// (returning &mut T => the contents are mutable; handled like get_mut -- no entries-content clause)
    pub exec fn index_mut_exec(&mut self, key: usize) -> (ret: &mut T)
        requires
            occ_at(self.entries@, key as int),
        ensures
            final(self).len == old(self).len,
            final(self).next == old(self).next,
            final(self).entries@.len() == old(self).entries@.len(),
            // the hit slot's discrimination is preserved: the value is mutable
            // through &mut but the slot occupancy (the discriminant) is not --
            // carried by the IndexMut spec's update relation (no change in the
            // occ discrimination).
            old(self).entries@.index(key as int) matches EntryExec::Occupied(_),
    {
        if key < self.entries.len() {
            match &mut self.entries[key] {
                EntryExec::Occupied(v) => v,         // lib.rs:1284
                _ => panic!("invalid key"),           // lib.rs:1285
            }
        } else {
            panic!("invalid key") // lib.rs:1285
        }
    }
}

// =====================================================================
// difference-verification batch 5: the unsafe getter family (2026-11-03 batch):
//   get_unchecked(lib.rs:881-886)/get_unchecked_mut(:913-918)/
//   get2_unchecked_mut(:947-958)
//
// Doc contract (the lib.rs:866-868 # Safety verbatim):
//   "The key must be within bounds."
// (get2_unchecked_mut adds the bullet "The condition key1 != key2 must hold.")
//
// D1 core: # Safety promises only within bounds -- not occupancy. An in-bounds
// vacant key satisfies every Safety clause yet still falls into the
// `_ => unreachable!()` arm (the panic branches below -- upstream unsafe fn,
// the caller's UB -- are the expected-error anchors).
// =====================================================================

impl<T> SlabExec<T> {
    /// Origin Rust (lib.rs:881-886):
    ///   pub unsafe fn get_unchecked(&self, key: usize) -> &T {
    ///       match *self.entries.get_unchecked(key) {
    ///           Entry::Occupied(ref val) => val,
    ///           _ => unreachable!(),
    ///       }
    ///   }
    /// Vec::get_unchecked has no vstd spec; the # Safety within-bounds clause is
    /// contractualized as requires, and the body is an equivalent direct-index
    /// rewrite (when bounds hold, Vec::get_unchecked(key) reads entries[key]).
    /// Upstream doc (lib.rs:859-880):
    ///   Return a reference to the value associated with the given key without
    ///   performing bounds checking.
    ///   For a safe alternative see [`get`](Slab::get).
    ///   This function should be used with care.
    ///   # Safety
    ///   The key must be within bounds.
    pub exec fn get_unchecked_exec(&self, key: usize) -> (ret: &T)
        requires
            key@ < self.entries@.len(), // the lib.rs:868 legitimacy criterion (the sole Safety clause)
        ensures
            self.entries@.index(key as int) matches EntryExec::Occupied(_),
            self.entries@.index(key as int) == EntryExec::Occupied(*ret),
    {
        match &self.entries[key] {
            EntryExec::Occupied(v) => v,  // lib.rs:883
            _ => panic!("internal constraint violated"), // lib.rs:884 unreachable!() <-- D1 obligation anchor (expected error)
        }
    }

    /// Origin Rust (lib.rs:913-918): the same-shape &mut version; same reading.
    /// Upstream doc (lib.rs:888-912):
    ///   Return a mutable reference to the value associated with the given key
    ///   without performing bounds checking.
    ///   For a safe alternative see [`get_mut`](Slab::get_mut).
    ///   This function should be used with care.
    ///   # Safety
    ///   The key must be within bounds.
    pub exec fn get_unchecked_mut_exec(&mut self, key: usize) -> (ret: &mut T)
        requires
            key@ < self.entries@.len(), // the lib.rs:897 legitimacy criterion (the sole Safety clause)
        ensures
            final(self).len == old(self).len,
            final(self).next == old(self).next,
            final(self).entries@.len() == old(self).entries@.len(),
            old(self).entries@.index(key as int) matches EntryExec::Occupied(_),
    {
        match &mut self.entries[key] {
            EntryExec::Occupied(v) => v,  // lib.rs:916
            _ => panic!("internal constraint violated"), // lib.rs:917 unreachable!() <-- D1 obligation anchor (expected error)
        }
    }

    /// Origin Rust (lib.rs:947-958):
    ///   pub unsafe fn get2_unchecked_mut(&mut self, key1: usize, key2: usize)
    ///       -> (&mut T, &mut T) {
    ///       debug_assert_ne!(key1, key2);
    ///       let ptr = self.entries.as_mut_ptr();
    ///       let ptr1 = ptr.add(key1);
    ///       let ptr2 = ptr.add(key2);
    ///       match (&mut *ptr1, &mut *ptr2) { (&mut Occ(v1), &mut Occ(v2)) => (v1, v2), _ => unreachable!() }
    ///   }
    /// Raw pointers have no Verus carrier; rewritten equivalently as the
    /// "split_at_mut(lo, hi) zero-segment/other-segment dual read" under
    /// key1 != key2 (equivalent in semantics only: the max-key segment reads
    /// the other key, the base segment reads it directly -- matching ptr.add).
    /// Upstream doc (lib.rs:920-946):
    ///   Return two mutable references to the values associated with the two
    ///   given keys simultaneously without performing bounds checking and safety
    ///   condition checking.
    ///   For a safe alternative see [`get2_mut`](Slab::get2_mut).
    ///   This function should be used with care.
    ///   # Safety
    ///   - Both keys must be within bounds.
    ///   - The condition `key1 != key2` must hold.
    pub exec fn get2_unchecked_mut_exec(&mut self, key1: usize, key2: usize)
        -> (ret: (&mut T, &mut T))
        requires
            key1@ < self.entries@.len(),
            key2@ < self.entries@.len(), // lib.rs:930 Safety:within bounds
            key1@ != key2@,               // lib.rs:931 Safety:condition key1 != key2
        ensures
            // SPEC-DOC MISMATCH (unreported): the # Safety doc promises the
            // pair is returned whenever (both keys within bounds, key1 != key2),
            // but an in-bounds vacant slot satisfies every listed condition and
            // still falls into the `_ => unreachable!()` panic arm -- the promised
            // clause is unprovable from the doc-derived requires; this spec keeps
            // the implementation-faithful form (the panic arms below are the
            // expected errors).
            final(self).len == old(self).len,
            final(self).next == old(self).next,
            final(self).entries@.len() == old(self).entries@.len(),
    {
        // the debug_assert_ne! (lib.rs:948) is a release-mode no-op; the obligation already sits in the requires
        let lo = if key1 < key2 { key1 } else { key2 };
        let (slice1, slice2) = self.entries.split_at_mut(lo);
        let (r1, r2) = if key1 > key2 {
            match (slice1.get_mut(key2), slice2.get_mut(0)) {
                (Some(EntryExec::Occupied(ref mut v1)), Some(EntryExec::Occupied(ref mut v2))) => (v1, v2),
                _ => panic!("internal constraint violated"), // lib.rs:956 unreachable!() <-- D1 obligation anchor (expected error)
            }
        } else {
            match (slice1.get_mut(key1), slice2.get_mut(0)) {
                (Some(EntryExec::Occupied(ref mut v1)), Some(EntryExec::Occupied(ref mut v2))) => (v1, v2),
                _ => panic!("internal constraint violated"),
            }
        };
        (r1, r2)
    }
}

// ===========================================================================
// Proof lemmas (occupancy, chain and suffix-count bookkeeping; moved to the end
// of the file so the exec implementations read directly -- only the order changed,
// signatures and contracts untouched)
// ===========================================================================
/// occ_cnt_prefix is monotonically nondecreasing in n.
proof fn occ_monotone<T>(es: Seq<EntryExec<T>>, n1: int, n2: int)
    requires
        0 <= n1 <= n2 <= es.len(),
    ensures
        occ_cnt_prefix(es, n1) <= occ_cnt_prefix(es, n2),
    decreases n2 - n1,
{
    if n1 < n2 {
        occ_monotone(es, n1, n2 - 1);
        assert(occ_cnt_prefix(es, n2)
            == (if es[n2 - 1] matches EntryExec::Occupied(_) { 1int } else { 0int })
                + occ_cnt_prefix(es, n2 - 1));
    }
}

/// occ_cnt_prefix(es, n) is in [0, n].
proof fn occ_prefix_bounds<T>(es: Seq<EntryExec<T>>, n: int)
    requires
        0 <= n <= es.len(),
    ensures
        0 <= occ_cnt_prefix(es, n) <= n,
    decreases n,
{
    if n > 0 {
        occ_prefix_bounds(es, n - 1);
        assert(occ_cnt_prefix(es, n)
            == (if es[n - 1] matches EntryExec::Occupied(_) { 1int } else { 0int })
                + occ_cnt_prefix(es, n - 1));
    }
}

/// An in-bounds occupied slot => occ_cnt >= 1 (the len lower bound, serving
/// the no-underflow proof of `len -= 1`).
proof fn occ_cnt_ge_at<T>(es: Seq<EntryExec<T>>, i: int)
    requires
        0 <= i < es.len(),
        es[i] matches EntryExec::Occupied(_),
    ensures
        occ_cnt(es) >= 1,
{
    occ_prefix_bounds(es, i);
    occ_monotone(es, i + 1, es.len() as int);
    assert(occ_cnt_prefix(es, i + 1)
        == (1int) + occ_cnt_prefix(es, i));
}

/// Push does not touch the occ_cnt prefix below n (indices < n <= es.len()
/// stay within the pre-push prefix).
proof fn occ_prefix_push_eq<T>(es: Seq<EntryExec<T>>, v: EntryExec<T>, n: int)
    requires
        0 <= n <= es.len(),
    ensures
        occ_cnt_prefix(es.push(v), n) == occ_cnt_prefix(es, n),
    decreases n,
{
    if n > 0 {
        occ_prefix_push_eq(es, v, n - 1);
        vstd::seq::lemma_seq_push_index_different(es, v, n - 1);
        assert(es.push(v)[n - 1] == es[n - 1]);
    }
}

/// The whole-sequence push delta = the indicator of the new element.
proof fn occ_cnt_push<T>(es: Seq<EntryExec<T>>, v: EntryExec<T>)
    ensures
        occ_cnt(es.push(v))
            == occ_cnt(es) + (if v matches EntryExec::Occupied(_) { 1int } else { 0int }),
{
    occ_prefix_push_eq(es, v, es.len() as int);
    vstd::seq::lemma_seq_push_len(es, v);
    vstd::seq::lemma_seq_push_index_same(es, v, es.len() as int);
    // prefix n = len+1 one recursion step: the new element's term + the
    // prefix-push equality
}

/// An update affects only prefixes > i; the delta is occ_bump.
proof fn occ_prefix_update_le<T>(es: Seq<EntryExec<T>>, i: int, v: EntryExec<T>, n: int)
    requires
        0 <= i < es.len(),
        0 <= n <= i,
    ensures
        occ_cnt_prefix(es.update(i, v), n) == occ_cnt_prefix(es, n),
    decreases n,
{
    if n > 0 {
        occ_prefix_update_le(es, i, v, n - 1);
        vstd::seq::lemma_seq_update_different(es, i, n - 1, v);
        assert(es.update(i, v)[n - 1] == es[n - 1]);
    }
}

proof fn occ_prefix_update_gt<T>(es: Seq<EntryExec<T>>, i: int, v: EntryExec<T>, n: int)
    requires
        0 <= i < n <= es.len(),
    ensures
        occ_cnt_prefix(es.update(i, v), n) == occ_cnt_prefix(es, n) + occ_bump(es[i], v),
    decreases n - i,
{
    if n == i + 1 {
        occ_prefix_update_le(es, i, v, i);
        vstd::seq::lemma_seq_update_same(es, i, v);
        assert(es.update(i, v)[i] == v);
        assert(occ_cnt_prefix(es.update(i, v), i + 1)
            == (if v matches EntryExec::Occupied(_) { 1int } else { 0int })
                + occ_cnt_prefix(es.update(i, v), i));
        assert(occ_cnt_prefix(es, i + 1)
            == (if es[i] matches EntryExec::Occupied(_) { 1int } else { 0int })
                + occ_cnt_prefix(es, i));
    } else {
        occ_prefix_update_gt(es, i, v, n - 1);
        vstd::seq::lemma_seq_update_different(es, i, n - 1, v);
        assert(es.update(i, v)[n - 1] == es[n - 1]);
        assert(occ_cnt_prefix(es.update(i, v), n)
            == (if es[n - 1] matches EntryExec::Occupied(_) { 1int } else { 0int })
                + occ_cnt_prefix(es.update(i, v), n - 1));
        assert(occ_cnt_prefix(es, n)
            == (if es[n - 1] matches EntryExec::Occupied(_) { 1int } else { 0int })
                + occ_cnt_prefix(es, n - 1));
    }
}

proof fn occ_cnt_update<T>(es: Seq<EntryExec<T>>, i: int, v: EntryExec<T>)
    requires
        0 <= i < es.len(),
    ensures
        occ_cnt(es.update(i, v)) == occ_cnt(es) + occ_bump(es[i], v),
{
    vstd::seq::lemma_seq_update_len(es, i, v);
    if 0 <= i < es.len() {
        occ_prefix_update_gt(es, i, v, es.len() as int);
    }
}

// =====================================================================
// Vacant-chain update lemmas (pure structural facts behind the upstream
// internal invariant).
//
// Both are composition facts of a deterministic chain walk (the walk only
// visits vacant slots and never revisits a node re-occupied or newly
// created); the inductive bookkeeping is skipped via admit (the hard-helper
// tier this pipeline allows). They serve only the invariant-maintenance
// bookkeeping and absorb no obligation at any panic or contract site.
// =====================================================================

/// Disclosed: chain-head consumption (insert_at's vacant branch: once the
/// next slot is re-occupied, the chain continues well-formed along the
/// old chain pointer). See the file-header note -- the admit-tier helpers.
proof fn chain_consume_head<T>(es: Seq<EntryExec<T>>, cur: int, budget: int, e: EntryExec<T>)
    requires
        0 <= cur < es.len(),
        chain_ok(es, cur, budget),
    ensures
        chain_ok(es.update(cur, e), vacant_link(es[cur]), budget - 1),
{
    admit();
}

/// Disclosed: chain-head insertion (try_remove: after the occupied slot
/// turns vacant and points at the old next, the chain remains well-formed).
/// Admit-tier helper lemma, as above.
proof fn chain_insert_head<T>(es: Seq<EntryExec<T>>, key: int, new_next: int, budget: int)
    requires
        0 <= key < es.len(),
        0 <= new_next <= es.len(),
        es[key] matches EntryExec::Occupied(_),
        chain_ok(es, new_next, budget),
    ensures
        chain_ok(es.update(key, EntryExec::Vacant(new_next as usize)), key, budget + 1),
{
    admit();
}

/// High-index frame preservation under update (the structural fact of
/// retain's suffix frame).
proof fn suffix_update_frame<T>(
    es: Seq<EntryExec<T>>, i: int, next: int,
    lo: int, hi: int,
)
    requires
        0 <= i < es.len(),
        0 <= next <= es.len(),
        i < lo <= hi <= es.len(),
    ensures
        forall|j: int| lo <= j < hi
            ==> es.update(i, EntryExec::Vacant(next as usize)).index(j) == es.index(j),
{
    assert forall|j: int| lo <= j < hi
        implies es.update(i, EntryExec::Vacant(next as usize)).index(j) == es.index(j) by {
        vstd::seq::lemma_seq_update_different(es, i, j, EntryExec::Vacant(next as usize));
    };
}

/// A chain_ok definitional lemma: with cur the end marker, any budget is
/// well-formed.
proof fn chain_end_marker<T>(es: Seq<EntryExec<T>>, budget: int)
    ensures
        chain_ok(es, es.len() as int, budget),
{
}

/// A chain_ok definitional lemma: the chain-head slot is Vacant, its pointer
/// in bounds.
proof fn chain_head_bound<T>(es: Seq<EntryExec<T>>, cur: int, budget: int)
    requires
        0 <= cur < es.len(),
        chain_ok(es, cur, budget),
    ensures
        es[cur] matches EntryExec::Vacant(_),
        0 <= vacant_link(es[cur]) <= es.len(),
{
}

/// Skip bookkeeping: a Vacant slot at lo => the prefix count is unchanged (the suffixes from lo and lo+1 coincide).
proof fn suffix_skip_vacant<T>(es: Seq<EntryExec<T>>, lo: int)
    requires
        0 <= lo < es.len(),
        es[lo] matches EntryExec::Vacant(_),
    ensures
        occ_cnt_prefix(es, lo + 1) == occ_cnt_prefix(es, lo),
{
    // one definitional step: es[lo]'s indicator term is 0
    reveal_with_fuel(occ_cnt_prefix, 2);
    assert(es[lo] matches EntryExec::Vacant(_));
}

/// Hit bookkeeping: an Occupied slot at lo => the prefix count +1.
proof fn suffix_step_occupied<T>(es: Seq<EntryExec<T>>, lo: int)
    requires
        0 <= lo < es.len(),
        es[lo] matches EntryExec::Occupied(_),
    ensures
        occ_cnt_prefix(es, lo + 1) == occ_cnt_prefix(es, lo) + 1,
        occ_cnt_prefix(es, lo + 1) >= 1, // a hit slot counts in => a long prefix >= 1 (for the len lower bound)
{
    reveal_with_fuel(occ_cnt_prefix, 2);
    assert(es[lo] matches EntryExec::Occupied(_));
    occ_prefix_bounds(es, lo); // occ_cnt_prefix(es, lo) >= 0
}

/// Swap-out bookkeeping (IntoIter's consuming readout): after the occupied slot
/// at lo is swapped for the dummy Vacant, the prefix count up to lo+1 == the
/// original prefix count up to lo (the lo slot's indicator term 1->0; deeper
/// positions untouched).
proof fn upd_vacant_step<T>(es: Seq<EntryExec<T>>, lo: int)
    requires
        0 <= lo < es.len(),
        es[lo] matches EntryExec::Occupied(_),
    ensures
        occ_cnt_prefix(es.update(lo, EntryExec::Vacant(0usize)), lo + 1)
            == occ_cnt_prefix(es, lo),
{
    reveal_with_fuel(occ_cnt_prefix, 2);
    // existing lemma: the prefix < lo is unaffected by the update at lo
    occ_prefix_update_le(es, lo, EntryExec::Vacant(0usize), lo);
    vstd::seq::lemma_seq_update_same(es, lo, EntryExec::Vacant(0usize));
}

/// witness (reachability, spec layer; the F1 spec-copy counterpart shape):
/// an input satisfying the documented precondition
/// (the # Panics sole condition key1 != key2) with max(key) > len exists -- the
/// input on which F1's obligation necessarily fails is genuinely reachable.
proof fn f1_reachability_witness() {
    let len: int = 1;
    let key1: int = 5;
    let key2: int = 0;
    assert(key1 != key2); // satisfies the sole # Panics condition declared at lib.rs:773-775
    assert(key1 > len); // but the split point max(key1, key2) = 5 is strictly greater than len
}

} // verus!

fn main() {}
