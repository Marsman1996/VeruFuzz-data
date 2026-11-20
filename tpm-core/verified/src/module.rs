//! tpm-core 0.1.4 orchestration-facing handle-space module
//! (src/module.rs) -- Verus translation.
//!
//! Upstream face: the IoErr taxonomy, the abstract ContextIo
//! trait (the trusted boundary for context round trips), the
//! user-visible Space and its Transaction working-copy discipline,
//! the cleanup walker flush_all, and the two bulk loaders
//! load_space / save_space (src/module.rs:1-224).
//!
//! Re-erected here:
//!  - the ContextIo trait carries exactly the discipline the bulk
//!    loaders need to chain the peer-controlled offsets: on Ok a
//!    load consumes at least CTX_FIXED bytes inside blob[off..]
//!    and a save writes a nonzero count inside out[off..] (both
//!    discharged by the verified CtxIo implementation in chip.rs,
//!    so the trusted boundary adds no unproven claim);
//!  - transaction atomicity: begin is an exact working copy (the
//!    Copy derive upstream is spelled out here because this build
//!    has no derive support), commit replaces the table wholesale,
//!    abort flushes EVERY live slot and session and ends empty on
//!    both arrays (the doc's "no residual state" end state);
//!  - flush_all's two-phase clear (ctx first, sessions second) is
//!    closed as the table_cleared face.
//!
//! DEFERRED RECORD (D-T5-2, see out/kverus-run/T5/notes.md): the
//! two generic bulk loaders load_space / save_space are NOT
//! transcribed in this batch. Their verified bodies require the
//! same two-facet loop treatment per table slot across a GENERIC
//! trait boundary (this batch's probe rounds show every such loop
//! costs the full idiom-tuning cycle); the offset-chain discipline
//! they need is already banked as the ContextIo trait face below,
//! so a later batch re-opens only the two loop bodies, not the
//! boundary.

use vstd::prelude::*;

verus! {

use super::handle::SLOTS;
use super::table::{
    clone_of_space_table, spec_slot_is_empty, CtxSlot, SpaceTable,
};

// ------------------------------------------------------------------
// IoErr (module.rs:10-34)
// ------------------------------------------------------------------

/// Origin Rust: #[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pub enum IoErr { ... 9 doc-carrying variants ... }
/// (module.rs:10-34; the derives carry no Verus twin -- variants
/// are consumed downstream by pattern shape only)
pub enum IoErr {
    /// The target no longer exists: the context was externally released or the counter no longer
    /// matches. Recoverable -- the corresponding slot can simply be forgotten.
    NotFound,
    /// Backup data integrity check failed.
    Integrity,
    /// The backup buffer is too small.
    NoSpace,
    /// Polling budget exhausted; pure wait timeout, worth retrying with backoff.
    Timeout,
    /// Physical bus failure; retries are pointless.
    Bus,
    /// The chip returned data that violates protocol conventions (length, status bits, or specification
    /// mismatches).
    Protocol,
    /// The command the caller passed is internally inconsistent (length field does not match the buffer).
    /// This is a coding-layer logic error, not a device fault.
    BadCommand,
    /// Calling-order error: the interface was called when its preconditions were not satisfied.
    NotReady,
    /// The internal invariant between the table and chip state has already been broken; the only safe
    /// action is to clear everything and start over.
    Fatal,
}

// ------------------------------------------------------------------
// ContextIo (module.rs:35-50) -- trusted boundary with the exact
// offset-chain discipline
// ------------------------------------------------------------------

/// Origin Rust: /// Abstract interface for context access.
/// ///
/// /// Implementations are provided by the outer layer; they build the request/response packets and classify
/// /// return codes, which are the responsibilities of the encoding/decoding layer. This module depends only
/// /// on the preconditions and postconditions written here.
/// pub trait ContextIo {
///     fn load(&mut self, blob: &[u8], off: usize) -> Result<(u32, usize), IoErr>;
///     /// Saving itself does not release the handle; release must be done explicitly via [`ContextIo::flush`].
///     fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> Result<usize, IoErr>;
///     fn flush(&mut self, h: u32);
/// } (module.rs:35-50; the two data-moving methods carry the
/// minimal offset-chain face: on Ok the load consumes at least the
/// fixed 18-byte backup header inside blob[off..] and the save
/// writes at least one byte inside out[off..] -- the verified
/// CtxIo impl (chip.rs) discharges both, so the trust boundary adds
/// nothing unproven. The fixed backup header size is 18 upstream
/// (chip.rs CTX_FIXED); the constant is restated here because the
/// public module face may not cite the private one)
pub trait ContextIo {
    fn load(&mut self, blob: &[u8], off: usize) -> (r: Result<(u32, usize), IoErr>)
        requires
            (off as int) <= (blob.len() as int),
        ensures
            match r {
                Result::Ok((_, used)) =>
                    (used as int) >= 18
                        && (off as int) + (used as int) <= (blob.len() as int),
                Result::Err(_) => true,
            };

    fn save(&mut self, h: u32, out: &mut [u8], off: usize) -> (r: Result<usize, IoErr>)
        requires
            (off as int) <= (out.len() as int),
        ensures
            match r {
                Result::Ok(used) =>
                    (used as int) >= 1
                        && (off as int) + (used as int) <= (old(out).len() as int),
                Result::Err(_) => true,
            };

    fn flush(&mut self, h: u32);
}

// ------------------------------------------------------------------
// Space / Transaction (module.rs:51-99)
// ------------------------------------------------------------------

/// Origin Rust: pub struct Space { tbl: SpaceTable }
/// (module.rs:51-55; the field is private upstream; the twin opens
/// it pub because the public begin/commit contracts talk about it,
/// visibility only)
pub struct Space {
    pub tbl: SpaceTable,
}

/// Origin Rust: pub struct Transaction { work: SpaceTable }
/// (module.rs:56-62; same visibility note; upstream additionally
/// derives neither Clone nor a public constructor, which the twin
/// keeps structurally -- begin is the only constructor)
pub struct Transaction {
    pub work: SpaceTable,
}

impl Space {
    /// Origin Rust: pub fn new() -> Self { Space { tbl: SpaceTable::new() } }
    /// (module.rs:63-68 plus Default at :70-75)
    pub exec fn new() -> (s: Space)
        ensures
            forall|k: int|
                0 <= k < SLOTS as int ==> spec_slot_is_empty(s.tbl.ctx@.index(k)),
            forall|k: int| 0 <= k < SLOTS as int ==> s.tbl.sessions@.index(k) == 0,
    {
        Space {
            tbl: SpaceTable::new(),
        }
    }
}

impl Default for Space {
    fn default() -> Self {
        Self::new()
    }
}

impl Space {
    /// Origin Rust: pub fn begin(&self) -> Transaction {
    ///     Transaction { work: self.tbl }
    /// } (module.rs:77-81; upstream rides the Copy derive, which
    /// this build lacks -- the copy goes through the spelled-out
    /// clone helper with exact-view faces)
    pub exec fn begin(&self) -> (t: Transaction)
        ensures
            t.work.ctx@ == self.tbl.ctx@,
            t.work.sessions@ == self.tbl.sessions@,
    {
        Transaction {
            work: clone_of_space_table(&self.tbl),
        }
    }

    /// Origin Rust: pub fn commit(&mut self, t: Transaction) {
    ///     self.tbl = t.work;
    /// } (module.rs:82-86)
    pub exec fn commit(&mut self, t: Transaction)
        ensures
            final(self).tbl.ctx@ == t.work.ctx@,
            final(self).tbl.sessions@ == t.work.sessions@,
    {
        self.tbl = t.work;
    }
}

impl Transaction {
    /// Origin Rust: pub fn table(&mut self) -> &mut SpaceTable { &mut self.work }
    /// (module.rs:87-89; the &mut field-out borrow is kept as-is;
    /// only the identity face is claimable at this shape)
    pub exec fn table(&mut self) -> (r: &mut SpaceTable)
        // no ensures: this build's new-mut-ref model cannot state
        // the identity between the returned &mut and the field
        // (the final-continuation of the returned borrow is not
        // available); the access itself is total and the borrow
        // discipline is enforced by Rust's aliasing rules
    {
        &mut self.work
    }

    /// Origin Rust: /// Cleanup after transaction failure: release residual handles on the chip, then discard the copy.
    /// ///
    /// /// `self` is taken by value instead of borrowed -- after cleanup, this transaction can no longer be
    /// /// committed.
    /// pub fn abort<I: ContextIo>(self, io: &mut I) {
    ///     let mut t = self;
    ///     flush_all(&mut t.work, io);
    /// } (module.rs:90-99)
    pub exec fn abort<I: ContextIo>(self, io: &mut I)
        // no ensures: the transaction is consumed by value, so no
        // post state of it remains observable; the cleared-table
        // fact lives inside flush_all's own contract (final(tbl)
        // is table_cleared there), and this body constructs the
        // only caller -- the Rust aliasing of the by-value take is
        // precisely the upstream "can no longer be committed"
        // discipline
    {
        let mut t = self;
        flush_all(&mut t.work, io);
    }
}

// ------------------------------------------------------------------
// flush_all (module.rs:100-118)
// ------------------------------------------------------------------

/// The fully-cleared end state of a table (the flush_all face).
pub open spec fn table_cleared(t: &SpaceTable) -> bool {
    (forall|k: int|
        0 <= k < SLOTS as int ==> spec_slot_is_empty(t.ctx@.index(k)))
        && (forall|k: int| 0 <= k < SLOTS as int ==> t.sessions@.index(k) == 0)
}

/// Origin Rust: /// Release all live handles and all sessions from the table and clear both tables.
/// ///
/// /// This is the cleanup action on error paths: after this call, no residual state from this space remains
/// /// on the chip.
/// fn flush_all<I: ContextIo>(tbl: &mut SpaceTable, io: &mut I) {
///     for i in 0..SLOTS {
///         if let CtxSlot::Live(h) = tbl.slot_at(i) { io.flush(h); }
///         tbl.set_slot_free(i, false);
///     }
///     for i in 0..SLOTS {
///         let h = tbl.session_at(i);
///         if h != 0 { io.flush(h); tbl.clear_session(i); }
///     }
/// } (module.rs:100-118; for-loops lowered to while-walks; the
/// slot value copies re-materialize through slot_at's match form
/// because this build has no derives)
fn flush_all<I: ContextIo>(tbl: &mut SpaceTable, io: &mut I)
    ensures
        table_cleared(final(tbl)),
{
    let mut i: usize = 0;
    while i < SLOTS
        invariant
            (i as int) <= SLOTS as int,
            forall|k: int|
                0 <= k < (i as int) ==> spec_slot_is_empty(tbl.ctx@.index(k)),
            forall|k: int|
                0 <= k < SLOTS as int
                    ==> tbl.sessions@.index(k) == old(tbl).sessions@.index(k),
        decreases
            SLOTS as int - (i as int),
    {
        match tbl.slot_at(i) {
            CtxSlot::Live(h) => {
                io.flush(h);
            }
            _ => {}
        }
        tbl.set_slot_free(i, false);
        i += 1;
    }
    let mut j: usize = 0;
    while j < SLOTS
        invariant
            (j as int) <= SLOTS as int,
            forall|k: int|
                0 <= k < SLOTS as int ==> spec_slot_is_empty(tbl.ctx@.index(k)),
            forall|k: int| 0 <= k < (j as int) ==> tbl.sessions@.index(k) == 0,
            forall|k: int|
                (j as int) <= k < SLOTS as int
                    ==> tbl.sessions@.index(k) == old(tbl).sessions@.index(k),
        decreases
            SLOTS as int - (j as int),
    {
        let h = tbl.session_at(j);
        if h != 0 {
            io.flush(h);
            tbl.clear_session(j);
        }
        j += 1;
    }
}

} // verus!
