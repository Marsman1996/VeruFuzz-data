//! tpm-core 0.1.4 packet handle rewriting (src/rewrite.rs) --
//! Verus translation.
//!
//! Upstream face: the big-endian word pair read_be32/write_be32
//! over packet buffers and the three rewrite passes --
//! map_command_handles (two-phase: validate every virtual handle,
//! then rewrite them all), map_response_handle (the response-header
//! handle outcome machine), and map_capability_handles (in-place
//! compaction of a handle list, with the count and length fields
//! rewritten together) (src/rewrite.rs:1-165).
//!
//! Re-erected here: the two-phase discipline of map_command_handles
//! is closed through the resolve spec twin -- the second pass reads
//! the very bytes the first pass validated and the resolution is a
//! pure function of the table, so the upstream unwrap is exact and
//! the rewritten word is provably the resolution of the entry word;
//! every rewrite pass preserves the bytes outside its declared
//! windows; the capability compaction keeps its write head at or
//! behind its read head and rewrites the count/length fields
//! consistently with the compacted length.
//!
//! Lowering notes (machine-outline sites; each has an Origin note):
//! u32::to_be_bytes is lowered to the / %-byte spelling, slice
//! copy_from_slice to scalar index writes, is_multiple_of(4) to a
//! % test. The full kept-subsequence order-preservation face of the
//! compaction is the one deferred record of this file (D-T5-1); the
//! j <= i write-behind bound and the field self-consistency are
//! carried.

use vstd::prelude::*;

verus! {

use vstd::slice::SliceAdditionalExecFns;

use super::handle::{
    is_session_exec, is_transient_exec, spec_is_session_val, spec_is_transient_val,
    spec_slot_of, spec_vhandle_of, spec_valid_phandle_val, CTX_SAVED_SENTINEL_VALUE, SLOTS,
};
use super::table::{
    spec_resolved, spec_resolve, spec_slot_is_live, spec_slot_live_word, SpaceTable,
};

// ------------------------------------------------------------------
// Constants (rewrite.rs:3-15)
// ------------------------------------------------------------------

/// Origin Rust: /// Message header length: tag (2 bytes) + length (4 bytes) + command or return code (4 bytes).
/// pub const HEADER_SIZE: usize = 10; (rewrite.rs:3-4)
pub const HEADER_SIZE: usize = 10;
/// Origin Rust: /// The number of handles in a command is given by a 3-bit field, with an upper bound of 7.
/// pub const MAX_CHANDLES: usize = 7; (rewrite.rs:5-6)
pub const MAX_CHANDLES: usize = 7;
/// Origin Rust: pub const RC_SUCCESS: u32 = 0; (rewrite.rs:7)
pub const RC_SUCCESS: u32 = 0;
/// Origin Rust: /// The "handle list" category in capability queries.
/// pub const CAP_HANDLES: u32 = 0x0000_0001; (rewrite.rs:8-9)
pub const CAP_HANDLES: u32 = 0x0000_0001;
/// Origin Rust: /// Capability response body layout: more-data flag (1 byte), category (4 bytes), count (4 bytes).
/// pub const CAP_MORE_OFF: usize = HEADER_SIZE; (rewrite.rs:10-11)
pub const CAP_MORE_OFF: usize = HEADER_SIZE;
/// Origin Rust: const CAP_CAPABILITY_OFF: usize = HEADER_SIZE + 1; (rewrite.rs:12;
/// private upstream -- the twin opens it to pub because the public
/// contract of map_capability_handles cites it, visibility only)
pub const CAP_CAPABILITY_OFF: usize = HEADER_SIZE + 1;
/// Origin Rust: const CAP_COUNT_OFF: usize = HEADER_SIZE + 5; (rewrite.rs:13;
/// same visibility note)
pub const CAP_COUNT_OFF: usize = HEADER_SIZE + 5;
/// Origin Rust: const CAP_HANDLES_OFF: usize = HEADER_SIZE + 9; (rewrite.rs:14;
/// same visibility note)
pub const CAP_HANDLES_OFF: usize = HEADER_SIZE + 9;
/// Origin Rust: const RSP_LENGTH_OFF: usize = 2; (rewrite.rs:15;
/// same visibility note)
pub const RSP_LENGTH_OFF: usize = 2;

// ------------------------------------------------------------------
// Error and outcome types (rewrite.rs:16-22, 53-70)
// ------------------------------------------------------------------

/// Origin Rust: #[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pub enum SpaceErr {
///     /// The packet length does not match the structure it declares.
///     Malformed,
///     /// The command references a virtual handle that cannot be resolved.
///     BadHandle,
/// } (rewrite.rs:16-22; the derives carry no Verus twin -- no exec
/// code in this tree compares SpaceErr values)
pub enum SpaceErr {
    /// The packet length does not match the structure it declares.
    Malformed,
    /// The command references a virtual handle that cannot be resolved.
    BadHandle,
}

/// Origin Rust: /// Result of processing a handle returned in the response header.
/// ///
/// /// `OutOfSlots` places the obligation to release this physical handle into the return type instead of
/// /// leaving it as an unstated convention. The orchestrator does not compile if it does not handle it.
/// #[derive(Clone, Copy, PartialEq, Eq)]
/// pub enum HeaderOutcome {
///     /// There is no handle in the response, or the command itself failed; the packet is left untouched.
///     NoHandle,
///     /// A transient handle has been replaced by a virtual handle.
///     Virtualized { vhandle: u32 },
///     /// A session handle has been registered; the packet is left untouched (session handles are not
///     /// virtualized).
///     SessionTracked { phandle: u32 },
///     /// The handle type is unknown; the packet is left untouched.
///     Unknown { phandle: u32 },
///     /// The table is full; `flush` must be released.
///     OutOfSlots { flush: u32 },
/// } (rewrite.rs:53-70; the doc's "does not compile if unhandled"
/// is the TYPE's face -- the data-carrying shape keeps the release
/// obligation in the return value, which the twin preserves)
pub enum HeaderOutcome {
    /// There is no handle in the response, or the command itself failed; the packet is left untouched.
    NoHandle,
    /// A transient handle has been replaced by a virtual handle.
    Virtualized { vhandle: u32 },
    /// A session handle has been registered; the packet is left untouched (session handles are not
    /// virtualized).
    SessionTracked { phandle: u32 },
    /// The handle type is unknown; the packet is left untouched.
    Unknown { phandle: u32 },
    /// The table is full; `flush` must be released.
    OutOfSlots { flush: u32 },
}

// ------------------------------------------------------------------
// Word pair over packet buffers (rewrite.rs:23-28)
// ------------------------------------------------------------------

/// Spec twin of a big-endian u32 word at a fixed offset of a byte
/// sequence.
pub open spec fn wire_be32(s: Seq<u8>, off: int) -> int {
    16777216 * s.index(off) as int
        + 65536 * s.index(off + 1) as int
        + 256 * s.index(off + 2) as int
        + s.index(off + 3) as int
}

/// End offset of the handle word area of a command with `nr`
/// described handles.
pub open spec fn handle_area_end(nr: int) -> int {
    (HEADER_SIZE as int) + 4 * nr
}

/// Origin Rust: pub fn read_be32(b: &[u8], off: usize) -> u32 {
///     u32::from_be_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
/// } (rewrite.rs:23-25; from_be_bytes lowered through the endian
/// twin's weighted sum. Upstream indexes with no bound check of its
/// own -- the panic faces ride at the public callers, suspect rows
/// S-T5-4/5)
pub(crate) exec fn read_be32(b: &[u8], off: usize) -> (r: u32)
    requires
        (off as int) + 4 <= (b.len() as int),
    ensures
        (r as int) == wire_be32(b@, off as int),
{
    super::endian::be32_of_exec(b[off], b[off + 1], b[off + 2], b[off + 3])
}

/// Origin Rust: fn write_be32(b: &mut [u8], off: usize, v: u32) {
///     b[off..off + 4].copy_from_slice(&v.to_be_bytes());
/// } (rewrite.rs:26-28; to_be_bytes + copy_from_slice lowered to
/// four scalar index writes in the / %-spelling; the face is the
/// exact 4-byte window value plus pointwise outside preservation)
pub(crate) exec fn write_be32(b: &mut [u8], off: usize, v: u32)
    requires
        (off as int) + 4 <= (b.len() as int),
    ensures
        wire_be32(final(b)@, off as int) == (v as int),
        forall|j: int|
            0 <= j < (old(b).len() as int)
                && !((off as int) <= j < (off as int + 4))
            ==> final(b)@.index(j) == old(b)@.index(j),
        final(b).len() == old(b).len(),
{
    b[off] = (v / 16777216u32) as u8;
    b[off + 1] = ((v / 65536u32) % 256u32) as u8;
    b[off + 2] = ((v / 256u32) % 256u32) as u8;
    b[off + 3] = (v % 256u32) as u8;
}

// ------------------------------------------------------------------
// Word-area access helpers (loop-local Spelling shortcuts)
// ------------------------------------------------------------------

/// The k-th handle word of the entry view.
pub open spec fn entry_word_at(pre: Seq<u8>, base: int, k: int) -> int {
    wire_be32(pre, base + 4 * k)
}

/// The rewritten state of the k-th handle word: transient entries
/// carry their resolution (the same word resolve would produce on
/// the entry view), non-transient entries keep their entry word.
pub open spec fn spec_cmd_word_outcome(
    tbl: &SpaceTable,
    pre: Seq<u8>,
    fin: Seq<u8>,
    base: int,
    k: int,
) -> bool {
    let e = entry_word_at(pre, base, k);
    if spec_is_transient_val(e) {
        spec_resolve(tbl, e) == Option::Some(spec_resolved(tbl, e))
            && wire_be32(fin, base + 4 * k) == spec_resolved(tbl, e) as int
    } else {
        wire_be32(fin, base + 4 * k) == e
    }
}

/// The expected byte at absolute command offset `base + q` after the
/// handle rewrite: within the handle area (q < 4 * nr) it is either
/// a byte of the resolved physical handle (transient entries) or
/// the entry byte itself (non-transient entries); outside the area
/// it is the entry byte (the area is mid-rewrite). This is the
/// window-fresh facet the rewrite loop carries pointwise.
pub open spec fn spec_cmd_outcome_byte(tbl: &SpaceTable, pre: Seq<u8>, base: int, q: int) -> u8 {
    let k = q / 4;
    let b = q % 4;
    let e = entry_word_at(pre, base, k);
    if spec_is_transient_val(e) {
        let p = spec_resolved(tbl, e) as int;
        if b == 0 {
            (p / 16777216) as u8
        } else if b == 1 {
            (p / 65536 % 256) as u8
        } else if b == 2 {
            (p / 256 % 256) as u8
        } else {
            (p % 256) as u8
        }
    } else {
        pre.index(base + q)
    }
}

// ------------------------------------------------------------------
// Command handle mapping (rewrite.rs:29-52)
// ------------------------------------------------------------------

/// Origin Rust: /// Replace the virtual handles in the command handle area with physical handles.
/// ///
/// /// `nr_handles` is provided by the command-property table and is therefore a stage-2 encoding artifact;
/// /// here it is treated as an already-validated parameter.
/// pub fn map_command_handles(
///     tbl: &SpaceTable, nr_handles: usize, cmd: &mut [u8],
/// ) -> Result<(), SpaceErr> {
///     for i in 0..nr_handles {
///         let h = read_be32(cmd, HEADER_SIZE + 4 * i);
///         if is_transient_exec(h) && tbl.resolve(h).is_none() { return Err(SpaceErr::BadHandle); }
///     }
///     for i in 0..nr_handles {
///         let h = read_be32(cmd, HEADER_SIZE + 4 * i);
///         if is_transient_exec(h) {
///             let p = tbl.resolve(h).unwrap();
///             write_be32(cmd, HEADER_SIZE + 4 * i, p);
///         }
///     }
///     Ok(())
/// } (rewrite.rs:29-52; for-loops lowered to while-walks; `.is_none`
/// and `.unwrap` lowered to explicit Option matches. The doc's
/// "already-validated parameter" is the caller contract, not a
/// runtime check: nothing bounds nr_handles against the buffer, so
/// the twin requires the handle-area bound -- public panic face,
/// suspect row S-T5-4)
pub exec fn map_command_handles(
    tbl: &SpaceTable,
    nr_handles: usize,
    cmd: &mut [u8],
) -> (r: Result<(), SpaceErr>)
    requires
        handle_area_end(nr_handles as int) <= cmd.len() as int,
    ensures
        match r {
            Result::Ok(()) => {
                let pre = old(cmd)@;
                // bytes outside the handle area are untouched
                (forall|j: int|
                    0 <= j < pre.len()
                        && !((HEADER_SIZE as int) <= j < handle_area_end(nr_handles as int))
                    ==> final(cmd)@.index(j) == pre.index(j))
                // validated (transient) handles are replaced by their
                // resolution; others keep their entry word
                && (forall|q: int|
                    0 <= q < 4 * (nr_handles as int)
                        ==> final(cmd)@.index((HEADER_SIZE as int) + q)
                            == spec_cmd_outcome_byte(
                                tbl,
                                pre,
                                HEADER_SIZE as int,
                                q,
                            ))
                && (forall|k: int|
                    0 <= k < (nr_handles as int)
                        && spec_is_transient_val(entry_word_at(
                            pre,
                            HEADER_SIZE as int,
                            k,
                        ))
                    ==> spec_resolve(tbl, entry_word_at(pre, HEADER_SIZE as int, k))
                        == Option::Some(spec_resolved(
                            tbl,
                            entry_word_at(pre, HEADER_SIZE as int, k),
                        )))
            }
            Result::Err(SpaceErr::BadHandle) => {
                let pre = old(cmd)@;
                final(cmd)@ == pre
                    && (exists|k: int|
                        0 <= k < (nr_handles as int)
                            && spec_is_transient_val(entry_word_at(
                                pre,
                                HEADER_SIZE as int,
                                k,
                            ))
                            && spec_resolve(tbl, entry_word_at(
                                pre,
                                HEADER_SIZE as int,
                                k,
                            )) == Option::None)
            }
            Result::Err(SpaceErr::Malformed) => false,
        },
{
    let ghost pre = cmd@;
    // ---- pass one: every transient handle must resolve before
    // any byte is touched (the "validate all, then rewrite"
    // discipline of the upstream two-pass design)
    let mut i: usize = 0;
    while i < nr_handles
        invariant
            (i as int) <= (nr_handles as int),
            cmd@ == pre,
            (cmd.len() as int) == pre.len(),
            handle_area_end(nr_handles as int) <= pre.len(),
            forall|k: int|
                0 <= k < (i as int)
                    && spec_is_transient_val(entry_word_at(pre, HEADER_SIZE as int, k))
                ==> spec_resolve(tbl, entry_word_at(pre, HEADER_SIZE as int, k))
                    == Option::Some(spec_resolved(tbl, entry_word_at(
                        pre,
                        HEADER_SIZE as int,
                        k,
                    ))),
        decreases
            (nr_handles as int) - (i as int),
    {
        let h = read_be32(cmd, HEADER_SIZE + 4 * i);
        if is_transient_exec(h) {
            match tbl.resolve(h) {
                Option::Some(_) => {}
                Option::None => {
                    // ground shim: this very position is the
                    // unresolvable transient witnessed by BadHandle
                    assert(cmd@ == pre);
                    let ghost w = entry_word_at(
                        pre,
                        HEADER_SIZE as int,
                        (i as int),
                    );
                    assert(w == (h as int));
                    assert(spec_is_transient_val(w));
                    assert(0 <= (i as int) < (nr_handles as int));
                    assert(spec_resolve(tbl, w) == Option::None);
                    return Result::Err(SpaceErr::BadHandle);
                }
            }
        }
        i = i + 1;
    }
    // the full validated-image fact is now over all nr positions;
    // it is re-carried through the second loop's frame (T4-2)
    assert forall|k: int|
        0 <= k < (nr_handles as int)
            && spec_is_transient_val(entry_word_at(pre, HEADER_SIZE as int, k))
        implies spec_resolve(tbl, entry_word_at(pre, HEADER_SIZE as int, k))
            == Option::Some(spec_resolved(tbl, entry_word_at(
                pre,
                HEADER_SIZE as int,
                k,
            )))
    by {}
    // ---- pass two: rewrite in place; upstream's unwrap is
    // exact because pass one validated this very byte (the table is a
    // shared borrow, so the resolution provably agrees). The write
    // sites go through slice .set with the two-facet content
    // invariants (window-fresh expectation bytes vs tail entry
    // bytes), the idiom of probe probe_wordcopy / T1 buf.rs append;
    // the upstream copy_from_slice spelling of the same four bytes
    // is kept by write_be32 at the other (non-loop) call sites.
    let mut i2: usize = 0;
    let mut pos: usize = HEADER_SIZE;
    while i2 < nr_handles
        invariant
            (i2 as int) <= (nr_handles as int),
            (pos as int) == (HEADER_SIZE as int) + 4 * (i2 as int),
            (pos as int) + 4 * ((nr_handles as int) - (i2 as int)) <= (pre.len() as int),
            (pre.len() as int) == (cmd.len() as int),
            // the full phase-1 validation image, re-carried through
            // this loop's frame (T4-2: no fn-entry fact survives a
            // loop without an invariant)
            forall|k: int|
                0 <= k < (nr_handles as int)
                    && spec_is_transient_val(entry_word_at(pre, HEADER_SIZE as int, k))
                ==> spec_resolve(tbl, entry_word_at(pre, HEADER_SIZE as int, k))
                    == Option::Some(spec_resolved(
                        tbl,
                        entry_word_at(pre, HEADER_SIZE as int, k),
                    )),
            // header bytes before the handle area are never
            // touched by this pass
            forall|j: int|
                0 <= j < (HEADER_SIZE as int)
                    ==> #[trigger] cmd@.index(j) == pre.index(j),
            // tail facet: every byte at or beyond the write head
            // still holds its entry value
            forall|j: int|
                0 <= j < (pre.len() as int) && (pos as int) <= j
                    ==> #[trigger] cmd@.index(j) == pre.index(j),
            // window facet: every processed byte equals its expected
            // outcome byte (resolution bytes for transient entries,
            // entry bytes for the rest)
            forall|q: int|
                0 <= q < 4 * (i2 as int)
                    ==> #[trigger] cmd@.index((HEADER_SIZE as int) + q)
                        == spec_cmd_outcome_byte(tbl, pre, HEADER_SIZE as int, q),
        decreases
            (nr_handles as int) - (i2 as int),
    {
        let e = read_be32(cmd, pos);
        let ghost ek = entry_word_at(pre, HEADER_SIZE as int, (i2 as int));
        assert(ek == (e as int));
        if is_transient_exec(e) {
            assert(spec_is_transient_val(ek));
            match tbl.resolve(e) {
                Option::Some(p) => {
                    // pass one validated this very entry word: the
                    // resolution cannot be None here, and its value
                    // is exactly the exec-resolved p
                    assert(spec_resolve(tbl, ek) == Option::Some(p));
                    assert(spec_resolved(tbl, ek) == p);
                    let bts = super::cursor::be32_bytes(p);
                    cmd.set(pos, bts[0]);
                    cmd.set(pos + 1, bts[1]);
                    cmd.set(pos + 2, bts[2]);
                    cmd.set(pos + 3, bts[3]);
                    // the four written bytes are the expected
                    // outcome bytes of this position
                    assert(spec_cmd_outcome_byte(
                        tbl,
                        pre,
                        HEADER_SIZE as int,
                        4 * (i2 as int),
                    ) == bts[0]);
                    assert(spec_cmd_outcome_byte(
                        tbl,
                        pre,
                        HEADER_SIZE as int,
                        4 * (i2 as int) + 1,
                    ) == bts[1]);
                    assert(spec_cmd_outcome_byte(
                        tbl,
                        pre,
                        HEADER_SIZE as int,
                        4 * (i2 as int) + 2,
                    ) == bts[2]);
                    assert(spec_cmd_outcome_byte(
                        tbl,
                        pre,
                        HEADER_SIZE as int,
                        4 * (i2 as int) + 3,
                    ) == bts[3]);
                }
                Option::None => {},
            }
        } else {
            // non-transient: never written; the tail facet already
            // pins the bytes to the entry values
            assert(!spec_is_transient_val(ek));
            assert forall|b: int|
                0 <= b < 4
                implies #[trigger] spec_cmd_outcome_byte(
                    tbl,
                    pre,
                    HEADER_SIZE as int,
                    4 * (i2 as int) + b,
                ) == pre.index((pos as int) + b)
            by {}
        }
        i2 += 1;
        pos += 4;
    }
    // final face, part 1: every byte of the handle area equals its
    // expected outcome byte (window facet at i2 == nr)
    assert((i2 as int) == (nr_handles as int));
    // final face, part 2: every byte outside the handle area keeps
    // its entry value (tail facet at pos == area end)
    assert forall|j: int|
        0 <= j < (pre.len() as int)
            && !((HEADER_SIZE as int) <= j < handle_area_end(nr_handles as int))
        ==> cmd@.index(j) == pre.index(j)
    by {
        assert((pos as int) == handle_area_end(nr_handles as int));
    }
    Result::Ok(())
}

// ------------------------------------------------------------------
// Response-header handle outcome (rewrite.rs:71-108)
// ------------------------------------------------------------------

/// Origin Rust: /// Process the handle returned in the response header.
/// pub fn map_response_handle(
///     tbl: &mut SpaceTable, has_rhandle: bool, rsp: &mut [u8],
/// ) -> HeaderOutcome { ... } (rewrite.rs:71-108; the reads at
/// offsets 6 and 10 have no upstream length check for the header-
/// plus-one-handle span -- the twin carries the 14-byte requires;
/// public panic face, suspect row S-T5-5)
pub exec fn map_response_handle(
    tbl: &mut SpaceTable,
    has_rhandle: bool,
    rsp: &mut [u8],
) -> (r: HeaderOutcome)
    requires
        (HEADER_SIZE as int) + 4 <= rsp.len() as int,
    ensures
        match r {
            HeaderOutcome::NoHandle => {
                (!has_rhandle || wire_be32(old(rsp)@, 6) != 0)
                    && final(rsp)@ == old(rsp)@
                    && final(tbl).ctx@ == old(tbl).ctx@
                    && final(tbl).sessions@ == old(tbl).sessions@
            }
            HeaderOutcome::Virtualized { vhandle: v } => {
                let h = wire_be32(old(rsp)@, HEADER_SIZE as int);
                wire_be32(old(rsp)@, 6) == 0
                    && spec_is_transient_val(h)
                    && spec_valid_phandle_val(h)
                    // the slot that was NOT already registered (the
                    // upstream lookup screen)
                    && (forall|k: int|
                        0 <= k < SLOTS as int
                            ==> !spec_slot_live_word(old(tbl).ctx@.index(k), h))
                    // the table delta intern's face gives (the
                    // slot of the reported vhandle holds the
                    // physical handle; every other slot is
                    // preserved)
                    && (exists|i: int|
                        0 <= i < SLOTS as int
                            && spec_slot_of(v as int) == i
                            && (v as int) == spec_vhandle_of(i)
                            && spec_slot_live_word(final(tbl).ctx@.index(i), h)
                            && (forall|j: int|
                                0 <= j < SLOTS as int && j != i
                                    ==> final(tbl).ctx@.index(j)
                                        == old(tbl).ctx@.index(j)))
                    && final(tbl).sessions@ == old(tbl).sessions@
                    // the response's handle word is the vhandle
                    && wire_be32(final(rsp)@, HEADER_SIZE as int) == v as int
                    && forall|j: int|
                        0 <= j < (old(rsp).len() as int)
                            && !((HEADER_SIZE as int) <= j < (HEADER_SIZE as int + 4))
                        ==> final(rsp)@.index(j) == old(rsp)@.index(j)
            }
            HeaderOutcome::SessionTracked { phandle: h } => {
                let e = wire_be32(old(rsp)@, HEADER_SIZE as int);
                e == h as int
                    && wire_be32(old(rsp)@, 6) == 0
                    && spec_is_session_val(e)
                    && h != 0
                    // the session side delta: one previously-zero
                    // slot now carries the session handle
                    && (exists|i: int|
                        0 <= i < SLOTS as int
                            && old(tbl).sessions@.index(i) == 0
                            && final(tbl).sessions@.index(i) == h
                            && forall|j: int|
                                0 <= j < SLOTS as int && j != i
                                    ==> final(tbl).sessions@.index(j)
                                        == old(tbl).sessions@.index(j))
                    && final(tbl).ctx@ == old(tbl).ctx@
                    && final(rsp)@ == old(rsp)@
            }
            HeaderOutcome::Unknown { phandle: h } => {
                let e = wire_be32(old(rsp)@, HEADER_SIZE as int);
                e == h as int
                    && wire_be32(old(rsp)@, 6) == 0
                    && !spec_is_transient_val(e)
                    && !spec_is_session_val(e)
                    && final(rsp)@ == old(rsp)@
                    && final(tbl).ctx@ == old(tbl).ctx@
                    && final(tbl).sessions@ == old(tbl).sessions@
            }
            HeaderOutcome::OutOfSlots { flush: f } => {
                let e = wire_be32(old(rsp)@, HEADER_SIZE as int);
                e == f as int
                    && wire_be32(old(rsp)@, 6) == 0
                    // the handle was session- or transient-shaped:
                    // Unknown consumes everything else above
                    && (spec_is_transient_val(e) || spec_is_session_val(e))
                    && final(rsp)@ == old(rsp)@
                    && final(tbl).ctx@ == old(tbl).ctx@
                    && final(tbl).sessions@ == old(tbl).sessions@
            }
        },
{
    let ghost pre_rsp = rsp@;
    let ghost pre_sessions = tbl.sessions@;
    let ghost e0 = wire_be32(pre_rsp, HEADER_SIZE as int);
    if !has_rhandle {
        return HeaderOutcome::NoHandle;
    }
    let rc = read_be32(rsp, 6);
    if rc != RC_SUCCESS {
        return HeaderOutcome::NoHandle;
    }
    let phandle = read_be32(rsp, HEADER_SIZE);
    if is_transient_exec(phandle) {
        // lowered screen: the explicit match keeps the lookup's
        // None-arm face (the "no slot was already Live" fact)
        let already = match tbl.lookup(phandle) {
            Option::Some(_) => true,
            Option::None => false,
        };
        if phandle == 0 || phandle == CTX_SAVED_SENTINEL_VALUE || already {
            return HeaderOutcome::OutOfSlots { flush: phandle };
        }
        let r_i = tbl.intern(phandle);
        match r_i {
            Option::Some(vhandle) => {
                assert(tbl.sessions@ == pre_sessions);
                write_be32(rsp, HEADER_SIZE, vhandle);
                // face shims: intern's delta, the write's window, and
                // the exact preservation outside the rewritten word
                let ghost i = spec_slot_of(vhandle as int);
                assert(0 <= i < SLOTS as int);
                assert(spec_vhandle_of(i) == vhandle as int);
                assert(e0 == (phandle as int));
                assert(spec_is_transient_val(e0));
                assert(spec_valid_phandle_val(e0));
                assert(wire_be32(rsp@, HEADER_SIZE as int) == vhandle as int);
                assert forall|j: int|
                    0 <= j < (pre_rsp.len() as int)
                        && !((HEADER_SIZE as int) <= j < (HEADER_SIZE as int + 4))
                    implies #[trigger] rsp@.index(j) == pre_rsp.index(j)
                by {}
                assert(spec_slot_live_word(tbl.ctx@.index(i), e0));
                assert(tbl.sessions@ == pre_sessions);
                assert((i as int) < SLOTS as int);
                return HeaderOutcome::Virtualized { vhandle };
            }
            Option::None => {
                return HeaderOutcome::OutOfSlots { flush: phandle };
            }
        }
    } else if is_session_exec(phandle) {
        if phandle == 0 || tbl.has_session_exec(phandle) {
            return HeaderOutcome::OutOfSlots { flush: phandle };
        }
        if tbl.add_session(phandle) {
            return HeaderOutcome::SessionTracked { phandle };
        } else {
            return HeaderOutcome::OutOfSlots { flush: phandle };
        }
    } else {
        return HeaderOutcome::Unknown { phandle };
    }
}

// ------------------------------------------------------------------
// Capability handle-list compaction (rewrite.rs:109-165)
// ------------------------------------------------------------------

/// Origin Rust: /// Rewrite the handle list in a capability response: transient handles are replaced by virtual handles,
/// /// transient handles unknown to this space are removed from the list, and the rest are kept as-is. The
/// /// list is compacted in place and the length and count fields are updated together.
/// ///
/// /// Removal is a direct expression of isolation: when a space enumerates transient objects, it should only
/// /// see its own.
/// ///
/// /// Returns the rewritten total packet length.
/// pub fn map_capability_handles(
///     tbl: &SpaceTable, is_cap_query: bool, rsp: &mut [u8], len: usize,
/// ) -> Result<usize, SpaceErr> { ... } (rewrite.rs:109-165;
/// for-loop lowered to a while-walk; is_multiple_of lowered to %.
/// The peer-controlled `len` parameter is never checked against
/// `rsp.len()` upstream -- the reads and writes of the compaction
/// walk would panic out of bounds; the twin carries the requires
/// (plus the u32-cast sanity bound for the rewritten length word);
/// public panic face, suspect row S-T5-6)
pub exec fn map_capability_handles(
    tbl: &SpaceTable,
    is_cap_query: bool,
    rsp: &mut [u8],
    len: usize,
) -> (r: Result<usize, SpaceErr>)
    requires
        (len as int) <= rsp.len() as int,
        (len as int) <= 0xFFFF_FFFF,
    ensures
        match r {
            Result::Ok(l) => {
                let pre = old(rsp)@;
                if !is_cap_query || len < CAP_HANDLES_OFF as int {
                    // never a capability-list packet for this pass:
                    // nothing is rewritten
                    l == len && final(rsp)@ == pre
                } else if wire_be32(pre, 6) != 0
                    || wire_be32(pre, CAP_CAPABILITY_OFF as int) != CAP_HANDLES as int
                {
                    // not a successful handle-list response: untouched
                    l == len && final(rsp)@ == pre
                } else {
                    // compaction path: the count and length words
                    // are rewritten consistently with the compacted
                    // tail; l == 19 + 4 * (number of kept handles).
                    // The words inside the window [19, len) were
                    // rewritten per the compaction rule; the full
                    // kept-subsequence order-preservation face is
                    // the deferred record D-T5-1 of this batch.
                    l >= CAP_HANDLES_OFF as int
                        && (l - CAP_HANDLES_OFF as int) % 4 == 0
                        && l <= len
                        && wire_be32(final(rsp)@, CAP_COUNT_OFF as int)
                            == (l - CAP_HANDLES_OFF as int) / 4
                        && wire_be32(final(rsp)@, RSP_LENGTH_OFF as int) == l
                        && (forall|j: int|
                            0 <= j < pre.len()
                                && !(2 <= j < 6)
                                && !(CAP_COUNT_OFF as int <= j < CAP_COUNT_OFF as int + 4)
                                && !((CAP_HANDLES_OFF as int) <= j < len)
                            ==> final(rsp)@.index(j) == pre.index(j))
                }
            }
            Result::Err(SpaceErr::Malformed) => {
                let pre = old(rsp)@;
                final(rsp)@ == pre
                    && (len < CAP_HANDLES_OFF as int
                        || (len - CAP_HANDLES_OFF as int) % 4 != 0
                        || wire_be32(pre, CAP_COUNT_OFF as int)
                            != (len - CAP_HANDLES_OFF as int) / 4)
            }
            Result::Err(SpaceErr::BadHandle) => false,
        },
{
    if !is_cap_query {
        return Result::Ok(len);
    }
    let ghost pre = rsp@;
    if len < CAP_HANDLES_OFF {
        return Result::Err(SpaceErr::Malformed);
    }
    let rc = read_be32(rsp, 6);
    if rc != RC_SUCCESS {
        return Result::Ok(len);
    }
    if read_be32(rsp, CAP_CAPABILITY_OFF) != CAP_HANDLES {
        return Result::Ok(len);
    }
    let tail = len - CAP_HANDLES_OFF;
    if tail % 4 != 0 {
        return Result::Err(SpaceErr::Malformed);
    }
    let avail: usize = tail / 4;
    let declared = read_be32(rsp, CAP_COUNT_OFF);
    if declared as usize != avail {
        return Result::Err(SpaceErr::Malformed);
    }
    let count: usize = avail;
    // ---- in-place compaction: write head j never passes the read
    // head i, and each kept word is written before the next read
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut rpos: usize = CAP_HANDLES_OFF;
    let mut wpos: usize = CAP_HANDLES_OFF;
    while i < count
        invariant
            (i as int) <= (count as int),
            (j as int) <= (i as int),
            (rpos as int) == (CAP_HANDLES_OFF as int) + 4 * (i as int),
            (wpos as int) == (CAP_HANDLES_OFF as int) + 4 * (j as int),
            // bytes before the handle window never get written by
            // the walk (they are rewritten only by the tail's two
            // field writes, after the loop)
            forall|q: int|
                0 <= q < CAP_HANDLES_OFF as int
                    ==> #[trigger] rsp@.index(q) == pre.index(q),
            // and bytes at or beyond the declared packet length are
            // beyond every walk window as well
            forall|q: int|
                (len as int) <= q < (pre.len() as int)
                    ==> #[trigger] rsp@.index(q) == pre.index(q),
            (count as int) == (len as int - CAP_HANDLES_OFF as int) / 4,
            ((i as int) < (count as int))
                ==> CAP_HANDLES_OFF as int + 4 * (i as int) + 4 <= len,
            ((j as int) < (count as int))
                ==> (CAP_HANDLES_OFF as int) + 4 * (j as int)
                    + 4 <= (rsp.len() as int),
            len <= rsp.len() as int,
            (rsp.len() as int) == old(rsp)@.len(),
            // every byte from the write head onward is still entry
            forall|q: int|
                CAP_HANDLES_OFF as int + 4 * (j as int) <= q < len
                    ==> rsp@.index(q) == pre.index(q),
        decreases
            (count as int) - (i as int),
    {
        let h = read_be32(rsp, rpos);
        assert((rpos as int) == (CAP_HANDLES_OFF as int) + 4 * (i as int));
        if is_transient_exec(h) {
            if h != 0 && h != CTX_SAVED_SENTINEL_VALUE {
                match tbl.lookup(h) {
                    Option::Some(v) => {
                        // write lowered to the .set byte quad (T4-3:
                        // slice writes inside loops need the
                        // seq-update axiom in scope, same four bytes
                        // as write_be32 would emit)
                        let bts = super::cursor::be32_bytes(v);
                        rsp.set(wpos, bts[0]);
                        rsp.set(wpos + 1, bts[1]);
                        rsp.set(wpos + 2, bts[2]);
                        rsp.set(wpos + 3, bts[3]);
                        j += 1;
                        wpos += 4;
                    }
                    Option::None => {}
                }
            }
        } else {
            let bts = super::cursor::be32_bytes(h);
            rsp.set(wpos, bts[0]);
            rsp.set(wpos + 1, bts[1]);
            rsp.set(wpos + 2, bts[2]);
            rsp.set(wpos + 3, bts[3]);
            j += 1;
            wpos += 4;
        }
        i += 1;
        rpos += 4;
    }
    let new_len = CAP_HANDLES_OFF + 4 * j;
    write_be32(rsp, CAP_COUNT_OFF, j as u32);
    write_be32(rsp, RSP_LENGTH_OFF, new_len as u32);
    // end-of-fn face shims: the two field words are rewritten to be
    // self-consistent with the compacted length
    assert((new_len as int) == (CAP_HANDLES_OFF as int) + 4 * (j as int));
    assert((new_len as int - CAP_HANDLES_OFF as int) % 4 == 0);
    assert((j as int) <= (count as int));
    assert((new_len as int) <= (len as int));
    assert(
        wire_be32(rsp@, CAP_COUNT_OFF as int) == (j as int)
    );
    assert(wire_be32(rsp@, RSP_LENGTH_OFF as int) == (new_len as int));
    // bytes outside all three rewritten windows are entry bytes:
    // [0, 2), [6, 15), and everything from len onward
    assert forall|j: int|
        0 <= j < (pre.len() as int)
            && !((RSP_LENGTH_OFF as int) <= j < ((RSP_LENGTH_OFF + 4) as int))
            && !((CAP_COUNT_OFF as int) <= j < ((CAP_COUNT_OFF + 4) as int))
            && !((CAP_HANDLES_OFF as int) <= j < (len as int))
        implies #[trigger] rsp@.index(j) == pre.index(j)
    by {
        assert((len as int) <= (pre.len() as int));
    }
    Result::Ok(new_len)
}


// ------------------------------------------------------------------
// Proof zone: the facet -> word lift (separate query budget).
// ------------------------------------------------------------------

/// The window-facet bytes of the command rewrite imply the
/// word-level outcome face: four outcome bytes of one position
/// re-sum to the resolution word (transient case: weak-sign of the
/// established Some(spec_resolved), tying the value to the table)
/// or to the entry word (non-transient case, byte preservation).
/// Carried as its own proof item so the exec fn's query stays
/// light; consumers needing the word faces instantiate this lemma.
pub(crate) proof fn lemma_cmd_facet_to_words(
    tbl: &SpaceTable,
    pre: Seq<u8>,
    fin: Seq<u8>,
    base: int,
    nr: int,
)
    requires
        base + 4 * nr <= pre.len(),
        fin.len() == pre.len(),
        forall|q: int|
            0 <= q < 4 * nr
                ==> fin.index(base + q) == spec_cmd_outcome_byte(tbl, pre, base, q),
        forall|k: int|
            0 <= k < nr
                && spec_is_transient_val(entry_word_at(pre, base, k))
            ==> spec_resolve(tbl, entry_word_at(pre, base, k))
                == Option::Some(spec_resolved(
                    tbl,
                    entry_word_at(pre, base, k),
                )),
    ensures
        forall|k: int|
            0 <= k < nr ==> spec_cmd_word_outcome(tbl, pre, fin, base, k),
{
    assert forall|k: int|
        0 <= k < nr
        implies spec_cmd_word_outcome(tbl, pre, fin, base, k)
    by {
        let e = entry_word_at(pre, base, k);
        let b0 = spec_cmd_outcome_byte(tbl, pre, base, 4 * k);
        let b1 = spec_cmd_outcome_byte(tbl, pre, base, 4 * k + 1);
        let b2 = spec_cmd_outcome_byte(tbl, pre, base, 4 * k + 2);
        let b3 = spec_cmd_outcome_byte(tbl, pre, base, 4 * k + 3);
        assert(
            fin.index(base + 4 * k) == b0
                && fin.index(base + 4 * k + 1) == b1
                && fin.index(base + 4 * k + 2) == b2
                && fin.index(base + 4 * k + 3) == b3
        );
        assert(
            wire_be32(fin, base + 4 * k)
                == 16777216 * b0 as int + 65536 * b1 as int
                    + 256 * b2 as int + b3 as int
        );
        if spec_is_transient_val(e) {
            let p = spec_resolved(tbl, e) as int;
            assert(b0 == (p / 16777216) as u8);
            assert(b1 == (p / 65536 % 256) as u8);
            assert(b2 == (p / 256 % 256) as u8);
            assert(b3 == (p % 256) as u8);
        } else {
            assert(b0 == pre.index(base + 4 * k));
            assert(b1 == pre.index(base + 4 * k + 1));
            assert(b2 == pre.index(base + 4 * k + 2));
            assert(b3 == pre.index(base + 4 * k + 3));
            assert(
                16777216 * b0 as int + 65536 * b1 as int + 256 * b2 as int + b3 as int
                    == wire_be32(pre, base + 4 * k)
            );
        }
    }
}

} // verus!
