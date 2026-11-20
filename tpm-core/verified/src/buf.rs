//! tpm-core 0.1.4 fixed-size command buffer (src/buf.rs) -- Verus
//! translation.
//!
//! Upstream module doc (buf.rs:1-13, abridged): "The commands used in
//! the boot phase are written directly into the fixed-size temporary
//! buffer by `boot`, ... its error model is the sticky flags `overflow`
//! and `boundary_error` with a final uniform collection, ... its byte
//! order also follows `endian` rather than `cursor`."
//!
//! Faces re-erected here: the length invariant length <= N, the
//! sticky-flag discipline (once set, a flag never clears and no
//! further byte is written), and the length-field write-back of
//! sync_length per BufKind (the wire field is a TRUNCATED image of
//! self.length -- the Tpm2b branch narrows through u16 and the
//! Command branch through u32, kept as the faithful truncation face
//! rather than silently tightened; see the wire-size spec fns).

use vstd::prelude::*;

verus! {

use super::endian::{be16_of, be16_of_exec, be32_of, be32_of_exec};
use super::types::{tag_code, TpmTag};
use super::cursor::{be16_bytes_spec, be32_bytes_spec};

/// Origin Rust: /// Size of `struct tpm_header`: tag (2) + length (4) + ordinal/return_code (4).
/// pub const TPM_HEADER_SIZE: usize = 10; (src/buf.rs:17-18)
pub const TPM_HEADER_SIZE: usize = 10;

/// Origin Rust: /// TPM2B header: a single 16-bit size field.
/// pub const TPM2B_HEADER_SIZE: usize = 2; (src/buf.rs:19-20)
pub const TPM2B_HEADER_SIZE: usize = 2;

/// Origin Rust: /// The kernel glue layer should reimplement this as page allocation and Box it to avoid placing a
/// 4 KiB buffer on the kernel stack; the default implementation here is only for host-side differential
/// testing.
/// fn alloc_zeroed_storage<const N: usize>() -> [u8; N] {
///     [0u8; N]
/// } (src/buf.rs:21-26)
fn alloc_zeroed_storage<const N: usize>() -> (r: [u8; N])
    ensures
        r@.len() == (N as int),
        forall|i: int| 0 <= i < (N as int) ==> r@.index(i) == 0,
{
    let mut out = [0u8; N];
    out
}

/// Origin Rust: /// It differs from `overflow`/`boundary_error` in that the kind is fixed at construction time and then
/// never changes.
/// #[derive(Clone, Copy)]
/// pub enum BufKind { Command, Tpm2b } (src/buf.rs:27-35 with variant
/// docs: "Ordinary command buffer with a struct tpm_header prefix.",
/// "TPM2B buffer with a 2-byte size prefix.")
#[derive(Clone, Copy)]
pub enum BufKind {
    Command,
    Tpm2b,
}

/// spec twin of the kind test (the exec twin is the upstream match
/// body of is_tpm2b).
pub open spec fn kind_is_tpm2b(k: BufKind) -> bool {
    match k {
        BufKind::Tpm2b => true,
        BufKind::Command => false,
    }
}

/// Origin Rust: pub struct TpmBuf<const N: usize> {
///     pub data: [u8; N], pub length: usize, pub kind: BufKind,
///     pub overflow: bool, pub boundary_error: bool, pub handles: u8,
/// } (src/buf.rs:36-43)
pub struct TpmBuf<const N: usize> {
    pub data: [u8; N],
    pub length: usize,
    pub kind: BufKind,
    pub overflow: bool,
    pub boundary_error: bool,
    pub handles: u8,
}

/// Seq agreement outside a written index range [from, to).
pub open spec fn same_outside_range(a: Seq<u8>, b: Seq<u8>, from: int, to: int) -> bool {
    a.len() == b.len()
        && forall|j: int| 0 <= j < a.len() && !(from <= j < to) ==> a[j] == b[j]
}

/// Seq agreement outside two written index ranges (the kind's header
/// window and the append tail window).
pub open spec fn same_outside_two(
    a: Seq<u8>,
    b: Seq<u8>,
    h_from: int,
    h_to: int,
    w_from: int,
    w_to: int,
) -> bool {
    a.len() == b.len()
        && forall|j: int|
            0 <= j < a.len()
                && !((h_from <= j < h_to) || (w_from <= j < w_to))
                ==> a[j] == b[j]
}

/// Wire size field of a Tpm2b buffer: the content size
/// (length minus the 2-byte size prefix) narrowed through u16.
/// This is the FAITHFUL truncation face of the upstream
/// `(self.length - TPM2B_HEADER_SIZE) as u16` (src/buf.rs:55): for a
/// Tpm2b buffer whose content exceeds 65535 bytes the upstream write
/// wraps, and the doc line on sync_length ("Write back self.length to
/// the length field in the header", src/buf.rs:51) then does not hold
/// of the wire bytes. Kept as the truncation face so a suspects row
/// can state the wrap concretely (out/ ledger; not filed here).
pub open spec fn tpm2b_wire_size(content_len: int) -> int {
    content_len % 65536
}

/// Wire size field of a Command buffer: the total size narrowed
/// through u32 (same truncation-face treatment as tpm2b_wire_size;
/// the upstream body is `self.length as u32`, src/buf.rs:59).
pub open spec fn command_wire_size(total_len: int) -> int {
    total_len % 0x1_0000_0000
}

/// sync_length's exit face: the wire length field equals the kind's
/// wire-size image of self.length.
/// SPEC-DOC MISMATCH candidate (not filed): the sync_length doc says
/// "Write back `self.length` to the length field in the header";
/// the wire field is the u16/u32-narrowed image, so a Tpm2b buffer
/// with more than 65535 content bytes stores a wrapped size (see
/// tpm2b_wire_size). Suspects row in the out/ ledger carries the
/// concrete wrap value.
pub open spec fn wire_consistent<const N: usize>(b: TpmBuf<N>) -> bool {
    match b.kind {
        BufKind::Command => {
            b.data@.subrange(2, 6) == be32_bytes_spec(command_wire_size(b.length as int) as u32)
        }
        BufKind::Tpm2b => {
            b.data@.subrange(0, 2)
                == be16_bytes_spec(tpm2b_wire_size(b.length as int - TPM2B_HEADER_SIZE as int) as u16)
        }
    }
}

impl<const N: usize> TpmBuf<N> {
    /// Origin Rust: fn put_be16(&mut self, at: usize, v: u16) {
    ///     self.data[at..at + 2].copy_from_slice(&v.to_be_bytes());
    /// } (src/buf.rs:45-47; copy_from_slice lowered to the two
    /// element assignments, same bytes)
    exec fn put_be16(&mut self, at: usize, v: u16)
        requires
            (at as int) + 2 <= (N as int),
        ensures
            final(self).data@.index(at as int) == (v / 256) as u8,
            final(self).data@.index(at as int + 1) == (v % 256) as u8,
            same_outside_range(old(self).data@, final(self).data@, at as int, at as int + 2),
            final(self).data@.len() == (N as int),
            final(self).length == old(self).length,
            final(self).kind == old(self).kind,
            final(self).overflow == old(self).overflow,
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
    {
        self.data[at] = (v / 256u16) as u8;
        self.data[at + 1] = (v % 256u16) as u8;
    }

    /// Origin Rust: fn put_be32(&mut self, at: usize, v: u32) {
    ///     self.data[at..at + 4].copy_from_slice(&v.to_be_bytes());
    /// } (src/buf.rs:48-50; copy_from_slice lowered to the four
    /// element assignments, same bytes)
    exec fn put_be32(&mut self, at: usize, v: u32)
        requires
            (at as int) + 4 <= (N as int),
        ensures
            final(self).data@.index(at as int) == (v / 16777216) as u8,
            final(self).data@.index(at as int + 1) == (v / 65536 % 256) as u8,
            final(self).data@.index(at as int + 2) == (v / 256 % 256) as u8,
            final(self).data@.index(at as int + 3) == (v % 256) as u8,
            same_outside_range(old(self).data@, final(self).data@, at as int, at as int + 4),
            final(self).data@.len() == (N as int),
            final(self).length == old(self).length,
            final(self).kind == old(self).kind,
            final(self).overflow == old(self).overflow,
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
    {
        self.data[at] = (v / 16777216u32) as u8;
        self.data[at + 1] = (v / 65536u32 % 256u32) as u8;
        self.data[at + 2] = (v / 256u32 % 256u32) as u8;
        self.data[at + 3] = (v % 256u32) as u8;
    }

    /// Origin Rust: /// Write back `self.length` to the length field in the header.
    /// fn sync_length(&mut self) {
    ///     match self.kind {
    ///         BufKind::Tpm2b => {
    ///             let sz: u16 = (self.length - TPM2B_HEADER_SIZE) as u16;
    ///             self.put_be16(0, sz);
    ///         }
    ///         BufKind::Command => {
    ///             let l: u32 = self.length as u32;
    ///             self.put_be32(2, l);
    ///         }
    ///     }
    /// } (src/buf.rs:51-63)
    /// The `as u16` / `as u32` narrowing casts are spelled through
    /// the modulus form so the transcription keeps the truncation
    /// semantics (not a tightening); the wire_consistent face states
    /// the exact narrowed image.
    exec fn sync_length(&mut self)
        requires
            (self.length as int) <= (N as int),
            kind_is_tpm2b(self.kind) ==> (TPM2B_HEADER_SIZE as int) <= (self.length as int),
            kind_is_tpm2b(self.kind) ==> (2 as int) <= (N as int),
            !kind_is_tpm2b(self.kind) ==> (6 as int) <= (N as int),
        ensures
            final(self).data@.len() == (N as int),
            final(self).length == old(self).length,
            final(self).kind == old(self).kind,
            final(self).overflow == old(self).overflow,
            final(self).boundary_error == old(self).boundary_error,
            final(self).handles == old(self).handles,
            wire_consistent(*final(self)),
            // data preserved outside the kind's length-field window
            // (the header-rewrite footprint), so callers can compose
            // append-tail faces across a sync_length call
            match final(self).kind {
                BufKind::Tpm2b => {
                    same_outside_range(old(self).data@, final(self).data@, 0, 2)
                }
                BufKind::Command => {
                    same_outside_range(old(self).data@, final(self).data@, 2, 6)
                }
            },
    {
        match self.kind {
            BufKind::Tpm2b => {
                let content = (self.length - TPM2B_HEADER_SIZE) % 65536;
                let sz = content as u16;
                self.put_be16(0, sz);
                proof {
                    let h = tpm2b_wire_size(self.length as int - TPM2B_HEADER_SIZE as int);
                    assert(h == content as int);
                    assert(h as u16 == sz);
                    assert(self.data@.subrange(0, 2) == be16_bytes_spec(sz));
                    assert(self.data@.subrange(0, 2) == be16_bytes_spec(h as u16));
                }
            }
            BufKind::Command => {
                let l = ((self.length as u64) % 4294967296u64) as u32;
                self.put_be32(2, l);
                proof {
                    let w = command_wire_size(self.length as int);
                    let w32 = w as u32;
                    assert(w == l as int);
                    assert(w32 == l);
                    assert(self.data@.subrange(2, 6) == be32_bytes_spec(w32));
                }
            }
        }
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_reset()`: initialize an existing storage area in place as a command.
    /// pub fn reset_command(&mut self, tag: TpmTag, ordinal: u32) (src/buf.rs:64-75)
    /// Upstream indexes data[2..6] and data[6..10] with no N >=
    /// TPM_HEADER_SIZE guard: TpmBuf::<N> with N < 10 panics inside
    /// reset_command/new_command. The requires below carries the
    /// missing bound (suspects row in the out/ ledger; upstream doc
    /// states no # Panics entry).
    pub exec fn reset_command(&mut self, tag: TpmTag, ordinal: u32)
        requires
            (TPM_HEADER_SIZE as int) <= (N as int),
        ensures
            final(self).data@.len() == (N as int),
            final(self).kind == BufKind::Command,
            final(self).overflow == false,
            final(self).boundary_error == false,
            final(self).handles == 0,
            final(self).length == TPM_HEADER_SIZE,
            final(self).data@.subrange(0, 2)
                == be16_bytes_spec(tag_code(tag)),
            final(self).data@.subrange(2, 6)
                == be32_bytes_spec((TPM_HEADER_SIZE as u32)),
            final(self).data@.subrange(6, 10)
                == be32_bytes_spec(ordinal),
            same_outside_range(
                old(self).data@,
                final(self).data@,
                0,
                TPM_HEADER_SIZE as int,
            ),
            wire_consistent(*final(self)),
    {
        self.kind = BufKind::Command;
        self.overflow = false;
        self.boundary_error = false;
        self.handles = 0;
        self.length = TPM_HEADER_SIZE;
        let t = tag.code();
        self.put_be16(0, t);
        self.put_be32(2, TPM_HEADER_SIZE as u32);
        self.put_be32(6, ordinal);
        proof {
            let w = command_wire_size(self.length as int);
            assert(w == TPM_HEADER_SIZE as int);
            assert(w as u32 == TPM_HEADER_SIZE as u32);
            assert(self.data@.subrange(2, 6) == be32_bytes_spec(w as u32));
            assert(self.data@.subrange(2, 6) == be32_bytes_spec(TPM_HEADER_SIZE as u32));
        }
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_reset_sized()`.
    /// pub fn reset_sized(&mut self) {
    ///     self.kind = BufKind::Tpm2b; ... self.put_be16(0, 0u16);
    /// } (src/buf.rs:76-84)
    pub exec fn reset_sized(&mut self)
        requires
            (2 as int) <= (N as int),
        ensures
            final(self).data@.len() == (N as int),
            final(self).kind == BufKind::Tpm2b,
            final(self).overflow == false,
            final(self).boundary_error == false,
            final(self).handles == 0,
            final(self).length == TPM2B_HEADER_SIZE,
            final(self).data@.subrange(0, 2) == be16_bytes_spec(0u16),
            same_outside_range(old(self).data@, final(self).data@, 0, 2),
            wire_consistent(*final(self)),
    {
        self.kind = BufKind::Tpm2b;
        self.overflow = false;
        self.boundary_error = false;
        self.handles = 0;
        self.length = TPM2B_HEADER_SIZE;
        self.put_be16(0, 0u16);
        proof {
            // pinned faces for the reset wire claim (Tpm2b size 0)
            assert(self.data@.index(0) == 0u8);
            assert(self.data@.index(1) == 0u8);
            assert(self.data@.subrange(0, 2) == be16_bytes_spec(0u16));
            assert(tpm2b_wire_size(
                self.length as int - TPM2B_HEADER_SIZE as int
            ) == 0);
        }
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_init()`: allocate + initialize.
    /// pub fn new_command(tag: TpmTag, ordinal: u32) -> Self (src/buf.rs:85-97)
    pub exec fn new_command(tag: TpmTag, ordinal: u32) -> (b: Self)
        requires
            (TPM_HEADER_SIZE as int) <= (N as int),
        ensures
            b.data@.len() == (N as int),
            b.kind == BufKind::Command,
            b.overflow == false,
            b.boundary_error == false,
            b.handles == 0,
            b.length == TPM_HEADER_SIZE,
            b.data@.subrange(0, 2) == be16_bytes_spec(tag_code(tag)),
            b.data@.subrange(2, 6) == be32_bytes_spec((TPM_HEADER_SIZE as u32)),
            b.data@.subrange(6, 10) == be32_bytes_spec(ordinal),
            forall|j: int| 10 <= j < (N as int) ==> b.data@.index(j) == 0,
            wire_consistent(b),
    {
        let mut buf = TpmBuf {
            data: alloc_zeroed_storage::<N>(),
            length: 0,
            kind: BufKind::Command,
            overflow: false,
            boundary_error: false,
            handles: 0,
        };
        buf.reset_command(tag, ordinal);
        buf
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_init_sized()`.
    /// pub fn new_sized() -> Self (src/buf.rs:98-110)
    pub exec fn new_sized() -> (b: Self)
        requires
            (2 as int) <= (N as int),
        ensures
            b.data@.len() == (N as int),
            b.kind == BufKind::Tpm2b,
            b.overflow == false,
            b.boundary_error == false,
            b.handles == 0,
            b.length == TPM2B_HEADER_SIZE,
            b.data@.subrange(0, 2) == be16_bytes_spec(0u16),
            forall|j: int| 2 <= j < (N as int) ==> b.data@.index(j) == 0,
            wire_consistent(b),
    {
        let mut buf = TpmBuf {
            data: alloc_zeroed_storage::<N>(),
            length: 0,
            kind: BufKind::Tpm2b,
            overflow: false,
            boundary_error: false,
            handles: 0,
        };
        buf.reset_sized();
        buf
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_append()`.
    /// pub fn append(&mut self, src: &[u8]) (src/buf.rs:111-125)
    /// Sticky-overflow face: an already-set overflow leaves the
    /// buffer untouched; a fresh overflow sets the flag without
    /// writing any byte; a fit appends src at the tail and keeps the
    /// wire length field consistent.
    pub exec fn append(&mut self, src: &[u8])
        requires
            (old(self).length as int) <= (N as int),
            kind_is_tpm2b(old(self).kind)
                ==> (TPM2B_HEADER_SIZE as int) <= (old(self).length as int),
            kind_is_tpm2b(old(self).kind) ==> (2 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind) ==> (6 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind)
                ==> (6 as int) <= (old(self).length as int),
            wire_consistent(*old(self)),
        ensures
            old(self).overflow ==> *final(self) == *old(self),
            !old(self).overflow ==>
                (src.len() <= (N as int) - (old(self).length as int)) == !final(self).overflow,
            !old(self).overflow && !final(self).overflow ==>
                final(self).length == old(self).length + src.len()
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles
                    && wire_consistent(*final(self))
                    && match final(self).kind {
                        BufKind::Tpm2b => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            0,
                            2,
                            (old(self).length) as int,
                            (old(self).length + src.len()) as int,
                        ),
                        BufKind::Command => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            2,
                            6,
                            (old(self).length) as int,
                            (old(self).length + src.len()) as int,
                        ),
                    }
                    && forall|i: int| 0 <= i < src.len()
                        ==> final(self).data@.index((old(self).length + i) as int)
                            == src@.index(i),
            !old(self).overflow && final(self).overflow ==>
                final(self).data@ == old(self).data@
                    && final(self).length == old(self).length
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles
                    && wire_consistent(*final(self)),
    {
        if self.overflow {
            return;
        }
        let avail: usize = N - self.length;
        if src.len() > avail {
            self.overflow = true;
            return;
        }
        let start: usize = self.length;
        let ghost prev = self.data@;
        let ghost prev_k = self.kind;
        let ghost prev_be = self.boundary_error;
        let ghost prev_h = self.handles;

        let mut i: usize = 0;
        while i < src.len()
            invariant
                i <= src.len(),
                self.data@.len() == (N as int),
                ((start as int) + (src.len() as int)) <= (N as int),
                ((start as int) + (i as int)) <= (N as int),
                self.length == start,
                self.kind == prev_k,
                self.boundary_error == prev_be,
                self.handles == prev_h,
                self.overflow == false,
                forall|j: int|
                    0 <= j < (N as int) && !((start as int) <= j < (start as int + i as int))
                        ==> self.data@.index(j) == prev.index(j),
                forall|j: int| 0 <= j < (i as int)
                    ==> self.data@.index((start as int) + j) == src@.index(j),
            decreases
                src.len() - i,
        {
            self.data[start + i] = src[i];
            i += 1;
        }
        self.length = start + src.len();
        self.sync_length();
        proof {
            // link the loop-exit faces through the sync write:
            // the loop preserved everything outside the window
            // [start, start + src.len()) into self.data@; sync_length
            // then rewrote only the kind's header window inside
            // [0, 6), so both the tail bytes and the outside-window
            // region survive into the final state.
            assert(self.length == start + src.len());
            assert(self.kind == prev_k);
            assert(self.boundary_error == prev_be);
            assert(self.handles == prev_h);
            assert(self.overflow == false);
            assert forall|j: int|
                0 <= j < (N as int)
                    && !match self.kind {
                        BufKind::Tpm2b => 0 <= j < 2,
                        BufKind::Command => 2 <= j < 6,
                    }
                    && !((start as int) <= j < ((start + src.len()) as int))
                implies self.data@.index(j) == prev.index(j)
            by {
                // skolem j: outside both the kind's header window and
                // the append tail window, so both preservation faces
                // apply
            }
            assert(forall|i2: int|
                0 <= i2 < (src.len() as int)
                    ==> self.data@.index((start + i2) as int) == src@.index(i2)
            ) by {
                // the loop wrote the window bytes; the sync rewrite
                // stays inside the header window, disjoint from it
            }
        }
    }

    /// Origin Rust: pub fn append_u8(&mut self, v: u8) (src/buf.rs:126-138)
    pub exec fn append_u8(&mut self, v: u8)
        requires
            (old(self).length as int) <= (N as int),
            kind_is_tpm2b(old(self).kind)
                ==> (TPM2B_HEADER_SIZE as int) <= (old(self).length as int),
            kind_is_tpm2b(old(self).kind) ==> (2 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind) ==> (6 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind)
                ==> (6 as int) <= (old(self).length as int),
            wire_consistent(*old(self)),
        ensures
            old(self).overflow ==> *final(self) == *old(self),
            !old(self).overflow ==>
                ((old(self).length as int) < (N as int)) == !final(self).overflow,
            !old(self).overflow && !final(self).overflow ==>
                final(self).length == old(self).length + 1
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles
                    && wire_consistent(*final(self))
                    && final(self).data@.index(old(self).length as int) == v
                    && match final(self).kind {
                        BufKind::Tpm2b => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            0,
                            2,
                            (old(self).length) as int,
                            (old(self).length + 1) as int,
                        ),
                        BufKind::Command => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            2,
                            6,
                            (old(self).length) as int,
                            (old(self).length + 1) as int,
                        ),
                    },
            !old(self).overflow && final(self).overflow ==>
                final(self).data@ == old(self).data@
                    && final(self).length == old(self).length
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles
                    && wire_consistent(*final(self)),
    {
        if self.overflow {
            return;
        }
        if self.length >= N {
            self.overflow = true;
            return;
        }
        let start = self.length;
        self.data[start] = v;
        self.length = start + 1;
        self.sync_length();
    }

    /// Origin Rust: pub fn append_u16(&mut self, v: u16) (src/buf.rs:139-151)
    pub exec fn append_u16(&mut self, v: u16)
        requires
            (old(self).length as int) <= (N as int),
            kind_is_tpm2b(old(self).kind)
                ==> (TPM2B_HEADER_SIZE as int) <= (old(self).length as int),
            kind_is_tpm2b(old(self).kind) ==> (2 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind) ==> (6 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind)
                ==> (6 as int) <= (old(self).length as int),
            wire_consistent(*old(self)),
        ensures
            old(self).overflow ==> *final(self) == *old(self),
            !old(self).overflow ==>
                (2 <= (N as int) - (old(self).length as int)) == !final(self).overflow,
            !old(self).overflow && !final(self).overflow ==>
                final(self).length == old(self).length + 2
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles
                    && wire_consistent(*final(self))
                    && final(self).data@.index(old(self).length as int) == (v / 256) as u8
                    && final(self).data@.index((old(self).length + 1) as int) == (v % 256) as u8
                    && match final(self).kind {
                        BufKind::Tpm2b => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            0,
                            2,
                            (old(self).length) as int,
                            (old(self).length + 2) as int,
                        ),
                        BufKind::Command => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            2,
                            6,
                            (old(self).length) as int,
                            (old(self).length + 2) as int,
                        ),
                    },
            !old(self).overflow && final(self).overflow ==>
                final(self).data@ == old(self).data@
                    && final(self).length == old(self).length
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles
                    && wire_consistent(*final(self)),
    {
        if self.overflow {
            return;
        }
        if N - self.length < 2 {
            self.overflow = true;
            return;
        }
        let start = self.length;
        self.put_be16(start, v);
        self.length = start + 2;
        self.sync_length();
    }

    /// Origin Rust: pub fn append_u32(&mut self, v: u32) (src/buf.rs:152-164)
    pub exec fn append_u32(&mut self, v: u32)
        requires
            (old(self).length as int) <= (N as int),
            kind_is_tpm2b(old(self).kind)
                ==> (TPM2B_HEADER_SIZE as int) <= (old(self).length as int),
            kind_is_tpm2b(old(self).kind) ==> (2 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind) ==> (6 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind)
                ==> (6 as int) <= (old(self).length as int),
            wire_consistent(*old(self)),
        ensures
            old(self).overflow ==> *final(self) == *old(self),
            !old(self).overflow ==>
                (4 <= (N as int) - (old(self).length as int)) == !final(self).overflow,
            !old(self).overflow && !final(self).overflow ==>
                final(self).length == old(self).length + 4
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles
                    && wire_consistent(*final(self))
                    && final(self).data@.index(old(self).length as int) == (v / 16777216) as u8
                    && final(self).data@.index((old(self).length + 1) as int)
                        == (v / 65536 % 256) as u8
                    && final(self).data@.index((old(self).length + 2) as int)
                        == (v / 256 % 256) as u8
                    && final(self).data@.index((old(self).length + 3) as int) == (v % 256) as u8
                    && match final(self).kind {
                        BufKind::Tpm2b => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            0,
                            2,
                            (old(self).length) as int,
                            (old(self).length + 4) as int,
                        ),
                        BufKind::Command => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            2,
                            6,
                            (old(self).length) as int,
                            (old(self).length + 4) as int,
                        ),
                    },
            !old(self).overflow && final(self).overflow ==>
                final(self).data@ == old(self).data@
                    && final(self).length == old(self).length
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles
                    && wire_consistent(*final(self)),
    {
        if self.overflow {
            return;
        }
        if N - self.length < 4 {
            self.overflow = true;
            return;
        }
        let start = self.length;
        self.put_be32(start, v);
        self.length = start + 4;
        self.sync_length();
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_append_handle()`.
    /// pub fn append_handle(&mut self, handle: u32) -> bool (src/buf.rs:165-183)
    /// The doc of the handle cap (handles == 255 refused) and the
    /// Tpm2b refusal ride the bool face.
    pub exec fn append_handle(&mut self, handle: u32) -> (r: bool)
        requires
            (old(self).length as int) <= (N as int),
            kind_is_tpm2b(old(self).kind)
                ==> (TPM2B_HEADER_SIZE as int) <= (old(self).length as int),
            kind_is_tpm2b(old(self).kind) ==> (2 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind) ==> (6 as int) <= (N as int),
            !kind_is_tpm2b(old(self).kind)
                ==> (6 as int) <= (old(self).length as int),
            wire_consistent(*old(self)),
        ensures
            kind_is_tpm2b(old(self).kind) && r == false ==> *final(self) == *old(self),
            !kind_is_tpm2b(old(self).kind) && old(self).handles == 255 && r == false
                ==> *final(self) == *old(self),
            old(self).overflow && r == false ==> *final(self) == *old(self),
            r
                ==> !final(self).overflow
                    && final(self).length == old(self).length + 4
                    && final(self).kind == old(self).kind
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles + 1
                    && wire_consistent(*final(self))
                    && final(self).data@.index(old(self).length as int)
                        == (handle / 16777216) as u8
                    && final(self).data@.index((old(self).length + 1) as int)
                        == (handle / 65536 % 256) as u8
                    && final(self).data@.index((old(self).length + 2) as int)
                        == (handle / 256 % 256) as u8
                    && final(self).data@.index((old(self).length + 3) as int)
                        == (handle % 256) as u8
                    && match final(self).kind {
                        BufKind::Tpm2b => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            0,
                            2,
                            (old(self).length) as int,
                            (old(self).length + 4) as int,
                        ),
                        BufKind::Command => same_outside_two(
                            old(self).data@,
                            final(self).data@,
                            2,
                            6,
                            (old(self).length) as int,
                            (old(self).length + 4) as int,
                        ),
                    },
            !kind_is_tpm2b(old(self).kind)
                && old(self).handles < 255
                && !old(self).overflow
                && 4 <= (N as int) - (old(self).length as int)
                ==> r,
    {
        if self.is_tpm2b() {
            return false;
        }
        if self.handles == 255 {
            return false;
        }

        if self.overflow {
            return false;
        }
        if N - self.length < 4 {
            self.overflow = true;
            return false;
        }
        self.append_u32(handle);
        self.handles += 1;
        true
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_read_u8()`.
    /// pub fn read_u8(&mut self, offset: &mut usize) -> u8 (src/buf.rs:184-196)
    /// Sticky-boundary face: an already-set boundary_error leaves
    /// everything unchanged; a fresh out-of-bounds sets the flag and
    /// yields 0; an in-bounds read advances *offset by one.
    pub exec fn read_u8(&mut self, offset: &mut usize) -> (r: u8)
        requires
            (self.length as int) <= (N as int),
        ensures
            old(self).boundary_error
                ==> r == 0
                    && *final(self) == *old(self)
                    && (*final(offset)) == (*old(offset)),
            !old(self).boundary_error ==>
                final(self).boundary_error
                    == (((*old(offset)) as int) > (old(self).length as int)
                        || (old(self).length - (*old(offset))) < 1),
            !old(self).boundary_error && !final(self).boundary_error ==>
                r == old(self).data@.index((*old(offset)) as int)
                    && (*final(offset)) == (*old(offset)) + 1
                    && ((*old(offset)) + 1) <= old(self).length
                    && final(self).data@ == old(self).data@
                    && final(self).length == old(self).length
                    && final(self).kind == old(self).kind
                    && final(self).overflow == old(self).overflow
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles,
            !old(self).boundary_error && final(self).boundary_error ==> r == 0,
    {
        if self.boundary_error {
            return 0;
        }
        if *offset > self.length || self.length - *offset < 1 {
            self.boundary_error = true;
            return 0;
        }
        let v = self.data[*offset];
        *offset += 1;
        v
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_read_u16()`.
    /// pub fn read_u16(&mut self, offset: &mut usize) -> u16 (src/buf.rs:197-211)
    pub exec fn read_u16(&mut self, offset: &mut usize) -> (r: u16)
        requires
            (self.length as int) <= (N as int),
        ensures
            old(self).boundary_error
                ==> r == 0
                    && *final(self) == *old(self)
                    && (*final(offset)) == (*old(offset)),
            !old(self).boundary_error ==>
                final(self).boundary_error
                    == (((*old(offset)) as int) > (old(self).length as int)
                        || (old(self).length - (*old(offset))) < 2),
            !old(self).boundary_error && !final(self).boundary_error ==>
                (r as int)
                    == be16_of(
                        old(self).data@.index((*old(offset)) as int),
                        old(self).data@.index(((*old(offset)) + 1) as int),
                    )
                    && (*final(offset)) == (*old(offset)) + 2
                    && ((*old(offset)) + 2) <= old(self).length
                    && final(self).data@ == old(self).data@
                    && final(self).length == old(self).length
                    && final(self).kind == old(self).kind
                    && final(self).overflow == old(self).overflow
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles,
            !old(self).boundary_error && final(self).boundary_error ==> r == 0,
    {
        if self.boundary_error {
            return 0;
        }
        if *offset > self.length || self.length - *offset < 2 {
            self.boundary_error = true;
            return 0;
        }
        let o = *offset;
        let b0 = self.data[o];
        let b1 = self.data[o + 1];
        *offset = o + 2;
        be16_of_exec(b0, b1)
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_read_u32()`.
    /// pub fn read_u32(&mut self, offset: &mut usize) -> u32 (src/buf.rs:212-228)
    pub exec fn read_u32(&mut self, offset: &mut usize) -> (r: u32)
        requires
            (self.length as int) <= (N as int),
        ensures
            old(self).boundary_error
                ==> r == 0
                    && *final(self) == *old(self)
                    && (*final(offset)) == (*old(offset)),
            !old(self).boundary_error ==>
                final(self).boundary_error
                    == (((*old(offset)) as int) > (old(self).length as int)
                        || (old(self).length - (*old(offset))) < 4),
            !old(self).boundary_error && !final(self).boundary_error ==>
                (r as int)
                    == be32_of(
                        old(self).data@.index((*old(offset)) as int),
                        old(self).data@.index(((*old(offset)) + 1) as int),
                        old(self).data@.index(((*old(offset)) + 2) as int),
                        old(self).data@.index(((*old(offset)) + 3) as int),
                    )
                    && (*final(offset)) == (*old(offset)) + 4
                    && ((*old(offset)) + 4) <= old(self).length
                    && final(self).data@ == old(self).data@
                    && final(self).length == old(self).length
                    && final(self).kind == old(self).kind
                    && final(self).overflow == old(self).overflow
                    && final(self).boundary_error == old(self).boundary_error
                    && final(self).handles == old(self).handles,
            !old(self).boundary_error && final(self).boundary_error ==> r == 0,
    {
        if self.boundary_error {
            return 0;
        }
        if *offset > self.length || self.length - *offset < 4 {
            self.boundary_error = true;
            return 0;
        }
        let o = *offset;
        let b0 = self.data[o];
        let b1 = self.data[o + 1];
        let b2 = self.data[o + 2];
        let b3 = self.data[o + 3];
        *offset = o + 4;
        be32_of_exec(b0, b1, b2, b3)
    }

    /// Origin Rust: /// Corresponds to `tpm_buf_length()`.
    /// pub fn len(&self) -> usize (src/buf.rs:229-232)
    pub exec fn len(&self) -> (l: usize)
        ensures
            (l as int) == (self.length as int),
    {
        self.length
    }

    /// Origin Rust: pub fn is_empty(&self) -> bool (src/buf.rs:233-235)
    pub exec fn is_empty(&self) -> (r: bool)
        ensures
            r == ((self.length as int) == 0),
    {
        self.length == 0
    }

    /// Origin Rust: pub fn is_tpm2b(&self) -> bool {
    ///     match self.kind { BufKind::Tpm2b => true, BufKind::Command => false }
    /// } (src/buf.rs:236-241)
    pub exec fn is_tpm2b(&self) -> (r: bool)
        ensures
            r == kind_is_tpm2b(self.kind),
    {
        match self.kind {
            BufKind::Tpm2b => true,
            BufKind::Command => false,
        }
    }

    /// Origin Rust: pub fn has_overflow(&self) -> bool (src/buf.rs:242-244)
    pub exec fn has_overflow(&self) -> (r: bool)
        ensures
            r == self.overflow,
    {
        self.overflow
    }

    /// Origin Rust: pub fn has_boundary_error(&self) -> bool (src/buf.rs:245-247)
    pub exec fn has_boundary_error(&self) -> (r: bool)
        ensures
            r == self.boundary_error,
    {
        self.boundary_error
    }

    /// Origin Rust: pub fn handle_count(&self) -> u8 (src/buf.rs:248-250)
    pub exec fn handle_count(&self) -> (h: u8)
        ensures
            h == self.handles,
    {
        self.handles
    }

    /// Origin Rust: /// The raw bytes to hand to the transport layer. **This is meaningful only when there is no
    /// overflow**, so it requires `!overflow`.
    /// pub fn as_wire(&self) -> &[u8] {
    ///     &self.data[0..self.length]
    /// } (src/buf.rs:251-255)
    pub exec fn as_wire(&self) -> (r: &[u8])
        requires
            !self.overflow,
            (self.length as int) <= (N as int),
        ensures
            r@.len() == (self.length as int),
            r@ == self.data@.subrange(0, (self.length) as int),
    {
        &self.data[0..self.length]
    }
}

} // verus!
