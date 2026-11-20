//! tpm-core batch-T1 property harness (byte/word decode and buffer
//! accounting family) -- reference-style mount over the verified src
//! tree.
//!
//! Drivers (universal-input and pinned-case UT shapes, upstream
//! semantics re-erected as exec asserts):
//!   - ut_cursor_word_roundtrip: be16/be32 encodings decode back
//!   - ut_cursor_exhaustion_discipline: reads advance exactly,
//!     fails leave the position untouched
//!   - ut_read_bytes_bounds: peer-controlled lengths stay inside the
//!     slice, over-asks give None
//!   - ut_header_parse_inverse: parse_response accepts the header
//!     build_header emits and splits the right fields
//!   - ut_tpmbuf_sticky_overflow: append sequence crosses the capacity
//!     edge; the sticky flag springs exactly there and later appends
//!     write no byte
//!   - ut_tpmbuf_sized_wire: a Tpm2b buffer carries its content size
//!     in the 2-byte prefix
//!
//! Consumes verified/src/lib.rs via the #[path] mount; nothing from
//! the src zone is re-copied.

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod tpm;

use tpm::buf::{TpmBuf, TPM_HEADER_SIZE, TPM2B_HEADER_SIZE};
use tpm::cmd::pcr_read_payload;
use tpm::cursor::{be16_bytes, be32_bytes, Cursor};
use tpm::msg::{
    build_header, parse_response, ParseError, RC_SUCCESS, ST_NO_SESSIONS, ST_SESSIONS,
};
use tpm::types::TpmTag;

verus! {

/// be16/be32 emission decode back through the cursor (arbitrary word
/// inputs; the roundtrip obligation of the byte<->word bridge).
fn ut_cursor_word_roundtrip(w32: u32, w16: u16, b8: u8)
{
    let b32 = be32_bytes(w32);
    let b16 = be16_bytes(w16);
    let mut data = [0u8; 7];
    data[0] = b32[0];
    data[1] = b32[1];
    data[2] = b32[2];
    data[3] = b32[3];
    data[4] = b16[0];
    data[5] = b16[1];
    data[6] = b8;

    let mut c = Cursor::new();
    let p0 = c.pos();
    assert(p0 == 0);
    let v32 = c.read_be32(&data);
    assert(v32.is_Some());
    assert(v32 == Option::Some(w32));
    let v16 = c.read_be16(&data);
    assert(v16.is_Some());
    assert(v16 == Option::Some(w16));
    let v8 = c.read_u8(&data);
    assert(v8.is_Some());
    assert(v8 == Option::Some(b8));
    let p1 = c.pos();
    assert(p1 == 7);
    // exhausted cursor: every further read fails without advancing
    let e = c.is_exhausted(&data);
    assert(e);
    let n1 = c.read_u8(&data);
    assert(n1.is_None());
    let n2 = c.read_be16(&data);
    assert(n2.is_None());
    let n3 = c.read_be32(&data);
    assert(n3.is_None());
    let p2 = c.pos();
    assert(p2 == 7);
}

/// Failure-side position discipline and peer-controlled length
/// bounds: read_bytes gives inner slices on success, None without
/// advancing otherwise.
fn ut_cursor_none_faces(n_good: usize, n_bad: usize)
    requires
        n_good <= 5,
        n_bad > 5,
{
    let data = [0u8; 5];
    let mut c = Cursor::new();
    let s0 = c.read_bytes(&data, n_good);
    assert(s0.is_Some());
    let p1 = c.pos();
    assert(p1 == n_good);
    let t0 = c.read_bytes(&data, n_bad);
    assert(t0.is_None());
    let p2 = c.pos();
    assert(p2 == n_good);
    let u0 = c.read_bytes(&data, (5 - n_good) + 1);
    assert(u0.is_None());
    let p3 = c.pos();
    assert(p3 == n_good);
    // exact-fit skip then exhaustion
    let ok = c.skip(&data, 5 - n_good);
    assert(ok);
    let e = c.is_exhausted(&data);
    assert(e);
}

/// parse_response accepts exactly the header build_header emits for
/// a session-less success response and splits the payload tail. The
/// header's third slot is the ordinal in the request direction and
/// the return code in the response direction (the shared offset the
/// types.rs module doc warns about); the inverse pair meets at a
/// zero slot value (RC_SUCCESS).
fn ut_header_parse_inverse(bodies: [u8; 4])
{
    let hdr = build_header(ST_NO_SESSIONS, RC_SUCCESS, (10 + bodies.len()) as u32);
    let mut raw = [0u8; 14];
    raw[0] = hdr[0];
    raw[1] = hdr[1];
    raw[2] = hdr[2];
    raw[3] = hdr[3];
    raw[4] = hdr[4];
    raw[5] = hdr[5];
    raw[6] = hdr[6];
    raw[7] = hdr[7];
    raw[8] = hdr[8];
    raw[9] = hdr[9];
    raw[10] = bodies[0];
    raw[11] = bodies[1];
    raw[12] = bodies[2];
    raw[13] = bodies[3];
    let res = parse_response(&raw);
    assert(res.is_Ok());
    let resp = match res {
        Result::Ok(r) => r,
        Result::Err(_) => return,
    };
    let succ = resp.is_success();
    assert(resp.tag == ST_NO_SESSIONS);
    assert(resp.rc == RC_SUCCESS);
    assert(succ);
    assert(resp.body@.len() == 4);
    assert(resp.body@.index(0) == bodies[0]);
    assert(resp.body@.index(1) == bodies[1]);
    assert(resp.body@.index(2) == bodies[2]);
    assert(resp.body@.index(3) == bodies[3]);

    // rejection face: an incomplete header is Truncated, a size
    // field past the actual count is Malformed
    let short = [0u8; 9];
    let res_short = parse_response(&short);
    assert(res_short == Result::Err(ParseError::Truncated));

    let mut wrong = [0u8; 10];
    wrong[2] = 0u8;
    wrong[3] = 0u8;
    wrong[4] = 0u8;
    wrong[5] = 11u8;
    wrong[0] = ((ST_SESSIONS / 256) % 256) as u8;
    wrong[1] = (ST_SESSIONS % 256) as u8;
    let res_malformed = parse_response(&wrong);
    assert(res_malformed == Result::Err(ParseError::Malformed));
}

/// Tpm2b buffers carry the content size in the 2-byte prefix
/// (TPM2B_HEADER_SIZE excluded) right after construction and after
/// each append.
fn ut_tpmbuf_sized_wire(tag_bytes: [u8; 3])
{
    let mut buf = TpmBuf::<20>::new_sized();
    let k = buf.is_tpm2b();
    let l0 = buf.len();
    let w0 = buf.as_wire();
    assert(k);
    assert(l0 == TPM2B_HEADER_SIZE);
    assert(w0@.len() == 2);
    assert(w0@.index(0) == 0u8);
    assert(w0@.index(1) == 0u8);
    buf.append_u8(tag_bytes[0]);
    buf.append_u8(tag_bytes[1]);
    buf.append_u8(tag_bytes[2]);
    let ovf = buf.has_overflow();
    let l1 = buf.len();
    let w1 = buf.as_wire();
    assert(!ovf);
    assert(l1 == 5);
    assert(w1@.len() == 5);
    assert(w1@.index(0) == 0u8);
    assert(w1@.index(1) == 3u8);
    assert(w1@.index(2) == tag_bytes[0]);
}

/// Sticky-overflow sequence across the 18-byte boundary of a
/// Command buffer built by new_command (header is 10 bytes; 8 bytes
/// of room follow). On the ninth appended byte the sticky flag
/// springs, length freezes, and later appends write nothing.
fn ut_tpmbuf_sticky_overflow(bytes: [u8; 9])
{
    let mut buf = TpmBuf::<18>::new_command(TpmTag::Tpm2NoSessions, 0x0143u32);
    let l0 = buf.len();
    let ov0 = buf.has_overflow();
    let h0 = buf.handle_count();
    assert(l0 == TPM_HEADER_SIZE);
    assert(!ov0);
    assert(h0 == 0);

    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            buf.length == TPM_HEADER_SIZE + i,
            !buf.overflow,
            buf.kind == tpm::buf::BufKind::Command,
            buf.handles == 0,
            !buf.boundary_error,
            tpm::buf::wire_consistent(buf),
        decreases
            8 - i,
    {
        buf.append_u8(bytes[i]);
        i += 1;
    }
    let l_edge = buf.len();
    let ov_edge = buf.has_overflow();
    assert(l_edge == 18);
    assert(!ov_edge);

    // the last in-capacity wire snapshot (as_wire requires the no
    // overflow precondition, per its doc face)
    let w_edge = buf.as_wire();
    let ghost frozen = w_edge@.len();
    assert(frozen == 18);

    // the capacity edge: this one overflows and the flag sticks
    buf.append_u8(bytes[8]);
    let ov1 = buf.has_overflow();
    let l1 = buf.len();
    assert(ov1);
    assert(l1 == 18);
    let ghost data_edge = buf.data@;

    // sticky: further appends change no byte and clear no flag
    buf.append_u8(0xFF);
    let ov2 = buf.has_overflow();
    let l2 = buf.len();
    assert(ov2);
    assert(l2 == 18);
    assert(buf.data@ == data_edge);

    // boundary_error is an independent flag: it does not spring from
    // an overflow
    let be = buf.has_boundary_error();
    assert(!be);
}

/// The header layout new_command writes: tag/ordinal bytes land at
/// their fixed offsets and the command-tag code of TpmTag matches.
fn ut_tpmbuf_command_header(ordinal: u32)
{
    let buf = TpmBuf::<24>::new_command(TpmTag::Tpm2Sessions, ordinal);
    let l0 = buf.len();
    let k0 = buf.is_tpm2b();
    let w0 = buf.as_wire();
    assert(l0 == 10);
    assert(!(k0));
    assert(w0@.len() == 10);
    assert(w0@.index(0) == 0x80);
    assert(w0@.index(1) == 0x02);
    // wire size field: 10 as big-endian u32
    assert(w0@.index(2) == 0);
    assert(w0@.index(3) == 0);
    assert(w0@.index(4) == 0);
    assert(w0@.index(5) == 10);
    // allocation zeroes the tail beyond the header
    assert(buf.data@.index(10) == 0);
}

// The pcr-index domain is 0..24 (PLATFORM_PCR); the selection
// face (single-selection below 24) is proven on the src side, and the
// wrap onto byte 2 for pcr_idx >= 24 is recorded as the out/ ledger
// suspects row. One concrete wrap consolidated here as an exec
// observation: the 24-bit-index payload lands its mask in byte 2,
// not beyond the 3-byte bitmap (the upstream bit_value ladder maps
// pcr_idx % 8 only).
fn ut_pcr_bitmap_is_3_bytes(pcr_idx: u32)
{
    let sel = pcr_read_payload(0x000Bu16, pcr_idx);
    assert(sel@.len() == 10);
    assert(sel@.index(6) == 3u8); // sizeofSelect = 3 regardless of index
}

fn main() {}

} // verus!
