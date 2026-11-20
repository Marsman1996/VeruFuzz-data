//! tpm-core 0.1.4 response header validation and split (src/msg.rs) --
//! Verus translation.
//!
//! The doc contract of parse_response (msg.rs:42-47, quoted at the fn)
//! is re-erected as the exact error-kind discriminating poststate: the
//! three rejection classes and the success split are stated as
//! iff-faces over the wire fields.

use vstd::prelude::*;

verus! {

use super::cursor::{be16_bytes, be16_bytes_spec, be32_bytes, be32_bytes_spec, Cursor};

pub(crate) const TPM_HEADER_LEN: usize = 10;
/// Origin Rust: /// Response tag without sessions.
/// pub(crate) const ST_NO_SESSIONS: u16 = 0x8001; (src/msg.rs:4-5)
pub(crate) const ST_NO_SESSIONS: u16 = 0x8001;
/// Origin Rust: /// Response tag with sessions (authorization area).
/// pub const ST_SESSIONS: u16 = 0x8002; (src/msg.rs:6-7)
pub const ST_SESSIONS: u16 = 0x8002;
/// Origin Rust: /// Success return code.
/// pub const RC_SUCCESS: u32 = 0x0000; (src/msg.rs:8-9)
pub const RC_SUCCESS: u32 = 0x0000;

/// Origin Rust: #[derive(PartialEq, Eq)]
/// pub enum ParseError { Truncated, Malformed, Capacity, Unsupported, TpmError(u32) }
/// (src/msg.rs:10-23; the PartialEq/Eq derives have no Verus twin --
/// variant equality is structural in spec mode and no exec code in
/// this tree compares ParseError values by ==; per-variant doc lines:
/// Truncated "Not enough bytes to read the next field.", Malformed
/// "Length field does not match the actual byte count, or a field
/// value exceeds the specification.", Capacity "Count exceeds the
/// static capacity limit of this implementation.", Unsupported
/// "The syntax is valid but this implementation does not support it
/// (unknown algorithm, unexpected response shape).", TpmError "TPM
/// reported a non-zero return code.")
pub enum ParseError {
    Truncated,
    Malformed,
    Capacity,
    Unsupported,
    TpmError(u32),
}

/// Origin Rust: /// Abstract view of a message header. `code` is the command code in request
/// direction and the return code in response direction.
/// pub struct HeaderView { pub tag: u16, pub size: u32, pub code: u32 } (src/msg.rs:24-30)
pub struct HeaderView {
    pub tag: u16,
    pub size: u32,
    pub code: u32,
}

/// Origin Rust: /// A validated response: the three header fields plus the payload without the header.
/// pub struct Response<'a> { pub tag: u16, pub rc: u32, pub body: &'a [u8] } (src/msg.rs:31-36)
pub struct Response<'a> {
    pub tag: u16,
    pub rc: u32,
    pub body: &'a [u8],
}

impl<'a> Response<'a> {
    /// Origin Rust: pub fn is_success(&self) -> bool {
    ///     self.rc == RC_SUCCESS
    /// } (src/msg.rs:37-40)
    pub exec fn is_success(&self) -> (r: bool)
        ensures
            r == (self.rc == RC_SUCCESS),
    {
        self.rc == RC_SUCCESS
    }
}

// ------------------------------------------------------------------
// wire faces of the header fields
// ------------------------------------------------------------------

/// Tag field at wire offset 0 (guarded: the header faces only carry
/// meaning once the header prefix exists).
pub(crate) open spec fn resp_wire_tag(raw: &[u8]) -> u16 {
    if (2 as int) <= (raw.len() as int) {
        ((raw@[0] as int) * 256 + (raw@[1] as int)) as u16
    } else {
        0u16
    }
}

/// Size field at wire offset 2.
pub(crate) open spec fn resp_wire_size(raw: &[u8]) -> int {
    if (6 as int) <= (raw.len() as int) {
        16777216 * (raw@[2] as int)
            + 65536 * (raw@[3] as int)
            + 256 * (raw@[4] as int)
            + (raw@[5] as int)
    } else {
        0
    }
}

/// Return-code (or ordinal) field at wire offset 6.
pub(crate) open spec fn resp_wire_rc(raw: &[u8]) -> int {
    if (10 as int) <= (raw.len() as int) {
        16777216 * (raw@[6] as int)
            + 65536 * (raw@[7] as int)
            + 256 * (raw@[8] as int)
            + (raw@[9] as int)
    } else {
        0
    }
}

/// The two valid response tags.
pub(crate) open spec fn resp_tag_ok(raw: &[u8]) -> bool {
    resp_wire_tag(raw) == ST_NO_SESSIONS || resp_wire_tag(raw) == ST_SESSIONS
}

/// Origin Rust: /// Validate and split a response.
/// ///
/// /// Rejects three kinds of input: length shorter than a header, `size` not matching the actual byte
/// /// count, and a tag that is not one of the two valid response tags. If the return code is non-zero,
/// the payload is no longer parsed -- the payload contents of a failure response are undefined by the
/// specification.
/// pub(crate) fn parse_response(raw: &[u8]) -> Result<Response<'_>, ParseError> (src/msg.rs:42-67;
/// upstream doc glyphs converted ASCII; the ok_or + ? chains are
/// lowered to match arms of the same None/Some semantics)
pub(crate) exec fn parse_response(raw: &[u8]) -> (r: Result<Response, ParseError>)
    ensures
        match r {
            Result::Ok(resp) =>
                (raw.len() as int) >= (TPM_HEADER_LEN as int)
                    && resp_wire_size(raw) == (raw.len() as int)
                    && resp_tag_ok(raw)
                    && resp.rc == RC_SUCCESS
                    && resp.tag == resp_wire_tag(raw)
                    && resp.body@ == raw@.subrange(
                        TPM_HEADER_LEN as int,
                        raw.len() as int,
                    ),
            Result::Err(ParseError::Truncated) =>
                (raw.len() as int) < (TPM_HEADER_LEN as int),
            Result::Err(ParseError::Malformed) =>
                (raw.len() as int) >= (TPM_HEADER_LEN as int)
                    && (resp_wire_size(raw) != (raw.len() as int)
                        || !resp_tag_ok(raw)),
            Result::Err(ParseError::TpmError(c)) =>
                (raw.len() as int) >= (TPM_HEADER_LEN as int)
                    && resp_wire_size(raw) == (raw.len() as int)
                    && resp_tag_ok(raw)
                    && c != RC_SUCCESS
                    && c as int == resp_wire_rc(raw),
            Result::Err(ParseError::Capacity) => false,
            Result::Err(ParseError::Unsupported) => false,
        },
{
    if raw.len() < TPM_HEADER_LEN {
        return Err(ParseError::Truncated);
    }
    let mut c = Cursor::new();
    let tag = match c.read_be16(raw) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    let size = match c.read_be32(raw) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    let rc = match c.read_be32(raw) {
        Option::Some(v) => v,
        Option::None => return Err(ParseError::Truncated),
    };
    if size as usize != raw.len() {
        return Err(ParseError::Malformed);
    }
    if tag != ST_NO_SESSIONS && tag != ST_SESSIONS {
        return Err(ParseError::Malformed);
    }
    if rc != RC_SUCCESS {
        return Err(ParseError::TpmError(rc));
    }
    let body = &raw[TPM_HEADER_LEN..raw.len()];
    proof {
        assert(body@ == raw@.subrange(TPM_HEADER_LEN as int, raw.len() as int));
    }
    Ok(Response { tag, rc, body })
}

/// Origin Rust: /// Byte layout of the request header. The command payload is constructed by the `cmd`
/// module, and the two are concatenated to form the full request.
/// ///
/// /// `size` must be filled in after the payload length is known, so this module only provides a pure
/// function that generates the header from a total length; the buffer layer calls it at the end.
/// pub(crate) fn build_header(tag: u16, code: u32, total_size: u32) -> [u8; 10] (src/msg.rs:68-78)
pub(crate) exec fn build_header(tag: u16, code: u32, total_size: u32) -> (r: [u8; 10])
    ensures
        r@ == be16_bytes_spec(tag)
            .add(be32_bytes_spec(total_size))
            .add(be32_bytes_spec(code)),
{
    let t = be16_bytes(tag);
    let s = be32_bytes(total_size);
    let c = be32_bytes(code);
    [t[0], t[1], s[0], s[1], s[2], s[3], c[0], c[1], c[2], c[3]]
}

} // verus!
