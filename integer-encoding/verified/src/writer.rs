//! verified/src/writer.rs -- the per-function mirror of the upstream
//! code/src/writer.rs (a KVerus migrate artifact)
//!
//! Mirror and relaxation ledger:
//! 1. `impl<Inner: Write> VarIntWriter for Inner` (writer.rs:37-45) and the async
//!    variant depend on the std::io::Write trait; mirrored as the byte-level
//!    model of a 10-byte fixed buffer + encode_var_u64 (write_all semantics =
//!    the whole buffer segment written out), returning the number of bytes
//!    written (used). The IO boundary itself is recorded as blocked / out of
//!    scope.
//! 2. `impl<W: Write> FixedIntWriter for W` (writer.rs:69-77): a [0u8;8] stack
//!    buffer + encode_fixed -- upstream puts no >8-byte constraint on the FI
//!    size (a potential panic face: a custom FixedInt impl wider than 8 bytes
//!    panics with an out-of-bounds slice at buf[..size_of::<FI>()]; the witness
//!    of this obligation chain is in harness/coverage_props.rs).
//!
//! The upstream tree is untouched; this file is the verified/ side copy.

use super::fixed::*;
use super::varint::*;
use vstd::prelude::*;

verus! {

/// Origin: writer.rs:38-44 write_varint: 10-byte buffer + encode_var + write_all
/// Upstream doc (writer.rs:12-13):
///   A trait for writing integers in [`VarInt`] encoding to any [`Write`] type. This packs encoding and
///   writing into one step.
/// (Provenance note: the VarIntWriter trait header doc; the write_varint impl
///  method itself carries no upstream rustdoc.)
pub exec fn write_varint_bytes_u64(n: u64, dst: &mut [u8]) -> (r: usize)
    requires dst.len() >= req_space(n as int),
    ensures
        r as int == req_space(n as int),
{
    // Origin: let mut buf = [0_u8; 10]; let used = n.encode_var(&mut buf[..]);
    proof {
        // within the u64 domain req_space(n) <= 10 (a 10-byte buffer suffices)
        lemma_req_space_within_10(n);
    }
    let mut buf: [u8; 10] = [0; 10];
    let slice: &mut [u8] = &mut buf[0..10];
    let used = encode_var_u64(n, slice);
    proof {
        // the first `used` bytes of buf are exactly the varint encoding
        //   (established by encode_var_u64's ensures)
    }
    // Origin: self.write_all(&buf[0..used])?; Ok(used)
    let mut i: usize = 0;
    while i < used
        invariant
            i <= used,
            used <= 10,
            dst.len() >= used,
        decreases used - i
    {
        dst[i] = buf[i];
        i += 1;
    }
    used
}

/// Origin: writer.rs:70-77 write_fixedint: 8-byte buffer + encode_fixed + write_all
/// Upstream doc (writer.rs:47-47):
///   A trait for writing integers without encoding (i.e. `FixedInt`) to any `Write` type.
/// (Provenance note: the FixedIntWriter trait header doc; the write_fixedint impl
///  method itself carries no upstream rustdoc.)
pub exec fn write_fixedint_bytes_u64(n: u64, dst: &mut [u8]) -> (r: usize)
    requires dst.len() >= 8,
    ensures
        r == 8,
        final(dst).len() == 8,
{
    let mut buf: [u8; 8] = [0; 8];
    let slice: &mut [u8] = &mut buf[0..8];
    let _o = encode_fixed_u64(n, slice);
    proof {
        // encode_fixed_u64 fills all 8 bytes when len == 8 (established by
        //   its ensures)
        assert(_o matches Some(_));
    }
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            dst.len() >= 8,
        decreases 8 - i
    {
        dst[i] = buf[i];
        i += 1;
    }
    8
}

} // verus!
