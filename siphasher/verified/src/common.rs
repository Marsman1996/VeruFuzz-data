//! verified/src/common.rs -- Verus-translated mirror of code/src/common.rs
//! (pin 2fcf2a7)
//!
//! This file holds the low-level building blocks shared by sip.rs / sip128.rs
//! (the compression round + the little-endian assembling).
//! Translation adaptations (auditability notes; none of them changes the
//! semantics; the semantic equivalence is cross-checked API by API
//! against the upstream pin tree by runtime re-verification drivers):
//!
//! - [Origin Rust: code/src/common.rs:2-22 `macro_rules! compress`]
//!   The compression-round macro becomes `compress_spec` (spec twin) and
//!   `compress_exec` (exec mirror),
//!   the two statement-by-statement isomorphic (wrapping_add /
//!   ((x<<k)|(x>>(64-k))) is rotate_left(k)).
//!   The macro's field-reference order (v0,v1,v2,v3) is passed as a tuple;
//!   the upstream State struct's SIMD field order
//!   (v0,v2,v1,v3) is kept in the same order in sip.rs / sip128.rs.
//! - [Origin Rust: code/src/common.rs:25-36 `macro_rules! load_int_le`]
//!   The unsafe `ptr::copy_nonoverlapping` becomes the byte-by-byte
//!   indexed little-endian assembling `load_u64_le`.
//! - [Origin Rust: code/src/common.rs:43-62 `u8to64_le`]
//!   The unsafe three-branch shape (4/2/1-byte strides) is semantically
//!   equal to "byte-by-byte bitwise-or";
//!   the exec mirror takes the flat 7-if assembling isomorphic to the
//!   spec twin (the upstream branch choice is a performance-only form),
//!   and `get_unchecked`/`load_int_le!` uniformly become index reads
//!   carrying preceding preconditions.
//!   The value-level contract is blocked by an encoding limitation;
//!   the L0 contract is intact.

use vstd::prelude::*;

verus! {

/* ============================================================
 * Little-endian assembling -- the spec twins (flat or-shaped form;
 * constant inputs resolve term by term on the ground)
 * ============================================================ */

/// 8-byte little-endian assembling (the semantics of `load_int_le!(buf, i, u64)`)
pub open spec fn spec_load_u64(seq: Seq<u8>, i: int) -> u64 {
    let b0 = seq[i] as u64;
    let b1 = seq[i + 1] as u64;
    let b2 = seq[i + 2] as u64;
    let b3 = seq[i + 3] as u64;
    let b4 = seq[i + 4] as u64;
    let b5 = seq[i + 5] as u64;
    let b6 = seq[i + 6] as u64;
    let b7 = seq[i + 7] as u64;
    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
        | (b4 << 32) | (b5 << 40) | (b6 << 48) | (b7 << 56)
}

/// Little-endian assembling of len (< 8) bytes (the semantics of `u8to64_le`).
/// Uses the accumulator shape isomorphic to the exec mirror (position k
/// participates iff k < len),
/// making the exec<->spec bridge a flat congruence; the property "the
/// participating bits are the k < len ones" is consumed on the
/// harness side as ground assertions (bit_vector).
pub open spec fn spec_u8to64_le(seq: Seq<u8>, start: int, len: int) -> u64 {
    let s0 = if 0 < len { seq[start + 0] as u64 } else { 0u64 };
    let s1 = if 1 < len { s0 | ((seq[start + 1] as u64) << 8) } else { s0 };
    let s2 = if 2 < len { s1 | ((seq[start + 2] as u64) << 16) } else { s1 };
    let s3 = if 3 < len { s2 | ((seq[start + 3] as u64) << 24) } else { s2 };
    let s4 = if 4 < len { s3 | ((seq[start + 4] as u64) << 32) } else { s3 };
    let s5 = if 5 < len { s4 | ((seq[start + 5] as u64) << 40) } else { s4 };
    let s6 = if 6 < len { s5 | ((seq[start + 6] as u64) << 48) } else { s5 };
    s6
}

/* ============================================================
 * Compression round -- the spec twin + exec mirror of `macro_rules! compress`
 *
 * Statement-by-statement semantics (s = (v0,v1,v2,v3)):
 *   a0 = v0 [+] v1;  a1 = rotl13(v1) ^ a0;  a2 = rotl32(a0)
 *   b0 = v2 [+] v3;  b1 = rotl16(v3) ^ b0
 *   c0 = a2 [+] b1;  c1 = rotl21(b1) ^ c0
 *   d0 = b0 [+] a1;  d1 = rotl17(a1) ^ d0;  d2 = rotl32(d0)
 *   final = (c0, d1, d2, c1)         ([+] = wrapping_add)
 * ============================================================ */

pub open spec fn compress_spec(s: (u64, u64, u64, u64)) -> (u64, u64, u64, u64) {
    let (v0, v1, v2, v3) = s;
    let a0 = v0.wrapping_add(v1);
    let a1 = ((v1 << 13) | (v1 >> 51)) ^ a0;
    let a2 = (a0 << 32) | (a0 >> 32);
    let b0 = v2.wrapping_add(v3);
    let b1 = ((v3 << 16) | (v3 >> 48)) ^ b0;
    let c0 = a2.wrapping_add(b1);
    let c1 = ((b1 << 21) | (b1 >> 43)) ^ c0;
    let d0 = b0.wrapping_add(a1);
    let d1 = ((a1 << 17) | (a1 >> 47)) ^ d0;
    let d2 = (d0 << 32) | (d0 >> 32);
    (c0, d1, d2, c1)
}

/// Exec mirror: statement-by-statement isomorphic to compress_spec
/// (the bridge is a flat congruence)
/// Upstream doc (common.rs:1-1):
///   Compression round for SipHash algorithm.
pub exec fn compress_exec(s: (u64, u64, u64, u64)) -> (r: (u64, u64, u64, u64))
    ensures r == compress_spec(s)
{
    let (v0, v1, v2, v3) = s;
    let a0 = v0.wrapping_add(v1);
    let a1 = ((v1 << 13) | (v1 >> 51)) ^ a0;
    let a2 = (a0 << 32) | (a0 >> 32);
    let b0 = v2.wrapping_add(v3);
    let b1 = ((v3 << 16) | (v3 >> 48)) ^ b0;
    let c0 = a2.wrapping_add(b1);
    let c1 = ((b1 << 21) | (b1 >> 43)) ^ c0;
    let d0 = b0.wrapping_add(a1);
    let d1 = ((a1 << 17) | (a1 >> 47)) ^ d0;
    let d2 = (d0 << 32) | (d0 >> 32);
    (c0, d1, d2, c1)
}

/* ============================================================
 * exec assembling functions (index-based, unsafe removed)
 * ============================================================ */

/// [Origin Rust: load_int_le!(buf, i, u64)]
/// Upstream doc (common.rs:24-24):
///   Loads an integer of the desired type from a byte stream, in LE order.
pub exec fn load_u64_le(buf: &[u8], i: usize) -> (r: u64)
    requires i + 8 <= buf.len()
    ensures r == spec_load_u64(buf@, i as int)
{
    let b0 = buf[i] as u64;
    let b1 = buf[i + 1] as u64;
    let b2 = buf[i + 2] as u64;
    let b3 = buf[i + 3] as u64;
    let b4 = buf[i + 4] as u64;
    let b5 = buf[i + 5] as u64;
    let b6 = buf[i + 6] as u64;
    let b7 = buf[i + 7] as u64;
    b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
        | (b4 << 32) | (b5 << 40) | (b6 << 48) | (b7 << 56)
}

/// [Origin Rust: u8to64_le(buf, start, len)]
///
/// Contract note (blocked):
/// The value-level ensures (r == spec_u8to64_le(...)) is not provable
/// under the default encoding --
/// the per-bit accumulation behind the if(len k) gates needs the bv
/// algebra, and the bv channel rejects Seq-index terms
/// (probe-measured: `bit_vector` rejects Seq::index; the default encoding
/// cannot fold an or-of-ite).
/// Therefore this translation keeps only the L0 contract
/// (out-of-bounds panic-free). The ground verification of the slice
/// value-level
/// semantics is carried by the harness-side scalarized paths + the
/// runtime re-verification (API-by-API comparison against upstream).
/// Upstream doc (common.rs:38-42):
///   Loads a u64 using up to 7 bytes of a byte slice.
///   # Safety
///   The caller must ensure that `start + len <= buf.len()` and `len < 8`.
pub exec fn u8to64_le_exec(buf: &[u8], start: usize, len: usize) -> (r: u64)
    requires
        start + len <= buf.len(),
        len < 8,
{
    let mut out = 0u64;
    if 0 < len {
        out = out | (buf[start] as u64);
    }
    if 1 < len {
        out = out | ((buf[start + 1] as u64) << 8);
    }
    if 2 < len {
        out = out | ((buf[start + 2] as u64) << 16);
    }
    if 3 < len {
        out = out | ((buf[start + 3] as u64) << 24);
    }
    if 4 < len {
        out = out | ((buf[start + 4] as u64) << 32);
    }
    if 5 < len {
        out = out | ((buf[start + 5] as u64) << 40);
    }
    if 6 < len {
        out = out | ((buf[start + 6] as u64) << 48);
    }
    out
}

} // verus!

fn main() {}
