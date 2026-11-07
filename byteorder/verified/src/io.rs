//! byteorder 1.5.0 (pin 5a82625) x Verus 0.2026.10.29 -- mirror of the upstream `src/io.rs`
//! (aggregated mirror of the former per-API fragment files).
//!
//! Mirror-attribution convention: the `ReadBytesExt`/`WriteBytesExt` methods
//! of the upstream io.rs are aggregated here as verbatim transcriptions, in
//! the upstream method order (read_u64 :321 -> read_uint :427 -> read_int
//! :452 -> read_uint128 :460 -> write_uint :1442); the obligations of the
//! upstream lib.rs `ByteOrder::read_uint/read_uint128` (the lib.rs:1914/1923
//! asserts) stay in this file as **caller-forwarded obligations** (the two
//! transcriptions order_read_uint / order_read_uint128); the
//! `ByteOrder::write_uint` obligations (the F3 target lib.rs:1952), the
//! pack_size block, and the f3 witness block are attributed to
//! verified/src/lib.rs -- this file's io-layer write_uint carries that
//! cross-file callee via an external_body forward
//! (order_write_uint_io_forward; the io layer supplies its own 8-byte
//! buffer, so the call site passes all obligations).
//!
//! Expected error set of this file (aggregate tally, `--multiple-errors 100`):
//! 6 failing functions / 10 error reports after dedup
//! (the two new slices of io_read_i128_upstream, i.e. the read_int128 shape of
//! F5; the write-side wrappers io_write_int / io_write_uint128 /
//! io_write_int128 are all 0 error):
//!   - API#1 `read_uint` / API#2 `read_int` (F5, io.rs:427-431 / 452-456): the
//!     lib.rs:1914 assert transcription of order_read_uint (hit after an
//!     nbytes==0 empty read via the forward call; the two fragments each held
//!     one copy, merged and deduped into one), plus, for each of
//!     io_read_uint_upstream / io_read_int_upstream, the `&mut buf[..nbytes]`
//!     slice and the forwarded-argument second slice (the four sites
//!     io.rs:429/430 and 454/455; nbytes > 8 => the `nbytes <= buf.len()`
//!     premise unsatisfied);
//!   - API#3 `read_uint128` (F5, io.rs:460-464): the lib.rs:1923 assert
//!     transcription of order_read_uint128 (nbytes==0) + the two slices of
//!     io_read_u128_upstream (io.rs:462/463, nbytes > 16);
//!   - API#5 `read_u64` (control group, io.rs:321-325) and API#4 `write_uint`
//!     on the io layer (io.rs:1442-1450): **0 error** (no nbytes parameter /
//!     self-supplied buffer; no panic reachable under the doc premises).
//! Pass criteria: the errors are exactly the sites above; fixed (bounds check
//! via Err) / control (legal domain) / everything else verified.
//!
//! Model A std semantic assumption: the read error channel belongs wholly to
//! the reader and the write error channel to the writer (external_body total
//! functions, `# Errors` contracts abstracted); the harness failure face is
//! only the nbytes-related sites.
//!
//! Runtime double evidence: out/verus-bugfinder/run-f5-*.rs (run after swapping
//! main via `verus --no-verify --compile`; the panics match the upstream PoC
//! measurements verbatim).

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_small_mod, lemma_mod_bound};
use vstd::arithmetic::mul::{lemma_mul_strict_inequality_converse, lemma_mul_inequality, lemma_mul_is_commutative};

verus! {

// ===========================================================================
// A1: abstraction of std::io::Read::read_exact
// `# Errors: This method returns the same errors as Read::read_exact` =>
// the error semantics belong to the reader, unrelated to this finding; modeled as an external-body total function (no checking face).
#[verifier::external_body]
pub exec fn read_exact_model(buf: &mut [u8]) -> (r: Result<(), ()>)
    ensures
        true,
{
    Ok(()) // body not verified; semantics per the `# Errors` contract
}

// ===========================================================================
// A2: abstraction of std::io::Write::write_all
// ===========================================================================
// `# Errors: same as Write::write_all` => the error channel belongs to the writer, external_body.
#[verifier::external_body]
pub exec fn write_all_model(buf: &[u8]) -> (r: Result<(), ()>)
    ensures
        true,
{
    Ok(()) // body not verified; semantics per the `# Errors` contract
}

// ===========================================================================
// API#5 (control group): ReadBytesExt::read_u64
// lib.rs:1902-1904 (BigEndian::read_u64) x io.rs:321-325 (ReadBytesExt::read_u64)
// ===========================================================================

// ---------- spec: big-endian value of the first k bytes ----------
pub open spec fn be_val_k(seq: Seq<u8>, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        256 * be_val_k(seq, (k - 1) as nat) + seq[k - 1] as int
    }
}

// ---------- spec: powers of two (recursive, computable via compute_only) ----------
pub open spec fn pw2(e: nat) -> int
    decreases e,
{
    if e == 0 { 1 } else { 2 * pw2((e - 1) as nat) }
}


// ---------- L0: lib.rs:1902-1904 (BigEndian::read_u64) transcription ----------
/// Origin Rust (lib.rs:1902-1904):
/// `fn read_u64(buf: &[u8]) -> u64 { u64::from_be_bytes(buf[..8].try_into().unwrap()) }`
/// -- the slice obligation of `buf[..8]` (8 <= buf.len()) is carried by
/// requires (consistent with the trait doc `# Panics: buf.len() < 8`); the
/// `try_into` array conversion is unsupported, rewritten as the equivalent
/// byte-wise accumulation (v = 256*v + buf[i]); the value semantics are
/// anchored at `be_val_k(buf@, 8)`.
/// (The obligation of lib.rs:1902-1904 is attributed to verified/src/lib.rs,
/// but its F5 control-group obligations all pass with no failure site; it
/// stays in this file in the fragment-original (caller-counterpart) form.)
/// Upstream doc (lib.rs:244-248):
///   Reads an unsigned 64 bit integer from `buf`.
///   # Panics
///   Panics when `buf.len() < 8`.
pub exec fn order_read_u64(buf: &[u8]) -> (r: u64)
    requires
        buf.len() == 8,
    ensures
        r as int == be_val_k(buf@, 8),
{
    let mut v: u64 = 0;
    let mut i: usize = 0;
    while i < buf.len()
        invariant
            0 <= i <= buf.len(),
            buf.len() == 8,
            v as int == be_val_k(buf@, i as nat),
        decreases buf.len() - i,
    {
        // overflow domain: v < 256^i <= 256^7 < 2^64; the new round's v' < 256^(i+1) <= 2^64
        proof {
            lemma_be_val_bound(buf@, i as nat);
            lemma_pw2_shift8((8 * i) as nat);
            assert((v as int) < pw2((8 * i) as nat));
            assert(((256 * (v as int)) + (buf@[i as int] as int)) < pw2((8 * (i as nat + 1)) as nat));
            assert(buf.len() == 8);
            assert((i as int) + 1 <= buf.len() as int);
            assert((i as int) + 1 <= 8);
            assert((8 * ((i as int) + 1)) <= 64);
            lemma_pw2_monotone((8 * (i as nat + 1)) as nat, 64);
            assert(pw2((8 * (i as nat + 1)) as nat) <= pw2(64));
            assert(pw2(64) == 18446744073709551616) by (compute_only);
            assert(((256 * (v as int)) + (buf@[i as int] as int)) <= 18446744073709551615);
        }
        v = 256 * v + buf[i] as u64;
        i += 1;
    }
    v
}

// ---------- L0: io.rs:321-325 (ReadBytesExt::read_u64) verbatim transcription ----------
/// No nbytes parameter: the only obligation face is the fixed 8-byte slice;
/// inside the legal domain **everything should pass** (0 error expected --
/// also a ReadBytesExt member, read_u64 has no panic reachable under the doc
/// premises; the F5 control-group shape).
/// Upstream doc (io.rs:301-305):
///   Reads an unsigned 64 bit integer from the underlying reader.
///   # Errors
///   This method returns the same errors as [`Read::read_exact`].
pub exec fn io_read_u64_upstream() -> (r: Result<u64, ()>) {
    let mut buf = [0u8; 8];                // io.rs:322 (buf is [u8; 8])
    read_exact_model(&mut buf)?;           // io.rs:323 -- the slice is the whole buffer, always satisfied
    Ok(order_read_u64(&buf))               // io.rs:324 -> lib.rs:1902
}

// ===========================================================================
// API#1: ReadBytesExt::read_uint (the main F5 site)
// transcription of the callee `ByteOrder::read_uint` (BigEndian, lib.rs:1912-1918)
// ===========================================================================

// ---------- L0: lib.rs:1912-1918 (BigEndian::read_uint) verbatim transcription ----------
/// Transcription of `ByteOrder::read_uint` (BigEndian as the representative;
/// of lib.rs:1913-1917 only the assert line is relevant to this finding --
/// the byte reassembly of 1913/1915-1917 is afterwards replaced by a sentinel
/// value, which does not affect the control-flow site).
/// The trait doc (lib.rs:282-300) **does** declare that assert -- the lower
/// layer is Documented while
/// the upper io forward declares nothing; that is exactly the "io-layer absence
/// of the documented contract" shape of F5. By the mirror-attribution
/// convention, that lib.rs:1914 obligation already appears in the io
/// transcription as a caller (forwarded) obligation, so it stays in this file.
/// Upstream doc (lib.rs:282-287):
///   Reads an unsigned n-bytes integer from `buf`.
///   # Panics
///   Panics when `nbytes < 1` or `nbytes > 8` or
///   `buf.len() < nbytes`
pub exec fn order_read_uint(nbytes: usize, buf: &[u8]) -> (r: u64)
    ensures
        true,
{
    // Origin Rust (lib.rs:1914): assert!(1 <= nbytes && nbytes <= out.len() && nbytes <= buf.len());
    // (out is the [0; 8] of lib.rs:1913; out.len() == 8)
    assert!(1 <= nbytes && nbytes <= 8 && nbytes <= buf.len()); // <-- EXPECTED (F5)
    // ...lib.rs:1915-1917 start/copy_from_slice/from_be_bytes (unrelated to F5, omitted)
    0
}

// ---------- L0: io.rs:427-431 (ReadBytesExt::read_uint) verbatim transcription ----------
/// Only `# Errors`: **no `# Panics`, no precondition on nbytes at all**.
/// Hence the `requires` of this transcription is empty (copied from the doc),
/// letting the obligations land truthfully on the slice and assert
/// transcription lines.
///
/// Expected error set (the io.rs:429 slice / the io.rs:430 second
/// forwarded-argument slice; the forward lib.rs:1914 assert is at
/// order_read_uint above):
///   1. the `assert!` of `order_read_uint` -- the lib.rs:1914 transcription
///      (after an nbytes==0 io-side empty read, the forward call hits it);
///   2. the `&mut buf[..nbytes]` of `io_read_uint_upstream` -- the io.rs:429
///      transcription (nbytes > 8 => the `nbytes <= buf.len()` premise
///      unsatisfied);
///   3. the io.rs:430 transcription second slice (at the forwarded call
///      argument; nbytes==0/9 the same as before).
/// Pass criteria: the errors are exactly the sites above; fixed (bounds check
/// via Err) / control (nbytes==4 / legal domain) / witness all verified.
///
/// Runtime double evidence: after swapping main for `io_read_uint_upstream(9)`
/// and running `verus --no-verify --compile`, the panic matches the upstream
/// PoC measurement verbatim:
/// `range end index 9 out of range for slice of length 8` (see the Actual
/// results table of out/issue-report.md).
/// Upstream doc (io.rs:408-412):
///   Reads an unsigned n-bytes integer from the underlying reader.
///   # Errors
///   This method returns the same errors as [`Read::read_exact`].
pub exec fn io_read_uint_upstream(nbytes: usize) -> (r: Result<u64, ()>) {
    let mut buf = [0u8; 8];                      // io.rs:428 (buf is [u8; 8])
    read_exact_model(&mut buf[..nbytes])?;       // io.rs:429 <-- EXPECTED: slice range precondition (nbytes > 8)
    Ok(order_read_uint(nbytes, &buf[..nbytes]))  // io.rs:430 -> the lib.rs:1914 assert (hit after an nbytes == 0 empty read)
}

// ---------- repair counter-proof (Fix Code: bounds check via the error channel) ----------
/// The Fix Code shape suggested by the issue draft: `nbytes == 0 || nbytes > 8`
/// returns an `io::Error` (modeled as Err); everything else verbatim as
/// upstream -- after that, all obligations pass (inside the legal domain both
/// the slice and the assert are satisfiable), the return type is unchanged, no
/// API breakage.
pub exec fn io_read_uint_fixed(nbytes: usize) -> (r: Result<u64, ()>) {
    if nbytes == 0 || nbytes > 8 {               // FIX: bounds check
        return Err(());
    }
    let mut buf = [0u8; 8];
    read_exact_model(&mut buf[..nbytes])?;
    Ok(order_read_uint(nbytes, &buf[..nbytes]))
}

// ---------- control: legal input nbytes == 4 ----------
/// PoC control group: the legal domain `1 <= nbytes <= 8`; every layer's obligations are all satisfiable.
pub exec fn io_read_uint_control(nbytes: usize) -> (r: Result<u64, ()>)
    requires
        1 <= nbytes,
        nbytes <= 8,
{
    let mut buf = [0u8; 8];
    read_exact_model(&mut buf[..nbytes])?;
    Ok(order_read_uint(nbytes, &buf[..nbytes]))
}


// ===========================================================================
// API#2: ReadBytesExt::read_int (F5 site 2)
// callee chain `ByteOrder::read_int` (lib.rs:630-633, the default implementation =
// extend_sign(read_uint); extend_sign is the out-of-scope helper of lib.rs:88-91)
// and `ByteOrder::read_uint` (BigEndian, lib.rs:1912-1918 -- its transcription is
// the order_read_uint of API#1 above, reused)
// ===========================================================================

// ---------- out-of-scope helper: extend_sign (lib.rs:88-91) ----------
// `fn extend_sign(val: u64, nbytes: usize) -> i64 { let shift = (8 - nbytes)*8;
//  (val << shift) as i64 >> shift }` -- the sign extension of read_int, unrelated
// to the F5 site (F5 is only about the bounds of nbytes); modeled as an
// external body (the obligation is neither shouldered nor hidden by it).
#[verifier::external_body]
pub exec fn extend_sign_model(val: u64, nbytes: usize) -> (r: i64)
    ensures
        true,
{
    val as i64 // body not verified; sign extension semantics of lib.rs:88-91
}

// ---------- L0: lib.rs:630-633 (ByteOrder::read_int default implementation) transcription ----------
/// lib.rs:631-633 (VERBATIM structure):
/// `fn read_int(buf: &[u8], nbytes: usize) -> i64 { extend_sign(Self::read_uint(buf, nbytes), nbytes) }`
/// The trait doc (lib.rs:612-629) declares that assert -- a Documented lower
/// layer + an Undocumented io upper layer.
/// Upstream doc (lib.rs:612-617):
///   Reads a signed n-bytes integer from `buf`.
///   # Panics
///   Panics when `nbytes < 1` or `nbytes > 8` or
///   `buf.len() < nbytes`
pub exec fn order_read_int(nbytes: usize, buf: &[u8]) -> (r: i64)
    ensures
        true,
{
    let ext = order_read_uint(nbytes, buf); // lib.rs:632 <-> the lib.rs:1914 assert (hit after an nbytes == 0 empty read)
    extend_sign_model(ext, nbytes)          // lib.rs:632 extend_sign (out-of-scope helper)
}

// ---------- L0: io.rs:452-456 (ReadBytesExt::read_int) verbatim transcription ----------
/// Same as read_uint: only `# Errors`, no `# Panics`, no nbytes
/// precondition => requires is empty (copied from the doc).
///
/// Expected error set: same shape as read_uint -- the lib.rs:1914 assert
/// transcription of order_read_uint (hit via the io.rs:455 forward) + the
/// two io.rs:454/455 slices. fixed / control / witness
/// all verified.
/// Upstream doc (io.rs:433-437):
///   Reads a signed n-bytes integer from the underlying reader.
///   # Errors
///   This method returns the same errors as [`Read::read_exact`].
pub exec fn io_read_int_upstream(nbytes: usize) -> (r: Result<i64, ()>) {
    let mut buf = [0u8; 8];                     // io.rs:453 (buf is [u8; 8])
    read_exact_model(&mut buf[..nbytes])?;      // io.rs:454 <-- EXPECTED: slice range precondition (nbytes > 8)
    Ok(order_read_int(nbytes, &buf[..nbytes]))  // io.rs:455 -> lib.rs:631 -> lib.rs:1914
}

// ---------- repair counter-proof (Fix Code: io-layer bounds check -> Err) ----------
pub exec fn io_read_int_fixed(nbytes: usize) -> (r: Result<i64, ()>) {
    if nbytes == 0 || nbytes > 8 {              // FIX: bounds check
        return Err(());
    }
    let mut buf = [0u8; 8];
    read_exact_model(&mut buf[..nbytes])?;
    Ok(order_read_int(nbytes, &buf[..nbytes]))
}

// ---------- control: legal input (e.g. nbytes == 3, the io.rs:443-450 doc example) ----------
pub exec fn io_read_int_control(nbytes: usize) -> (r: Result<i64, ()>)
    requires
        1 <= nbytes,
        nbytes <= 8,
{
    let mut buf = [0u8; 8];
    read_exact_model(&mut buf[..nbytes])?;
    Ok(order_read_int(nbytes, &buf[..nbytes]))
}


// ===========================================================================
// API#3: ReadBytesExt::read_uint128 (the F5 128-bit shape)
// transcription of the callee `ByteOrder::read_uint128` (BigEndian, lib.rs:1921-1927)
// ===========================================================================

// ---------- L0: lib.rs:1921-1927 (BigEndian::read_uint128) verbatim transcription ----------
/// The io layer (io.rs:458-459, whole doc two lines) **lacks even `# Errors`**,
/// let alone `# Panics` / an nbytes precondition (the io-layer doc is quoted
/// at io_read_u128_upstream below); the trait doc (lib.rs:302-320) declares
/// the assert.
/// Upstream doc (lib.rs:302-307):
///   Reads an unsigned n-bytes integer from `buf`.
///   # Panics
///   Panics when `nbytes < 1` or `nbytes > 16` or
///   `buf.len() < nbytes`
pub exec fn order_read_uint128(nbytes: usize, buf: &[u8]) -> (r: u128)
    ensures
        true,
{
    // Origin Rust (lib.rs:1923): assert!(1 <= nbytes && nbytes <= out.len() && nbytes <= buf.len());
    // (out is the [0; 16] of lib.rs:1922; out.len() == 16)
    assert!(1 <= nbytes && nbytes <= 16 && nbytes <= buf.len()); // <-- EXPECTED (F5)
    // ...lib.rs:1924-1926 byte reassembly (unrelated to F5, omitted)
    0
}

// ---------- L0: io.rs:460-464 (ReadBytesExt::read_uint128) verbatim transcription ----------
/// Expected error set: the lib.rs:1923 assert transcription (nbytes==0) + the
/// io.rs:462 slice, the io.rs:463 forward slice (same order as read_uint:
/// first the slices (gs 462/463), then the assert); fixed / control / witness
/// all verified.
/// The corresponding measured PoC shape: nbytes == 17 -> `range end index 17 out
/// of range for slice of length 16` (io.rs:462:33); nbytes == 0 -> the same
/// assert as lib.rs:1914 (the 128-bit version of read_uint128, lib.rs:1923).
/// Upstream doc (io.rs:458-458):
///   Reads an unsigned n-bytes integer from the underlying reader.
pub exec fn io_read_u128_upstream(nbytes: usize) -> (r: Result<u128, ()>) {
    let mut buf = [0u8; 16];                      // io.rs:461 (buf is [u8; 16])
    read_exact_model(&mut buf[..nbytes])?;        // io.rs:462 <-- EXPECTED: slice range precondition (nbytes > 16)
    Ok(order_read_uint128(nbytes, &buf[..nbytes])) // io.rs:463 -> the lib.rs:1923 assert (hit after an nbytes == 0 empty read)
}

// ---------- repair counter-proof (Fix Code: io-layer bounds check -> Err) ----------
pub exec fn io_read_u128_fixed(nbytes: usize) -> (r: Result<u128, ()>) {
    if nbytes == 0 || nbytes > 16 {               // FIX: bounds check (128-bit domain)
        return Err(());
    }
    let mut buf = [0u8; 16];
    read_exact_model(&mut buf[..nbytes])?;
    Ok(order_read_uint128(nbytes, &buf[..nbytes]))
}

// ---------- control: legal input (1 <= nbytes <= 16) ----------
pub exec fn io_read_u128_control(nbytes: usize) -> (r: Result<u128, ()>)
    requires
        1 <= nbytes,
        nbytes <= 16,
{
    let mut buf = [0u8; 16];
    read_exact_model(&mut buf[..nbytes])?;
    Ok(order_read_uint128(nbytes, &buf[..nbytes]))
}


// ===========================================================================
// API#4 (io layer): WriteBytesExt::write_uint (the F3 counterpart -- the I/O layer supplies its own buffer)
// The documented panic conditions (io.rs:1416-1440, quoted at
// io_write_uint_upstream below) are only "n not representable in nbytes"
// and "nbytes > 8". The third assertion of its cross-file callee
// `ByteOrder::write_uint` (lib.rs:1950-1961) -- `nbytes <= buf.len()`
// (lib.rs:1952, written into no trait/io doc -- the doc-gap shape of F3) --
// is by obligation attribution moved to verified/src/lib.rs (together with
// the pack_size block and the f3 witness).
// ===========================================================================

// ---------- spec: the mathematical equivalent of pack_size (for the io-layer
// doc-premise transcription; the spec+exec pair at the lib.rs definition site
// is in verified/src/lib.rs; this is the io-layer cross-file copy, one per
// single-file driver closure -- not a conflict) ----------
/// Mathematical equivalent: packSize(n) = the least k with n < 256^k (when
/// n >= 0; check: n < 256 => the high 56 bits of (n|1) are zero => lz>>3 >= 7
/// => r <= 1 while r >= 1).
/// (Origin Rust lib.rs:112-114 `8 - ((n|1).leading_zeros() >> 3)`)
pub open spec fn pack_size_spec(n: int) -> int
    decreases n,
{
    if n <= 0 {
        1
    } else if n < 256 {
        1
    } else {
        1 + pack_size_spec(n / 256)
    }
}

// ---------- cross-file callee forward: ByteOrder::write_uint (lib.rs:1950-1961) ----------
/// The full verbatim transcription (order_write_uint, with the obligations of
/// the lib.rs:1951/1952 assertions and the F3 counterexample witness block) is
/// located in verified/src/lib.rs. The requires set matches the documented
/// requires of the lib.rs-side order_write_uint item by item (the two # Panics
/// conditions); the lib.rs:1952 `nbytes <= buf.len()` gap obligation is not
/// absorbed here (the io-layer buf is [0;8], so that condition is always
/// provable at the io call site).
#[verifier::external_body]
/// Upstream doc (lib.rs:440-445):
///   Writes an unsigned integer `n` to `buf` using only `nbytes`.
///   # Panics
///   If `n` is not representable in `nbytes`, or if `nbytes` is `> 8`, then
///   this method panics.
pub exec fn order_write_uint_io_forward(n: u64, nbytes: usize, buf: &mut [u8])
    requires
        1 <= nbytes,
        nbytes <= 8,                             // doc: "If nbytes > 8, this method panics"
        pack_size_spec(n as int) <= nbytes as int, // doc: "n not representable in nbytes => panics"
        nbytes <= buf.len(),                     // the io layer supplies [0;8], always provable (not the doc-gap side)
    ensures
        true,
{
    // body not verified; callee transcription (lib.rs:1950-1961) resides in
    // verified/src/lib.rs::order_write_uint
}

// ---------- L0: io.rs:1442-1450 (WriteBytesExt::write_uint) verbatim transcription ----------
/// The io layer supplies its own [0;8] buffer; all obligations pass under the
/// doc premises (the I/O layer has no gap -- the F3 gap sits only in the
/// direct short-buffer call on the ByteOrder layer; the evidence and
/// counterexample are in order_write_uint / f3_witness_short_buf of
/// verified/src/lib.rs). requires copies the first two conditions of the
/// io.rs:1424-1427 `# Panics` + the self-supplied-buffer fact.
/// Upstream doc (io.rs:1416-1427):
///   Writes an unsigned n-bytes integer to the underlying writer.
///   # Errors
///   This method returns the same errors as [`Write::write_all`].
///   # Panics
///   If the given integer is not representable in the given number of bytes,
///   this method panics. If `nbytes > 8`, this method panics.
pub exec fn io_write_uint_upstream(n: u64, nbytes: usize) -> (r: Result<(), ()>)
    requires
        1 <= nbytes,
        nbytes <= 8,
        pack_size_spec(n as int) <= nbytes as int, // the first two conditions of the io.rs:1424-1427 # Panics
{
    let mut buf = [0u8; 8];              // io.rs:1447 (buf is [u8; 8])
    order_write_uint_io_forward(n, nbytes, &mut buf); // io.rs:1448 -- buf.len()==8 => the callee premises are provable
    write_all_model(&buf[0..nbytes])     // io.rs:1449 -- nbytes <= 8 => the slice obligation is satisfied
}

// ===========================================================================
// Difference batch (2026-11-03) section 4: the ReadBytesExt/WriteBytesExt
// wrapper-layer difference set. This section adds: read_int128 (io.rs:468-473,
// the int128 shape of F5 -- completing the full obligation anchors of
// read_{uint,int,uint128,int128}), the write-side io wrappers (write_int
// io.rs:1478-1493 / write_uint128 io.rs:1493-1501 / write_int128
// io.rs:1508-1516), and the fixed-width read-wrapper representative read_u8.
// The cross-file helper copies (unextend_sign_spec / unextend_sign_model /
// unextend_sign128_model / lemma_pack_size_bound) are the same text as the
// lib.rs side, one per single-file driver closure (the existing mirror
// convention, not a conflict).
// ===========================================================================

// ---------- spec/helper copy (same text as verified/src/lib.rs) ----------
pub open spec fn unextend_sign_spec(n: int, k: int) -> int
    recommends 1 <= k,
{
    n % pw2((8 * k) as nat)
}


/// lib.rs:100-103 transcription (external_body: out-of-scope helper; the semantic contract as on the lib.rs side)
#[verifier::external_body]
pub exec fn unextend_sign_model(n: i64, nbytes: usize) -> (r: u64)
    requires
        1 <= nbytes,
        nbytes <= 8,
    ensures
        r as int == unextend_sign_spec(n as int, nbytes as int),
{
    0 // body not verified; Origin Rust (lib.rs:100-103)
}

/// lib.rs:106-109 transcription (unextend_sign128; as above)
#[verifier::external_body]
pub exec fn unextend_sign128_model(n: i128, nbytes: usize) -> (r: u128)
    requires
        1 <= nbytes,
        nbytes <= 16,
    ensures
        r as int == unextend_sign_spec(n as int, nbytes as int),
{
    0 // body not verified; Origin Rust (lib.rs:106-109)
}

/// Out-of-scope helper (lib.rs:166-169): extend_sign128 -- the same modeling
/// convention as the existing extend_sign_model (io.rs side); it shoulders no
/// error/sign-semantics obligation.
#[verifier::external_body]
pub exec fn extend_sign128_model(val: u128, nbytes: usize) -> (r: i128)
    ensures
        true,
{
    val as i128 // body not verified; sign extension semantics of lib.rs:106-109
}

// ===========================================================================
// API#6: ReadBytesExt::read_int128 (F5 shape 4, io.rs:468-473)
// callee `ByteOrder::read_int128` (the default implementation lib.rs:654-656 =
// extend_sign128(Self::read_uint128(buf, nbytes), nbytes) -> the lib.rs:1923
// assert; the read_uint128 transcription is the API#3 order_read_uint128
// above, reused)
// Contract declaration (io.rs:467, the whole doc one line): "Reads a signed
// n-bytes integer from the underlying reader." -- it lacks even # Errors =>
// requires is empty (copied from the doc).
// Expected error set: the io.rs:471 slice + the io.rs:472 forward slice
// (nbytes==0/17 same shape as read_uint128); fixed/control 0 error.
// ===========================================================================

// ---------- L0: lib.rs:654-656 (read_int128 default implementation) transcription ----------
/// Upstream doc (lib.rs:635-640):
///   Reads a signed n-bytes integer from `buf`.
///   # Panics
///   Panics when `nbytes < 1` or `nbytes > 16` or
///   `buf.len() < nbytes`
pub exec fn order_read_int128(nbytes: usize, buf: &[u8]) -> (r: i128)
    ensures
        true,
{
    let ext = order_read_uint128(nbytes, buf); // lib.rs:655 <-> the lib.rs:1923 assert
    extend_sign128_model(ext, nbytes)          // lib.rs:655 extend_sign128 (out-of-scope helper)
}

// ---------- L0: io.rs:468-473 (ReadBytesExt::read_int128) verbatim transcription ----------
/// Upstream doc (io.rs:466-466):
///   Reads a signed n-bytes integer from the underlying reader.
pub exec fn io_read_i128_upstream(nbytes: usize) -> (r: Result<i128, ()>) {
    let mut buf = [0u8; 16];                      // io.rs:469 (buf is [u8; 16])
    read_exact_model(&mut buf[..nbytes])?;        // io.rs:470 <-- EXPECTED: slice range precondition (nbytes > 16)
    Ok(order_read_int128(nbytes, &buf[..nbytes])) // io.rs:471 -> lib.rs:655 -> the lib.rs:1923 assert (hit after an nbytes == 0 empty read)
}

// ---------- repair counter-proof (Fix Code: bounds check -> Err, 128-bit domain) ----------
pub exec fn io_read_i128_fixed(nbytes: usize) -> (r: Result<i128, ()>) {
    if nbytes == 0 || nbytes > 16 {               // FIX: bounds check (128-bit domain, same origin as the shape #229 suggests)
        return Err(());
    }
    let mut buf = [0u8; 16];
    read_exact_model(&mut buf[..nbytes])?;
    Ok(order_read_int128(nbytes, &buf[..nbytes]))
}

// ---------- control: legal input (1 <= nbytes <= 16) ----------
pub exec fn io_read_i128_control(nbytes: usize) -> (r: Result<i128, ()>)
    requires
        1 <= nbytes,
        nbytes <= 16,
{
    let mut buf = [0u8; 16];
    read_exact_model(&mut buf[..nbytes])?;
    Ok(order_read_int128(nbytes, &buf[..nbytes]))
}


// ===========================================================================
// API#7: WriteBytesExt::write_int (io.rs:1478-1485; corresponding to the known
// #205/#229; the io layer's same-text doc declares two # Panics conditions at
// io.rs:1455-1461)
// Implementation chain: T::write_int(&mut [0;8], n, nbytes) -> the trait
// default implementation (lib.rs:855-859) -> unextend_sign + write_uint -- the
// representability check is always true for the truncated value (dead check)
// => the doc-promised panic branch does not exist on the io layer either (the
// #205 re-verification, known, no separate case filed). Expected **0 error**.
// ===========================================================================
/// Upstream doc (io.rs:1452-1463):
///   Writes a signed n-bytes integer to the underlying writer.
///   # Errors
///   This method returns the same errors as [`Write::write_all`].
///   # Panics
///   If the given integer is not representable in the given number of bytes,
///   this method panics. If `nbytes > 8`, this method panics.
pub exec fn io_write_int_upstream(n: i64, nbytes: usize) -> (r: Result<(), ()>)
    requires
        1 <= nbytes,
        nbytes <= 8,   // doc (io.rs:1459-1460): the legal domain of "If nbytes > 8, this method panics"
{
    let mut buf = [0u8; 8];       // io.rs:1481 (buf is [u8; 8])
    // io.rs:1481: T::write_int(&mut buf, n, nbytes) -- the trait default-chain transcription:
    let v = unextend_sign_model(n, nbytes); // lib.rs:858 unextend_sign(n, nbytes)
    proof {
        lemma_pw2_pos((8 * nbytes) as nat);
        lemma_fundamental_div_mod(n as int, pw2((8 * nbytes) as nat));
        assert(v as int == (n as int) % pw2((8 * nbytes) as nat));
        assert(v as int >= 0);
        assert((v as int) < (pw2((8 * nbytes) as nat)));
        // the truncated value fits the same width => the doc-promised "unrepresentable => panic" branch does not exist
        lemma_pack_size_bound(v as int, nbytes as nat);
    }
    order_write_uint_io_forward(v, nbytes, &mut buf); // lib.rs:858 -> the write_uint legal domain
    write_all_model(&buf[0..nbytes])                 // io.rs:1482 -- nbytes <= 8 => the slice obligation is satisfied
}

// ===========================================================================
// API#8: WriteBytesExt::write_uint128 (io.rs:1493-1501) and
// write_int128 (io.rs:1508-1516)
// The doc of write_uint128 (io.rs:1490-1492) has the two conditions in the
// same shape as io_write_uint; the obligation anchor of its callee's
// lib.rs:1966 undocumented condition (the 128-bit F3 shape) is carried in
// src/lib.rs order_write_uint128; the io layer supplies its own [0;16]
// buffer, so the call site's obligations are all **0 error** (the same io
// counterpart shape as the 64-bit write_uint).
// The write_int128 doc (io.rs:1504-1506) is the same as write_int => the
// #205 re-verification (0 error).
// ===========================================================================
/// Upstream doc (io.rs:1488-1491):
///   Writes an unsigned n-bytes integer to the underlying writer.
///   If the given integer is not representable in the given number of bytes,
///   this method panics. If `nbytes > 16`, this method panics.
pub exec fn io_write_uint128_upstream(n: u128, nbytes: usize) -> (r: Result<(), ()>)
    requires
        1 <= nbytes,
        nbytes <= 16,
        pack_size_spec(n as int) <= nbytes as int, // the io.rs:1490-1492 # Panics conditions (pack_size128 and pack_size_spec are definition-layer equivalent)
{
    let mut buf = [0u8; 16];                          // io.rs:1496 (buf is [u8; 16])
    order_write_uint128_io_forward(n, nbytes, &mut buf); // io.rs:1497 -- buf.len()==16 => the callee premises are provable
    write_all_model(&buf[0..nbytes])                  // io.rs:1498 -- nbytes <= 16 => the slice obligation is satisfied
}

/// Cross-file callee forward: ByteOrder::write_uint128 (lib.rs:1964-1975;
/// its verbatim transcription and the lib.rs:1966 obligation anchor are in
/// verified/src/lib.rs).
#[verifier::external_body]
/// Upstream doc (lib.rs:460-465):
///   Writes an unsigned integer `n` to `buf` using only `nbytes`.
///   # Panics
///   If `n` is not representable in `nbytes`, or if `nbytes` is `> 16`, then
///   this method panics.
pub exec fn order_write_uint128_io_forward(n: u128, nbytes: usize, buf: &mut [u8])
    requires
        1 <= nbytes,
        nbytes <= 16,
        pack_size_spec(n as int) <= nbytes as int,
        nbytes <= buf.len(),   // the io layer supplies [0;16], always provable (not the doc-gap side)
    ensures
        true,
{
    // body not verified; callee transcription (lib.rs:1964-1975) resides in
    // verified/src/lib.rs::order_write_uint128
}

/// Upstream doc (io.rs:1503-1506):
///   Writes a signed n-bytes integer to the underlying writer.
///   If the given integer is not representable in the given number of bytes,
///   this method panics. If `nbytes > 16`, this method panics.
pub exec fn io_write_int128_upstream(n: i128, nbytes: usize) -> (r: Result<(), ()>)
    requires
        1 <= nbytes,
        nbytes <= 16,   // doc (io.rs:1504-1506): the legal domain of "If nbytes > 16, this method panics"
{
    let mut buf = [0u8; 16];                            // io.rs:1511 (buf is [u8; 16])
    // io.rs:1511: T::write_int128(&mut buf, n, nbytes) -- the trait default-chain transcription:
    let v = unextend_sign128_model(n, nbytes);          // lib.rs:879 unextend_sign128(n, nbytes)
    proof {
        lemma_pw2_pos((8 * nbytes) as nat);
        lemma_fundamental_div_mod(n as int, pw2((8 * nbytes) as nat));
        assert(v as int == (n as int) % pw2((8 * nbytes) as nat));
        assert(v as int >= 0);
        assert((v as int) < (pw2((8 * nbytes) as nat)));
        lemma_pack_size_bound(v as int, nbytes as nat);
    }
    order_write_uint128_io_forward(v, nbytes, &mut buf); // lib.rs:879 -> the write_uint128 legal domain
    write_all_model(&buf[0..nbytes])                    // io.rs:1512 -- the slice obligation is satisfied
}

// ===========================================================================
// API#9 (representative): ReadBytesExt::read_u8 (io.rs:55-58)
// The representative shape of the fixed-width no-nbytes wrappers (no T
// generic, a pure 1-byte read): the io.rs:52-53 doc carries only # Errors
// (same as read_exact) => all obligations **0 error** (the same shape as
// io_read_u64, the API#5 control group; the remaining fixed-width wrappers
// such as write_u8/read_u16 have isomorphic obligation faces; this section
// covers them with this representative + the runtime theorems, no per-item
// transcription).
// ===========================================================================
/// Upstream doc (io.rs:31-38):
///   Reads an unsigned 8 bit integer from the underlying reader.
///   Note that since this reads a single byte, no byte order conversions
///   are used. It is included for completeness.
///   # Errors
///   This method returns the same errors as [`Read::read_exact`].
pub exec fn io_read_u8_upstream() -> (r: Result<u8, ()>) {
    let mut buf = [0u8; 1];    // io.rs:56 (buf is [u8; 1])
    read_exact_model(&mut buf)?; // io.rs:57 -- the whole-buffer slice is always satisfied
    Ok(buf[0])                    // io.rs:58
}


// ===========================================================================
// Proof lemmas and reachability witnesses (power/value bounds, the pack_size
// dead-check lemma, and the F5 reachability witnesses; moved to the end of
// the file before the close of verus! so the exec implementations read
// directly -- only the order changed, signatures and contracts untouched)
// ===========================================================================
// ---------- power lemmas ----------
/// pw2(e+1) == 2 * pw2(e) (single-layer definitional unfold of pw2)
proof fn lemma_pw2_step(e: nat)
    ensures
        pw2((e + 1) as nat) == 2 * pw2(e),
{
    // definitional unfold of pw2 at e+1 (fuel 1)
}

/// pw2(e) >= 1 (induction)
proof fn lemma_pw2_pos(e: nat)
    ensures
        1 <= pw2(e),
    decreases e,
{
    if e == 0 {
        assert(pw2(0) == 1);
    } else {
        lemma_pw2_pos((e - 1) as nat);
        lemma_pw2_step((e - 1) as nat);
    }
}

/// pw2(m+8) == 256 * pw2(m)
proof fn lemma_pw2_shift8(m: nat)
    ensures
        pw2((m + 8) as nat) == 256 * pw2(m),
    decreases m,
{
    if m == 0 {
        assert(pw2(8) == 256) by (compute_only);
    } else {
        lemma_pw2_step((m + 7) as nat);
        lemma_pw2_shift8((m - 1) as nat);
        lemma_pw2_step((m - 1) as nat);
        assert(pw2((m + 8) as nat) == 2 * pw2((m + 7) as nat));
        assert(pw2((m + 7) as nat) == 256 * pw2((m - 1) as nat));
        assert(pw2(m) == 2 * pw2((m - 1) as nat));
        assert(2 * 256 * pw2((m - 1) as nat) == 256 * (2 * pw2((m - 1) as nat))) by (nonlinear_arith);
    }
}

/// pw2 monotone: e1 <= e2 => pw2(e1) <= pw2(e2)
proof fn lemma_pw2_monotone(e1: nat, e2: nat)
    requires
        e1 <= e2,
    ensures
        pw2(e1) <= pw2(e2),
    decreases e2 - e1,
{
    if e1 == e2 {
        assert(pw2(e1) == pw2(e1 as nat));
    } else {
        lemma_pw2_monotone(e1, (e2 - 1) as nat);
        lemma_pw2_step((e2 - 1) as nat);
        lemma_pw2_pos(e1);
    }
}

/// Big-endian value of the first k bytes < 256^k
proof fn lemma_be_val_bound(seq: Seq<u8>, k: nat)
    ensures
        be_val_k(seq, k) < pw2((8 * k) as nat),
    decreases k,
{
    if k == 0 {
        assert(be_val_k(seq, 0) == 0);
        assert(pw2(0) == 1);
    } else {
        lemma_be_val_bound(seq, (k - 1) as nat);
        lemma_pw2_pos((8 * (k - 1)) as nat);
        lemma_pw2_shift8((8 * (k - 1)) as nat);
        assert(256 * pw2((8 * (k - 1)) as nat) == pw2((8 * k) as nat));
        // be_val_k = 256*v + b, v < 256^(k-1), b <= 255
        assert((seq[k - 1] as int) <= 255);
        assert(((256 * be_val_k(seq, (k - 1) as nat)) + (seq[k - 1] as int))
            < ((256 * pw2((8 * (k - 1)) as nat)) + 256));
        // 256*x >= x+1 (x >= 1, linear)
        assert((256 * pw2((8 * (k - 1)) as nat)) >= (pw2((8 * (k - 1)) as nat) + 1));
        assert((pw2((8 * (k - 1)) as nat) + 1) <= pw2((8 * k) as nat));
    }
}

// ---------- reachability witness ----------
/// Both `nbytes == 9` (slice obligation false) and `nbytes == 0` (assert
/// obligation false) satisfy the (empty) doc premises and are genuinely
/// inputtable => an input on which the upstream obligation necessarily fails
/// exists. Consistent with the expectation.
proof fn f5_read_uint_reachability_witness() {
    assert(9 > 8);       // the io.rs:429 slice obligation is false (nbytes == 9)
    assert(!(1 <= 0));   // the lib.rs:1914 assert obligation is false (nbytes == 0)
}

// ---------- reachability witness ----------
proof fn f5_read_int_reachability_witness() {
    assert(9 > 8);       // the io.rs:454 slice obligation is false (nbytes == 9)
    assert(!(1 <= 0));   // the lib.rs:1914 assert obligation is false (nbytes == 0, hit via the io.rs:455 -> lib.rs:631 forward)
}

// ---------- reachability witness ----------
proof fn f5_read_u128_reachability_witness() {
    assert(17 > 16);     // the io.rs:462 slice obligation is false (nbytes == 17)
    assert(!(1 <= 0));   // the lib.rs:1923 assert obligation is false (nbytes == 0)
}

/// 0 <= v < 256^k => pack_size_spec(v) <= k (the dead-check lemma; the argument is the same as in lib.rs)
pub proof fn lemma_pack_size_bound(v: int, k: nat)
    requires
        1 <= k,
        0 <= v,
        v < pw2((8 * k) as nat),
    ensures
        1 <= pack_size_spec(v),
        pack_size_spec(v) <= k,
    decreases k,
{
    if k == 1 {
        assert(pw2(8) == 256) by (compute_only);
        assert(0 <= v);
        assert(v < 256);
        assert(pack_size_spec(v) == 1);
    } else {
        if v < 256 {
            assert(pack_size_spec(v) == 1);
            assert(1 <= k);
        } else {
            let q = v / 256;
            let r = v % 256;
            lemma_fundamental_div_mod(v, 256);
            assert(v == 256 * q + r);
            assert(0 <= r < 256);
            lemma_pw2_pos((8 * (k - 1)) as nat);
            lemma_pw2_shift8((8 * (k - 1)) as nat);
            assert(pw2((8 * k) as nat) == 256 * pw2((8 * (k - 1)) as nat));
            assert(256 * q <= v);
            assert(256 * q < 256 * pw2((8 * (k - 1)) as nat));
            lemma_mul_strict_inequality_converse(q, pw2((8 * (k - 1)) as nat), 256);
            assert(q < pw2((8 * (k - 1)) as nat));
            lemma_pack_size_bound(q, (k - 1) as nat);
            assert(pack_size_spec(v) == 1 + pack_size_spec(q));
            assert(1 + pack_size_spec(q) <= k);
        }
    }
}

// ---------- reachability witness ----------
proof fn f5_read_i128_reachability_witness() {
    assert(17 > 16);     // the io.rs:470 slice obligation is false (nbytes == 17)
    assert(!(1 <= 0));   // the lib.rs:1923 assert obligation is false (nbytes == 0, hit via the io.rs:471 -> lib.rs:655 forward)
}
}

fn main() {}
