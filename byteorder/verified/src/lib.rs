//! byteorder 1.5.0 (pin 5a82625) x Verus 0.2026.10.29 -- mirror of the upstream `src/lib.rs`
//! (library code proper: ByteOrder-layer value-semantics kernels and the F3
//! obligation anchors -- order_write_uint / pack_size / f3 witness; the
//! UT-property theorems live in verified/harness/ut_roundtrip.rs and
//! verified/harness/cov_generic_family.rs, which pull this file in via
//! `#[path="../src/lib.rs"] mod`; the single verification fact source is
//! this src file).
//!
//! Mirror-attribution convention: this file carries the F3 obligation body --
//! the `BigEndian::write_uint` transcription of lib.rs:1950-1961, including
//! the lib.rs:1952 assertion `nbytes <= buf.len()` that no doc declares --
//! via the full ByteOrder-layer transcription + the counterexample witness.
//! The lib.rs:1914/1923 obligations stay in src/io.rs as caller-forwarded
//! obligations, together with the io-layer write_uint call-site counterpart
//! (io_write_uint_upstream). pw2 / be_val_k / le_val_k and the power lemmas
//! are duplicated with src/io.rs (one copy per single-file driver closure,
//! not a conflict).
//!
//! Expected errors of this file under `--multiple-errors 100`: **2 errors** --
//!   - the lib.rs:1952 transcription line of `order_write_uint` (the doc
//!     premise set cannot prove `nbytes <= buf.len()`; the undocumented
//!     condition, the 64-bit shape of F3);
//!   - the lib.rs:1966 transcription line of `order_write_uint128` (the
//!     same-shape undocumented condition, the 128-bit shape of the F3
//!     family; the LE shape at lib.rs:2142 is same-shaped and not
//!     separately transcribed);
//!   - everything else fully verified (the UT roundtrip theorems live in
//!     harness/ and reference this file).
//!
//! Runtime re-verification of F3: out/verus-bugfinder/run-f3-write-uint.rs
//! (`order_write_uint(0, 1, &mut [])` panics with
//! `assertion failed: nbytes <= buf.len()`) and the pin-tree cargo PoC
//! out/verus-bugfinder/poc-f3/.
//!
//! Minimal visibility relaxation for the reference-style harness (semantics
//! unchanged, pub only): the power lemmas lemma_pw2_pos / lemma_pw2_monotone
//! / lemma_pw2_shift8 / lemma_be_val_bound / lemma_le_val_bound (for
//! ut_roundtrip.rs) and lemma_le_val_stable (for the slice-family theorems
//! of the harness cov_generic_family.rs) were
//! made pub; the other lemmas stay private.
//!
//! Transcription notes:
//! - the `ByteOrder::read_uint/write_uint` (BigEndian, lib.rs:1912-1918 /
//!   1950-1961) `from_be_bytes` / `copy_from_slice` / unsafe rewrites follow
//!   the exec-code-preservation rule as isomorphic byte-wise computations;
//!   the control-flow sites (the lib.rs:1914/1951/1952 assertions) carry the
//!   obligations: 1914 on the io side (caller-forwarded obligation form),
//!   1951/1952 in order_write_uint of this file;
//! - the write-side "n representable in nbytes" domain is `n < 256^k` (the
//!   equivalent domain of the lib.rs:112-114 pack_size), stated on the
//!   requires / the ensures of `pack_size_model`.

use vstd::prelude::*;
use vstd::seq::Seq;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_small_mod, lemma_mod_bound};
use vstd::arithmetic::mul::{lemma_mul_nonzero, lemma_mul_strict_inequality_converse, lemma_mul_inequality, lemma_mul_is_commutative};

verus! {

// ---------- spec: powers of two, and the big/little-endian value of the first k bytes ----------
pub open spec fn pw2(e: nat) -> int
    decreases e,
{
    if e == 0 { 1 } else { 2 * pw2((e - 1) as nat) }
}

/// Big-endian value of the first k bytes (buf[0] most significant)
pub open spec fn be_val_k(seq: Seq<u8>, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        256 * be_val_k(seq, (k - 1) as nat) + seq[k - 1] as int
    }
}

/// Little-endian value of the first k bytes (buf[0] least significant)
pub open spec fn le_val_k(seq: Seq<u8>, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        le_val_k(seq, (k - 1) as nat) + (seq[k - 1] as int) * pw2((8 * (k - 1)) as nat)
    }
}


// ===========================================================================
// F3 (obligation attributed to this file): the ByteOrder::write_uint section.
// The io-layer call-site counterpart of `WriteBytesExt::write_uint`
// (io.rs:1442-1450) is io_write_uint_upstream in verified/src/io.rs; this
// section is the complete transcription of that cross-file callee plus the
// counterexample.
// Contract declaration (rustdoc verbatim):
// - lib.rs:440-458 (trait layer) declares the two # Panics conditions;
//   io.rs:1416-1440 (I/O layer) declares the same two.
// -- the documented panic conditions are only "n not representable in nbytes"
// and "nbytes > 8"; the implementation's third assertion
// `nbytes <= buf.len()` (lib.rs:1952) is written into no trait/io doc (always
// true while a tool supplies its own buffer; triggered only when a user calls
// the trait layer directly with a short buffer) -- that is the doc-gap shape
// of F3.
// Expected results:
//   - io_write_uint_upstream (io layer, own [0;8] buffer, in src/io.rs):
//     under the doc premises **all obligations pass** (the I/O layer itself
//     lacks nothing; the gap sits only in the user buffer of the ByteOrder
//     layer);
//   - order_write_uint (trait-layer target site): requires copies the two
//     documented conditions verbatim; the obligation fails exactly at the
//     lib.rs:1952 transcription line (`nbytes <= buf.len()`);
//   - f3_witness_short_buf: the counterexample concretized -- n=0, nbytes=1,
//     buf.len()==0, every doc premise satisfied while lib.rs:1952 is false
//     (runtime re-verification: out/verus-bugfinder/run-f3-write-uint.rs).
// pack_size modeling: the mathematical equivalent of the lib.rs:112-114
// `8 - ((n|1).leading_zeros() >> 3)` is `pack_size_spec` = the least k with
// n < 256^k (recursive division by 256); the exec side is external_body with
// an ensures stating their equality (an out-of-scope helper, not a target
// site -- every F3 obligation stays on the lib.rs:1951/1952 transcription
// lines).
// ===========================================================================

// ---------- pack_size (lib.rs:112-114): spec + exec pair ----------
/// Mathematical equivalent: packSize(n) = the least k with n < 256^k (when
/// n >= 0; check: n < 256 => the high 56 bits of (n|1) are zero => lz>>3 >= 7
/// => r <= 1 while r >= 1). (The io-layer doc-premise transcription site in
/// src/io.rs holds another copy of this same spec -- one per single-file
/// driver closure, not a conflict.)
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

/// lib.rs:112-114 transcription (external_body: out-of-scope helper; the equivalence is stated by the ensures).
#[verifier::external_body]
pub exec fn pack_size_model(n: u64) -> (r: usize)
    ensures
        1 <= r,
        r <= 8,
        pack_size_spec(n as int) == r as int,
{
    1 // body not verified; Origin Rust: (8 - ((n|1).leading_zeros() >> 3)) as usize
}

// ---------- L0: lib.rs:1950-1961 (BigEndian::write_uint) verbatim transcription ----------
/// requires copies the two conditions of the trait doc (lib.rs:443-445).
/// Origin Rust (lib.rs:1950-1961) (LittleEndian has the same shape at
/// lib.rs:2130-2137; its lib.rs:2131 same-shape assertion is not separately
/// transcribed -- same-shape obligation, see the issue report).
/// Upstream doc (lib.rs:440-445):
///   Writes an unsigned integer `n` to `buf` using only `nbytes`.
///   # Panics
///   If `n` is not representable in `nbytes`, or if `nbytes` is `> 8`, then
///   this method panics.
pub exec fn order_write_uint(n: u64, nbytes: usize, buf: &mut [u8])
    requires
        1 <= nbytes,
        nbytes <= 8,                             // doc: "If nbytes > 8, this method panics"
        pack_size_spec(n as int) <= nbytes as int, // doc: "n not representable in nbytes => panics"
    // SPEC-DOC MISMATCH (BurntSushi/byteorder#230): the doc # Panics declare only
    // "n not representable in nbytes" / "nbytes > 8"; the doc-promised premise set
    // cannot prove the asserted `nbytes <= buf.len()` -- a precondition the doc omits.
    // Kept in the implementation-faithful form (the expected error is that assertion).
{
    let ps = pack_size_model(n); // the pack_size(n) call at the head of lib.rs:1951
    // Origin Rust (lib.rs:1951): assert!(pack_size(n) <= nbytes && nbytes <= 8);
    assert!(ps <= nbytes && nbytes <= 8);
    // Origin Rust (lib.rs:1952): assert!(nbytes <= buf.len());
    assert!(nbytes <= buf.len()); // <-- EXPECTED: not provable from the doc premises (undocumented condition)
    // ...lib.rs:1953-1960 unsafe pointer-side copy (unrelated to F3, omitted)
}

// ---------- counterexample concretization (F3 reachability + runtime re-verification entry) ----------
/// n = 0 (pack_size = 1), nbytes = 1, buf.len() == 0: every doc premise
/// satisfied, the lib.rs:1952 assertion (1 <= 0) is false. The proof-layer
/// fact is given inside the exec via a ghost assert.
pub exec fn f3_witness_short_buf(buf: &mut [u8])
    requires
        buf.len() == 0,
{
    assert(pack_size_spec(0int) == 1); // spec-computable by recursion: 0 < 256 => 1
    order_write_uint(0, 1, buf);       // doc premises satisfied; the lib.rs:1952 obligation fails
}


// ---------- L0: BigEndian::read_uint (lib.rs:1912-1918) value-semantics transcription ----------
/// Origin Rust (lib.rs:1912-1918):
/// `read_uint(buf, n)` = `u64::from_be_bytes` of `buf[..n]` (via a [0;8]
/// zero-padded right alignment). Rewritten as a forward byte-wise
/// accumulation (v = 256*v + buf[i]); the semantics are anchored at
/// `be_val_k(buf@, k)`. The assertion obligation of lib.rs:1914 (documented)
/// is carried by the caller-forwarded obligation form in src/io.rs; the
/// legal-domain requirement here appears as requires.
/// Upstream doc (lib.rs:282-287):
///   Reads an unsigned n-bytes integer from `buf`.
///   # Panics
///   Panics when `nbytes < 1` or `nbytes > 8` or
///   `buf.len() < nbytes`
pub exec fn order_read_uint_trans(buf: &[u8], k: usize) -> (r: u64)
    requires
        1 <= k,
        k <= buf.len(),
        k <= 8,
    ensures
        r as int == be_val_k(buf@, k as nat),
{
    let mut v: u64 = 0;
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            k <= buf.len() as int,
            k <= 8,
            buf@.len() == buf.len(),
            v as int == be_val_k(buf@, i as nat),
        decreases k - i,
    {
        proof {
            lemma_be_val_bound(buf@, i as nat);
            lemma_pw2_shift8((8 * i) as nat);
            assert((v as int) < pw2((8 * i) as nat));
            assert(((256 * (v as int)) + (buf@[i as int] as int)) < pw2((8 * ((i as int) + 1)) as nat));
            assert((i as int) + 1 <= k);
            assert((i as int) + 1 <= 8);
            assert((8 * ((i as int) + 1)) <= 64);
            lemma_pw2_monotone((8 * ((i as int) + 1)) as nat, 64);
            assert(pw2((8 * ((i as int) + 1)) as nat) <= pw2(64));
            assert(pw2(64) == 18446744073709551616) by (compute_only);
            assert(((256 * (v as int)) + (buf@[i as int] as int)) <= 18446744073709551615);
        }
        v = 256 * v + buf[i] as u64;
        i += 1;
    }
    v
}

// ---------- L0: BigEndian::write_uint (lib.rs:1950-1961) value-semantics transcription ----------
/// Origin Rust (lib.rs:1950-1961): copy the last nbytes bytes of the
/// big-endian 8-byte representation of n into buf[0..nbytes] (under the
/// domain n < 256^nbytes this is just "the k-byte big-endian representation").
/// Rewritten as forward digit extraction: the weight w starts at 256^(k-1)
/// and is divided by 256 each round; `b = m / w`, `m = m % w`. The
/// lib.rs:1951/1952 assertion obligations are carried by order_write_uint
/// above in this file (the legal domain here appears as requires: n < 256^k,
/// the equivalent domain of pack_size(n) <= k).
/// Upstream doc (lib.rs:440-445):
///   Writes an unsigned integer `n` to `buf` using only `nbytes`.
///   # Panics
///   If `n` is not representable in `nbytes`, or if `nbytes` is `> 8`, then
///   this method panics.
pub exec fn order_write_uint_trans(buf: &mut [u8], n: u64, k: usize)
    requires
        1 <= k,
        k <= buf.len(),
        k <= 8,
        (n as int) < pw2((8 * k) as nat),
    ensures
        be_val_k(final(buf)@, k as nat) == n as int,
{
    // Origin Rust (lib.rs:1951): assert!(pack_size(n) <= nbytes && nbytes <= 8);
    // (in-place assertion completed by the difference batch: always true under the
    // n < 256^k premise; the signed chain order_write_int_lib below proves "the
    // pack_size check is always true on the truncating chain")
    let ps = pack_size_model(n);
    proof {
        lemma_pack_size_bound(n as int, k as nat);
    }
    assert!(ps <= k && k <= 8);
    // Origin Rust (lib.rs:1952): assert!(nbytes <= buf.len());
    assert!(k <= buf.len());
    // prelude: machine weight w := 256^(k-1)
    let mut w: u64 = 1;
    let mut j: usize = 0;
    while j < k - 1
        invariant
            0 <= j <= k - 1,
            k <= 8,
            w as int == pw2((8 * j) as nat),
        decreases k - 1 - j,
    {
        proof {
            // overflow domain: entry j <= k-2 <= 6 => w = 256^j <= 256^6 => 256w <= 256^7 < 2^64
            assert(j as int <= k - 2);
            assert(j as int <= 6);
            lemma_pw2_monotone((8 * j) as nat, 48);
            assert((w as int) <= pw2(48));
            assert((256 * (w as int)) <= (256 * pw2(48)));
            lemma_pw2_shift8(48);
            assert(256 * pw2(48) == pw2(56));
            assert(pw2(56) == 72057594037927936) by (compute_only);
            assert((256 * (w as int)) < 18446744073709551616);
            // maintenance: w_new = 256*w == 256^(j+1) = pw2(8(j+1))
            lemma_pw2_shift8((8 * j) as nat);
            assert(pw2((8 * ((j as int) + 1)) as nat) == 256 * pw2((8 * j) as nat));
        }
        w = 256 * w;
        j += 1;
    }
    // main loop: forward write of the k big-endian bytes
    let mut m: u64 = n;
    let mut i: usize = 0;
    let ghost n_int = n as int;
    proof {
        // loop-entry invariant: m == n % 256^k (i.e. n itself), be_val_k(buf@,0) == n/256^k == 0
        assert(0 <= n_int);
        assert(n_int < pw2((8 * k) as nat));
        lemma_small_mod(n_int as nat, (pw2((8 * k) as nat)) as nat);
        assert(n_int % pw2((8 * k) as nat) == n_int);
        lemma_fundamental_div_mod(n_int, pw2((8 * k) as nat));
        assert(pw2((8 * k) as nat) != 0);
        assert(n_int == pw2((8 * k) as nat) * (n_int / pw2((8 * k) as nat)) + n_int);
        assert(pw2((8 * k) as nat) * (n_int / pw2((8 * k) as nat)) == 0);
        if n_int / pw2((8 * k) as nat) != 0 {
            lemma_mul_nonzero(pw2((8 * k) as nat), n_int / pw2((8 * k) as nat));
            assert(pw2((8 * k) as nat) * (n_int / pw2((8 * k) as nat)) != 0);
            assert(false);
        }
        assert(n_int / pw2((8 * k) as nat) == 0);
        assert(be_val_k(buf@, 0) == 0);
    }
    while i < k
        invariant
            0 <= i <= k,
            k <= buf.len() as int,
            k <= 8,
            buf@.len() == buf.len(),
            (i < k) ==> (w as int == pw2((8 * (k - i - 1)) as nat)),
            m as int == n_int % pw2((8 * (k - i)) as nat),
            be_val_k(buf@, i as nat) == n_int / pw2((8 * (k - i)) as nat),
        decreases k - i,
    {
        let ghost pre_w = w as int;
        let ghost pre_m = m as int;
        let ghost pre_seq = buf@;
        let ghost D = pw2((8 * (k - i)) as nat);
        let ghost q = n_int / D;
        let ghost b = pre_m / pre_w;
        let ghost s = pre_m % pre_w;
        proof {
            // D == 256*w (region width = 256 * positional weight)
            lemma_pw2_shift8((8 * (k - i - 1)) as nat);
            assert(D == 256 * pw2((8 * (k - i - 1)) as nat));
            assert(pw2((8 * (k - i - 1)) as nat) == pre_w);
            assert(D == 256 * pre_w);
            // w >= 1 (positive positional weight; nonzero machine-division denominator)
            lemma_pw2_pos((8 * (k - i - 1)) as nat);
            assert(1 <= pre_w);
            assert(w != 0);
            // Euclidean decomposition: pre_m == pre_w*b + s, 0 <= s < pre_w
            lemma_fundamental_div_mod(pre_m, pre_w);
            assert(pre_w != 0);
            assert(pre_m == pre_w * b + s);
            assert(0 <= s < pre_w);
            // m < D = 256*w => b = m/w < 256
            assert(pre_m < D);
            assert(D == 256 * pre_w);
            assert(pre_m < 256 * pre_w);
            assert(pre_w * b <= pre_m);
            assert(pre_w * b < 256 * pre_w);
            assert(b * pre_w < 256 * pre_w);
            assert(pre_w > 0);
            lemma_mul_strict_inequality_converse(b, 256, pre_w);
            assert(b < 256);
            // n = D*q + m = 256*w*q + (w*b + s) = w*(256*q + b) + s
            lemma_fundamental_div_mod(n_int, D);
            assert(D != 0);
            assert(n_int == D * q + pre_m);
            assert((256 * pre_w) * q == pre_w * (256 * q)) by (nonlinear_arith);
            assert(pre_w * (256 * q + b) == pre_w * (256 * q) + pre_w * b) by (nonlinear_arith);
            assert(n_int == pre_w * (256 * q + b) + s);
            // => (used at the exit invariant): n/w == 256q + b; n%w == s
            lemma_fundamental_div_mod_converse(n_int, pre_w, 256 * q + b, s);
            assert(n_int / pre_w == 256 * q + b);
            assert(n_int % pre_w == s);
        }
        let bm: u64 = m / w;
        assert(bm as int == b); // machine division == integer division (nonnegative domain)
        buf[i] = bm as u8;
        m = m % w;
        w = w / 256;
        i += 1;
        proof {
            // (1) new w: w == pre_w/256 == pw2(8(k-i-1)) (when i < k)
            if i < k {
                lemma_pw2_shift8((8 * (k - i - 1)) as nat);
                assert(pw2((8 * (k - i)) as nat) == 256 * pw2((8 * (k - i - 1)) as nat));
                assert(pre_w == pw2((8 * (k - i)) as nat));
                assert(pre_w == 256 * pw2((8 * (k - i - 1)) as nat));
                lemma_fundamental_div_mod_converse(pre_w, 256, pw2((8 * (k - i - 1)) as nat), 0);
                assert(w as int == pw2((8 * (k - i - 1)) as nat));
            }
            // (2) new m: m == pre_m % pre_w == s == n % pw2(8(k-i))
            assert(m as int == pre_m % pre_w);
            assert(pw2((8 * (k - i)) as nat) == pre_w);
            assert(m as int == n_int % pw2((8 * (k - i)) as nat));
            // (3) new be_val: the current buf@ == pre_seq.update(i-1, bm) (the write);
            //     the value of the prefix <= i-1 is unchanged
            assert(buf@ == pre_seq.update((i - 1) as int, bm as u8));
            lemma_be_val_stable(pre_seq, (i - 1) as int, bm as u8, (i - 1) as nat);
            assert(be_val_k(buf@, (i - 1) as nat) == be_val_k(pre_seq, (i - 1) as nat));
            lemma_be_val_step(buf@, (i - 1) as nat);
            assert(be_val_k(buf@, i as nat) == 256 * be_val_k(buf@, (i - 1) as nat) + buf@[(i - 1) as int] as int);
            assert(buf@[(i - 1) as int] as int == b);
            assert(be_val_k(buf@, i as nat) == 256 * q + b);
            assert(be_val_k(buf@, i as nat) == n_int / pre_w);
            assert(be_val_k(buf@, i as nat) == n_int / pw2((8 * (k - i)) as nat));
        }
    }
    proof {
        // exit: i == k => pw2(0) == 1, n/1 == n
        assert(pw2(0) == 1);
        assert(n_int / pw2(0) == n_int);
        assert((n_int / 1) == n_int) by (nonlinear_arith);
    }
}

// ===========================================================================
// Difference batch (2026-11-03) section 1: the ByteOrder::write_int signed
// write chain (upstream known: issue #205 + fix PR #229; this block is an
// independent obligation-layer re-verification, **no separate case filed**).
// Adds write_int/write_int128 (the lib.rs:849-859/872-880 default
// implementations, the unextend_sign truncation chain); the LE
// single-value / u128 / slice families are sections 2/3/4.
//
// Contract: the trait doc (lib.rs:836-841, quoted at order_write_int_lib
// below) and the io layer (io.rs:1455-1460) declare only the two # Panics
// conditions -- whereas the implementation is write_int = write_uint(unextend_sign(n,
// nbytes), nbytes): the representability check (pack_size) only ever sees
// the truncated value, so the assertion is always true => a dead check; an
// unrepresentable n is silently written truncated (high bits dropped, sign
// possibly flipped).
// Expected results: every exec transcription of this section is **0 error**
// (the w205 witness includes a doc-premise counterexample proof:
// !int_repr(100000, 2) while all obligations hold) -- the obligation-layer
// formal re-verification of "write_int never panics on out of range input"
// (the #205 title verbatim). (BigEndian as the representative shape;
// LittleEndian goes through the same default implementation, same shape,
// not separately transcribed.)
// Independent runtime evidence: out/poc/write-int-truncate/ (the upstream
// pin-tree true source, debug + release double profile).
// ===========================================================================

// ---------- spec: the signed k-byte doc semantic domain ----------
/// The doc-meaning signed k-byte representable domain (two's-complement range [-2^(8k-1), 2^(8k-1)))
pub open spec fn int_repr(n: int, k: int) -> bool
    recommends 1 <= k,
{
    -pw2(((8 * k) - 1) as nat) <= n && n < pw2(((8 * k) - 1) as nat)
}

/// The mathematical semantics of lib.rs:100-103 (unextend_sign): the low k
/// bytes of the i64 bit string = n mod 256^k (Euclidean modulus, the value
/// always in [0, 256^k))
pub open spec fn unextend_sign_spec(n: int, k: int) -> int
    recommends 1 <= k,
{
    n % pw2((8 * k) as nat)
}

/// lib.rs:100-103 transcription (external_body: out-of-scope helper; the
/// semantic contract is declared by the ensures; the semantics were also
/// independently measured by the upstream-true-source PoC --
/// `(val << shift) as u64 >> shift == val mod 256^nbytes`, shift = (8-nbytes)*8,
/// see out/poc/write-int-truncate/).
#[verifier::external_body]
pub exec fn unextend_sign_model(n: i64, nbytes: usize) -> (r: u64)
    requires
        1 <= nbytes,
        nbytes <= 8,
    ensures
        r as int == unextend_sign_spec(n as int, nbytes as int),
{
    0 // body not verified; Origin Rust (lib.rs:100-103):
      // let shift = (8 - nbytes) * 8; ((val << shift) as u64) >> shift
}


// ---------- L0: lib.rs:849-859 (ByteOrder::write_int default implementation) transcription ----------
/// requires copies the legal domain declared by the trait doc (the two
/// conditions of lib.rs:853-855) plus the target buffer; the representability
/// of n is **not in requires** -- the doc only promises a panic when
/// unrepresentable, which does not form a caller precondition.
/// Obligation chain: write_int -> unextend_sign (lib.rs:858) -> write_uint
/// (lib.rs:1950-1961; its in-place assertions are the lib.rs:1951/1952
/// transcription lines at the top of order_write_uint_trans).
/// Expected **0 error**: for every n, every doc-legal nbytes, every
/// nbytes <= buf.len() -- the lib.rs:1951 pack_size assertion is always
/// satisfied for the truncated value via lemma_pack_size_bound; i.e. the
/// "n not representable => panics" panic branch promised by the doc does
/// not exist in this implementation (n is silently written two's-complement
/// truncated).
/// Upstream doc (lib.rs:836-841):
///   Writes a signed integer `n` to `buf` using only `nbytes`.
///   # Panics
///   If `n` is not representable in `nbytes`, or if `nbytes` is `> 8`, then
///   this method panics.
pub exec fn order_write_int_lib(n: i64, nbytes: usize, buf: &mut [u8])
    requires
        1 <= nbytes,
        nbytes <= 8,   // doc: legal domain of "or if nbytes is > 8, this method panics"
        nbytes <= buf.len(),
    // SPEC-DOC MISMATCH (BurntSushi/byteorder#230): the `nbytes <= buf.len()`
    // precondition is not listed by the write_int # Panics; carried here as part of
    // the implementation-faithful requires.
    ensures
        be_val_k(final(buf)@, nbytes as nat) == unextend_sign_spec(n as int, nbytes as int),
{
    let v = unextend_sign_model(n, nbytes); // lib.rs:858 unextend_sign(n, nbytes)
    proof {
        // v@ = n % 256^nbytes lies in [0, 256^nbytes) (the Euclidean modulus bound via the div_mod lemmas)
        lemma_pw2_pos((8 * nbytes) as nat);
        lemma_fundamental_div_mod(n as int, pw2((8 * nbytes) as nat));
        assert(v as int == (n as int) % pw2((8 * nbytes) as nat));
        assert(v as int >= 0);
        assert((v as int) < (pw2((8 * nbytes) as nat)));
        // => pack_size_spec(v@) <= nbytes (the truncated value fits the same width = dead check)
        lemma_pack_size_bound(v as int, nbytes as nat);
    }
    order_write_uint_trans(buf, v, nbytes) // lib.rs:858 -> lib.rs:1950-1961
}

// ---------- counterexample / positive-obligation concretization (#205 shape; upstream known, #205/#229) ----------
/// Doc-premise counterexample instance: n = 100000, nbytes = 2,
/// buf.len() == 2 -- 100000 >= 32768 = 2^15 => !int_repr(100000, 2)
/// (doc-meaning unrepresentable; per the doc it should panic); while on the
/// implementation side every obligation holds (0 error), silently writing
/// the two's-complement truncation 100000 mod 65536 = 34464 = 0x86A0 (be
/// semantics); read_uint reads back 34464, extend_sign (read_int semantics)
/// folds it to 34464 - 65536 = **-31072** (sign flip). Runtime double
/// evidence (upstream true source, debug + release): out/poc/write-int-truncate/.
pub exec fn w205_witness_silent_trunc(buf: &mut [u8])
    requires
        buf.len() == 2,
{
    proof {
        assert(pw2(15) == 32768) by (compute_only);
        assert(100000 >= 32768);
        assert(!int_repr(100000, 2)); // doc premise: n unrepresentable => the doc promises a panic
    }
    order_write_int_lib(100000, 2, buf); // implementation side: no panic-obligation failure (0 error)
    proof {
        assert(pw2(16) == 65536) by (compute_only);
        assert(unextend_sign_spec(100000, 2) == 100000int % 65536int);
        assert(100000int % 65536int == 34464);
        // write-side truncated value (callee ensures forwarded): buf now holds the truncated bytes, not 100000
        assert(be_val_k(buf@, 2 as nat) == 34464);
        // read_int read-back value (extend_sign(34464, 2) = 34464 - 2^16, the
        // lib.rs:88-91 constant-folded shape): sign flipped; the roundtrip hope of
        // n=100000 falls through
        assert(34464 - 65536 == -31072);
    }
}

// ===========================================================================
// Difference-batch section 2: the LittleEndian generic single-value
// read/write family (the lib.rs:2072-2147 implementation family) -- the LE
// generic in-value kernels:
//   - order_read_uint_le_trans: the value kernel of lib.rs:2094-2098
//     read_uint (LE, any 1<=k<=8) (= u64::from_le_bytes(buf[..k]), the
//     semantics anchored at le_val_k); the LE fixed-width family
//     read_u16/read_u32/read_u48/read_u64 (lib.rs:2074/2079/ the read_u48
//     default :240/2084) is exactly the k=2/4/6/8 special cases of this
//     kernel;
//   - order_write_uint_le_trans: the value kernel of lib.rs:2130-2137
//     write_uint (LE) + the in-place assertions (lib.rs:2131/2132, the same
//     F3 shape -- always true inside the legal domain); the LE fixed-width
//     family write_u16/write_u32/write_u48/write_u64 (lib.rs:2110/2115/
//     :398/2120) is exactly the k=2/4/6/8 special cases (write_f32/
//     write_f64 ride the same chain via to_bits).
// Accumulation direction: LE read = sum b_i*256^i (forward weight); the exec
// accumulation carries the width of the final round w = 256^8 = 2^64 in u128
// (a direct u64 accumulation would overflow);
// LE write = forward low-digit extraction (b = m % 256, m = m / 256), no
// overflow face.
// ===========================================================================


// ---------- L0: lib.rs:2094-2098 (LE read_uint) value kernel ----------
/// Upstream doc (lib.rs:282-287):
///   Reads an unsigned n-bytes integer from `buf`.
///   # Panics
///   Panics when `nbytes < 1` or `nbytes > 8` or
///   `buf.len() < nbytes`
pub exec fn order_read_uint_le_trans(buf: &[u8], k: usize) -> (r: u64)
    requires
        1 <= k,
        k <= buf.len(),
        k <= 8,
    ensures
        r as int == le_val_k(buf@, k as nat),
{
    let mut v: u128 = 0; // carrying width: the final round's v + b*256^7*256 term < 2^72 < 2^128
    let mut w: u128 = 1;
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            k <= buf.len() as int,
            k <= 8,
            buf@.len() == buf.len(),
            w as int == pw2((8 * i) as nat),
            v as int == le_val_k(buf@, i as nat),
        decreases k - i,
    {
        proof {
            lemma_le_val_bound(buf@, i as nat);
            lemma_pw2_pos((8 * i) as nat);
            // overflow domain: v = le_val (first i bytes) < 256^i <= 256^7; b <= 255;
            // v' = v + b*w < 256^i + 255*256^i = 256^(i+1) <= 256^8 < 2^64 <= 2^128
            lemma_pw2_shift8((8 * i) as nat);
            assert(pw2((8 * (i + 1)) as nat) == 256 * pw2((8 * i) as nat));
            lemma_mul_inequality(buf@[i as int] as int, 255, pw2((8 * i) as nat));
            assert((buf@[i as int] as int) * pw2((8 * i) as nat) <= 255 * pw2((8 * i) as nat));
            assert((v as int) < pw2((8 * i) as nat));
            assert((v as int) + (buf@[i as int] as int) * (w as int)
                < pw2((8 * i) as nat) + 255 * pw2((8 * i) as nat));
            assert(pw2((8 * i) as nat) + 255 * pw2((8 * i) as nat)
                == 256 * pw2((8 * i) as nat));
            assert((v as int) + (buf@[i as int] as int) * (w as int)
                < pw2((8 * (i + 1)) as nat));
            assert((v as int) + (buf@[i as int] as int) * (w as int)
                < pw2((8 * (i + 1)) as nat));
            assert((i as int) + 1 <= 8);
            assert(pw2(64) == 18446744073709551616) by (compute_only);
            lemma_pw2_monotone((8 * (i + 1)) as nat, 64);
            assert(pw2((8 * (i + 1)) as nat) <= 18446744073709551616);
            assert((v as int) + (buf@[i as int] as int) * (w as int) <= 18446744073709551615);
            // maintenance: w_new = 256*w == 256^(i+1); v_new = v + b*w = le_val (first i+1)
            lemma_pw2_pos((8 * (i + 1)) as nat);
            assert(256 * (w as int) == pw2((8 * (i + 1)) as nat));
            assert(256 * (w as int) <= 18446744073709551616);
        }
        v = v + (buf[i] as u128) * w;
        w = 256 * w;
        proof {
            lemma_le_val_step(buf@, i as nat);
        }
        i += 1;
    }
    proof {
        // exit: v = le_val_k(buf@, k) < 256^k <= 256^8 = 2^64 => safely lands in u64
        lemma_le_val_bound(buf@, k as nat);
        lemma_pw2_monotone((8 * k) as nat, 64);
        assert(pw2(64) == 18446744073709551616) by (compute_only);
        assert((v as int) < pw2((8 * k) as nat));
        assert(pw2((8 * k) as nat) <= 18446744073709551616);
        assert((v as int) <= 18446744073709551615);
    }
    v as u64
}

// ---------- L0: lib.rs:2130-2137 (LE write_uint) value kernel ----------
/// The in-place assertions are lib.rs:2131/2132 (the same shape as the BE
/// lib.rs:1951/1952: the LE configuration of the F3 family, always true
/// inside the legal domain -- the difference face of F3 is on the doc side;
/// the buf.len() precondition here is carried by requires, the assertion
/// merely records the shape).
/// Upstream doc (lib.rs:440-445):
///   Writes an unsigned integer `n` to `buf` using only `nbytes`.
///   # Panics
///   If `n` is not representable in `nbytes`, or if `nbytes` is `> 8`, then
///   this method panics.
pub exec fn order_write_uint_le_trans(buf: &mut [u8], n: u64, k: usize)
    requires
        1 <= k,
        k <= buf.len(),
        k <= 8,
        (n as int) < pw2((8 * k) as nat),
    ensures
        le_val_k(final(buf)@, k as nat) == n as int,
{
    // Origin Rust (lib.rs:2131): assert!(pack_size(n) <= nbytes && nbytes <= 8);
    let ps = pack_size_model(n);
    proof {
        lemma_pack_size_bound(n as int, k as nat);
    }
    assert!(ps <= k && k <= 8);
    // Origin Rust (lib.rs:2132): assert!(nbytes <= buf.len());
    assert!(k <= buf.len());
    // forward low-digit write: b_i = (n/256^i) mod 256, m = n/256^i divided by 256 each round
    let ghost n_int = n as int;
    let mut m: u64 = n;
    let mut i: usize = 0;
    proof {
        // entry invariant: m == n/1 == n; le_val(buf@, 0) == 0 == n % 1
        assert(pw2(0) == 1);
        lemma_fundamental_div_mod_converse(n_int, 1, n_int, 0);
        assert(n_int / 1 == n_int);
        assert(n_int % 1 == 0);
        assert(le_val_k(buf@, 0 as nat) == 0);
    }
    while i < k
        invariant
            0 <= i <= k,
            k <= buf.len() as int,
            k <= 8,
            buf@.len() == buf.len(),
            m as int == n_int / pw2((8 * i) as nat),
            le_val_k(buf@, i as nat) == n_int % pw2((8 * i) as nat),
        decreases k - i,
    {
        let ghost pre_seq = buf@;
        let ghost pre_m = m as int;
        let ghost D = pw2((8 * i) as nat);
        proof {
            // D > 0, pw2(8(i+1)) == 256*D (the two domain parameters of the digit-merge lemma)
            lemma_pw2_pos((8 * i) as nat);
            assert(D > 0);
            lemma_pw2_shift8((8 * i) as nat);
            assert(pw2(((8 * i) + 8) as nat) == 256 * pw2((8 * i) as nat));
            assert((8 * (i + 1)) == (8 * i) + 8);
            // digit merge: n/pw2(8(i+1)) == (n/D)/256; n%pw2(8(i+1)) == n%D + (m%256)*D
            lemma_digit_merge(n_int, D, pw2((8 * (i + 1)) as nat), pre_m);
        }
        let b: u8 = (m % 256) as u8; // the position-i byte of the low-k-byte order
        proof {
            // machine %/cast == the spec value (inside the m >= 0 domain)
            assert(m as int == pre_m);
            assert((m % 256) as int == pre_m % 256);
            assert(b as int == pre_m % 256);
        }
        buf[i] = b;
        proof {
            // after the write buf@ == pre_seq.update(i, b); the le_val of the first i bytes is unchanged
            assert(buf@ == pre_seq.update(i as int, b));
            lemma_le_val_stable(pre_seq, i as int, b, i as nat);
            assert(le_val_k(buf@, i as nat) == le_val_k(pre_seq, i as nat));
        }
        m = m / 256;
        i += 1;
        proof {
            // new m == n / pw2(8i) (digit-merge first conclusion + machine division == integer division)
            assert(m as int == pre_m / 256);
            assert(m as int == n_int / pw2((8 * i) as nat));
            // new le_val: step unfold + juxtaposition of the digit-merge second conclusion
            lemma_le_val_step(buf@, (i - 1) as nat);
            assert(buf@[(i - 1) as int] == b);
            assert(pw2((8 * (i - 1)) as nat) == D);
            assert(le_val_k(buf@, (i - 1) as nat) == n_int % D);
            assert(le_val_k(buf@, i as nat) == (n_int % D) + (b as int) * D);
            assert((n_int % D) + ((pre_m % 256) * D) == n_int % pw2((8 * i) as nat));
            assert(le_val_k(buf@, i as nat) == n_int % pw2((8 * i) as nat));
        }
    }
    proof {
        // exit: i == k: m == n / 256^k; le_val(buf@, k) == n % 256^k == n
        lemma_pw2_pos((8 * k) as nat);
        lemma_small_mod(n_int as nat, (pw2((8 * k) as nat)) as nat);
        assert(n_int % pw2((8 * k) as nat) == n_int);
        assert(le_val_k(buf@, k as nat) == n_int);
    }
}

// ===========================================================================
// Difference-batch section 3: the u128 family (fixed-width read_u128/
// write_u128 at lib.rs:1907-1909/1945-1947, variable-width read_uint128/
// write_uint128 at lib.rs:1921-1927/1964-1975, the LE implementation family
// at lib.rs:2089-2091/2102-2107/2125-2127/2140-2147).
// This section contains:
//   - the BE/LE u128 read/write value kernels (any 1<=k<=16);
//   - the verbatim write_uint128 transcription order_write_uint128
//     (lib.rs:1964-1975): its lib.rs:1966 assertion `nbytes <= buf.len()`
//     is the same F3-family 128-bit shape as write_uint's lib.rs:1952
//     (listed in no trait # Panics) -- expected **1 error**, an obligation
//     anchor standing beside the 64-bit F3; the LE shape lib.rs:2142 is
//     same-shaped and not separately transcribed (same F3 convention).
//   - the write_int128 chain (lib.rs:872-880 default implementation): after
//     the unextend_sign128 truncation the pack_size128 check is likewise
//     always true => the 128-bit shape of #205 (known; the #229 fix face
//     already covers write_int128), re-verified at 0 error.
// ===========================================================================

// ---------- L0: lib.rs:1907-1909 (BigEndian::read_u128) value kernel ----------
/// Upstream doc (lib.rs:263-267):
///   Reads an unsigned 128 bit integer from `buf`.
///   # Panics
///   Panics when `buf.len() < 16`.
pub exec fn order_read_u128_trans(buf: &[u8], k: usize) -> (r: u128)
    requires
        1 <= k,
        k <= buf.len(),
        k <= 16,
    ensures
        r as int == be_val_k(buf@, k as nat),
{
    let mut v: u128 = 0;
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            k <= buf.len() as int,
            k <= 16,
            buf@.len() == buf.len(),
            v as int == be_val_k(buf@, i as nat),
        decreases k - i,
    {
        proof {
            lemma_be_val_bound(buf@, i as nat);
            lemma_pw2_pos((8 * i) as nat);
            assert(pw2(64) == 18446744073709551616) by (compute_only);
            lemma_pw2_shift8((8 * i) as nat);
            assert(pw2((8 * (i + 1)) as nat) == 256 * pw2((8 * i) as nat));
            // overflow domain: v' < 256^(i+1) <= 256^16 = 2^128 (inside the u128 domain)
            assert((v as int) < pw2((8 * i) as nat));
            assert(((256 * (v as int)) + (buf@[i as int] as int)) < pw2((8 * (i + 1)) as nat));
            assert((i as int) + 1 <= 16);
            lemma_pw2_monotone((8 * (i + 1)) as nat, 128);
            assert(pw2((8 * (i + 1)) as nat) <= pw2(128));
            assert(pw2(128) == 340282366920938463463374607431768211456) by (compute_only);
            assert(340282366920938463463374607431768211456 == 18446744073709551616 * 18446744073709551616) by (compute_only);
            assert(((256 * (v as int)) + (buf@[i as int] as int)) <= 340282366920938463463374607431768211455);
            assert(v as int <= 340282366920938463463374607431768211455);
        }
        v = 256 * v + buf[i] as u128;
        i += 1;
    }
    v
}

// ---------- L0: lib.rs:1945-1947 (BigEndian::write_u128) value kernel ----------
/// The top carries the lib.rs:1965 in-place assertion (the write_uint128
/// shape; this creation is the ultimate callee of the order_write_int128
/// chain).
/// Upstream doc (lib.rs:421-425):
///   Writes an unsigned 128 bit integer `n` to `buf`.
///   # Panics
///   Panics when `buf.len() < 16`.
pub exec fn order_write_u128_trans(buf: &mut [u8], n: u128, k: usize)
    requires
        1 <= k,
        k <= buf.len(),
        k <= 16,
        (n as int) < pw2((8 * k) as nat),
    ensures
        be_val_k(final(buf)@, k as nat) == n as int,
{
    // Origin Rust (lib.rs:1965): assert!(pack_size128(n) <= nbytes && nbytes <= 16);
    let ps = pack_size128_model(n);
    proof {
        lemma_pack_size_bound(n as int, k as nat);
        lemma_pack_size128_eq(n as int);
    }
    assert!(ps <= k && k <= 16);
    // prelude: machine weight w := 256^(k-1)
    let mut w: u128 = 1;
    let mut j: usize = 0;
    while j < k - 1
        invariant
            0 <= j <= k - 1,
            k <= 16,
            w as int == pw2((8 * j) as nat),
        decreases k - 1 - j,
    {
        proof {
            assert((j as int) <= k - 2);
            assert((j as int) <= 14);
            lemma_pw2_monotone((8 * j) as nat, 112);
            assert((w as int) <= pw2(112));
            lemma_pw2_shift8(112);
            assert(256 * pw2(112) == pw2(120));
            assert(pw2(120) == 1329227995784915872903807060280344576) by (compute_only);
            assert((256 * (w as int)) <= pw2(120));
            assert(pw2(120) <= 340282366920938463463374607431768211456);
            // maintenance: w_new = 256*w == pw2(8(j+1))
            lemma_pw2_shift8((8 * j) as nat);
            assert(pw2((8 * ((j as int) + 1)) as nat) == 256 * pw2((8 * j) as nat));
        }
        w = 256 * w;
        j += 1;
    }
    // main loop: forward write of the k big-endian bytes
    let mut m: u128 = n;
    let mut i: usize = 0;
    let ghost n_int = n as int;
    proof {
        // loop-entry invariant: m == n % 256^k == n; be_val_k(buf@,0) == n/256^k == 0
        lemma_small_mod(n_int as nat, (pw2((8 * k) as nat)) as nat);
        assert(n_int % pw2((8 * k) as nat) == n_int);
        lemma_fundamental_div_mod(n_int, pw2((8 * k) as nat));
        assert(pw2((8 * k) as nat) != 0);
        assert(n_int == pw2((8 * k) as nat) * (n_int / pw2((8 * k) as nat)) + n_int);
        if n_int / pw2((8 * k) as nat) != 0 {
            lemma_mul_nonzero(pw2((8 * k) as nat), n_int / pw2((8 * k) as nat));
            assert(pw2((8 * k) as nat) * (n_int / pw2((8 * k) as nat)) != 0);
            assert(false);
        }
        assert(n_int / pw2((8 * k) as nat) == 0);
        assert(be_val_k(buf@, 0) == 0);
    }
    while i < k
        invariant
            0 <= i <= k,
            k <= buf.len() as int,
            k <= 16,
            buf@.len() == buf.len(),
            (i < k) ==> (w as int == pw2((8 * (k - i - 1)) as nat)),
            m as int == n_int % pw2((8 * (k - i)) as nat),
            be_val_k(buf@, i as nat) == n_int / pw2((8 * (k - i)) as nat),
        decreases k - i,
    {
        let ghost pre_w = w as int;
        let ghost pre_m = m as int;
        let ghost pre_seq = buf@;
        let ghost D = pw2((8 * (k - i)) as nat);
        let ghost q = n_int / D;
        let ghost b = pre_m / pre_w;
        let ghost s = pre_m % pre_w;
        proof {
            // D == 256*w; w >= 1; Euclidean decomposition pre_m == pre_w*b + s
            lemma_pw2_shift8((8 * (k - i - 1)) as nat);
            assert(D == 256 * pw2((8 * (k - i - 1)) as nat));
            assert(pw2((8 * (k - i - 1)) as nat) == pre_w);
            assert(D == 256 * pre_w);
            lemma_pw2_pos((8 * (k - i - 1)) as nat);
            assert(1 <= pre_w);
            assert(w != 0);
            lemma_fundamental_div_mod(pre_m, pre_w);
            assert(pre_m == pre_w * b + s);
            assert(0 <= s < pre_w);
            // m < D = 256*w => b = m/w < 256
            assert(pre_m < D);
            assert(pre_w * b <= pre_m);
            assert(pre_w * b < 256 * pre_w);
            lemma_mul_strict_inequality_converse(b, 256, pre_w);
            assert(b < 256);
            // n = D*q + m = 256*w*q + (w*b + s) = w*(256q+b) + s
            lemma_fundamental_div_mod(n_int, D);
            assert(D != 0);
            assert(n_int == D * q + pre_m);
            assert((256 * pre_w) * q == pre_w * (256 * q)) by (nonlinear_arith);
            assert(pre_w * (256 * q + b) == pre_w * (256 * q) + pre_w * b) by (nonlinear_arith);
            assert(n_int == pre_w * (256 * q + b) + s);
            lemma_fundamental_div_mod_converse(n_int, pre_w, 256 * q + b, s);
            assert(n_int / pre_w == 256 * q + b);
        }
        let bm: u128 = m / w;
        proof {
            assert(bm as int == b); // machine division == integer division (nonnegative domain)
        }
        buf[i] = bm as u8;
        m = m % w;
        w = w / 256;
        i += 1;
        proof {
            // (1) new w: w == pre_w/256 == pw2(8(k-i-1)) (when i < k)
            if i < k {
                lemma_pw2_shift8((8 * (k - i - 1)) as nat);
                assert(pw2((8 * (k - i)) as nat) == 256 * pw2((8 * (k - i - 1)) as nat));
                assert(pre_w == pw2((8 * (k - i)) as nat));
                assert(pre_w == 256 * pw2((8 * (k - i - 1)) as nat));
                lemma_fundamental_div_mod_converse(pre_w, 256, pw2((8 * (k - i - 1)) as nat), 0);
                assert(w as int == pw2((8 * (k - i - 1)) as nat));
            }
            // (2) new m: m == pre_m % pre_w == s == n % pw2(8(k-i))
            assert(m as int == pre_m % pre_w);
            assert(pw2((8 * (k - i)) as nat) == pre_w);
            assert(m as int == n_int % pw2((8 * (k - i)) as nat));
            // (3) new be_val: the write lands at position i-1; the first i-1 prefix is unchanged
            assert(buf@ == pre_seq.update((i - 1) as int, bm as u8));
            lemma_be_val_stable(pre_seq, (i - 1) as int, bm as u8, (i - 1) as nat);
            assert(be_val_k(buf@, (i - 1) as nat) == be_val_k(pre_seq, (i - 1) as nat));
            lemma_be_val_step(buf@, (i - 1) as nat);
            assert(be_val_k(buf@, i as nat) == 256 * be_val_k(buf@, (i - 1) as nat) + buf@[(i - 1) as int] as int);
            assert(buf@[(i - 1) as int] as int == b);
            assert(be_val_k(buf@, i as nat) == 256 * q + b);
            assert(be_val_k(buf@, i as nat) == n_int / pre_w);
            assert(be_val_k(buf@, i as nat) == n_int / pw2((8 * (k - i)) as nat));
        }
    }
    proof {
        // exit: i == k => pw2(0) == 1, n/1 == n
        assert(pw2(0) == 1);
        assert((n_int / 1) == n_int) by (nonlinear_arith);
    }
}

// ---------- pack_size128 spec + exec pair (lib.rs:117-119; the definitional-equivalence lemma sits at the file tail) ----------

/// Mathematical equivalent: packSize128(n) = the least k with n < 256^k (the
/// u128 domain k in 1..=16; the same recursion as pack_size_spec, the n
/// domain wider).
pub open spec fn pack_size128_spec(n: int) -> int
    decreases n,
{
    if n <= 0 {
        1
    } else if n < 256 {
        1
    } else {
        1 + pack_size128_spec(n / 256)
    }
}

/// lib.rs:117-119 transcription (external_body: out-of-scope helper; the equivalence is stated by the ensures).
#[verifier::external_body]
pub exec fn pack_size128_model(n: u128) -> (r: usize)
    ensures
        1 <= r,
        r <= 16,
        pack_size128_spec(n as int) == r as int,
{
    1 // body not verified; Origin Rust: (16 - ((n|1).leading_zeros() >> 3)) as usize
}

// ---------- L0: lib.rs:1964-1975 (BigEndian::write_uint128) verbatim transcription ----------
/// requires copies the two conditions of the trait doc (the # Panics of
/// lib.rs:471-476: "not representable" / "nbytes > 16").
/// Expected **1 error**: the lib.rs:1966 transcription line (the
/// undocumented `nbytes <= buf.len()`, the 128-bit shape of F3 -- the
/// obligation anchor standing beside the 64-bit F3; the LE shape is
/// lib.rs:2142).
/// Origin Rust (lib.rs:1964-1975):
/// `fn write_uint128(buf, n, nbytes) { assert!(pack_size128(n) <= nbytes && nbytes <= 16);
///  assert!(nbytes <= buf.len()); unsafe {...} }` (`unsafe` is unrelated to
/// this finding, omitted)
/// Upstream doc (lib.rs:460-465):
///   Writes an unsigned integer `n` to `buf` using only `nbytes`.
///   # Panics
///   If `n` is not representable in `nbytes`, or if `nbytes` is `> 16`, then
///   this method panics.
pub exec fn order_write_uint128(n: u128, nbytes: usize, buf: &mut [u8])
    requires
        1 <= nbytes,
        nbytes <= 16,                                 // doc: "If nbytes > 16, this method panics"
        pack_size128_spec(n as int) <= nbytes as int, // doc: "n not representable in nbytes => panics"
    // SPEC-DOC MISMATCH (BurntSushi/byteorder#230): the doc # Panics declare only
    // "n not representable in nbytes" / "nbytes > 16"; the doc-promised premise set
    // cannot prove the asserted `nbytes <= buf.len()` -- a precondition the doc omits.
    // Kept in the implementation-faithful form (the expected error is that assertion).
{
    let ps = pack_size128_model(n); // the pack_size128(n) call at the head of lib.rs:1965
    // Origin Rust (lib.rs:1965): assert!(pack_size128(n) <= nbytes && nbytes <= 16);
    assert!(ps <= nbytes && nbytes <= 16);
    // Origin Rust (lib.rs:1966): assert!(nbytes <= buf.len());
    assert!(nbytes <= buf.len()); // <-- EXPECTED: not provable from the doc premises (undocumented condition, the 128-bit F3 shape)
    // ...lib.rs:1967-1974 unsafe pointer-side copy (unrelated to this finding, omitted)
}

// ---------- L0: lib.rs:872-880 (write_int128 default implementation) transcription ----------
/// lib.rs:879:write_int128 = write_uint128(unextend_sign128(n, nbytes), nbytes)
/// -- the pack_size128 check likewise only sees the truncated value => the
/// 128-bit shape of #205 (known: the #205 finding + the #229 fix face both
/// cover write_int128); this transcription is 0 error and, together with the
/// 64-bit write_int chain, completes the obligation-layer re-verification of
/// that finding. (The positive lib.rs:1965 assertion is carried by
/// order_write_u128_trans; the gap obligation of the base-form lib.rs:1966
/// is carried by order_write_uint128.)
#[verifier::external_body]
pub exec fn unextend_sign128_model(n: i128, nbytes: usize) -> (r: u128)
    requires
        1 <= nbytes,
        nbytes <= 16,
    ensures
        r as int == unextend_sign_spec(n as int, nbytes as int),
{
    0 // body not verified; Origin Rust (lib.rs:106-109):
      // let shift = (16 - nbytes) * 8; ((val << shift) as u128) >> shift
}

/// Upstream doc (lib.rs:859-864):
///   Writes a signed integer `n` to `buf` using only `nbytes`.
///   # Panics
///   If `n` is not representable in `nbytes`, or if `nbytes` is `> 16`, then
///   this method panics.
pub exec fn order_write_int128_lib(n: i128, nbytes: usize, buf: &mut [u8])
    requires
        1 <= nbytes,
        nbytes <= 16,   // doc: legal domain of "or if nbytes is > 16, this method panics"
        nbytes <= buf.len(),
    // SPEC-DOC MISMATCH (BurntSushi/byteorder#230): the `nbytes <= buf.len()`
    // precondition is not listed by the write_int128 # Panics; carried here as part
    // of the implementation-faithful requires.
    ensures
        be_val_k(final(buf)@, nbytes as nat) == unextend_sign_spec(n as int, nbytes as int),
{
    let v = unextend_sign128_model(n, nbytes); // lib.rs:879 unextend_sign128(n, nbytes)
    proof {
        // v@ = n % 256^nbytes lies in [0, 256^nbytes) (the Euclidean modulus bound via the div_mod lemmas)
        lemma_pw2_pos((8 * nbytes) as nat);
        lemma_fundamental_div_mod(n as int, pw2((8 * nbytes) as nat));
        assert(v as int == (n as int) % pw2((8 * nbytes) as nat));
        assert(v as int >= 0);
        assert((v as int) < (pw2((8 * nbytes) as nat)));
        // => pack_size128_spec(v@) <= nbytes (dead check, same as the 64-bit chain)
        lemma_pack_size_bound(v as int, nbytes as nat);
        // definitional-layer equivalence of pack_size128_spec and pack_size_spec (lemma)
        lemma_pack_size128_eq(v as int);
    }
    order_write_u128_trans(buf, v, nbytes) // lib.rs:879 -> the lib.rs:1965 assertion + the main loop
}

// ---------- L0: lib.rs:2089-2091 (LittleEndian::read_u128) value kernel ----------
/// LE u128 read: sum b_i*256^i (k <= 16; k=16 is exactly the fixed-width
/// read_u128 shape). The w maintenance uses a guard (the final round's
/// 256^15 * 256 = 2^128 exactly overflows u128, and the final-round w is
/// not needed anymore).
/// Upstream doc (lib.rs:263-267):
///   Reads an unsigned 128 bit integer from `buf`.
///   # Panics
///   Panics when `buf.len() < 16`.
pub exec fn order_read_u128_le_trans(buf: &[u8], k: usize) -> (r: u128)
    requires
        1 <= k,
        k <= buf.len(),
        k <= 16,
    ensures
        r as int == le_val_k(buf@, k as nat),
{
    let mut v: u128 = 0;
    let mut w: u128 = 1;
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            k <= buf.len() as int,
            k <= 16,
            buf@.len() == buf.len(),
            (i < k) ==> (w as int == pw2((8 * i) as nat)),
            v as int == le_val_k(buf@, i as nat),
        decreases k - i,
    {
        proof {
            lemma_le_val_bound(buf@, i as nat);
            lemma_pw2_pos((8 * i) as nat);
            assert((v as int) < pw2((8 * i) as nat));
            assert((i < k) ==> ((w as int) == pw2((8 * i) as nat)));
            // overflow domain: v' = v + b*w < 256^i + 255*256^i = 256^(i+1) <= 2^128 (inside the u128 domain)
            lemma_mul_inequality(buf@[i as int] as int, 255, pw2((8 * i) as nat));
            assert((buf@[i as int] as int) * pw2((8 * i) as nat) <= 255 * pw2((8 * i) as nat));
            assert(pw2((8 * i) as nat) + 255 * pw2((8 * i) as nat) == 256 * pw2((8 * i) as nat));
            assert((v as int) + (buf@[i as int] as int) * (w as int) < 256 * pw2((8 * i) as nat));
            lemma_pw2_shift8((8 * i) as nat);
            assert(256 * pw2((8 * i) as nat) == pw2(((8 * i) + 8) as nat));
            assert((8 * (i + 1)) == (8 * i) + 8);
            assert((v as int) + (buf@[i as int] as int) * (w as int) < pw2((8 * (i + 1)) as nat));
            assert((i as int) + 1 <= 16);
            lemma_pw2_monotone((8 * (i + 1)) as nat, 128);
            assert(pw2(128) == 340282366920938463463374607431768211456) by (compute_only);
            assert(pw2((8 * (i + 1)) as nat) <= 340282366920938463463374607431768211455 + 1);
            assert((v as int) + (buf@[i as int] as int) * (w as int) <= 340282366920938463463374607431768211455);
        }
        v = v + (buf[i] as u128) * w;
        proof {
            // guard domain: i < k-1 <=> i+1 < k => i <= k-2 <= 14, w = 256^i,
            // machine check 256*w <= 2^120 < 2^128; maintenance w_new == pw2(8(i+1))
            if i < k - 1 {
                assert((i as int) <= (k as int) - 2);
                assert((i as int) <= 14);
                lemma_pw2_monotone((8 * i) as nat, 112);
                assert((w as int) <= pw2(112));
                lemma_pw2_shift8(112);
                assert(256 * pw2(112) == pw2(120));
                assert(pw2(120) == 1329227995784915872903807060280344576) by (compute_only);
                assert(pw2(120) < 340282366920938463463374607431768211456);
                lemma_pw2_shift8((8 * i) as nat);
                assert(pw2((8 * (i + 1)) as nat) == 256 * pw2((8 * i) as nat));
                assert((256 * (w as int)) < 340282366920938463463374607431768211456);
            }
        }
        if i < k - 1 {
            w = 256 * w; // final round not updated (256^15*256 = 2^128 exactly overflows; the next round exits)
        }
        proof {
            // maintenance: v_new = le_val (first i+1)
            lemma_le_val_step(buf@, i as nat);
        }
        i += 1;
    }
    proof {
        // exit: v = le_val(buf@, k) < 256^k, returned
        lemma_le_val_bound(buf@, k as nat);
        assert((v as int) < pw2((8 * k) as nat));
    }
    v
}

// ---------- L0: lib.rs:2125-2127/2140-2147 (LittleEndian::write_u128/write_uint128) value kernel ----------
/// LE u128 write: forward low-digit extraction (b = m % 256); the top
/// carries the lib.rs:2141 in-place assertion (always true inside the
/// k <= 16 legal domain; the lib.rs:2142 buf.len() gap is the same family as
/// the BE shape, see order_write_uint128).
/// Upstream doc (lib.rs:421-425):
///   Writes an unsigned 128 bit integer `n` to `buf`.
///   # Panics
///   Panics when `buf.len() < 16`.
pub exec fn order_write_u128_le_trans(buf: &mut [u8], n: u128, k: usize)
    requires
        1 <= k,
        k <= buf.len(),
        k <= 16,
        (n as int) < pw2((8 * k) as nat),
    ensures
        le_val_k(final(buf)@, k as nat) == n as int,
{
    // Origin Rust (lib.rs:2141): assert!(pack_size128(n) <= nbytes && nbytes <= 16);
    let ps = pack_size128_model(n);
    proof {
        lemma_pack_size_bound(n as int, k as nat);
        lemma_pack_size128_eq(n as int);
    }
    assert!(ps <= k && k <= 16);
    // forward low-digit write
    let ghost n_int = n as int;
    let mut m: u128 = n;
    let mut i: usize = 0;
    proof {
        // entry invariant: m == n/1 == n; le_val(buf@, 0) == 0 == n % 1
        assert(pw2(0) == 1);
        lemma_fundamental_div_mod_converse(n_int, 1, n_int, 0);
        assert(n_int / 1 == n_int);
        assert(n_int % 1 == 0);
        assert(le_val_k(buf@, 0 as nat) == 0);
    }
    while i < k
        invariant
            0 <= i <= k,
            k <= buf.len() as int,
            k <= 16,
            buf@.len() == buf.len(),
            m as int == n_int / pw2((8 * i) as nat),
            le_val_k(buf@, i as nat) == n_int % pw2((8 * i) as nat),
        decreases k - i,
    {
        let ghost pre_seq = buf@;
        let ghost pre_m = m as int;
        let ghost D = pw2((8 * i) as nat);
        proof {
            lemma_pw2_pos((8 * i) as nat);
            assert(D > 0);
            lemma_pw2_shift8((8 * i) as nat);
            assert(pw2(((8 * i) + 8) as nat) == 256 * pw2((8 * i) as nat));
            assert((8 * (i + 1)) == (8 * i) + 8);
            lemma_digit_merge(n_int, D, pw2((8 * (i + 1)) as nat), pre_m);
        }
        proof {
            assert(m as int == pre_m);
            assert((m % 256) as int == pre_m % 256);
        }
        let b: u8 = (m % 256) as u8;
        assert(b as int == pre_m % 256);
        buf[i] = b;
        proof {
            assert(buf@ == pre_seq.update(i as int, b));
            lemma_le_val_stable(pre_seq, i as int, b, i as nat);
            assert(le_val_k(buf@, i as nat) == le_val_k(pre_seq, i as nat));
        }
        m = m / 256;
        i += 1;
        proof {
            // new m == n / pw2(8i) (digit-merge first conclusion)
            assert(m as int == pre_m / 256);
            assert(m as int == n_int / pw2((8 * i) as nat));
            // new le_val: step unfold + digit-merge second conclusion
            lemma_le_val_step(buf@, (i - 1) as nat);
            assert(buf@[(i - 1) as int] == b);
            assert(pw2((8 * (i - 1)) as nat) == D);
            assert(le_val_k(buf@, (i - 1) as nat) == n_int % D);
            assert(le_val_k(buf@, i as nat) == (n_int % D) + (pre_m % 256) * D);
            assert(le_val_k(buf@, i as nat) == n_int % pw2((8 * i) as nat));
        }
    }
    proof {
        // exit: le_val(buf@, k) == n % 256^k == n
        lemma_pw2_pos((8 * k) as nat);
        lemma_small_mod(n_int as nat, (pw2((8 * k) as nat)) as nat);
        assert(n_int % pw2((8 * k) as nat) == n_int);
        assert(le_val_k(buf@, k as nat) == n_int);
    }
}


// ===========================================================================
// Proof lemmas (power/value bounds and step/stable facts, the digit-merge
// lemma, the pack_size bounds and the reachability witnesses; moved to the
// end of the file before the close of verus! so the exec implementations
// read directly -- only the order changed, signatures and contracts untouched)
// ===========================================================================
// ---------- power lemmas (already verified back in the io_read_u64 fragment era) ----------
proof fn lemma_pw2_step(e: nat)
    ensures
        pw2((e + 1) as nat) == 2 * pw2(e),
{
}

pub proof fn lemma_pw2_pos(e: nat)
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

pub proof fn lemma_pw2_monotone(e1: nat, e2: nat)
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

pub proof fn lemma_pw2_shift8(m: nat)
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

/// Big-endian value of the first k bytes < 256^k
pub proof fn lemma_be_val_bound(seq: Seq<u8>, k: nat)
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
        assert((seq[k - 1] as int) <= 255);
        assert(((256 * be_val_k(seq, (k - 1) as nat)) + (seq[k - 1] as int))
            < ((256 * pw2((8 * (k - 1)) as nat)) + 256));
        assert((256 * pw2((8 * (k - 1)) as nat)) >= (pw2((8 * (k - 1)) as nat) + 1));
        assert((pw2((8 * (k - 1)) as nat) + 1) <= pw2((8 * k) as nat));
    }
}

/// Little-endian value of the first k bytes < 256^k
pub proof fn lemma_le_val_bound(seq: Seq<u8>, k: nat)
    ensures
        le_val_k(seq, k) < pw2((8 * k) as nat),
    decreases k,
{
    if k == 0 {
        assert(le_val_k(seq, 0) == 0);
        assert(pw2(0) == 1);
    } else {
        lemma_le_val_bound(seq, (k - 1) as nat);
        lemma_pw2_pos((8 * (k - 1)) as nat);
        lemma_pw2_shift8((8 * (k - 1)) as nat);
        assert(256 * pw2((8 * (k - 1)) as nat) == pw2((8 * k) as nat));
        assert((seq[k - 1] as int) <= 255);
        // le_val(k) = le_val(k-1) + b*256^(k-1) < 256^(k-1) + 255*256^(k-1) = 256^k
        let P1 = pw2((8 * (k - 1)) as nat);
        lemma_mul_inequality((seq[k - 1] as int), 255, P1);
        assert((seq[k - 1] as int) * P1 <= 255 * P1);
        assert((le_val_k(seq, (k - 1) as nat) + (seq[k - 1] as int) * P1)
            < P1 + 255 * P1);
        assert(P1 + 255 * P1 == 256 * P1);
        assert((le_val_k(seq, (k - 1) as nat) + (seq[k - 1] as int) * P1)
            < pw2((8 * k) as nat));
    }
}

/// be_val_k definitional unfold: be_val_k(seq, j+1) == 256*be_val_k(seq, j) + seq[j]
proof fn lemma_be_val_step(seq: Seq<u8>, j: nat)
    requires
        (j + 1) as int <= seq.len(),
    ensures
        be_val_k(seq, (j + 1) as nat) == 256 * be_val_k(seq, j) + seq[j as int] as int,
{
}

/// The prefix value is unchanged when the updated index >= the prefix length
proof fn lemma_be_val_stable(seq: Seq<u8>, idx: int, v: u8, j: nat)
    requires
        0 <= idx < seq.len(),
        j as int <= idx,
    ensures
        be_val_k(seq.update(idx, v), j) == be_val_k(seq, j),
    decreases j,
{
    if j == 0 {
        assert(be_val_k(seq.update(idx, v), 0) == 0);
    } else {
        lemma_be_val_stable(seq, idx, v, (j - 1) as nat);
        // update touches only the element at index idx; j-1 < idx
        assert(seq.update(idx, v)[(j - 1) as int] == seq[(j - 1) as int]);
    }
}

// ---------- reachability witness (pure proof layer) ----------
proof fn f3_reachability_witness() {
    assert(pack_size_spec(0int) == 1);
    assert(1 <= 1 && 1 <= 8);  // (n=0, nbytes=1) satisfies the doc premises
    assert(!(1 <= 0));         // while buf.len()==0 => the lib.rs:1952 obligation is false
}

/// 0 <= v < 256^k => pack_size_spec(v) <= k.
/// The root lemma of the signed-write-chain always-true assertion: the
/// pack_size check of write_uint only ever sees the truncated value (< 256^k),
/// so that check is dead code on the write_int chain.
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
            // v >= 256 => k >= 2; induction: v/256 < 256^(k-1)
            let q = v / 256;
            let r = v % 256;
            lemma_fundamental_div_mod(v, 256);
            assert(v == 256 * q + r);
            assert(0 <= r < 256);
            lemma_pw2_pos((8 * (k - 1)) as nat);
            assert(pw2((8 * (k - 1)) as nat) >= 1);
            lemma_pw2_shift8((8 * (k - 1)) as nat);
            assert(pw2((8 * k) as nat) == 256 * pw2((8 * (k - 1)) as nat));
            assert(256 * q <= v);
            assert(256 * q < 256 * pw2((8 * (k - 1)) as nat));
            lemma_mul_strict_inequality_converse(q, pw2((8 * (k - 1)) as nat), 256);
            assert(q < pw2((8 * (k - 1)) as nat));
            lemma_pack_size_bound(q, (k - 1) as nat);
            assert(pack_size_spec(v) == 1 + pack_size_spec(q)); // pack_size_spec definitional unfold (fuel 1)
            assert(1 + pack_size_spec(q) <= k);
        }
    }
}

// ---------- LE lemmas ----------
/// le_val_k definitional unfold: le_val_k(seq, j+1) == le_val_k(seq, j) + seq[j]*256^j
proof fn lemma_le_val_step(seq: Seq<u8>, j: nat)
    requires
        ((j + 1) as int) <= seq.len(),
    ensures
        le_val_k(seq, (j + 1) as nat) == le_val_k(seq, j) + (seq[j as int] as int) * pw2((8 * j) as nat),
{
    // single-layer definitional unfold of le_val_k (fuel 1)
}

/// Digit-merge lemma (the core of the LE write-kernel maintenance):
///   n = D*pre_m + r0, pre_m = 256*mp + b, P2 = 256*D =>
///   n/P2 = mp, n%P2 = r0 + b*D
/// -- i.e. "after taking the low byte b, quotient and remainder juxtapose
/// on the 256x-width domain".
proof fn lemma_digit_merge(n: int, D: int, P2: int, pre_m: int)
    requires
        D > 0,
        pre_m == n / D,
        P2 == 256 * D,
    ensures
        n / P2 == pre_m / 256,
        n % P2 == n % D + (pre_m % 256) * D,
{
    lemma_fundamental_div_mod(n, D);
    lemma_mod_bound(n, D);
    assert(n == D * pre_m + n % D);
    assert(0 <= n % D);
    assert(n % D < D);
    lemma_mod_bound(pre_m, 256);
    assert(0 <= pre_m % 256 < 256);
    assert(pre_m == 256 * (pre_m / 256) + pre_m % 256);
    // product chain (single-step nonlinear equalities: commutativity/distributivity/rearrangement):
    assert(D * pre_m == pre_m * D) by { lemma_mul_is_commutative(D, pre_m); };
    assert(pre_m * D == (256 * (pre_m / 256) + pre_m % 256) * D) by (nonlinear_arith);
    assert((256 * (pre_m / 256)) * D == (pre_m / 256) * (256 * D)) by (nonlinear_arith);
    assert((pre_m % 256) * D == D * (pre_m % 256)) by { lemma_mul_is_commutative(pre_m % 256, D); };
    assert(D * pre_m == (pre_m / 256) * (256 * D) + D * (pre_m % 256)) by (nonlinear_arith);
    // remainder upper bound:
    lemma_mul_inequality(pre_m % 256, 255, D);
    assert((pre_m % 256) * D <= 255 * D);
    assert((n % D) + (pre_m % 256) * D < D + 255 * D);
    assert(D + 255 * D == 256 * D);
    assert((n % D) + (pre_m % 256) * D < 256 * D);
    // quotient/remainder uniqueness + congruence to P2:
    assert(n == ((pre_m / 256) * (256 * D)) + ((n % D) + D * (pre_m % 256)));
    lemma_fundamental_div_mod_converse(n, 256 * D, pre_m / 256, (n % D) + D * (pre_m % 256));
    assert(n % (256 * D) == (n % D) + D * (pre_m % 256));
    assert(n / (256 * D) == pre_m / 256);
    assert(n % P2 == (n % D) + D * (pre_m % 256));
    assert(n / P2 == pre_m / 256);
}

/// The LE prefix value is unchanged when the updated index >= the prefix
/// length (same shape as lemma_be_val_stable). (pub: referenced by the
/// harness slice-family theorems; the pub relaxation is noted in the file
/// header.)
pub proof fn lemma_le_val_stable(seq: Seq<u8>, idx: int, v: u8, j: nat)
    requires
        0 <= idx < seq.len(),
        j as int <= idx,
    ensures
        le_val_k(seq.update(idx, v), j) == le_val_k(seq, j),
    decreases j,
{
    if j == 0 {
        assert(le_val_k(seq.update(idx, v), 0) == 0);
    } else {
        lemma_le_val_stable(seq, idx, v, (j - 1) as nat);
        lemma_le_val_step(seq, (j - 1) as nat);
        lemma_le_val_step(seq.update(idx, v), (j - 1) as nat);
        // update touches only the element at index idx; j-1 < idx
        assert(seq.update(idx, v)[(j - 1) as int] == seq[(j - 1) as int]);
    }
}

pub proof fn lemma_le_val_step_pub(seq: Seq<u8>, j: nat)
    requires
        ((j + 1) as int) <= seq.len(),
    ensures
        le_val_k(seq, (j + 1) as nat) == le_val_k(seq, j) + (seq[j as int] as int) * pw2((8 * j) as nat),
{
    lemma_le_val_step(seq, j);
}

/// Definitional-layer equivalence of pack_size128_spec and pack_size_spec (the same recursion; the u128 domain is wider).
pub proof fn lemma_pack_size128_eq(n: int)
    requires
        0 <= n,
    ensures
        pack_size128_spec(n) == pack_size_spec(n),
    decreases n,
{
    if 0 <= n && n < 256 {
        assert(pack_size128_spec(n) == 1);
        assert(pack_size_spec(n) == 1);
    } else {
        assert(n >= 256);
        assert((n / 256) < n);
        lemma_pack_size128_eq(n / 256);
        assert(pack_size128_spec(n) == 1 + pack_size128_spec(n / 256));
        assert(pack_size_spec(n) == 1 + pack_size_spec(n / 256));
    }
}
}

fn main() {}
