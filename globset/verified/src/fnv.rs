//! globset `src/fnv.rs` mirror -- the FNV hasher face, pinned
//! uninterpreted (the batch-plan ruling D6: the wrapping xor/mul residue
//! body is NOT expanded into verified arithmetic; the fireable
//! container behavior never depends on digest values, only on byte
//! equality of the hashed keys).
//!
//! Upstream pin: crates/globset/src/fnv.rs @
//! 178cc027e283fd965cb72d0a7395b219eada170c (30 lines).
//!
//! What this file delivers (GL1 scope):
//!  - the two FNV-1a 64 constants, transcribed verbatim from
//!    fnv.rs:9-10 and certified against the upstream tree by the
//!    closing python diff sweep plus the two-arm spot lattice below;
//!  - `fnv_bytes_digest`, the uninterpreted digest face (one function
//!    symbol; determinism -- equal byte sequences, equal digests -- is
//!    inherent in being a mathematical function);
//!  - the ten spot-check pins: digest values computed NOW by the
//!    two independent arms (python plain-int arithmetic on the two
//!    constants, out/kverus-run/GL1/fnv_spot_values.py; and the real
//!    upstream fnv.rs copy executed on the same inputs under cargo,
//!    out/kverus-run/GL1/oracle-run.txt -- the arms matched on all
//!    ten), pinned here as external-body constants tied to the
//!    uninterpreted symbol. Literals are script-transcribed (zero
//!    hand transcription); the lattice spans: the empty write (a
//!    fresh hasher's finish), the two extreme single bytes 0x00/0xff,
//!    short/medium strings, and the globset-realistic key shapes
//!    (extension keys like `.rs`/`.c`/`.gitignore`, one full
//!    source-path literal) that the later strategy tiers hash.
//!    Enough spans to underwrite every conclusion this tree draws on
//!    the fnv face (constant-transcription correctness; the
//!    unwritten-finish basis; the pattern-matching `a`/`abc`/
//!    `hello world` rows cross-agreeing with the published FNV-1a
//!    test vectors).
//!
//! Out of GL1 scope (recorded, later batches):
//!  - the `HashMap<K, V> = std::collections::HashMap<.., BuildHasherDefault<Hasher>>`
//!    container alias comes with the strategy-tier batches as a
//!    trusted std-container face spec'd by membership under key byte
//!    equality (insert(k,v) then get(k') == the stored value when
//!    k' == k by bytes), erasing digest values entirely;
//!  - the `Hasher` struct + `write`/`finish` methods never reappear
//!    as verified exec here (their behavioral content is exactly the
//!    pinned digest face).
//!
//! Upstream doc lines (fnv.rs:1-6, quoted verbatim):
//!   A convenience alias for creating a hash map with an FNV hasher.
//!   A hasher that implements the Fowler-Noll-Vo (FNV) hash.

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

/// Origin Rust (fnv.rs:9): `const OFFSET_BASIS: u64 = 0xcbf29ce484222325;`
pub const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;

/// Origin Rust (fnv.rs:10): `const PRIME: u64 = 0x100000001b3;`
pub const FNV_PRIME: u64 = 0x100000001b3;

/// The FNV-1a 64 digest function over the written byte sequence
/// (write calls concatenate; finish returns the digest). A pinned
/// uninterpreted symbol: no residue arithmetic, no collision claims --
/// only what determinism gives for free and what the ten pins below
/// certify.
pub uninterp spec fn fnv_bytes_digest(bytes: Seq<u8>) -> u64;

// ---------------------------------------------------------------------------
// Spot-check pins (trusted oracle constants; every value below is the
// output of the two-arm lattice; see the module header).
// ---------------------------------------------------------------------------

/// Pin: the fresh unwritten hasher -- digest of the empty sequence is
/// the offset basis itself (upstream `Default` seeds `Hasher(OFFSET_BASIS)`
/// and `finish` returns the state).
#[verifier::external_body]
pub fn fnv_pin_digest_empty() -> (r: u64)
    ensures
        r == fnv_bytes_digest(Seq::empty()),
{
    0xcbf29ce484222325
}

/// Pin: single 0x00 byte.
#[verifier::external_body]
pub fn fnv_pin_digest_nul() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![0x00]),
{
    0xaf63bd4c8601b7df
}

/// Pin: single 0xff byte (the top of the byte domain).
#[verifier::external_body]
pub fn fnv_pin_digest_hi_byte() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![0xff]),
{
    0xaf64724c8602eb6e
}

/// Pin: "a" (matches the published FNV-1a 64 test vector).
#[verifier::external_body]
pub fn fnv_pin_digest_a() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![0x61]),
{
    0xaf63dc4c8601ec8c
}

/// Pin: "abc" (matches the published FNV-1a 64 test vector).
#[verifier::external_body]
pub fn fnv_pin_digest_abc() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![0x61, 0x62, 0x63]),
{
    0xe71fa2190541574b
}

/// Pin: the `.rs` extension key (the ExtensionStrategy map shape).
#[verifier::external_body]
pub fn fnv_pin_digest_ext_rs() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![0x2e, 0x72, 0x73]),
{
    0xf8539117ecb2fb5e
}

/// Pin: the `.c` extension key.
#[verifier::external_body]
pub fn fnv_pin_digest_ext_c() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![0x2e, 0x63]),
{
    0x07da4d07b4a095d6
}

/// Pin: the `.gitignore` extension key (dotfile leads its own ext
/// family, per the file_name_ext semantics).
#[verifier::external_body]
pub fn fnv_pin_digest_ext_gitignore() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![0x2e, 0x67, 0x69, 0x74, 0x69, 0x67, 0x6e, 0x6f, 0x72, 0x65]),
{
    0x2939ff25ab5a98e5
}

/// Pin: "hello world" (matches the published FNV-1a 64 test vector).
#[verifier::external_body]
pub fn fnv_pin_digest_hello() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![
            0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64
        ]),
{
    0x779a65e7023cd2e7
}

/// Pin: "src/**/*.rs" (a full glob literal as the LiteralStrategy map
/// shape consumes).
#[verifier::external_body]
pub fn fnv_pin_digest_lit_source() -> (r: u64)
    ensures
        r == fnv_bytes_digest(seq![
            0x73, 0x72, 0x63, 0x2f, 0x2a, 0x2a, 0x2f, 0x2a, 0x2e, 0x72, 0x73
        ]),
{
    0xc4d337e40d363354
}

} // verus!

/// Single-file driver anchor (KVerus convention; consumers reference
/// this file via #[path]).
fn main() {}
