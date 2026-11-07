//! `alphabet.rs` mirror -- aggregation of the verified items from code/src/alphabet.rs
//!   (Alphabet/Symbol/ParseAlphabetError + the full-loop transcription of new_with_padding)
//!
//! Relaxations (see the lib.rs ledger): `&str` -> `&[u8]`; `Alphabet { symbols: [u8;64] }`
//! -> `AlphabetV { symbols: Vec<u8> }` (semantically equivalent: a 64-element sequence).

use vstd::prelude::*;

verus! {

pub const ALPHABET_LEN: usize = 64;

/// Origin: alphabet.rs:171 `pub struct Symbol(u8)`
/// private field -> named field (equivalent construction-side semantics, as_u8 same value)
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Symbol {
    pub val: u8,
}

impl Symbol {
    /// Origin: alphabet.rs:175 `pub const fn new(symbol: u8) -> Option<Self>`
    pub open spec fn new_spec(symbol: u8) -> Option<Symbol> {
        if is_valid_b64_symbol_spec(symbol) { Option::Some(Symbol { val: symbol }) } else { Option::None }
    }

    /// Upstream doc (alphabet.rs:174-174):
    ///   Returns `Some` if `symbol` is a valid printable ASCII symbol, otherwise `None`.
    pub exec fn new(symbol: u8) -> (r: Option<Symbol>)
        ensures r == Symbol::new_spec(symbol)
    {
        if is_valid_b64_symbol(symbol) {
            Option::Some(Symbol { val: symbol })
        } else {
            Option::None
        }
    }

    /// Origin: alphabet.rs:184 `pub const fn as_u8(&self) -> u8`
    pub open spec fn as_u8_spec(self) -> u8 {
        self.val
    }

    /// Upstream doc (alphabet.rs:183-183):
    ///   Returns the symbol as an ASCII byte.
    pub exec fn as_u8(self) -> (r: u8)
        ensures r == self.as_u8_spec()
    {
        self.val
    }
}

/// Origin: alphabet.rs:209 `is_valid_b64_symbol`
/// doc: "Must be ascii printable. 127 (DEL) is commonly considered printable
/// for some reason but clearly unsuitable for base64."
pub open spec fn is_valid_b64_symbol_spec(byte: u8) -> bool {
    32 <= byte <= 126
}

/// L0 exec mirror (the const fn body is verbatim-equivalent to the spec fn above)
/// Upstream doc (alphabet.rs:207-208):
///   Must be ascii printable. 127 (DEL) is commonly considered printable
///   for some reason but clearly unsuitable for base64.
pub exec fn is_valid_b64_symbol(byte: u8) -> (r: bool)
    ensures r == is_valid_b64_symbol_spec(byte)
{
    byte >= 32_u8 && byte <= 126_u8
}

/// Origin: alphabet.rs:223 ParseAlphabetError
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum ParseAlphabetError {
    InvalidLength,
    DuplicatedByte(u8),
    UnprintableByte(u8),
    ReservedByte(u8),
}

/// No duplication of position i against any other position (closure-body form avoids writing <=>)
pub open spec fn no_dup_at(bytes: Seq<u8>, b: u8, i: int) -> bool {
    forall|j: int| 0 <= j < bytes.len() ==> j == i || bytes[j] != b
}

/// The "fully clean" criterion for position i: printable && != pad && distinct from
/// every other position across the domain. Mirrors the upstream triple check at the outer index
/// (UnprintableByte -> ReservedByte -> DuplicatedByte, the latter's probe covering all 64 bytes).
pub open spec fn clean_at(bytes: Seq<u8>, padding: u8, i: int) -> bool {
    let b = bytes[i];
    is_valid_b64_symbol_spec(b) && b != padding && no_dup_at(bytes, b, i)
}

/// The error variant of the first violation (cascaded per the upstream check priority)
pub open spec fn error_at(bytes: Seq<u8>, padding: u8, i: int) -> ParseAlphabetError {
    let b = bytes[i];
    if !is_valid_b64_symbol_spec(b) {
        ParseAlphabetError::UnprintableByte(b)
    } else if b == padding {
        ParseAlphabetError::ReservedByte(b)
    } else {
        ParseAlphabetError::DuplicatedByte(b)
    }
}

/// The first-violation index (64 = no violation); strictly mirrors the ascending scan
/// of the upstream outer while loop
pub open spec fn first_violation(bytes: Seq<u8>, padding: u8, i: int) -> int
    decreases ALPHABET_LEN as int - i
{
    if i >= ALPHABET_LEN as int {
        ALPHABET_LEN as int
    } else if !clean_at(bytes, padding, i) {
        i
    } else {
        first_violation(bytes, padding, i + 1)
    }
}

/// Origin: alphabet.rs:54 `pub struct Alphabet` -> AlphabetV (sequence model)
pub struct AlphabetV {
    pub symbols: Vec<u8>,
}

impl AlphabetV {
    pub open spec fn as_seq(self) -> Seq<u8> {
        self.symbols@
    }
}

/// Origin: alphabet.rs:84/94 `Alphabet::new` / `new_with_padding`
/// (`&str` -> `&[u8]`; no panic surface: upstream already returns Result.
///  The contract fully characterizes the scan order: InvalidLength / first-violation
///  variant / Ok semantics)
/// Upstream doc (alphabet.rs:88-93):
///   Create an `Alphabet` from a string of 64 unique printable ASCII bytes, with a custom
///   padding symbol.
///   The padding symbol must not appear in the alphabet.
///   This is meant for strange alphabets that don't use `=` as the padding symbol.
pub exec fn alphabet_new_with_padding(
    alphabet: &[u8],
    padding: u8,
) -> (r: Result<AlphabetV, ParseAlphabetError>)
    ensures
        alphabet@.len() != ALPHABET_LEN as int ==> r == Result::Err(
            ParseAlphabetError::InvalidLength,
        ),
        alphabet@.len() == ALPHABET_LEN as int && first_violation(
            alphabet@,
            padding,
            0,
        ) == ALPHABET_LEN as int ==> r.is_ok()
            && r.get_Ok_0().as_seq() == alphabet@,
        alphabet@.len() == ALPHABET_LEN as int && first_violation(
            alphabet@,
            padding,
            0,
        ) < ALPHABET_LEN as int ==> r == Result::Err(
            error_at(alphabet@, padding, first_violation(alphabet@, padding, 0)),
        ),
{
    let ghost bytes = alphabet@;
    /* Origin Rust (alphabet.rs:99): let bytes = alphabet.as_bytes();
       if bytes.len() != ALPHABET_LEN { return Err(ParseAlphabetError::InvalidLength); } */
    if alphabet.len() != ALPHABET_LEN {
        return Result::Err(ParseAlphabetError::InvalidLength);
    }
    /* Origin Rust (alphabet.rs:104-130): the outer while loop -- the triple unprintable
       -> reserved -> duplicated check (the duplicated probe covers the whole domain) */
    let mut index: usize = 0;
    while index < ALPHABET_LEN
        invariant
            0 <= index <= ALPHABET_LEN,
            bytes == alphabet@,
            bytes.len() == ALPHABET_LEN as int,
            forall|j: int| 0 <= j < index as int ==> clean_at(bytes, padding, j),
        decreases ALPHABET_LEN - index
    {
        let byte = alphabet[index];
        assert(byte == bytes[index as int]);

        if !is_valid_b64_symbol(byte) {
            /* Origin Rust: return Err(ParseAlphabetError::UnprintableByte(byte)); */
            proof {
                fv_prefix_clean(bytes, padding, index as int);
                fv_unfold(bytes, padding, index as int);
                assert(first_violation(bytes, padding, 0) == index as int);
                assert(error_at(bytes, padding, index as int) == ParseAlphabetError::UnprintableByte(byte));
                assert(alphabet@ == bytes);
                assert(padding == padding);
                assert(first_violation(bytes, padding, 0) == first_violation(alphabet@, padding, 0));
                assert(first_violation(alphabet@, padding, 0) == index as int);
                assert(error_at(alphabet@, padding, index as int) == ParseAlphabetError::UnprintableByte(byte));
            }
            return Result::Err(ParseAlphabetError::UnprintableByte(byte));
        }
        assert(is_valid_b64_symbol_spec(byte));

        if byte == padding {
            /* Origin Rust: return Err(ParseAlphabetError::ReservedByte(byte)); */
            proof {
                fv_prefix_clean(bytes, padding, index as int);
                fv_unfold(bytes, padding, index as int);
                assert(first_violation(bytes, padding, 0) == index as int);
                assert(error_at(bytes, padding, index as int) == ParseAlphabetError::ReservedByte(byte));
                assert(alphabet@ == bytes);
                assert(first_violation(alphabet@, padding, 0) == index as int);
                assert(error_at(alphabet@, padding, index as int) == ParseAlphabetError::ReservedByte(byte));
            }
            return Result::Err(ParseAlphabetError::ReservedByte(byte));
        }
        assert(byte != padding);
        /* Origin Rust (alphabet.rs:119-126): let mut probe_index = 0;
           while probe_index < ALPHABET_LEN {
               if probe_index != index && byte == bytes[probe_index] {
                   return Err(ParseAlphabetError::DuplicatedByte(byte)); }
               probe_index += 1; } */
        let mut probe_index: usize = 0;
        while probe_index < ALPHABET_LEN
            invariant
                0 <= index < ALPHABET_LEN,
                0 <= probe_index <= ALPHABET_LEN,
                bytes == alphabet@,
                bytes.len() == ALPHABET_LEN as int,
                byte == bytes[index as int],
                is_valid_b64_symbol_spec(byte),
                byte != padding,
                forall|j: int| 0 <= j < index as int ==> clean_at(bytes, padding, j),
                forall|j: int| 0 <= j < probe_index as int ==> j == index as int || bytes[j] != byte,
            decreases ALPHABET_LEN - probe_index
        {
            assert(alphabet[probe_index as int] == bytes[probe_index as int]);
            if probe_index != index && byte == alphabet[probe_index] {
                proof {
                    fv_prefix_clean(bytes, padding, index as int);
                    fv_unfold(bytes, padding, index as int);
                    assert(first_violation(bytes, padding, 0) == index as int);
                    assert(error_at(bytes, padding, index as int) == ParseAlphabetError::DuplicatedByte(byte));
                }
                return Result::Err(ParseAlphabetError::DuplicatedByte(byte));
            }
            probe_index += 1;
        }
        assert(forall|j: int| 0 <= j < ALPHABET_LEN as int ==> j == index as int || bytes[j] != byte);
        index += 1;
    }
    /* Origin Rust (alphabet.rs:64-76): from_str_unchecked -- the const-fn byte-by-byte
       copy -> incremental Vec push construction (semantically equivalent: a 64-element sequence) */
    let mut symbols: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < ALPHABET_LEN
        invariant
            0 <= i <= ALPHABET_LEN,
            bytes == alphabet@,
            bytes.len() == ALPHABET_LEN as int,
            symbols@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> symbols@[j] == bytes[j],
        decreases ALPHABET_LEN - i
    {
        assert(bytes[i as int] == alphabet[i as int]);
        symbols.push(alphabet[i]);
        i += 1;
    }
    proof {
        fv_skip(bytes, padding, 0, ALPHABET_LEN as int);
        assert(first_violation(bytes, padding, 0) >= ALPHABET_LEN as int);
        assert(first_violation(bytes, padding, 0) == ALPHABET_LEN as int) by {
            assert(first_violation(bytes, padding, ALPHABET_LEN as int) == ALPHABET_LEN as int);
        }
        assert(forall|j: int| 0 <= j < ALPHABET_LEN as int ==> symbols@[j] == bytes[j]);
    }
    Result::Ok(AlphabetV { symbols })
}

// ===========================================================================
// Proof lemmas (the first_violation unfold/skip/lower-bound/prefix-clean
// facts; kept at file end so the exec scan reads directly)
// ===========================================================================
/// Lemma 1: the one-step unfold of fv (the seam of the recursive spec)
pub proof fn fv_unfold(bytes: Seq<u8>, padding: u8, i: int)
    requires
        0 <= i < ALPHABET_LEN as int,
    ensures
        clean_at(bytes, padding, i) ==> first_violation(bytes, padding, i)
            == first_violation(bytes, padding, i + 1),
        !clean_at(bytes, padding, i) ==> first_violation(bytes, padding, i) == i,
{
}

/// Lemma 2: no violation from z up to i ==> fv(z) == fv(i)
pub proof fn fv_skip(bytes: Seq<u8>, padding: u8, z: int, i: int)
    requires
        0 <= z <= i <= ALPHABET_LEN as int,
        forall|j: int| z <= j < i ==> clean_at(bytes, padding, j),
    ensures first_violation(bytes, padding, z) == first_violation(bytes, padding, i)
    decreases i - z
{
    if z == i {
    } else {
        fv_skip(bytes, padding, z, i - 1);
        fv_unfold(bytes, padding, i - 1);
    }
}

/// fv(i) >= i (the clean_at definition needs bytes.len() > i)
pub proof fn fv_lower_bound(bytes: Seq<u8>, padding: u8, i: int)
    requires
        0 <= i <= ALPHABET_LEN as int,
        ALPHABET_LEN as int <= bytes.len(),
    ensures first_violation(bytes, padding, i) >= i
    decreases ALPHABET_LEN as int - i
{
    if i >= ALPHABET_LEN as int {
    } else if !clean_at(bytes, padding, i) {
        assert(first_violation(bytes, padding, i) == i);
    } else {
        fv_lower_bound(bytes, padding, i + 1);
    }
}

/// Clean prefix ==> fv(0) == fv(k) >= k (the semantic counterpart of the exec loop invariant)
pub proof fn fv_prefix_clean(bytes: Seq<u8>, padding: u8, k: int)
    requires
        0 <= k <= ALPHABET_LEN as int <= bytes.len(),
        forall|j: int| 0 <= j < k ==> clean_at(bytes, padding, j),
    ensures
        first_violation(bytes, padding, 0) == first_violation(bytes, padding, k),
        first_violation(bytes, padding, k) >= k,
{
    fv_skip(bytes, padding, 0, k);
    fv_lower_bound(bytes, padding, k);
}
} // verus!
