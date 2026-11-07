//! harness: the case-table lemmas of the src/alphabet.rs UTs (the ten tests at alphabet.rs:294-404)
//!
//! Reference-style organization: `#[path]` includes verified/src/lib.rs.
//! Semantic load: the full scan-order contract of alphabet_new_with_padding (Ok semantics
//! / first-violation variant).
//! Any assertion failure is the three-way attribution starting point against the upstream UT expectations.
//!
//! Run: verus database/base64/verified/harness/ut_alphabet.rs

use vstd::prelude::*;

#[path = "../src/lib.rs"]
mod b64;

use b64::alphabet::{alphabet_new_with_padding, AlphabetV, ParseAlphabetError};

// harness helper: pulls the src-side lemma surface to consume exec callee contract premises
use b64::alphabet::first_violation;
use b64::alphabet::fv_prefix_clean;

verus! {

/// The standard alphabet sequence (the spec form of code/src/alphabet.rs:251 STANDARD)
pub open spec fn std_seq() -> Seq<u8> {
    Seq::new(
        64,
        |i: int|
            if 0 <= i < 26 {
                (65 + i) as u8
            } else if 26 <= i < 52 {
                (97 + (i - 26)) as u8
            } else if 52 <= i < 62 {
                (48 + (i - 52)) as u8
            } else if i == 62 {
                43u8 /* '+' */
            } else {
                47u8 /* '/' */
            },
    )
}

/// All 64 bytes of this input are clean (printable, not '=', pairwise distinct)
pub open spec fn all_clean(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < 64 ==> b64::alphabet::clean_at(s, 61, i)
}

/// UT str_same_as_unchecked / same_as_unchecked (alphabet.rs:357):
/// the standard 64-byte string has no violation under the scan order ==> Ok and symbols == input
pub exec fn ok_case(s: &[u8]) -> (r: Result<AlphabetV, ParseAlphabetError>)
    requires
        s@ == std_seq(),
        all_clean(s@),
{
    proof {
        fv_prefix_clean(s@, 61u8, 64);
    }
    assert(first_violation(s@, 61u8, 0) == 64);
    let rr = alphabet_new_with_padding(s, 61);
    assert(rr.is_ok());
    assert(rr.get_Ok_0().as_seq() == s@);
    rr
}

/// UT detects_unprintable (alphabet.rs:348): first byte \\x0c (form feed)
pub exec fn unprintable_case(s: &[u8]) -> (r: Result<AlphabetV, ParseAlphabetError>)
    requires
        s@ == std_seq().update(0, 12),
{
    proof {
        assert(s@[0] == 12u8);
        assert(!b64::alphabet::clean_at(s@, 61u8, 0));
        assert(first_violation(s@, 61u8, 0) == 0);
    }
    let rr = alphabet_new_with_padding(s, 61);
    assert(rr == Result::Err(ParseAlphabetError::UnprintableByte(12)));
    rr
}

/// UT detects_duplicate_start (alphabet.rs:300): bytes[1] equals bytes[0], both 'A'
pub exec fn dup_start_case(s: &[u8]) -> (r: Result<AlphabetV, ParseAlphabetError>)
    requires
        s@ == std_seq().update(1, 65),
        forall|j: int| 0 <= j < 1 ==> b64::alphabet::clean_at(s@, 61u8, j),
{
    proof {
        fv_prefix_clean(s@, 61u8, 1);
        assert(s@[0] == s@[1]);
        assert(!b64::alphabet::clean_at(s@, 61u8, 0));
        assert(first_violation(s@, 61u8, 0) == 0);
    }
    let rr = alphabet_new_with_padding(s, 61);
    assert(rr == Result::Err(ParseAlphabetError::DuplicatedByte(65)));
    rr
}

/// UT detects_padding (alphabet.rs:337): the trailing '=' hits ReservedByte
pub exec fn padding_case(s: &[u8]) -> (r: Result<AlphabetV, ParseAlphabetError>)
    requires
        s@ == std_seq().update(63, 61),
        forall|j: int| 0 <= j < 63 ==> b64::alphabet::clean_at(s@, 61u8, j),
{
    proof {
        fv_prefix_clean(s@, 61u8, 63);
        assert(s@[63] == 61u8);
        assert(!b64::alphabet::clean_at(s@, 61u8, 63));
        assert(first_violation(s@, 61u8, 0) == 63);
    }
    let rr = alphabet_new_with_padding(s, 61);
    assert(rr == Result::Err(ParseAlphabetError::ReservedByte(61)));
    rr
}

/// UT detects_length (alphabet.rs:326): length != 64
pub exec fn length_case(s: &[u8]) -> (r: Result<AlphabetV, ParseAlphabetError>)
    requires
        s@.len() != 64,
{
    let rr = alphabet_new_with_padding(s, 61);
    assert(rr == Result::Err(ParseAlphabetError::InvalidLength));
    rr
}

} // verus!

fn main() {}
