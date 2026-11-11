//! Transcription of the crate doc example (code/data-url/src/lib.rs:5-15,
//! with `"data:,Hello%20World!"`) at its smallest shadow inputs, plus one
//! representative arm of the data-url processor spec machines: the empty
//! header falls back to text/plain;charset=US-ASCII, the comma splits header
//! and body, and the body range covers the remainder.
//! Reference-style structure: `#[path = "../src/lib.rs"] mod datalib;` --
//! no spec of its own; the expectations below are the upstream ones.
//! Carrier note: literal slices carry opaque spec views in this build, so
//! the payloads are built as spec seq values.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod datalib;

verus! {

/// The doc example's header arm: "data:,X" processes to the default mime
/// (empty header) with a one-byte body range and no base64 flag.
proof fn ut_doc_example_header_arm()
    ensures
        datalib::data_url_spec(
            seq![b'd', b'a', b't', b'a', b':', b',', b'X'])
        == Some((
            datalib::default_mime_triple(),
            false,
            6,
            7,
        )),
{
    reveal_with_fuel(datalib::ltrim_c0, 8);
    reveal_with_fuel(datalib::rtrim_c0, 8);
    reveal_with_fuel(datalib::scheme_scan, 8);
    reveal_with_fuel(datalib::comma_scan, 8);
    reveal_with_fuel(datalib::b64tail_scan, 8);
    reveal_with_fuel(datalib::header_enc, 8);
    // header of the empty string: no base64, parse falls back
    assert(datalib::header_spec(
        seq![b'd', b'a', b't', b'a', b':', b',', b'X'],
        5, 5).1 == false);
    assert(datalib::header_enc(
        seq![b'd', b'a', b't', b'a', b':', b',', b'X'],
        5, 5, false) == Seq::empty());
}

/// The processor's scheme arm at the smallest scale: "DATA:,X"
/// (case-insensitive scheme) processes to the same shape.
proof fn ut_scheme_case_insensitive()
    ensures
        datalib::data_url_spec(
            seq![b'D', b'A', b'T', b'A', b':', b',', b'X'])
        == Some((
            datalib::default_mime_triple(),
            false,
            6,
            7,
        )),
{
    reveal_with_fuel(datalib::ltrim_c0, 8);
    reveal_with_fuel(datalib::rtrim_c0, 8);
    reveal_with_fuel(datalib::scheme_scan, 8);
    reveal_with_fuel(datalib::comma_scan, 8);
    reveal_with_fuel(datalib::b64tail_scan, 8);
    reveal_with_fuel(datalib::header_enc, 8);
    assert(datalib::header_spec(
        seq![b'D', b'A', b'T', b'A', b':', b',', b'X'],
        5, 5).1 == false);
    assert(datalib::header_enc(
        seq![b'D', b'A', b'T', b'A', b':', b',', b'X'],
        5, 5, false) == Seq::empty());
}

fn main() {}
}
