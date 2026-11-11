//! Transcription of the Display byte faces for the error carriers as
//! assertion exemplars over the src-zone mirrors: DataUrlError Display
//! (upstream lib.rs:54-64) and the InvalidBase64 / DecodeError message
//! family (upstream forgiving_base64.rs:11-24 and 59-66) carried by
//! B64Error. fmt::Display has no vstd spec, so the upstream messages are
//! carried by the display_bytes / wrapped_display_bytes byte serializers
//! in the src zone; each exemplar here pins the message literals the
//! mirrors write (length plus the same-literal slice_seq identity the
//! spec arms state). The remaining exposed Display arm -- the generic
//! write-error E of DecodeError -- is the blocked closure/carrier face
//! recorded in the inventory ledger.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod datalib;

verus! {

/// DataUrlError Display exemplars: both arms write the upstream messages.
exec fn ut_dataurl_err_display() {
    let e1 = datalib::DataUrlError::NotADataUrl;
    let m1 = e1.display_bytes();
    assert(m1@ == datalib::data_url_err_msg(&e1));
    assert(m1@ == datalib::mime::slice_seq(b"not a valid data url"@, 0, 20));
    assert(m1@.len() == 20);
    let e2 = datalib::DataUrlError::NoComma;
    let m2 = e2.display_bytes();
    assert(m2@ == datalib::data_url_err_msg(&e2));
    assert(m2@ == datalib::mime::slice_seq(
        b"data url is missing comma delimiting attributes and body"@,
        0,
        56,
    ));
    assert(m2@.len() == 56);
}

/// The InvalidBase64 message family exemplars: the carried byte prints as
/// its lowercase decimal expansion (the WPT base64.json "\0nonsense" vector
/// end-to-end leaves UnexpectedSymbol(0): "symbol with codepoint 0 not
/// expected" is 36 bytes), the other three kind messages verbatim.
exec fn ut_b64_err_display() {
    let e = datalib::forgiving_base64::B64Error::UnexpectedSymbol(0);
    let m = e.display_bytes();
    assert(m@ == datalib::b64_err_msg(&e));
    assert(datalib::dec_u8(0) == seq![0x30]);
    assert(m@ == datalib::mime::slice_seq(b"symbol with codepoint "@, 0, 22)
        + seq![0x30]
        + datalib::mime::slice_seq(b" not expected"@, 0, 13));
    assert(m@.len() == 36);

    let e1 = datalib::forgiving_base64::B64Error::AlphabetSymbolAfterPadding;
    let m1 = e1.display_bytes();
    assert(m1@ == datalib::b64_err_msg(&e1));
    assert(m1@ == datalib::mime::slice_seq(
        b"alphabet symbol present after padding"@,
        0,
        37,
    ));
    assert(m1@.len() == 37);

    let e2 = datalib::forgiving_base64::B64Error::LoneAlphabetSymbol;
    let m2 = e2.display_bytes();
    assert(m2@ == datalib::b64_err_msg(&e2));
    assert(m2@ == datalib::mime::slice_seq(
        b"lone alphabet symbol present"@,
        0,
        28,
    ));
    assert(m2@.len() == 28);

    let e3 = datalib::forgiving_base64::B64Error::Padding;
    let m3 = e3.display_bytes();
    assert(m3@ == datalib::b64_err_msg(&e3));
    assert(m3@ == datalib::mime::slice_seq(b"incorrect padding"@, 0, 17));
    assert(m3@.len() == 17);
}

/// The DecodeError blanket-arm payload exemplar: 18 bytes of prefix plus
/// the inner message (54 bytes for the carried code point 0 variant).
exec fn ut_b64_wrapper_prefix() {
    let e = datalib::forgiving_base64::B64Error::UnexpectedSymbol(0);
    let w = e.wrapped_display_bytes();
    assert(w@ == datalib::decode_err_msg(&e));
    assert(w@ == datalib::mime::slice_seq(b"base64 not valid: "@, 0, 18)
        + datalib::b64_err_msg(&e));
    assert(w@.len() == 18 + 36);
}

/// Byte-level spot-checking of the mirrored literals (m@.index(0) == b'n'
/// style) is beyond this build: the literal-slice view stays opaque below
/// slice_seq identity and length pins, the assertion level folded into the
/// exemplars above. Recorded as a machine limitation in the ledger, not
/// as a coverage gap of the mirrors (the spec arms reference the same
/// literals the mirrors write, closing by identity).

fn main() {}

}
