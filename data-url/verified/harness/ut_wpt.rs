//! Transcription of the WPT vector suite (code/data-url/tests/wpt.rs, a
//! custom tester binary): sampled example-vector theorems over the
//! already-verified src-zone spec machines, in three sections mirroring the
//! upstream drivers -- run_data_url over data-urls.json, run_base64 over
//! base64.json, and run_mime over generated-mime-types.json (the
//! mime-types.json vectors live in ut_mime.rs with the machine-eval family).
//! Every theorem states the upstream expectation verbatim (input bytes,
//! expected output bytes); the machine-evaluation technique is the chain
//! of per-byte transition asserts, with reveal fuel sized to the longest
//! single-step chain (out-of-tree probes validated each chain first).
//! Carrier note: literal slices carry opaque spec views in this build, so
//! payloads are built as spec seq values.

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/lib.rs"]
mod datalib;

verus! {

// ================= Section 1: run_data_url (data-urls.json samples) =================

/// data-urls.json vector "data:text/plain,X": the scheme scan and comma
/// split leave the header "text/plain" (parse keeps it, base64 off), body
/// range [16, 17) percent-decoding to the one byte "X".
proof fn w_data_plain()
    ensures
        datalib::data_url_spec(seq![b'd', b'a', b't', b'a', b':', b't', b'e', b'x', b't', 0x2F, b'p', b'l', b'a', b'i', b'n', 0x2C, b'X'])
            == Some(((seq![b't', b'e', b'x', b't'], seq![b'p', b'l', b'a', b'i', b'n'], Seq::empty()), false, 16, 17)),
        datalib::body_dec_spec(seq![b'd', b'a', b't', b'a', b':', b't', b'e', b'x', b't', 0x2F, b'p', b'l', b'a', b'i', b'n', 0x2C, b'X'], 16, 17) == (-1, seq![b'X']),
{
    let s = seq![b'd', b'a', b't', b'a', b':', b't', b'e', b'x', b't', 0x2F, b'p', b'l', b'a', b'i', b'n', 0x2C, b'X'];
    assert(s.len() == 17);
    reveal_with_fuel(datalib::ltrim_c0, 2);
    reveal_with_fuel(datalib::rtrim_c0, 2);
    reveal_with_fuel(datalib::scheme_scan, 2);
    reveal_with_fuel(datalib::comma_scan, 2);
    reveal_with_fuel(datalib::b64tail_scan, 2);
    reveal_with_fuel(datalib::header_enc, 2);
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::mime::find_byte, 7);
    reveal_with_fuel(datalib::mime::all_token, 7);
    reveal_with_fuel(datalib::mime::lower_span, 7);
    reveal_with_fuel(datalib::body_dec_spec, 2);
    assert(datalib::ltrim_c0(s, 0, 17) == 0);
    assert(datalib::scheme_scan(s, 0, 0, 17) == datalib::scheme_scan(s, 1, 1, 17));
    assert(datalib::scheme_scan(s, 1, 1, 17) == datalib::scheme_scan(s, 2, 2, 17));
    assert(datalib::scheme_scan(s, 2, 2, 17) == datalib::scheme_scan(s, 3, 3, 17));
    assert(datalib::scheme_scan(s, 3, 3, 17) == datalib::scheme_scan(s, 4, 4, 17));
    assert(datalib::scheme_scan(s, 4, 4, 17) == datalib::scheme_scan(s, 5, 5, 17));
    assert(datalib::scheme_scan(s, 5, 5, 17) == 5);
    assert(datalib::rtrim_c0(s, 17, 5) == 17);
    assert(datalib::comma_scan(s, 5, 17) == datalib::comma_scan(s, 6, 17));
    assert(datalib::comma_scan(s, 6, 17) == datalib::comma_scan(s, 7, 17));
    assert(datalib::comma_scan(s, 7, 17) == datalib::comma_scan(s, 8, 17));
    assert(datalib::comma_scan(s, 8, 17) == datalib::comma_scan(s, 9, 17));
    assert(datalib::comma_scan(s, 9, 17) == datalib::comma_scan(s, 10, 17));
    assert(datalib::comma_scan(s, 10, 17) == datalib::comma_scan(s, 11, 17));
    assert(datalib::comma_scan(s, 11, 17) == datalib::comma_scan(s, 12, 17));
    assert(datalib::comma_scan(s, 12, 17) == datalib::comma_scan(s, 13, 17));
    assert(datalib::comma_scan(s, 13, 17) == datalib::comma_scan(s, 14, 17));
    assert(datalib::comma_scan(s, 14, 17) == datalib::comma_scan(s, 15, 17));
    assert(datalib::comma_scan(s, 15, 17) == 15);
    // header: "text/plain" with no parameters or suffixes
    assert(datalib::mime::ltrim(s, 5, 15) == 5);
    assert(datalib::mime::rtrim(s, 5, 15) == 15);
    assert(datalib::b64tail_scan(s, 14, 0, 5, 15) == -1);
    assert(datalib::header_enc(s, 5, 15, false)
        == seq![s[5]] + datalib::header_enc(s, 6, 15, false));    assert(datalib::header_enc(s, 6, 15, false)
        == seq![s[6]] + datalib::header_enc(s, 7, 15, false));    assert(datalib::header_enc(s, 7, 15, false)
        == seq![s[7]] + datalib::header_enc(s, 8, 15, false));    assert(datalib::header_enc(s, 8, 15, false)
        == seq![s[8]] + datalib::header_enc(s, 9, 15, false));    assert(datalib::header_enc(s, 9, 15, false)
        == seq![s[9]] + datalib::header_enc(s, 10, 15, false));    assert(datalib::header_enc(s, 10, 15, false)
        == seq![s[10]] + datalib::header_enc(s, 11, 15, false));    assert(datalib::header_enc(s, 11, 15, false)
        == seq![s[11]] + datalib::header_enc(s, 12, 15, false));    assert(datalib::header_enc(s, 12, 15, false)
        == seq![s[12]] + datalib::header_enc(s, 13, 15, false));    assert(datalib::header_enc(s, 13, 15, false)
        == seq![s[13]] + datalib::header_enc(s, 14, 15, false));    assert(datalib::header_enc(s, 14, 15, false)
        == seq![s[14]] + datalib::header_enc(s, 15, 15, false));
    assert(datalib::header_enc(s, 15, 15, false) == Seq::empty());
    assert(seq![b't', b'e', b'x', b't'] + seq![0x2F]
        + seq![b'p', b'l', b'a', b'i', b'n']
        == seq![b't', b'e', b'x', b't', 0x2F, b'p', b'l', b'a', b'i', b'n']);
    assert(datalib::header_enc(s, 5, 15, false) == seq![b't', b'e', b'x', b't', 0x2F, b'p', b'l', b'a', b'i', b'n']);
    assert(datalib::mime::mime_parse_spec(
        seq![b't', b'e', b'x', b't', 0x2F, b'p', b'l', b'a', b'i', b'n'])
        == Some((seq![b't', b'e', b'x', b't'], seq![b'p', b'l', b'a', b'i', b'n'], Seq::empty())));
    assert(datalib::header_spec(s, 5, 15) == ((seq![b't', b'e', b'x', b't'], seq![b'p', b'l', b'a', b'i', b'n'], Seq::empty()), false));
    assert(datalib::body_dec_spec(s, 16, 17) == (-1, seq![b'X']));
    assert(datalib::data_url_spec(s)
        == Some(((seq![b't', b'e', b'x', b't'], seq![b'p', b'l', b'a', b'i', b'n'], Seq::empty()), false, 16, 17)));
}

/// data-urls.json vector "data:;x=x,X": the header starts with ';', so the
/// spec prepends "text/plain" before the re-encode, keeping the parameter
/// piece; body range [10, 11), body "X".
proof fn w_data_semi_param()
    ensures
        datalib::data_url_spec(seq![b'd', b'a', b't', b'a', b':', 0x3B, b'x', 0x3D, b'x', 0x2C, b'X'])
            == Some(((seq![b't', b'e', b'x', b't'], seq![b'p', b'l', b'a', b'i', b'n'],
                seq![(seq![b'x'], seq![b'x'])]), false, 10, 11)),
        datalib::body_dec_spec(seq![b'd', b'a', b't', b'a', b':', 0x3B, b'x', 0x3D, b'x', 0x2C, b'X'], 10, 11) == (-1, seq![b'X']),
{
    let s = seq![b'd', b'a', b't', b'a', b':', 0x3B, b'x', 0x3D, b'x', 0x2C, b'X'];
    assert(s.len() == 11);
    reveal_with_fuel(datalib::ltrim_c0, 2);
    reveal_with_fuel(datalib::rtrim_c0, 2);
    reveal_with_fuel(datalib::scheme_scan, 2);
    reveal_with_fuel(datalib::comma_scan, 2);
    reveal_with_fuel(datalib::b64tail_scan, 2);
    reveal_with_fuel(datalib::header_enc, 2);
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::mime::find_byte, 7);
    reveal_with_fuel(datalib::mime::all_token, 7);
    reveal_with_fuel(datalib::mime::lower_span, 7);
    reveal_with_fuel(datalib::mime::params_spec, 4);
    reveal_with_fuel(datalib::mime::has_name, 2);
    reveal_with_fuel(datalib::mime::all_valid, 4);
    reveal_with_fuel(datalib::body_dec_spec, 2);
    assert(datalib::ltrim_c0(s, 0, 11) == 0);
    // scheme steps
    assert(datalib::scheme_scan(s, 0, 0, 11) == datalib::scheme_scan(s, 1, 1, 11));
    assert(datalib::scheme_scan(s, 1, 1, 11) == datalib::scheme_scan(s, 2, 2, 11));
    assert(datalib::scheme_scan(s, 2, 2, 11) == datalib::scheme_scan(s, 3, 3, 11));
    assert(datalib::scheme_scan(s, 3, 3, 11) == datalib::scheme_scan(s, 4, 4, 11));
    assert(datalib::scheme_scan(s, 4, 4, 11) == datalib::scheme_scan(s, 5, 5, 11));
    assert(datalib::scheme_scan(s, 5, 5, 11) == 5);
    assert(datalib::rtrim_c0(s, 11, 5) == 11);
    // comma steps
    assert(datalib::comma_scan(s, 5, 11) == datalib::comma_scan(s, 6, 11));
    assert(datalib::comma_scan(s, 6, 11) == datalib::comma_scan(s, 7, 11));
    assert(datalib::comma_scan(s, 7, 11) == datalib::comma_scan(s, 8, 11));
    assert(datalib::comma_scan(s, 8, 11) == datalib::comma_scan(s, 9, 11));
    assert(datalib::comma_scan(s, 9, 11) == 9);
    // header ";x=x": datalib::forgiving_base64::prepend text/plain, then the parameter machine
    assert(datalib::mime::ltrim(s, 5, 9) == 5);
    assert(datalib::mime::rtrim(s, 5, 9) == 9);
    assert(datalib::b64tail_scan(s, 8, 0, 5, 9) == -1);
    assert(datalib::header_enc(s, 5, 9, false) == seq![s[5]] + datalib::header_enc(s, 6, 9, false));
    assert(datalib::header_enc(s, 6, 9, false) == seq![s[6]] + datalib::header_enc(s, 7, 9, false));
    assert(datalib::header_enc(s, 7, 9, false) == seq![s[7]] + datalib::header_enc(s, 8, 9, false));
    assert(datalib::header_enc(s, 8, 9, false) == seq![s[8]] + datalib::header_enc(s, 9, 9, false));
    assert(datalib::header_enc(s, 9, 9, false) == Seq::empty());
    // the spec's prepended re-encode: "text/plain" + ";x=x"
    assert(datalib::text_plain()
        == seq![b't', b'e', b'x', b't', 0x2F, b'p', b'l', b'a', b'i', b'n']);
    assert(datalib::header_enc(s, 8, 9, false) == seq![b'x']);
    assert(datalib::header_enc(s, 7, 9, false) == seq![0x3D, b'x']);
    assert(datalib::header_enc(s, 6, 9, false) == seq![b'x', 0x3D, b'x']);
    assert(datalib::header_enc(s, 5, 9, false) == seq![0x3B, b'x', 0x3D, b'x']);
    // parse of that flat header, machine-evaluated on the pieces
    let e2 = seq![b't', b'e', b'x', b't', 0x2F, b'p', b'l', b'a', b'i', b'n',
        0x3B, b'x', 0x3D, b'x'];
    assert(e2.len() == 14);
    assert(datalib::mime::ltrim(e2, 0, 14) == 0);
    assert(datalib::mime::find_byte(e2, 0, 14, 0x2F) == 4);
    assert(datalib::mime::all_token(e2, 0, 4));
    assert(datalib::mime::lower_span(e2, 0, 4) == seq![b't', b'e', b'x', b't']);
    assert(datalib::mime::find_byte(e2, 5, 14, 0x3B) == 10);
    assert(datalib::mime::rtrim(e2, 5, 10) == 10);
    assert(datalib::mime::all_token(e2, 5, 10));
    assert(datalib::mime::lower_span(e2, 5, 10) == seq![b'p', b'l', b'a', b'i', b'n']);
    assert(datalib::mime::params_spec(e2, 11, 14, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(e2, 12, 14, 11, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(e2, 12, 14, 11, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(e2, 13, 14, 11, 12, 13, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(e2, 13, 14, 11, 12, 13, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(e2, 14, 14, 11, 12, 14, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(e2, 14, 14, 11, 12, 14, 2, Seq::empty(), Seq::empty())
        == datalib::mime::unq_push(e2, 11, 12, 14, Seq::empty()));
    assert(datalib::mime::all_token(e2, 11, 12));
    assert(datalib::mime::has_name(Seq::empty(), datalib::mime::slice_seq(e2, 11, 12), 0) == false);
    assert(datalib::mime::all_valid(e2, 13, 14));
    assert(datalib::mime::lower_span(e2, 11, 12) == seq![b'x']);
    assert(datalib::mime::slice_seq(e2, 13, 14) == seq![b'x']);
    assert(datalib::mime::unq_push(e2, 11, 12, 14, Seq::empty())
        == seq![(seq![b'x'], seq![b'x'])]);
    assert(datalib::mime::mime_parse_spec(e2) == Some((seq![b't', b'e', b'x', b't'],
        seq![b'p', b'l', b'a', b'i', b'n'], seq![(seq![b'x'], seq![b'x'])])));
    // and the spec's own composed term agrees
    assert(datalib::text_plain() + seq![0x3B, b'x', 0x3D, b'x'] == e2);
    assert(datalib::mime::mime_parse_spec(datalib::text_plain() + seq![0x3B, b'x', 0x3D, b'x'])
        == Some((seq![b't', b'e', b'x', b't'], seq![b'p', b'l', b'a', b'i', b'n'],
            seq![(seq![b'x'], seq![b'x'])])));
    assert(datalib::header_spec(s, 5, 9) == ((seq![b't', b'e', b'x', b't'],
        seq![b'p', b'l', b'a', b'i', b'n'], seq![(seq![b'x'], seq![b'x'])]), false));
    assert(datalib::body_dec_spec(s, 10, 11) == (-1, seq![b'X']));
    assert(datalib::data_url_spec(s) == Some(((seq![b't', b'e', b'x', b't'],
        seq![b'p', b'l', b'a', b'i', b'n'], seq![(seq![b'x'], seq![b'x'])]),
        false, 10, 11)));
}

/// data-urls.json vector "data:;base64,W%20A": the right-to-left suffix
/// scan strips ";base64" (base64 flag on, fallback mime), the body
/// percent-decodes "%20" to a space which forgiving-base64 whitespace
/// skips, and "WA" decodes to the one byte 88.
proof fn w_data_base64()
    ensures
        datalib::data_url_spec(seq![b'd', b'a', b't', b'a', b':', 0x3B, b'b', b'a',
            b's', b'e', b'6', b'4', 0x2C, b'W', b'%', b'2', b'0', b'A'])
            == Some((datalib::default_mime_triple(), true, 13, 18)),
        datalib::body_dec_spec(seq![b'd', b'a', b't', b'a', b':', 0x3B, b'b', b'a',
            b's', b'e', b'6', b'4', 0x2C, b'W', b'%', b'2', b'0', b'A'], 13, 18)
            == (-1, seq![b'W', 0x20, b'A']),
        datalib::forgiving_base64::dec64_run(datalib::body_dec_spec(seq![b'd', b'a', b't', b'a', b':', 0x3B,
            b'b', b'a', b's', b'e', b'6', b'4', 0x2C, b'W', b'%', b'2', b'0',
            b'A'], 13, 18).1, 0, 0, 0, 0)
            == Ok(seq![88]),
{
    let s = seq![b'd', b'a', b't', b'a', b':', 0x3B, b'b', b'a', b's', b'e',
        b'6', b'4', 0x2C, b'W', b'%', b'2', b'0', b'A'];
    assert(s.len() == 18);
    reveal_with_fuel(datalib::ltrim_c0, 2);
    reveal_with_fuel(datalib::rtrim_c0, 2);
    reveal_with_fuel(datalib::scheme_scan, 2);
    reveal_with_fuel(datalib::comma_scan, 2);
    reveal_with_fuel(datalib::b64tail_scan, 2);
    reveal_with_fuel(datalib::header_enc, 2);
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::body_dec_spec, 2);
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 2);
    assert(datalib::ltrim_c0(s, 0, 18) == 0);
    assert(datalib::scheme_scan(s, 0, 0, 18) == datalib::scheme_scan(s, 1, 1, 18));
    assert(datalib::scheme_scan(s, 1, 1, 18) == datalib::scheme_scan(s, 2, 2, 18));
    assert(datalib::scheme_scan(s, 2, 2, 18) == datalib::scheme_scan(s, 3, 3, 18));
    assert(datalib::scheme_scan(s, 3, 3, 18) == datalib::scheme_scan(s, 4, 4, 18));
    assert(datalib::scheme_scan(s, 4, 4, 18) == datalib::scheme_scan(s, 5, 5, 18));
    assert(datalib::scheme_scan(s, 5, 5, 18) == 5);
    assert(datalib::rtrim_c0(s, 18, 5) == 18);
    // the comma sits right after the suffix
    assert(datalib::comma_scan(s, 5, 18) == datalib::comma_scan(s, 6, 18));
    assert(datalib::comma_scan(s, 6, 18) == datalib::comma_scan(s, 7, 18));
    assert(datalib::comma_scan(s, 7, 18) == datalib::comma_scan(s, 8, 18));
    assert(datalib::comma_scan(s, 8, 18) == datalib::comma_scan(s, 9, 18));
    assert(datalib::comma_scan(s, 9, 18) == datalib::comma_scan(s, 10, 18));
    assert(datalib::comma_scan(s, 10, 18) == datalib::comma_scan(s, 11, 18));
    assert(datalib::comma_scan(s, 11, 18) == datalib::comma_scan(s, 12, 18));
    assert(datalib::comma_scan(s, 12, 18) == 12);
    // header ";base64": the reversed suffix scan matches and yields pos 5
    assert(datalib::mime::ltrim(s, 5, 12) == 5);
    assert(datalib::mime::rtrim(s, 5, 12) == 12);
    assert(datalib::b64tail_scan(s, 11, 0, 5, 12) == datalib::b64tail_scan(s, 10, 1, 5, 12));
    assert(datalib::b64tail_scan(s, 10, 1, 5, 12) == datalib::b64tail_scan(s, 9, 2, 5, 12));
    assert(datalib::b64tail_scan(s, 9, 2, 5, 12) == datalib::b64tail_scan(s, 8, 3, 5, 12));
    assert(datalib::b64tail_scan(s, 8, 3, 5, 12) == datalib::b64tail_scan(s, 7, 4, 5, 12));
    assert(datalib::b64tail_scan(s, 7, 4, 5, 12) == datalib::b64tail_scan(s, 6, 5, 5, 12));
    assert(datalib::b64tail_scan(s, 6, 5, 5, 12) == datalib::b64tail_scan(s, 5, 6, 5, 12));
    assert(datalib::b64tail_scan(s, 5, 6, 5, 12) == 5);
    // the header body is empty: fallback mime, base64 flag set
    assert(datalib::header_enc(s, 5, 5, false) == Seq::empty());
    assert(datalib::mime::mime_parse_spec(Seq::empty()) == None);
    assert(datalib::header_spec(s, 5, 12) == (datalib::default_mime_triple(), true));
    // body "%20" percent-decode and the base64 run
    assert(datalib::hex_val(s[15]) == 2);
    assert(datalib::hex_val(s[16]) == 0);
    assert(datalib::body_dec_spec(s, 17, 18) == (-1, seq![b'A']));
    assert(datalib::body_dec_spec(s, 14, 18) == ((datalib::body_dec_spec(s, 17, 18)).0,
        seq![(2 * 16 + 0) as u8] + (datalib::body_dec_spec(s, 17, 18)).1));
    assert(datalib::body_dec_spec(s, 14, 18) == (-1, seq![0x20, b'A']));
    assert(datalib::body_dec_spec(s, 13, 18) == (-1, seq![b'W', 0x20, b'A']));
    let b = seq![b'W', 0x20, b'A'];
    assert(b.len() == 3);
    assert(datalib::forgiving_base64::dec64_run(b, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(b, 1, 22, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(b, 1, 22, 6, 0) == datalib::forgiving_base64::dec64_run(b, 2, 22, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(b, 2, 22, 6, 0) == datalib::forgiving_base64::dec64_run(b, 3, 1408, 12, 0));
    assert(datalib::forgiving_base64::dec64_run(b, 3, 1408, 12, 0) == Ok(seq![88]));
    assert(datalib::forgiving_base64::dec64_run(datalib::body_dec_spec(s, 13, 18).1, 0, 0, 0, 0) == Ok(seq![88]));
    assert(datalib::data_url_spec(s) == Some((datalib::default_mime_triple(), true, 13, 18)));
}

/// data-urls.json vector "data:,X#X": the '#' cuts the body (fragment
/// start 8, body "X") and the fragment slice percent-encodes to "X"
/// (printable ASCII passes through).
proof fn w_data_fragment()
    ensures
        datalib::data_url_spec(seq![b'd', b'a', b't', b'a', b':', 0x2C, b'X', 0x23,
            b'X']) == Some((datalib::default_mime_triple(), false, 6, 9)),
        datalib::body_dec_spec(seq![b'd', b'a', b't', b'a', b':', 0x2C, b'X', 0x23,
            b'X'], 6, 9) == (8, seq![b'X']),
        datalib::frag_enc_spec(seq![b'd', b'a', b't', b'a', b':', 0x2C, b'X', 0x23,
            b'X'], 8, 9) == seq![b'X'],
{
    let s = seq![b'd', b'a', b't', b'a', b':', 0x2C, b'X', 0x23, b'X'];
    assert(s.len() == 9);
    reveal_with_fuel(datalib::ltrim_c0, 2);
    reveal_with_fuel(datalib::rtrim_c0, 2);
    reveal_with_fuel(datalib::scheme_scan, 2);
    reveal_with_fuel(datalib::comma_scan, 2);
    reveal_with_fuel(datalib::b64tail_scan, 2);
    reveal_with_fuel(datalib::header_enc, 2);
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::body_dec_spec, 2);
    reveal_with_fuel(datalib::frag_enc_spec, 2);
    assert(datalib::ltrim_c0(s, 0, 9) == 0);
    assert(datalib::scheme_scan(s, 0, 0, 9) == datalib::scheme_scan(s, 1, 1, 9));
    assert(datalib::scheme_scan(s, 1, 1, 9) == datalib::scheme_scan(s, 2, 2, 9));
    assert(datalib::scheme_scan(s, 2, 2, 9) == datalib::scheme_scan(s, 3, 3, 9));
    assert(datalib::scheme_scan(s, 3, 3, 9) == datalib::scheme_scan(s, 4, 4, 9));
    assert(datalib::scheme_scan(s, 4, 4, 9) == datalib::scheme_scan(s, 5, 5, 9));
    assert(datalib::scheme_scan(s, 5, 5, 9) == 5);
    assert(datalib::rtrim_c0(s, 9, 5) == 9);
    assert(datalib::comma_scan(s, 5, 9) == 5);
    // the empty header: fallback mime, base64 flag off
    assert(datalib::mime::ltrim(s, 5, 5) == 5);
    assert(datalib::mime::rtrim(s, 5, 5) == 5);
    assert(datalib::b64tail_scan(s, 4, 0, 5, 5) == -1);
    assert(datalib::header_enc(s, 5, 5, false) == Seq::empty());
    assert(datalib::header_spec(s, 5, 5) == (datalib::default_mime_triple(), false));
    // the '#' cuts the body and seeds the fragment
    assert(datalib::body_dec_spec(s, 8, 9) == (-1, seq![b'X']));
    assert(datalib::body_dec_spec(s, 7, 9) == (8, Seq::empty()));
    assert(datalib::body_dec_spec(s, 6, 9) == (8, seq![b'X']));
    assert(datalib::frag_enc_spec(s, 8, 9) == seq![b'X']);
    assert(datalib::data_url_spec(s) == Some((datalib::default_mime_triple(), false, 6, 9)));
}

// ================= Section 2: run_base64 (base64.json samples) =================

/// base64.json vector "": empty input finishing clean with no output.
proof fn w_b64_empty()
    ensures
        datalib::forgiving_base64::dec64_run(seq![], 0, 0, 0, 0) == Ok(Seq::<u8>::empty()),
{
    let s = seq![];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == Ok(Seq::empty()));
}

/// base64.json vector "abcd": a full 24-bit group emits 105 183 29.
proof fn w_b64_abcd()
    ensures
        datalib::forgiving_base64::dec64_run(seq![b'a', b'b', b'c', b'd'], 0, 0, 0, 0)
            == Ok(seq![105, 183, 29]),
{
    let s = seq![b'a', b'b', b'c', b'd'];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0) == datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0) == datalib::forgiving_base64::dec64_run(s, 3, 108252, 18, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 3, 108252, 18, 0)
        == datalib::forgiving_base64::prepend(seq![105, 183, 29], datalib::forgiving_base64::dec64_run(s, 4, 6928157, 0, 0)));
    assert(datalib::forgiving_base64::dec64_run(s, 4, 6928157, 0, 0) == Ok(Seq::empty()));
}

/// base64.json vector "ab": the 12-bit finish emits the truncated byte.
proof fn w_b64_ab()
    ensures
        datalib::forgiving_base64::dec64_run(seq![b'a', b'b'], 0, 0, 0, 0) == Ok(seq![105]),
{
    let s = seq![b'a', b'b'];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0) == datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0) == Ok(seq![105]));
}

/// base64.json vector "ab==": the 12-bit finish with two pads emits 105.
proof fn w_b64_ab_pad()
    ensures
        datalib::forgiving_base64::dec64_run(seq![b'a', b'b', b'=', b'='], 0, 0, 0, 0) == Ok(seq![105]),
{
    let s = seq![b'a', b'b', 0x3D, 0x3D];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0) == datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0) == datalib::forgiving_base64::dec64_run(s, 3, 1691, 12, 1));
    assert(datalib::forgiving_base64::dec64_run(s, 3, 1691, 12, 1) == datalib::forgiving_base64::dec64_run(s, 4, 1691, 12, 2));
    assert(datalib::forgiving_base64::dec64_run(s, 4, 1691, 12, 2) == Ok(seq![105]));
}

/// base64.json vector "abc=": the 18-bit finish with one pad emits two bytes.
proof fn w_b64_abc_pad()
    ensures
        datalib::forgiving_base64::dec64_run(seq![b'a', b'b', b'c', b'='], 0, 0, 0, 0) == Ok(seq![105, 183]),
{
    let s = seq![b'a', b'b', b'c', 0x3D];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0) == datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0) == datalib::forgiving_base64::dec64_run(s, 3, 108252, 18, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 3, 108252, 18, 0) == datalib::forgiving_base64::dec64_run(s, 4, 108252, 18, 1));
    assert(datalib::forgiving_base64::dec64_run(s, 4, 108252, 18, 1) == Ok(seq![105, 183]));
}

/// base64.json vector "a": the lone-alphabet-symbol error at the finish.
proof fn w_b64_a_lone()
    ensures
        datalib::forgiving_base64::dec64_run(seq![b'a'], 0, 0, 0, 0) == Err((2, 0)),
{
    let s = seq![b'a'];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0) == Err((2, 0)));
}

/// base64.json vector "=a": an alphabet symbol after padding errors.
proof fn w_b64_a_after_pad()
    ensures
        datalib::forgiving_base64::dec64_run(seq![b'=', b'a'], 0, 0, 0, 0) == Err((1, 0)),
{
    let s = seq![0x3D, b'a'];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(s, 1, 0, 0, 1));
    assert(datalib::forgiving_base64::dec64_run(s, 1, 0, 0, 1) == Err((1, 0)));
}

/// base64.json vector "abcd===": the group emits, then the three pads end
/// in the padding error.
proof fn w_b64_abcd3pad()
    ensures
        datalib::forgiving_base64::dec64_run(seq![b'a', b'b', b'c', b'd', b'=', b'=', b'='], 0, 0, 0, 0)
            == Err((3, 0)),
{
    let s = seq![b'a', b'b', b'c', b'd', 0x3D, 0x3D, 0x3D];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0) == datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0) == datalib::forgiving_base64::dec64_run(s, 3, 108252, 18, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 3, 108252, 18, 0)
        == datalib::forgiving_base64::prepend(seq![105, 183, 29], datalib::forgiving_base64::dec64_run(s, 4, 6928157, 0, 0)));
    assert(datalib::forgiving_base64::dec64_run(s, 4, 6928157, 0, 0) == datalib::forgiving_base64::dec64_run(s, 5, 6928157, 0, 1));
    assert(datalib::forgiving_base64::dec64_run(s, 5, 6928157, 0, 1) == datalib::forgiving_base64::dec64_run(s, 6, 6928157, 0, 2));
    assert(datalib::forgiving_base64::dec64_run(s, 6, 6928157, 0, 2) == datalib::forgiving_base64::dec64_run(s, 7, 6928157, 0, 3));
    assert(datalib::forgiving_base64::dec64_run(s, 7, 6928157, 0, 3) == Err((3, 0)));
}

/// base64.json vector "\x00nonsense": a symbol outside the alphabet errors
/// immediately with the byte carried.
proof fn w_b64_sym()
    ensures
        datalib::forgiving_base64::dec64_run(seq![0x00, b'n', b'o', b'n', b's', b'e', b'n', b's', b'e'], 0, 0, 0, 0)
            == Err((0, 0x00)),
{
    let s = seq![0x00, b'n', b'o', b'n', b's', b'e', b'n', b's', b'e'];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == Err((0, 0x00)));
}

/// base64.json vector "ab\x0ccd": the form feed is skipped whitespace, the
/// group still decodes to 105 183 29.
proof fn w_b64_formfeed()
    ensures
        datalib::forgiving_base64::dec64_run(seq![b'a', b'b', 0x0C, b'c', b'd'], 0, 0, 0, 0)
            == Ok(seq![105, 183, 29]),
{
    let s = seq![b'a', b'b', 0x0C, b'c', b'd'];
    reveal_with_fuel(datalib::forgiving_base64::dec64_run, 1);
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 1, 26, 6, 0) == datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 2, 1691, 12, 0) == datalib::forgiving_base64::dec64_run(s, 3, 1691, 12, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 3, 1691, 12, 0) == datalib::forgiving_base64::dec64_run(s, 4, 108252, 18, 0));
    assert(datalib::forgiving_base64::dec64_run(s, 4, 108252, 18, 0)
        == datalib::forgiving_base64::prepend(seq![105, 183, 29], datalib::forgiving_base64::dec64_run(s, 5, 6928157, 0, 0)));
    assert(datalib::forgiving_base64::dec64_run(s, 5, 6928157, 0, 0) == Ok(Seq::empty()));
    assert(datalib::forgiving_base64::dec64_run(s, 0, 0, 0, 0) == Ok(seq![105, 183, 29]));
}

// ================= Section 3: run_mime (generated-mime-types.json samples) =================

/// generated-mime-types.json x/x family, byte 0x00 in the type position:
/// the token check fails, parse fails.
proof fn g_typepos_nul()
    ensures
        datalib::mime::mime_parse_spec(seq![0x00, b'/', b'x']) == None,
{
    let s = seq![0x00, b'/', b'x'];
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::mime::find_byte, 3);
    reveal_with_fuel(datalib::mime::all_token, 3);
    assert(datalib::mime::ltrim(s, 0, 3) == 0);
    assert(datalib::mime::rtrim(s, 0, 3) == 3);
    assert(datalib::mime::find_byte(s, 0, 3, 0x2F) == 1);
    assert(datalib::mime::all_token(s, 0, 1) == false);
}

/// generated-mime-types.json x/x family, byte 0x1F in the subtype
/// position: the token check fails, parse fails.
proof fn g_subpos_ctrl()
    ensures
        datalib::mime::mime_parse_spec(seq![b'x', b'/', 0x1F]) == None,
{
    let s = seq![b'x', b'/', 0x1F];
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::mime::find_byte, 3);
    reveal_with_fuel(datalib::mime::all_token, 3);
    assert(datalib::mime::ltrim(s, 0, 3) == 0);
    assert(datalib::mime::rtrim(s, 0, 3) == 3);
    assert(datalib::mime::find_byte(s, 0, 3, 0x2F) == 1);
    assert(datalib::mime::all_token(s, 0, 1));
    assert(datalib::mime::find_byte(s, 2, 3, 0x3B) == 3);
    assert(datalib::mime::rtrim(s, 2, 3) == 3);
    assert(datalib::mime::all_token(s, 2, 3) == false);
}

/// generated-mime-types.json 'x/x;\0=x;bonus=x': the name byte NUL is not
/// a token, so the parameter is dropped and bonus=x survives (upstream
/// output 'x/x;bonus=x').
proof fn g_namepos_nul()
    ensures
        datalib::mime::mime_parse_spec(seq![b'x', b'/', b'x', 0x3B, 0x00, b'=', b'x', 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x'])
            == Some((seq![b'x'], seq![b'x'], seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])])),
        datalib::mime::ser_mime(datalib::mime::mime_parse_spec(seq![b'x', b'/', b'x', 0x3B, 0x00, b'=', b'x', 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x']).unwrap()) == seq![b'x', 0x2F, b'x', 0x3B, b'b', b'o', b'n', b'u', b's', 0x3D, b'x'],
{
    let s = seq![b'x', b'/', b'x', 0x3B, 0x00, b'=', b'x', 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x'];
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::mime::find_byte, 6);
    reveal_with_fuel(datalib::mime::all_token, 7);
    reveal_with_fuel(datalib::mime::lower_span, 8);
    reveal_with_fuel(datalib::mime::params_spec, 4);
    reveal_with_fuel(datalib::mime::has_name, 2);
    reveal_with_fuel(datalib::mime::all_valid, 4);
    reveal_with_fuel(datalib::mime::ser_params, 2);
    assert(s.len() == 15);
    assert(datalib::mime::ltrim(s, 0, 15) == 0);
    assert(datalib::mime::rtrim(s, 0, 15) == 15);
    assert(datalib::mime::find_byte(s, 0, 15, 0x2F) == 1);
    assert(datalib::mime::all_token(s, 0, 1));
    assert(datalib::mime::find_byte(s, 2, 15, 0x3B) == 3);
    assert(datalib::mime::rtrim(s, 2, 3) == 3);
    assert(datalib::mime::all_token(s, 2, 3));
    // piece 1 fails the name check: the NUL byte is not a token
    assert(datalib::mime::params_spec(s, 4, 15, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 5, 15, 4, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 5, 15, 4, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 6, 15, 4, 5, 6, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 6, 15, 4, 5, 6, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 7, 15, 4, 5, 7, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 7, 15, 4, 5, 7, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 8, 15, -1, -1, -1, 0, Seq::empty(),
            datalib::mime::unq_push(s, 4, 5, 7, Seq::empty())));
    assert(datalib::mime::all_token(s, 4, 5) == false);
    assert(datalib::mime::unq_push(s, 4, 5, 7, Seq::empty()) == Seq::empty());
    // piece 2: bonus=x is fresh and valid
    assert(datalib::mime::params_spec(s, 8, 15, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 9, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 9, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 10, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 10, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 11, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 11, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 12, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 12, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 13, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 13, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 14, 15, 8, 13, 14, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 14, 15, 8, 13, 14, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 15, 15, 8, 13, 15, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 15, 15, 8, 13, 15, 2, Seq::empty(), Seq::empty())
        == datalib::mime::unq_push(s, 8, 13, 15, Seq::empty()));
    assert(datalib::mime::all_token(s, 8, 13));
    assert(datalib::mime::has_name(Seq::empty(), datalib::mime::slice_seq(s, 8, 13), 0) == false);
    assert(datalib::mime::all_valid(s, 14, 15));
    assert(datalib::mime::lower_span(s, 8, 13) == seq![b'b', b'o', b'n', b'u', b's']);
    assert(datalib::mime::slice_seq(s, 14, 15) == seq![b'x']);
    assert(Seq::empty()
        + seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]
        == seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]);
    assert(datalib::mime::unq_push(s, 8, 13, 15, Seq::empty()) == seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]);
    // serialization: the all-token survivor goes out raw
    assert(datalib::mime::ser_value(seq![b'x']) == seq![b'x']);
    assert(datalib::mime::ser_params(seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])], 1) == Seq::empty());
    assert(datalib::mime::ser_params(seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])], 0)
        == seq![0x3B] + seq![b'b', b'o', b'n', b'u', b's'] + seq![0x3D]
            + seq![b'x']);
    assert(datalib::mime::ser_mime((seq![b'x'], seq![b'x'], seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])])) == seq![b'x', 0x2F, b'x', 0x3B, b'b', b'o', b'n', b'u', b's', 0x3D, b'x']);
}

/// generated-mime-types.json 'x/x;x=\0;bonus=x': the unquoted value byte
/// NUL is not a valid value byte, so the parameter is dropped
/// (upstream output 'x/x;bonus=x').
proof fn g_valpos_nul()
    ensures
        datalib::mime::mime_parse_spec(seq![b'x', b'/', b'x', 0x3B, b'x', b'=', 0x00, 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x'])
            == Some((seq![b'x'], seq![b'x'], seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])])),
{
    let s = seq![b'x', b'/', b'x', 0x3B, b'x', b'=', 0x00, 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x'];
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::mime::find_byte, 6);
    reveal_with_fuel(datalib::mime::all_token, 7);
    reveal_with_fuel(datalib::mime::lower_span, 8);
    reveal_with_fuel(datalib::mime::params_spec, 4);
    reveal_with_fuel(datalib::mime::has_name, 2);
    reveal_with_fuel(datalib::mime::all_valid, 4);
    assert(s.len() == 15);
    assert(datalib::mime::ltrim(s, 0, 15) == 0);
    assert(datalib::mime::rtrim(s, 0, 15) == 15);
    assert(datalib::mime::find_byte(s, 0, 15, 0x2F) == 1);
    assert(datalib::mime::all_token(s, 0, 1));
    assert(datalib::mime::find_byte(s, 2, 15, 0x3B) == 3);
    assert(datalib::mime::rtrim(s, 2, 3) == 3);
    assert(datalib::mime::all_token(s, 2, 3));
    // piece 1 fails the value-validity check
    assert(datalib::mime::params_spec(s, 4, 15, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 5, 15, 4, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 5, 15, 4, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 6, 15, 4, 5, 6, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 6, 15, 4, 5, 6, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 7, 15, 4, 5, 7, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 7, 15, 4, 5, 7, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 8, 15, -1, -1, -1, 0, Seq::empty(),
            datalib::mime::unq_push(s, 4, 5, 7, Seq::empty())));
    assert(datalib::mime::all_token(s, 4, 5));
    assert(datalib::mime::has_name(Seq::empty(), datalib::mime::slice_seq(s, 4, 5), 0) == false);
    assert(datalib::mime::all_valid(s, 6, 7) == false);
    assert(datalib::mime::unq_push(s, 4, 5, 7, Seq::empty()) == Seq::empty());
    // piece 2: bonus=x survives
    assert(datalib::mime::params_spec(s, 8, 15, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 9, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 9, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 10, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 10, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 11, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 11, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 12, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 12, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 13, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 13, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 14, 15, 8, 13, 14, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 14, 15, 8, 13, 14, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 15, 15, 8, 13, 15, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 15, 15, 8, 13, 15, 2, Seq::empty(), Seq::empty())
        == datalib::mime::unq_push(s, 8, 13, 15, Seq::empty()));
    assert(datalib::mime::all_token(s, 8, 13));
    assert(datalib::mime::has_name(Seq::empty(), datalib::mime::slice_seq(s, 8, 13), 0) == false);
    assert(datalib::mime::all_valid(s, 14, 15));
    assert(datalib::mime::lower_span(s, 8, 13) == seq![b'b', b'o', b'n', b'u', b's']);
    assert(datalib::mime::slice_seq(s, 14, 15) == seq![b'x']);
    assert(Seq::empty()
        + seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]
        == seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]);
    assert(datalib::mime::unq_push(s, 8, 13, 15, Seq::empty()) == seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]);
    assert(datalib::mime::mime_parse_spec(s) == Some((seq![b'x'], seq![b'x'], seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])])));
}

/// generated-mime-types.json 'x/x;x="\0";bonus=x': the raw quoted-value
/// validity fails on the NUL inside the raw span, so the parameter is
/// dropped (upstream output 'x/x;bonus=x').
proof fn g_qpos_nul()
    ensures
        datalib::mime::mime_parse_spec(seq![b'x', b'/', b'x', 0x3B, b'x', b'=', 0x22, 0x00, 0x22, 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x'])
            == Some((seq![b'x'], seq![b'x'], seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])])),
{
    let s = seq![b'x', b'/', b'x', 0x3B, b'x', b'=', 0x22, 0x00, 0x22, 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x'];
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::mime::find_byte, 6);
    reveal_with_fuel(datalib::mime::all_token, 7);
    reveal_with_fuel(datalib::mime::lower_span, 8);
    reveal_with_fuel(datalib::mime::params_spec, 4);
    reveal_with_fuel(datalib::mime::has_name, 2);
    reveal_with_fuel(datalib::mime::all_valid, 4);
    reveal_with_fuel(datalib::mime::valid_upto, 3);
    assert(s.len() == 17);
    assert(datalib::mime::ltrim(s, 0, 17) == 0);
    assert(datalib::mime::rtrim(s, 0, 17) == 17);
    assert(datalib::mime::find_byte(s, 0, 17, 0x2F) == 1);
    assert(datalib::mime::all_token(s, 0, 1));
    assert(datalib::mime::find_byte(s, 2, 17, 0x3B) == 3);
    assert(datalib::mime::rtrim(s, 2, 3) == 3);
    assert(datalib::mime::all_token(s, 2, 3));
    // piece 1 opens the quoted form, scans the NUL, closes on the quote
    assert(datalib::mime::params_spec(s, 4, 17, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 5, 17, 4, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 5, 17, 4, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 6, 17, 4, 5, 6, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 6, 17, 4, 5, 6, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 7, 17, 4, 5, -1, 4, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 7, 17, 4, 5, -1, 4, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 8, 17, 4, 5, -1, 4, seq![0x00], Seq::empty()));
    // the raw-value validity fails: NUL inside the raw quoted span
    assert(datalib::mime::valid_upto(s, 6, 17) == false);
    assert(datalib::mime::all_token(s, 4, 5));
    assert(datalib::mime::has_name(Seq::empty(), datalib::mime::slice_seq(s, 4, 5), 0) == false);
    assert(datalib::mime::params_spec(s, 8, 17, 4, 5, -1, 4, seq![0x00], Seq::empty())
        == datalib::mime::params_spec(s, 9, 17, -1, -1, -1, 3, Seq::empty(), Seq::empty()));
    // stage 3 discards to the piece boundary, then bonus=x survives
    assert(datalib::mime::params_spec(s, 9, 17, -1, -1, -1, 3, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 10, 17, -1, -1, -1, 0, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 10, 17, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 11, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 11, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 12, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 12, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 13, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 13, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 14, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 14, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 15, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 15, 17, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 16, 17, 10, 15, 16, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 16, 17, 10, 15, 16, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 17, 17, 10, 15, 17, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 17, 17, 10, 15, 17, 2, Seq::empty(), Seq::empty())
        == datalib::mime::unq_push(s, 10, 15, 17, Seq::empty()));
    assert(datalib::mime::all_token(s, 10, 15));
    assert(datalib::mime::has_name(Seq::empty(), datalib::mime::slice_seq(s, 10, 15), 0) == false);
    assert(datalib::mime::all_valid(s, 16, 17));
    assert(datalib::mime::lower_span(s, 10, 15) == seq![b'b', b'o', b'n', b'u', b's']);
    assert(datalib::mime::slice_seq(s, 16, 17) == seq![b'x']);
    assert(Seq::empty()
        + seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]
        == seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]);
    assert(datalib::mime::unq_push(s, 10, 15, 17, Seq::empty()) == seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]);
    assert(datalib::mime::mime_parse_spec(s) == Some((seq![b'x'], seq![b'x'], seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])])));
}

/// generated-mime-types.json 'x/x;\=x;bonus=x': the name byte backslash
/// is not a token, so the parameter is dropped (upstream output
/// 'x/x;bonus=x').
proof fn g_namepos_backslash()
    ensures
        datalib::mime::mime_parse_spec(seq![b'x', b'/', b'x', 0x3B, 0x5C, b'=', b'x', 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x'])
            == Some((seq![b'x'], seq![b'x'], seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])])),
{
    let s = seq![b'x', b'/', b'x', 0x3B, 0x5C, b'=', b'x', 0x3B, b'b', b'o', b'n', b'u', b's', b'=', b'x'];
    reveal_with_fuel(datalib::mime::ltrim, 2);
    reveal_with_fuel(datalib::mime::rtrim, 2);
    reveal_with_fuel(datalib::mime::find_byte, 6);
    reveal_with_fuel(datalib::mime::all_token, 7);
    reveal_with_fuel(datalib::mime::lower_span, 8);
    reveal_with_fuel(datalib::mime::params_spec, 4);
    reveal_with_fuel(datalib::mime::has_name, 2);
    reveal_with_fuel(datalib::mime::all_valid, 4);
    assert(s.len() == 15);
    assert(datalib::mime::ltrim(s, 0, 15) == 0);
    assert(datalib::mime::rtrim(s, 0, 15) == 15);
    assert(datalib::mime::find_byte(s, 0, 15, 0x2F) == 1);
    assert(datalib::mime::all_token(s, 0, 1));
    assert(datalib::mime::find_byte(s, 2, 15, 0x3B) == 3);
    assert(datalib::mime::rtrim(s, 2, 3) == 3);
    assert(datalib::mime::all_token(s, 2, 3));
    // piece 1 fails the name check (backslash is not a token)
    assert(datalib::mime::params_spec(s, 4, 15, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 5, 15, 4, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 5, 15, 4, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 6, 15, 4, 5, 6, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 6, 15, 4, 5, 6, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 7, 15, 4, 5, 7, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 7, 15, 4, 5, 7, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 8, 15, -1, -1, -1, 0, Seq::empty(),
            datalib::mime::unq_push(s, 4, 5, 7, Seq::empty())));
    assert(datalib::mime::all_token(s, 4, 5) == false);
    assert(datalib::mime::unq_push(s, 4, 5, 7, Seq::empty()) == Seq::empty());
    // piece 2: bonus=x survives
    assert(datalib::mime::all_token(s, 8, 13));
    assert(datalib::mime::has_name(Seq::empty(), datalib::mime::slice_seq(s, 8, 13), 0) == false);
    assert(datalib::mime::all_valid(s, 14, 15));
    assert(datalib::mime::lower_span(s, 8, 13) == seq![b'b', b'o', b'n', b'u', b's']);
    assert(datalib::mime::slice_seq(s, 14, 15) == seq![b'x']);
    assert(Seq::empty()
        + seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]
        == seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]);
    assert(datalib::mime::unq_push(s, 8, 13, 15, Seq::empty()) == seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])]);
    assert(datalib::mime::params_spec(s, 8, 15, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 9, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 9, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 10, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 10, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 11, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 11, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 12, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 12, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 13, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 13, 15, 8, -1, -1, 1, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 14, 15, 8, 13, 14, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 14, 15, 8, 13, 14, 2, Seq::empty(), Seq::empty())
        == datalib::mime::params_spec(s, 15, 15, 8, 13, 15, 2, Seq::empty(), Seq::empty()));
    assert(datalib::mime::params_spec(s, 15, 15, 8, 13, 15, 2, Seq::empty(), Seq::empty())
        == datalib::mime::unq_push(s, 8, 13, 15, Seq::empty()));
    assert(datalib::mime::mime_parse_spec(s) == Some((seq![b'x'], seq![b'x'], seq![(seq![b'b', b'o', b'n', b'u', b's'], seq![b'x'])])));
}

fn main() {}
}

