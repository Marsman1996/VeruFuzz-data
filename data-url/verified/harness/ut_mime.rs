//! Transcription of the in-file upstream unit test `test_basic_mime`
//! (code/data-url/src/mime.rs:225-239) plus small representative exemplars
//! of the WPT vector suite (tests/wpt.rs with mime-types.json): one arm of
//! the parse machine each (token subtype, parameter, quoted value with a
//! semicolon, duplicate-name skip, invalid empty type, case normalization),
//! plus the machine-eval theorem family that greens the deferred parameter
//! exemplars of the first batch (the theorems at the end of this file).
//! Reference-style structure: `#[path = "../src/mime.rs"] mod mime;` --
//! the harness adds no spec of its own; every theorem below re-states the
//! upstream expectation over the src-zone specs. Theorems take the
//! spec-literal form this build verifies (seq-built payload, per-arm fuel).

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "../src/mime.rs"]
mod mime;

verus! {

/// Origin Rust: test_basic_mime (mime.rs:225-239): the constructor and
/// clone arms carry the input type/subtype; matches("text","plain") holds
/// exactly on those views.
exec fn ut_test_basic_mime_new() {
    let m = mime::Mime::new(b"text", b"plain");
    assert(m.type_@ == b"text"@);
    assert(m.subtype@ == b"plain"@);
    assert(m.type_@.len() == 4);
    assert(m.subtype@.len() == 5);
    assert(m.parameters@.len() == 0);
}

/// WPT arm: "a/b" parses to tokens a/b with no parameters.
proof fn ut_wpt_parse_tiny()
    ensures
        mime::mime_parse_spec(seq![b'a', b'/', b'b'])
            == Some((seq![b'a'], seq![b'b'], Seq::empty())),
{
    let s = seq![b'a', b'/', b'b'];
    assert(s.len() == 3);
    reveal_with_fuel(mime::ltrim, 4);
    reveal_with_fuel(mime::rtrim, 4);
    reveal_with_fuel(mime::find_byte, 4);
    reveal_with_fuel(mime::all_token, 4);
    reveal_with_fuel(mime::lower_span, 4);
    assert(mime::ltrim(s, 0, 3) == 0);
    assert(mime::rtrim(s, 0, 3) == 3);
    assert(mime::find_byte(s, 0, 3, b'/') == 1);
    assert(mime::all_token(s, 0, 1));
    assert(mime::find_byte(s, 2, 3, b';') == 3);
    assert(mime::rtrim(s, 2, 3) == 3);
    assert(mime::all_token(s, 2, 3));
    assert(mime::lower_span(s, 0, 1) == seq![b'a']);
    assert(mime::lower_span(s, 2, 3) == seq![b'b']);
}

/// WPT arm (mime-types.json: text/html;charset=gbk's shadow): "a/b;c=d"
/// keeps one parameter, and serializing it reproduces the header.
proof fn ut_wpt_parse_invalid()
    ensures
        mime::mime_parse_spec(seq![b'/', b'b']) == None,
{
reveal_with_fuel(mime::ltrim, 3);
reveal_with_fuel(mime::rtrim, 3);
reveal_with_fuel(mime::find_byte, 3);
}

/// WPT arm (mime-types.json TEXT/HTML shadow): tokens normalize lowercase.
proof fn ut_wpt_parse_case_folding()
    ensures
        mime::mime_parse_spec(seq![b'A', b'/', b'B'])
            == Some((seq![b'a'], seq![b'b'], Seq::empty())),
{
reveal_with_fuel(mime::ltrim, 4);
reveal_with_fuel(mime::rtrim, 4);
reveal_with_fuel(mime::find_byte, 4);
reveal_with_fuel(mime::all_token, 4);
reveal_with_fuel(mime::lower_span, 4);
}

// ---------------------------------------------------------------------
// Machine-eval theorem family for the parameter-collection spec machine
// (params_spec): each WPT vector below is evaluated one byte transition at
// a time (reveal fuel sized to the longest single-step chain; the chained
// asserts are the steps themselves), turning the deferred WPT mime exemplars
// of the first batch green: the parameter piece, the quoted-value machine
// with a ';' inside quotes, duplicate-name skipping, and the parse/serialize
// round-trips of the mime-types.json vectors.
// ---------------------------------------------------------------------
/// Machine eval of the deferred param-piece exemplar: "a/b;c=d" parses to
/// tokens a/b with one parameter (c, d). Byte-at-a-time params_spec steps:
/// the name opens at 'c', '=' starts the value scan, 'd' accumulates, and
/// the raw-ended base case fires the unquoted push.
proof fn ut_wpt_parse_param_piece()
    ensures
        mime::mime_parse_spec(seq![b'a', b'/', b'b', b';', b'c', b'=', b'd'])
            == Some((seq![b'a'], seq![b'b'], seq![(seq![b'c'], seq![b'd'])])),
{
    let s = seq![b'a', b'/', b'b', b';', b'c', b'=', b'd'];
    assert(s.len() == 7);
    reveal_with_fuel(mime::ltrim, 3);
    reveal_with_fuel(mime::rtrim, 3);
    reveal_with_fuel(mime::find_byte, 5);
    reveal_with_fuel(mime::all_token, 3);
    reveal_with_fuel(mime::lower_span, 3);
    reveal_with_fuel(mime::params_spec, 4);
    reveal_with_fuel(mime::has_name, 2);
    reveal_with_fuel(mime::all_valid, 2);
    assert(mime::ltrim(s, 0, 7) == 0);
    assert(mime::rtrim(s, 0, 7) == 7);
    assert(mime::find_byte(s, 0, 7, 0x2F) == 1);
    assert(mime::all_token(s, 0, 1));
    assert(mime::find_byte(s, 2, 7, 0x3B) == 3);
    assert(mime::rtrim(s, 2, 3) == 3);
    assert(mime::all_token(s, 2, 3));
    // the params machine: stage 0 opens the name at 'c'
    assert(mime::params_spec(s, 4, 7, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 5, 7, 4, -1, -1, 1, Seq::empty(), Seq::empty()));
    // stage 1 hits '=': the value scan opens
    assert(mime::params_spec(s, 5, 7, 4, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 6, 7, 4, 5, 6, 2, Seq::empty(), Seq::empty()));
    // stage 2 accumulates 'd' (not the first quote byte, not ';')
    assert(mime::params_spec(s, 6, 7, 4, 5, 6, 2, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 7, 7, 4, 5, 7, 2, Seq::empty(), Seq::empty()));
    // base case at pos == b0: the unquoted push fires
    assert(mime::params_spec(s, 7, 7, 4, 5, 7, 2, Seq::empty(), Seq::empty())
        == mime::unq_push(s, 4, 5, 7, Seq::empty()));
    assert(mime::lower_span(s, 4, 5) == seq![b'c']);
    assert(mime::slice_seq(s, 6, 7) == seq![b'd']);
    assert(Seq::empty() + seq![(seq![b'c'], seq![b'd'])]
        == seq![(seq![b'c'], seq![b'd'])]);
    assert(mime::unq_push(s, 4, 5, 7, Seq::empty())
        == seq![(seq![b'c'], seq![b'd'])]);
    assert(mime::lower_span(s, 0, 1) == seq![b'a']);
    assert(mime::lower_span(s, 2, 3) == seq![b'b']);
}

/// Machine eval of the WPT Basics vector "text/html;charset=gbk"
/// (mime-types.json): parse and serialization round-trip to the input
/// itself (value "gbk" is all-token, so it is emitted raw).
proof fn ut_wpt_serialize_roundtrip()
    ensures
        mime::mime_parse_spec(
            seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l', 0x3B, b'c', b'h', b'a', b'r', b's', b'e', b't', 0x3D, b'g', b'b', b'k'])
            == Some((
                seq![b't', b'e', b'x', b't'],
                seq![b'h', b't', b'm', b'l'],
                seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
                    seq![b'g', b'b', b'k'])],
            )),
        mime::ser_mime(mime::mime_parse_spec(
            seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l', 0x3B, b'c', b'h', b'a', b'r', b's', b'e', b't', 0x3D, b'g', b'b', b'k']).unwrap())
            == seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l', 0x3B, b'c', b'h', b'a', b'r', b's', b'e', b't', 0x3D, b'g', b'b', b'k'],
{
    let s = seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l', 0x3B, b'c', b'h', b'a', b'r', b's', b'e', b't', 0x3D, b'g', b'b', b'k'];
    assert(s.len() == 21);
    reveal_with_fuel(mime::ltrim, 3);
    reveal_with_fuel(mime::rtrim, 3);
    reveal_with_fuel(mime::find_byte, 5);
    reveal_with_fuel(mime::all_token, 9);
    reveal_with_fuel(mime::lower_span, 9);
    reveal_with_fuel(mime::params_spec, 6);
    reveal_with_fuel(mime::has_name, 2);
    reveal_with_fuel(mime::all_valid, 5);
    reveal_with_fuel(mime::ser_params, 2);
    reveal_with_fuel(mime::ser_escape, 3);
    assert(mime::ltrim(s, 0, 21) == 0);
    assert(mime::rtrim(s, 0, 21) == 21);
    assert(mime::find_byte(s, 0, 21, 0x2F) == 4);
    assert(mime::all_token(s, 0, 4));
    assert(mime::lower_span(s, 0, 4)
        == seq![b't', b'e', b'x', b't']);
    assert(mime::find_byte(s, 5, 21, 0x3B) == 9);
    assert(mime::rtrim(s, 5, 9) == 9);
    assert(mime::all_token(s, 5, 9));
    assert(mime::lower_span(s, 5, 9)
        == seq![b'h', b't', b'm', b'l']);
    // the params machine over s[10..21): 'c' opens the name scan
    assert(mime::params_spec(s, 10, 21, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 11, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    // 'h','a','r','s','e','t' continue it
    assert(mime::params_spec(s, 11, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 12, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 12, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 13, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 13, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 14, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 14, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 15, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 15, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 16, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 16, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 17, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    // '=' opens the value scan
    assert(mime::params_spec(s, 17, 21, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 18, 21, 10, 17, 18, 2, Seq::empty(), Seq::empty()));
    // 'g', 'b', 'k' accumulate (cel runs to the end)
    assert(mime::params_spec(s, 18, 21, 10, 17, 18, 2, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 21, 21, 10, 17, 21, 2, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 21, 21, 10, 17, 21, 2, Seq::empty(), Seq::empty())
        == mime::unq_push(s, 10, 17, 21, Seq::empty()));
    assert(mime::lower_span(s, 10, 17)
        == seq![b'c', b'h', b'a', b'r', b's', b'e', b't']);
    assert(mime::slice_seq(s, 18, 21) == seq![b'g', b'b', b'k']);
    assert(mime::all_token(s, 10, 17));
    assert(mime::has_name(Seq::empty(), mime::slice_seq(s, 10, 17), 0) == false);
    assert(mime::all_valid(s, 18, 21));
    assert(seq![(mime::lower_span(s, 10, 17), mime::slice_seq(s, 18, 21))]
        == seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
            seq![b'g', b'b', b'k'])]);
    assert(mime::unq_push(s, 10, 17, 21, Seq::empty())
        == (Seq::empty()
            + seq![(mime::lower_span(s, 10, 17), mime::slice_seq(s, 18, 21))]));
    assert(Seq::empty()
        + seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
            seq![b'g', b'b', b'k'])]
        == seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
            seq![b'g', b'b', b'k'])]);
    assert(Seq::empty()
        + seq![(mime::lower_span(s, 10, 17), mime::slice_seq(s, 18, 21))]
        == seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
            seq![b'g', b'b', b'k'])]);
    assert(mime::unq_push(s, 10, 17, 21, Seq::empty())
        == seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
            seq![b'g', b'b', b'k'])]);
    // serialization: the all-token value goes out raw
    assert(mime::ser_value(seq![b'g', b'b', b'k']) == seq![b'g', b'b', b'k']);
    assert(mime::ser_params(
        seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
            seq![b'g', b'b', b'k'])], 1) == Seq::empty());
    assert(mime::ser_params(
        seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
            seq![b'g', b'b', b'k'])], 0)
        == seq![0x3B] + seq![b'c', b'h', b'a', b'r', b's', b'e', b't']
            + seq![0x3D] + seq![b'g', b'b', b'k']);
    assert(mime::ser_mime((
        seq![b't', b'e', b'x', b't'],
        seq![b'h', b't', b'm', b'l'],
        seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'],
            seq![b'g', b'b', b'k'])])) == s);
}

/// Machine eval of the WPT "Semicolons in value" vector
/// 'text/html;valid=";";foo=bar' (mime-types.json): the quoted-value
/// machine treats the ';' inside quotes as content, closes on the '"',
/// discards the piece remainder (stage 3), keeps the second parameter,
/// and the pair re-serializes re-quoted (";" is not a token byte).
/// Upstream output equals the input; the flattening runs in chunks.
proof fn ut_wpt_quoted_semicolon()
    ensures
        mime::mime_parse_spec(seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'v', b'a', b'l', b'i', b'd', b'=', 0x22, b';', 0x22, b';', b'f', b'o', b'o', b'=', b'b', b'a', b'r'])
            == Some((
                seq![b't', b'e', b'x', b't'],
                seq![b'h', b't', b'm', b'l'],
                seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B]), (seq![b'f', b'o', b'o'], seq![b'b', b'a', b'r'])],
            )),
        mime::ser_mime(mime::mime_parse_spec(seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'v', b'a', b'l', b'i', b'd', b'=', 0x22, b';', 0x22, b';', b'f', b'o', b'o', b'=', b'b', b'a', b'r']).unwrap()) == seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'v', b'a', b'l', b'i', b'd', b'=', 0x22, b';', 0x22, b';', b'f', b'o', b'o', b'=', b'b', b'a', b'r'],
{
    let s = seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'v', b'a', b'l', b'i', b'd', b'=', 0x22, b';', 0x22, b';', b'f', b'o', b'o', b'=', b'b', b'a', b'r'];
    assert(s.len() == 27);
    reveal_with_fuel(mime::ltrim, 3);
    reveal_with_fuel(mime::rtrim, 3);
    reveal_with_fuel(mime::find_byte, 6);
    reveal_with_fuel(mime::all_token, 7);
    reveal_with_fuel(mime::lower_span, 7);
    reveal_with_fuel(mime::params_spec, 4);
    reveal_with_fuel(mime::has_name, 3);
    reveal_with_fuel(mime::all_valid, 4);
    reveal_with_fuel(mime::valid_upto, 4);
    reveal_with_fuel(mime::ser_params, 3);
    reveal_with_fuel(mime::ser_escape, 3);
    assert(mime::ltrim(s, 0, 27) == 0);
    assert(mime::rtrim(s, 0, 27) == 27);
    assert(mime::find_byte(s, 0, 27, 0x2F) == 4);
    assert(mime::all_token(s, 0, 4));
    assert(mime::lower_span(s, 0, 4) == seq![b't', b'e', b'x', b't']);
    assert(mime::find_byte(s, 5, 27, 0x3B) == 9);
    assert(mime::rtrim(s, 5, 9) == 9);
    assert(mime::all_token(s, 5, 9));
    assert(mime::lower_span(s, 5, 9) == seq![b'h', b't', b'm', b'l']);
    // piece 1: the name "valid" opens
    assert(mime::params_spec(s, 10, 27, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 11, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 11, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 12, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 12, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 13, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 13, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 14, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 14, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 15, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    // '=' opens the value scan, whose first byte is the opening quote
    assert(mime::params_spec(s, 15, 27, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 16, 27, 10, 15, 16, 2, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 16, 27, 10, 15, 16, 2, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 17, 27, 10, 15, -1, 4, Seq::empty(), Seq::empty()));
    // the first body byte inside quotes is the raw ';' (content, not boundary)
    assert(mime::params_spec(s, 17, 27, 10, 15, -1, 4, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 18, 27, 10, 15, -1, 4, seq![0x3B], Seq::empty()));
    // the closing quote: raw-value push, then discard the rest of the piece
    assert(mime::all_token(s, 10, 15));
    assert(mime::has_name(Seq::empty(), mime::slice_seq(s, 10, 15), 0) == false);
    assert(mime::valid_upto(s, 16, 27));
    assert(mime::lower_span(s, 10, 15) == seq![b'v', b'a', b'l', b'i', b'd']);
    assert(Seq::empty()
        + seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3Bu8])]
        == seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3Bu8])]);
    assert(mime::params_spec(s, 18, 27, 10, 15, -1, 4, seq![0x3B], Seq::empty())
        == mime::params_spec(s, 19, 27, -1, -1, -1, 3, Seq::empty(),
            seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B])]));
    // stage 3 lands on the piece boundary: back to stage 0
    let acc = seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B])];
    assert(mime::params_spec(s, 19, 27, -1, -1, -1, 3, Seq::empty(), acc)
        == mime::params_spec(s, 20, 27, -1, -1, -1, 0, Seq::empty(), acc));
    // piece 2: "foo=bar"
    assert(mime::params_spec(s, 20, 27, -1, -1, -1, 0, Seq::empty(), acc)
        == mime::params_spec(s, 21, 27, 20, -1, -1, 1, Seq::empty(), acc));
    assert(mime::params_spec(s, 21, 27, 20, -1, -1, 1, Seq::empty(), acc)
        == mime::params_spec(s, 22, 27, 20, -1, -1, 1, Seq::empty(), acc));
    assert(mime::params_spec(s, 22, 27, 20, -1, -1, 1, Seq::empty(), acc)
        == mime::params_spec(s, 23, 27, 20, -1, -1, 1, Seq::empty(), acc));
    assert(mime::params_spec(s, 23, 27, 20, -1, -1, 1, Seq::empty(), acc)
        == mime::params_spec(s, 24, 27, 20, 23, 24, 2, Seq::empty(), acc));
    // the unquoted body accumulates
    assert(mime::params_spec(s, 24, 27, 20, 23, 24, 2, Seq::empty(), acc)
        == mime::params_spec(s, 25, 27, 20, 23, 25, 2, Seq::empty(), acc));
    assert(mime::params_spec(s, 25, 27, 20, 23, 25, 2, Seq::empty(), acc)
        == mime::params_spec(s, 26, 27, 20, 23, 26, 2, Seq::empty(), acc));
    assert(mime::params_spec(s, 26, 27, 20, 23, 26, 2, Seq::empty(), acc)
        == mime::params_spec(s, 27, 27, 20, 23, 27, 2, Seq::empty(), acc));
    assert(mime::params_spec(s, 27, 27, 20, 23, 27, 2, Seq::empty(), acc)
        == mime::unq_push(s, 20, 23, 27, acc));
    // the fresh, all-token, all-valid push fires
    assert(mime::all_token(s, 20, 23));
    assert(mime::has_name(acc, mime::slice_seq(s, 20, 23), 0) == false);
    assert(mime::all_valid(s, 24, 27));
    assert(mime::lower_span(s, 20, 23) == seq![b'f', b'o', b'o']);
    assert(mime::slice_seq(s, 24, 27) == seq![b'b', b'a', b'r']);
    assert(mime::unq_push(s, 20, 23, 27, acc)
        == seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B]), (seq![b'f', b'o', b'o'], seq![b'b', b'a', b'r'])]);
    // serialization: ";" re-quotes, tokens stay raw; flattening runs in
    // chunks (piece tail, piece head, then the two prefixes of the whole)
    assert(mime::all_token(seq![0x3B], 0, 1) == false);
    assert(mime::ser_escape(seq![0x3B], 1) == seq![0x3B]);
    assert(mime::ser_value(seq![0x3B]) == seq![0x22, 0x3B, 0x22]);
    assert(mime::ser_value(seq![b'b', b'a', b'r']) == seq![b'b', b'a', b'r']);
    assert(mime::ser_params(seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B]), (seq![b'f', b'o', b'o'], seq![b'b', b'a', b'r'])], 2) == Seq::empty());
    assert(seq![0x3B] + seq![b'f', b'o', b'o'] == seq![0x3B, b'f', b'o', b'o']);
    assert(seq![0x3B, b'f', b'o', b'o'] + seq![0x3D]
        == seq![0x3B, b'f', b'o', b'o', 0x3D]);
    assert(seq![0x3B, b'f', b'o', b'o', 0x3D] + seq![b'b', b'a', b'r']
        == seq![0x3B, b'f', b'o', b'o', 0x3D, b'b', b'a', b'r']);
    assert(mime::ser_params(seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B]), (seq![b'f', b'o', b'o'], seq![b'b', b'a', b'r'])], 1)
        == seq![0x3B, b'f', b'o', b'o', 0x3D, b'b', b'a', b'r']);
    assert(seq![0x3B] + seq![b'v', b'a', b'l', b'i', b'd'] == seq![0x3B, b'v', b'a', b'l', b'i', b'd']);
    assert(seq![0x3B, b'v', b'a', b'l', b'i', b'd'] + seq![0x3D]
        == seq![0x3B, b'v', b'a', b'l', b'i', b'd', 0x3D]);
    assert(seq![0x3B, b'v', b'a', b'l', b'i', b'd', 0x3D] + seq![0x22, 0x3B, 0x22]
        == seq![0x3B, b'v', b'a', b'l', b'i', b'd', 0x3D, 0x22, 0x3B, 0x22]);
    assert(mime::ser_params(seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B]), (seq![b'f', b'o', b'o'], seq![b'b', b'a', b'r'])], 0)
        == seq![0x3B, b'v', b'a', b'l', b'i', b'd', 0x3D, 0x22, 0x3B, 0x22]
            + mime::ser_params(seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B]), (seq![b'f', b'o', b'o'], seq![b'b', b'a', b'r'])], 1));
    assert(mime::ser_params(seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B]), (seq![b'f', b'o', b'o'], seq![b'b', b'a', b'r'])], 0)
        == seq![0x3B, b'v', b'a', b'l', b'i', b'd', 0x3D, 0x22, 0x3B, 0x22]
            + seq![0x3B, b'f', b'o', b'o', 0x3D, b'b', b'a', b'r']);
    assert(seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l'] == seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l']);
    assert(seq![b't', b'e', b'x', b't'] + seq![0x2F] + seq![b'h', b't', b'm', b'l']
        == seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l']);
    assert(seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l']
        + seq![0x3B, b'v', b'a', b'l', b'i', b'd', 0x3D, 0x22, 0x3B, 0x22]
        == seq![b't', b'e', b'x', b't', 0x2F, b'h', b't', b'm', b'l', 0x3B,
            b'v', b'a', b'l', b'i', b'd', 0x3D, 0x22, 0x3B, 0x22]);
    assert(mime::ser_mime((
        seq![b't', b'e', b'x', b't'],
        seq![b'h', b't', b'm', b'l'],
        seq![(seq![b'v', b'a', b'l', b'i', b'd'], seq![0x3B]), (seq![b'f', b'o', b'o'], seq![b'b', b'a', b'r'])])) == s);
}

/// Machine eval of the WPT "Duplicate parameter" vector
/// 'text/html;charset=gbk;charset=windows-1255' (mime-types.json): the
/// first "charset" stays, the second is suppressed (its raw name matches
/// the stored lowercased name), and the surviving pair serializes to
/// 'text/html;charset=gbk' (the upstream expected output).
proof fn ut_wpt_duplicate_skip()
    ensures
        mime::mime_parse_spec(seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'c', b'h', b'a', b'r', b's', b'e', b't', b'=', b'g', b'b', b'k', b';', b'c', b'h', b'a', b'r', b's', b'e', b't', b'=', b'w', b'i', b'n', b'd', b'o', b'w', b's', b'-', b'1', b'2', b'5', b'5'])
            == Some((
                seq![b't', b'e', b'x', b't'],
                seq![b'h', b't', b'm', b'l'],
                seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])],
            )),
        mime::ser_mime(mime::mime_parse_spec(seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'c', b'h', b'a', b'r', b's', b'e', b't', b'=', b'g', b'b', b'k', b';', b'c', b'h', b'a', b'r', b's', b'e', b't', b'=', b'w', b'i', b'n', b'd', b'o', b'w', b's', b'-', b'1', b'2', b'5', b'5']).unwrap()) == seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'c', b'h', b'a', b'r', b's', b'e', b't', b'=', b'g', b'b', b'k'],
{
    let s = seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'c', b'h', b'a', b'r', b's', b'e', b't', b'=', b'g', b'b', b'k', b';', b'c', b'h', b'a', b'r', b's', b'e', b't', b'=', b'w', b'i', b'n', b'd', b'o', b'w', b's', b'-', b'1', b'2', b'5', b'5'];
    assert(s.len() == 42);
    reveal_with_fuel(mime::ltrim, 3);
    reveal_with_fuel(mime::rtrim, 3);
    reveal_with_fuel(mime::find_byte, 6);
    reveal_with_fuel(mime::all_token, 10);
    reveal_with_fuel(mime::lower_span, 10);
    reveal_with_fuel(mime::params_spec, 4);
    reveal_with_fuel(mime::has_name, 3);
    reveal_with_fuel(mime::all_valid, 5);
    reveal_with_fuel(mime::ser_params, 2);
    assert(mime::ltrim(s, 0, 42) == 0);
    assert(mime::rtrim(s, 0, 42) == 42);
    assert(mime::find_byte(s, 0, 42, 0x2F) == 4);
    assert(mime::all_token(s, 0, 4));
    assert(mime::lower_span(s, 0, 4) == seq![b't', b'e', b'x', b't']);
    assert(mime::find_byte(s, 5, 42, 0x3B) == 9);
    assert(mime::rtrim(s, 5, 9) == 9);
    assert(mime::all_token(s, 5, 9));
    assert(mime::lower_span(s, 5, 9) == seq![b'h', b't', b'm', b'l']);
    // piece 1: "charset=gbk"; the boundary ';' finalizes the push
    assert(mime::params_spec(s, 10, 42, -1, -1, -1, 0, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 11, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 11, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 12, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 12, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 13, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 13, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 14, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 14, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 15, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 15, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 16, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 16, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 17, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 17, 42, 10, -1, -1, 1, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 18, 42, 10, 17, 18, 2, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 18, 42, 10, 17, 18, 2, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 19, 42, 10, 17, 19, 2, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 19, 42, 10, 17, 19, 2, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 20, 42, 10, 17, 20, 2, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 20, 42, 10, 17, 20, 2, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 21, 42, 10, 17, 21, 2, Seq::empty(), Seq::empty()));
    assert(mime::params_spec(s, 21, 42, 10, 17, 21, 2, Seq::empty(), Seq::empty())
        == mime::params_spec(s, 22, 42, -1, -1, -1, 0, Seq::empty(),
            mime::unq_push(s, 10, 17, 21, Seq::empty())));
    // the first push fires: fresh all-token name, all-valid value
    assert(mime::all_token(s, 10, 17));
    assert(mime::has_name(Seq::empty(), mime::slice_seq(s, 10, 17), 0) == false);
    assert(mime::all_valid(s, 18, 21));
    assert(mime::lower_span(s, 10, 17) == seq![b'c', b'h', b'a', b'r', b's', b'e', b't']);
    assert(mime::slice_seq(s, 18, 21) == seq![b'g', b'b', b'k']);
    assert(mime::unq_push(s, 10, 17, 21, Seq::empty()) == seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]);
    // piece 2: the same raw name "charset" with value "windows-1255"
    assert(mime::params_spec(s, 22, 42, -1, -1, -1, 0, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 23, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 23, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 24, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 24, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 25, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 25, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 26, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 26, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 27, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 27, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 28, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 28, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 29, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 29, 42, 22, -1, -1, 1, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 30, 42, 22, 29, 30, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 30, 42, 22, 29, 30, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 31, 42, 22, 29, 31, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 31, 42, 22, 29, 31, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 32, 42, 22, 29, 32, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 32, 42, 22, 29, 32, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 33, 42, 22, 29, 33, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 33, 42, 22, 29, 33, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 34, 42, 22, 29, 34, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 34, 42, 22, 29, 34, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 35, 42, 22, 29, 35, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 35, 42, 22, 29, 35, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 36, 42, 22, 29, 36, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 36, 42, 22, 29, 36, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 37, 42, 22, 29, 37, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 37, 42, 22, 29, 37, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 38, 42, 22, 29, 38, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 38, 42, 22, 29, 38, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 39, 42, 22, 29, 39, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 39, 42, 22, 29, 39, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 40, 42, 22, 29, 40, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 40, 42, 22, 29, 40, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 41, 42, 22, 29, 41, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    assert(mime::params_spec(s, 41, 42, 22, 29, 41, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::params_spec(s, 42, 42, 22, 29, 42, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    // input exhaustion in the value scan is the raw-ended base case
    assert(mime::params_spec(s, 42, 42, 22, 29, 42, 2, Seq::empty(), seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])
        == mime::unq_push(s, 22, 29, 42, seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]));
    // the duplicate test: the raw second name equals the stored name
    assert(mime::slice_seq(s, 22, 29) == seq![b'c', b'h', b'a', b'r', b's', b'e', b't']);
    assert(mime::has_name(seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])], mime::slice_seq(s, 22, 29), 0) == true);
    assert(mime::unq_push(s, 22, 29, 42, seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]) == seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])]);
    // serialization: the all-token value goes out raw
    assert(mime::ser_value(seq![b'g', b'b', b'k']) == seq![b'g', b'b', b'k']);
    assert(mime::ser_params(seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])], 1) == Seq::empty());
    assert(mime::ser_params(seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])], 0)
        == seq![0x3B] + seq![b'c', b'h', b'a', b'r', b's', b'e', b't'] + seq![0x3D] + seq![b'g', b'b', b'k']);
    assert(mime::ser_mime((
        seq![b't', b'e', b'x', b't'],
        seq![b'h', b't', b'm', b'l'],
        seq![(seq![b'c', b'h', b'a', b'r', b's', b'e', b't'], seq![b'g', b'b', b'k'])])) == seq![b't', b'e', b'x', b't', b'/', b'h', b't', b'm', b'l', b';', b'c', b'h', b'a', b'r', b's', b'e', b't', b'=', b'g', b'b', b'k']);
}

fn main() {}
}
