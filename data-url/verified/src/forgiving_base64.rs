//! data-url 0.3.2 @ servo/rust-url 00a6ce58; module forgiving_base64.
//! Upstream source: database/data-url/code/data-url/src/forgiving_base64.rs
//! (all line references below are that upstream file's line numbers).
//! <https://infra.spec.whatwg.org/#forgiving-base64-decode>
//! Zone: this file's sole scope is the forgiving-base64 decoder: section A the
//!   spec model (the dec64_run state machine mirroring the feed loop lines
//!   109-149 and the finish match lines 153-171 one-to-one), section B the exec
//!   transcription (an Origin Rust note on every executable change).
//! Carrier decisions: the generic closure writer `F: FnMut(&[u8]) ->
//!   Result<(), E>` of Decoder (line 85) is blocked for quantification in this
//!   build; every obligation face carries the writer as the concrete buffer
//!   accumulator `out: &mut Vec<u8>` -- exactly the decode_to_vec face (line 71).
//!   The B64Error enum is the public data carrier mirroring InvalidBase64Details
//!   (lines 27-33); the InvalidBase64/DecodeError<E>/Impossible name wrappers
//!   and all Display/Error/From/Debug faces are out of zone (fmt has no vstd
//!   spec; presentation-only names with no obligation target).
//! Domain facts: an alphabet symbol contributes value in 0..=63; the u32
//!   bit_buffer arithmetic wraps mod 2^32 (the << re-expressions keep the exact
//!   wrap-around semantics); buffer_bit_length in {0,6,12,18} between symbols;
//!   padding_symbols saturates at 255.

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

// ================= Section A: the data carrier and the spec model =================

/// Origin Rust (lines 27-33):
///     enum InvalidBase64Details {
///         UnexpectedSymbol(u8), AlphabetSymbolAfterPadding,
///         LoneAlphabetSymbol, Padding,
///     }
/// The public carrier enum; it also carries the InvalidBase64/DecodeError<E>
/// name wrappers' payload per the file-header carrier note.
#[derive(Debug)]
pub enum B64Error {
    UnexpectedSymbol(u8),
    AlphabetSymbolAfterPadding,
    LoneAlphabetSymbol,
    Padding,
}

/// Spec kind view of B64Error (custom enum == is not usable in spec/ensures in
/// this build; all comparisons go through this view): the dec64_run error
/// payload convention is 0 = UnexpectedSymbol(b), 1 = AlphabetSymbolAfterPadding,
/// 2 = LoneAlphabetSymbol, 3 = Padding.
pub open spec fn kind_of(e: B64Error) -> int {
    match e {
        B64Error::UnexpectedSymbol(_) => 0,
        B64Error::AlphabetSymbolAfterPadding => 1,
        B64Error::LoneAlphabetSymbol => 2,
        B64Error::Padding => 3,
    }
}

/// Spec symbol view of B64Error: the carried offending byte (0 when the variant
/// carries no byte).
pub open spec fn sym_of(e: B64Error) -> u8 {
    match e {
        B64Error::UnexpectedSymbol(b) => b,
        B64Error::AlphabetSymbolAfterPadding => 0,
        B64Error::LoneAlphabetSymbol => 0,
        B64Error::Padding => 0,
    }
}

/// Origin Rust: the BASE64_DECODE_TABLE lookup (lines 111, 183-201):
/// `BASE64_DECODE_TABLE[byte as usize]`, -1 for symbols not in the alphabet
/// (RFC 4648 Table 1). The 256-entry table is kept as compiled data below the
/// verus zone; a universal spec model of it is not tractable in this build, so
/// the exec lookup is carried by b64_val_exec, an unfolded range/lookup chain
/// computing identical values.
pub open spec fn b64_val(b: u8) -> int {
    if b >= 0x41 && b <= 0x5A {
        b as int - 0x41
    } else if b >= 0x61 && b <= 0x7A {
        b as int - 0x61 + 26
    } else if b >= 0x30 && b <= 0x39 {
        b as int - 0x30 + 52
    } else if b == 0x2B {
        62
    } else if b == 0x2F {
        63
    } else {
        -1
    }
}

/// Origin Rust (line 116): the ASCII-whitespace removal set of the feed loop,
/// `matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | b'\x0C')`.
pub open spec fn b64_ws(b: u8) -> bool {
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D || b == 0x0C
}

/// Prepends emitted bytes to a run result: Ok appends, Err passes through.
pub open spec fn prepend(p: Seq<u8>, r: Result<Seq<u8>, (int, u8)>) -> Result<Seq<u8>, (int, u8)> {
    match r {
        Ok(rest) => Ok(p + rest),
        Err(k) => Err(k),
    }
}

/// The full decode machine from arbitrary state: dec64_run(input, i, buf, bits,
/// pad) is the forgiving-base64 run of input[i..] from the decoder state
/// (bit_buffer = buf mod 2^32, buffer_bit_length = bits, padding_symbols = pad).
/// The i >= s.len() branch is the finish() match (lines 153-171): (0, 0) emits
/// nothing (line 155), (12, 2)/(12, 0) emits buf >> 4 truncated (line 160),
/// (18, 1)/(18, 0) emits buf >> 10 and buf >> 2 truncated (line 166), bits == 6
/// is the lone-alphabet error (line 169), everything else the padding error
/// (line 170). The loop branch is the feed loop (lines 110-147): an alphabet
/// symbol accumulates `buf <<= 6; buf |= value` (lines 130-131) as the mod-2^32
/// product (upstream never resets bit_buffer after an emit, lines 144-145; the
/// % 256 truncation of each per-byte read below keeps that faithful), a 24-bit
/// group emits bit_buffer >> 16, >> 8 and truncated (lines 137-141), an
/// alphabet symbol after padding is the error of lines 127-129, whitespace is
/// skipped (line 118), '=' bumps padding_symbols saturating (line 121), and
/// any other symbol is the unexpected-symbol error of line 125 (byte
/// included). `as u8` upstream is the % 256 truncation of each division.
pub open spec fn dec64_run(s: Seq<u8>, i: int, buf: int, bits: int, pad: int) -> Result<Seq<u8>, (int, u8)>
    recommends
        0 <= i <= s.len() && 0 <= buf < 4294967296,
        bits == 0 || bits == 6 || bits == 12 || bits == 18,
        0 <= pad <= 255,
    decreases s.len() - i
{
    if i >= s.len() {
        // the finish() match (lines 153-171)
        if bits == 0 && pad == 0 {
            Ok(Seq::empty())
        } else if bits == 12 && (pad == 2 || pad == 0) {
            Ok(seq![((buf / 16) % 256) as u8])
        } else if bits == 18 && (pad == 1 || pad == 0) {
            Ok(seq![((buf / 1024) % 256) as u8, ((buf / 4) % 256) as u8])
        } else if bits == 6 {
            Err((2, 0))
        } else {
            Err((3, 0))
        }
    } else {
        let b = s[i];
        let v = b64_val(b);
        if v >= 0 {
            if pad > 0 {
                Err((1, 0))
            } else {
                let nb = (buf * 64 + v) % 4294967296;
                if bits < 18 {
                    dec64_run(s, i + 1, nb, bits + 6, pad)
                } else {
                    prepend(
                        seq![((nb / 65536) % 256) as u8, ((nb / 256) % 256) as u8, (nb % 256) as u8],
                        dec64_run(s, i + 1, nb, 0, pad),
                    )
                }
            }
        } else if b64_ws(b) {
            dec64_run(s, i + 1, buf, bits, pad)
        } else if b == 0x3D {
            let np = if pad + 1 > 255 { 255 } else { pad + 1 };
            dec64_run(s, i + 1, buf, bits, np)
        } else {
            Err((0, b))
        }
    }
}

// ================= Section B: the exec transcription =================

/// Exec carrier of the BASE64_DECODE_TABLE lookup (line 111); the range/lookup
/// chain computes the table's identical values.
pub exec fn b64_val_exec(byte: u8) -> (v: i8)
    ensures v as int == b64_val(byte)
{
    /* Origin Rust: let value = BASE64_DECODE_TABLE[byte as usize];
     * The 256-entry table has no tractable universal spec model in this build;
     * this chain unfolds the RFC 4648 classification directly. */
    if byte >= b'A' && byte <= b'Z' {
        (byte - b'A') as i8
    } else if byte >= b'a' && byte <= b'z' {
        (byte - b'a' + 26) as i8
    } else if byte >= b'0' && byte <= b'9' {
        (byte - b'0' + 52) as i8
    } else if byte == b'+' {
        62
    } else if byte == b'/' {
        63
    } else {
        -1
    }
}

/// Exec carrier of the ASCII-whitespace removal (line 116); carries the
/// b64_ws membership decision.
pub exec fn b64_ws_exec(byte: u8) -> (r: bool)
    ensures r == b64_ws(byte)
{
    /* Origin Rust: matches!(byte, b' ' | b'\t' | b'\n' | b'\r' | b'\x0C')
     * matches! is unsupported by Verus; the chain is the identical test. */
    byte == b' ' || byte == b'\t' || byte == b'\n' || byte == b'\r' || byte == b'\x0C'
}

/// Upstream doc (forgiving_base64.rs:84-84):
///   <https://infra.spec.whatwg.org/#forgiving-base64-decode>
/* Origin Rust (lines 85-93):
 *     pub struct Decoder<F, E> where F: FnMut(&[u8]) -> Result<(), E> {
 *         write_bytes: F, bit_buffer: u32, buffer_bit_length: u8, padding_symbols: u8,
 *     }
 * The generic closure writer is blocked for quantification (file-header carrier
 * note): the writer is the concrete `out: &mut Vec<u8>` parameter; the three
 * state fields are kept verbatim. */
pub struct Decoder {
    pub bit_buffer: u32,
    pub buffer_bit_length: u8,
    pub padding_symbols: u8,
}

impl Decoder {
    /* Origin Rust (lines 99-106):
     *     pub fn new(write_bytes: F) -> Self {
     *         Self { write_bytes, bit_buffer: 0, buffer_bit_length: 0, padding_symbols: 0 }
     *     }
     * The write_bytes field is the blocked closure carrier (nothing to
     * initialize); the state fields keep their zero inits. */
    pub exec fn new() -> (r: Self)
        ensures
            r.bit_buffer == 0,
            r.buffer_bit_length == 0,
            r.padding_symbols == 0,
    {
        Decoder { bit_buffer: 0, buffer_bit_length: 0, padding_symbols: 0 }
    }

    /// Upstream doc (forgiving_base64.rs:108-108):
    ///   Feed to the decoder partial input in an ASCII-compatible encoding
    /* Origin Rust (line 109):
     *     pub fn feed(&mut self, input: &[u8]) -> Result<(), DecodeError<E>>
     * The blocked-closure shape is instantiated at the concrete writer: the
     * write_bytes closure becomes the `out: &mut Vec<u8>` parameter and the
     * DecodeError<E> return is carried by B64Error (the WriteError variant is
     * empty for a Vec write; the InvalidBase64 variant is the whole payload).
     * Upstream feed starts from an arbitrary decoder state; the entry
     * buffer_bit_length domain below is the state-valid one dec64_run
     * recommends. */
    pub exec fn feed(&mut self, input: &[u8], out: &mut Vec<u8>) -> (r: Result<(), B64Error>)
        requires
            old(self).buffer_bit_length as int == 0
                || old(self).buffer_bit_length as int == 6
                || old(self).buffer_bit_length as int == 12
                || old(self).buffer_bit_length as int == 18,
        ensures
            old(out)@.len() <= final(out)@.len(),
            match r {
                Ok(()) => (
                    prepend(
                        final(out)@.subrange(old(out)@.len() as int, final(out)@.len() as int),
                        dec64_run(input@, input.len() as int,
                            final(self).bit_buffer as int,
                            final(self).buffer_bit_length as int,
                            final(self).padding_symbols as int))
                    == dec64_run(input@, 0,
                        old(self).bit_buffer as int,
                        old(self).buffer_bit_length as int,
                        old(self).padding_symbols as int)
                    && (
                        final(self).buffer_bit_length as int == 0
                            || final(self).buffer_bit_length as int == 6
                            || final(self).buffer_bit_length as int == 12
                            || final(self).buffer_bit_length as int == 18
                    )
                ),
                Err(e) => dec64_run(input@, 0,
                        old(self).bit_buffer as int,
                        old(self).buffer_bit_length as int,
                        old(self).padding_symbols as int)
                    == Err((kind_of(e), sym_of(e))),
            },
    {
        /* Origin Rust: <none; new executable code> The ghost sequence tracks
         * the bytes appended to out so far inside the feed loop. */
        let ghost mut P: Seq<u8> = Seq::empty();
        proof {
            lemma_add_empty_right(out@);
            lemma_prepend_empty(dec64_run(input@, 0, old(self).bit_buffer as int,
                old(self).buffer_bit_length as int, old(self).padding_symbols as int));
        }
        let mut i: usize = 0;
        while i < input.len()
            invariant
                0 <= i <= input.len(),
                out@ == old(out)@ + P,
                prepend(P, dec64_run(input@, i as int,
                        self.bit_buffer as int,
                        self.buffer_bit_length as int,
                        self.padding_symbols as int))
                    == dec64_run(input@, 0,
                        old(self).bit_buffer as int,
                        old(self).buffer_bit_length as int,
                        old(self).padding_symbols as int),
                self.buffer_bit_length as int == 0
                    || self.buffer_bit_length as int == 6
                    || self.buffer_bit_length as int == 12
                    || self.buffer_bit_length as int == 18,
            decreases input.len() - i,
        {
            let byte = input[i];
            /* Origin Rust: let value = BASE64_DECODE_TABLE[byte as usize];
             * Carried by b64_val_exec (the table note in section A). */
            let value = b64_val_exec(byte);
            if value < 0 {
                // A character that's not part of the alphabet
                // Remove ASCII whitespace
                if b64_ws_exec(byte) {
                    proof { reveal_with_fuel(dec64_run, 2); }
                    i = i + 1;
                    continue;
                }
                if byte == b'=' {
                    /* Origin Rust (line 121):
                     *     self.padding_symbols = self.padding_symbols.saturating_add(1);
                     * saturating_add has no usable vstd spec in this build; the
                     * branch re-expression is the exact saturating semantic. */
                    if self.padding_symbols < 255 {
                        self.padding_symbols = self.padding_symbols + 1;
                    } else {
                        self.padding_symbols = 255;
                    }
                    proof { reveal_with_fuel(dec64_run, 2); }
                    i = i + 1;
                    continue;
                }
                proof { reveal_with_fuel(dec64_run, 2); }
                return Err(B64Error::UnexpectedSymbol(byte));
            }
            if self.padding_symbols > 0 {
                proof { reveal_with_fuel(dec64_run, 2); }
                return Err(B64Error::AlphabetSymbolAfterPadding);
            }
            /* Origin Rust (lines 130-131):
             *     self.bit_buffer <<= 6;
             *     self.bit_buffer |= value as u32;
             * vstd has no spec for the shift operators in this build; the u64
             * expression below is the exact wrap-around (mod 2^32) semantics:
             * << 6 is *64 mod 2^32 and the low 6 bits are zero after the
             * shift, so |= is +. */
            self.bit_buffer =
                ((self.bit_buffer as u64 * 64 + value as u64) % 4294967296) as u32;
            // 18 before incrementing means we've just reached 24
            if self.buffer_bit_length < 18 {
                self.buffer_bit_length = self.buffer_bit_length + 6;
            } else {
                // We've accumulated four times 6 bits, which equals three times 8 bits.
                let ghost P_old = P;
                /* Origin Rust (lines 137-142):
                 *     let byte_buffer = [
                 *         (self.bit_buffer >> 16) as u8,
                 *         (self.bit_buffer >> 8) as u8,
                 *         self.bit_buffer as u8,
                 *     ];
                 *     (self.write_bytes)(&byte_buffer).map_err(DecodeError::WriteError)?;
                 * vstd has no spec for >>; each division/modulo below is the
                 * exact truncation semantics, and the closure writer is the
                 * out: &mut Vec<u8> accumulator (file-header carrier note). */
                let b0: u8 = ((self.bit_buffer / 65536) % 256) as u8;
                let b1: u8 = ((self.bit_buffer / 256) % 256) as u8;
                let b2: u8 = (self.bit_buffer % 256) as u8;
                out.push(b0);
                out.push(b1);
                out.push(b2);
                // No need to reset bit_buffer,
                // since next time we're only gonna read relevant bits.
                self.buffer_bit_length = 0;
                proof {
                    P = P_old + seq![b0, b1, b2];
                    reveal_with_fuel(dec64_run, 2);
                    prepend_assoc(P_old, seq![b0, b1, b2],
                        dec64_run(input@, (i + 1) as int,
                            self.bit_buffer as int,
                            self.buffer_bit_length as int,
                            self.padding_symbols as int));
                    assert(b0 == ((self.bit_buffer as int / 65536) % 256) as u8);
                    assert(b1 == ((self.bit_buffer as int / 256) % 256) as u8);
                    assert(b2 == (self.bit_buffer as int % 256) as u8);
                }
            }
            proof { reveal_with_fuel(dec64_run, 2); }
            i = i + 1;
        }
        proof { lemma_conc_suffix(old(out)@, P); }
        Ok(())
    }

    /// Upstream doc (forgiving_base64.rs:151-151):
    ///   Call this to signal the end of the input
    /* Origin Rust (line 152):
     *     pub fn finish(mut self) -> Result<(), DecodeError<E>>
     * The by-value self mirrors the upstream consuming finish; the concrete
     * writer parameter and the B64Error return are the carrier decisions of
     * feed (the same notes apply). */
    pub exec fn finish(self, out: &mut Vec<u8>) -> (r: Result<(), B64Error>)
        ensures
            match r {
                Ok(()) => match dec64_run(Seq::<u8>::empty(), 0, self.bit_buffer as int,
                        self.buffer_bit_length as int, self.padding_symbols as int) {
                    Ok(s) => final(out)@ == old(out)@ + s,
                    Err(_) => false,
                },
                Err(e) => final(out)@ == old(out)@ && dec64_run(Seq::<u8>::empty(), 0,
                        self.bit_buffer as int, self.buffer_bit_length as int,
                        self.padding_symbols as int)
                    == Err((kind_of(e), sym_of(e))),
            },
    {
        match (self.buffer_bit_length, self.padding_symbols) {
            (0, 0) => {
                // A multiple of four of alphabet symbols, and nothing else.
                proof { reveal_with_fuel(dec64_run, 2); }
            }
            (12, 2) | (12, 0) => {
                // A multiple of four of alphabet symbols, followed by two more symbols,
                // optionally followed by two padding characters (which make a total multiple of four).
                /* Origin Rust (lines 160-161):
                 *     let byte_buffer = [(self.bit_buffer >> 4) as u8];
                 *     (self.write_bytes)(&byte_buffer).map_err(DecodeError::WriteError)?;
                 * vstd has no spec for >>; the div/mod re-expression is the
                 * exact truncation semantics; the writer is the out carrier. */
                let b: u8 = ((self.bit_buffer / 16) % 256) as u8;
                out.push(b);
                proof {
                    reveal_with_fuel(dec64_run, 2);
                    assert(b == ((self.bit_buffer as int / 16) % 256) as u8);
                }
            }
            (18, 1) | (18, 0) => {
                // A multiple of four of alphabet symbols, followed by three more symbols,
                // optionally followed by one padding character (which make a total multiple of four).
                /* Origin Rust (lines 166-167):
                 *     let byte_buffer = [
                 *         (self.bit_buffer >> 10) as u8, (self.bit_buffer >> 2) as u8];
                 *     (self.write_bytes)(&byte_buffer).map_err(DecodeError::WriteError)?;
                 * Same >> note as the arm above. */
                let b0: u8 = ((self.bit_buffer / 1024) % 256) as u8;
                let b1: u8 = ((self.bit_buffer / 4) % 256) as u8;
                out.push(b0);
                out.push(b1);
                proof {
                    reveal_with_fuel(dec64_run, 2);
                    assert(b0 == ((self.bit_buffer as int / 1024) % 256) as u8);
                    assert(b1 == ((self.bit_buffer as int / 4) % 256) as u8);
                }
            }
            (6, _) => {
                proof { reveal_with_fuel(dec64_run, 2); }
                return Err(B64Error::LoneAlphabetSymbol);
            }
            _ => {
                proof { reveal_with_fuel(dec64_run, 2); }
                return Err(B64Error::Padding);
            }
        }
        Ok(())
    }
}

/// Upstream doc (forgiving_base64.rs:70-70):
///   `input` is assumed to be in an ASCII-compatible encoding
/* Origin Rust (lines 71-82):
 *     pub fn decode_to_vec(input: &[u8]) -> Result<Vec<u8>, InvalidBase64> {
 *         let mut v = Vec::new();
 *         {
 *             let mut decoder = Decoder::new(|bytes| {
 *                 v.extend_from_slice(bytes);
 *                 Ok(())
 *             });
 *             decoder.feed(input)?;
 *             decoder.finish()?;
 *         }
 *         Ok(v)
 *     }
 * The closure writer is carried by the &mut v argument of the Decoder methods
 * (file-header carrier note), the `?` operators are the explicit matches
 * below, and the InvalidBase64 return is carried by B64Error. */
pub exec fn decode_to_vec(input: &[u8]) -> (r: Result<Vec<u8>, B64Error>)
    ensures
        match r {
            Ok(v) => match dec64_run(input@, 0, 0, 0, 0) {
                Ok(o) => v@ == o,
                Err(_) => false,
            },
            Err(e) => match dec64_run(input@, 0, 0, 0, 0) {
                Ok(_) => false,
                Err((k, b)) => kind_of(e) == k && (k != 0 || sym_of(e) == b),
            },
        },
{
    let mut v: Vec<u8> = Vec::new();
    {
        let mut decoder = Decoder::new();
        match decoder.feed(input, &mut v) {
            Ok(()) => {}
            Err(e) => return Err(e),
        }
        let ghost v_feed_end = v@;
        match decoder.finish(&mut v) {
            Ok(()) => {}
            Err(e) => return Err(e),
        }
        proof {
            lemma_empty_add_left(v_feed_end);
            reveal_with_fuel(dec64_run, 2);
        }
    }
    Ok(v)
}

// ===========================================================================
// Standalone proof lemmas (living at the end of the file so the exec pipeline
// reads directly; only the order changed)
// ===========================================================================

/// Right-neutral concatenation (for the loop-entry invariant with P empty).
proof fn lemma_add_empty_right(p: Seq<u8>)
    ensures p + Seq::<u8>::empty() == p
{
    assert((p + Seq::<u8>::empty()).len() == p.len());
    assert forall|i: int| 0 <= i < p.len() implies
        #[trigger] (p + Seq::<u8>::empty())[i] == p[i] by {
        assert((p + Seq::<u8>::empty())[i] == p[i]);
    }
}

/// Left-neutral concatenation (prepend of the empty prefix is the identity).
proof fn lemma_empty_add_left(p: Seq<u8>)
    ensures Seq::<u8>::empty() + p == p
{
    assert((Seq::<u8>::empty() + p).len() == p.len());
    assert forall|i: int| 0 <= i < p.len() implies
        #[trigger] (Seq::<u8>::empty() + p)[i] == p[i] by {
        assert((Seq::<u8>::empty() + p)[i] == p[i]);
    }
}

/// Prepend of the empty prefix is the identity on run results
/// (the loop-entry state of feed).
proof fn lemma_prepend_empty(r: Result<Seq<u8>, (int, u8)>)
    ensures prepend(Seq::empty(), r) == r
{
    match r {
        Ok(s) => {
            lemma_empty_add_left(s);
        }
        Err(_) => {}
    }
}

/// Prepend associativity: prepending p + q equals prepending q then p.
proof fn prepend_assoc(p: Seq<u8>, q: Seq<u8>, r: Result<Seq<u8>, (int, u8)>)
    ensures prepend(p + q, r) == prepend(p, prepend(q, r))
{
    match r {
        Ok(s) => {
            assert((p + q + s).len() == p.len() + (q + s).len());
            assert forall|i: int| 0 <= i < (p + q + s).len() implies
                #[trigger] (p + q + s)[i] == (p + (q + s))[i] by {
                let pq_len = p.len() + q.len();
                if i < p.len() {
                    assert((p + q + s)[i] == p[i]);
                    assert((p + (q + s))[i] == p[i]);
                } else if i < pq_len {
                    assert((p + q + s)[i] == q[i - p.len()]);
                    assert((p + (q + s))[i] == (q + s)[i - p.len()]);
                    assert((q + s)[i - p.len()] == q[i - p.len()]);
                } else {
                    assert((p + q + s)[i] == s[i - pq_len]);
                    assert((p + (q + s))[i] == (q + s)[i - p.len()]);
                    assert((q + s)[i - p.len()] == s[i - pq_len]);
                }
            }
            assert((p + q + s) =~= p + (q + s));
            assert((p + q + s) == p + (q + s));
        }
        Err(_) => {}
    }
}

/// The suffix split: for out@ == old + P, the appended-prefix subrange is P
/// (the exit bridge of the feed loop).
proof fn lemma_conc_suffix(p: Seq<u8>, q: Seq<u8>)
    ensures (p + q).subrange(p.len() as int, (p + q).len() as int) == q
{
    assert((p + q).len() == p.len() + q.len());
    assert((p + q).subrange(p.len() as int, (p + q).len() as int).len() == q.len());
    assert forall|i: int| 0 <= i < q.len() implies
        #[trigger] (p + q).subrange(p.len() as int, (p + q).len() as int)[i] == q[i] by {
        assert((p + q).subrange(p.len() as int, (p + q).len() as int)[i] == (p + q)[p.len() + i]);
        assert((p + q)[p.len() + i] == q[i]);
    }
}

/// Domain fact: every alphabet classification is -1 or an in-range value.
proof fn lemma_b64_val_range(b: u8)
    ensures -1 <= b64_val(b) <= 63
{
}

}

/// Generated by `make_base64_decode_table.py` based on "Table 1: The Base 64 Alphabet"
/// at <https://tools.ietf.org/html/rfc4648#section-4>
///
/// Array indices are the byte value of symbols.
/// Array values are their positions in the base64 alphabet,
/// or -1 for symbols not in the alphabet.
/// The position contributes 6 bits to the decoded bytes.
#[rustfmt::skip]
const BASE64_DECODE_TABLE: [i8; 256] = [
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 62, -1, -1, -1, 63,
    52, 53, 54, 55, 56, 57, 58, 59, 60, 61, -1, -1, -1, -1, -1, -1,
    -1,  0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, -1, -1, -1, -1, -1,
    -1, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
    41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
];

fn main() {}

