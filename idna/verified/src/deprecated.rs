// Verified transcription of idna 1.1.0 src/deprecated.rs:
// the map_transitional core and the Config data face.
//
// Upstream pin: 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a (servo/rust-url,
// SUBDIR=idna, file src/deprecated.rs, 248 lines).
// Basis: database/idna/code/idna/src/deprecated.rs; the AsciiDenyList and
// Hyphens types consumed by Config::deny_list/hyphens are included from the
// sibling verified transcription via #[path] (no spec content copied).
// This is a standalone file (like the sibling faces): no external crate
// deps, ending with fn main() {}.
//
// Scope:
// * map_transitional as a pure char core: the per-character transitional
//   mapping map_char_pushes (sharp s doubles, final sigma normalizes, the
//   zero-width join controllers drop, everything else passes through),
//   the accumulator model map_all, the full model map_transitional_model,
//   and the exec core map_transitional_chars refined to the model.
// * the Config data face: the four flags, all five documented setters
//   (including the retained-obsolete use_idna_2008_rules with its
//   documented panic), default values, and the deny_list/hyphens
//   mappings onto the sibling uts46 face types.
// * the Idna struct and its constructor.
//
// Locked ledger of the blocked surface (one line each with reason):
// * Idna::to_ascii/to_unicode (deprecated.rs:78-129) and
//   Config::to_ascii/to_unicode (deprecated.rs:235-247): drive the blocked
//   Uts46::process pipeline (see the uts46 face ledger); batch C material.
// * the Cow<str> layer of map_transitional (deprecated.rs:25-62, the
//   Borrowed passthrough vs Owned rebuild): the verified core returns one
//   fresh Vec<char> whose value equals the model in both cases (the
//   borrow/owned ownership distinction has no byte-level semantics).
//   The core below is written as a single full-mapping loop over the
//   input; it is output-equal to the upstream scan-then-rebuild iterator
//   structure because every non-transitional char maps to itself, so the
//   scan prefix contributes an identity copy in both designs.
// * `impl Default for Config` and the #[deprecated]/#[must_use] attribute
//   trivia: represented by Config::default_ with identical semantics
//   (external trait impls are not verifiable faces).
//
// Upstream doc (deprecated.rs:20-22), map_transitional contract:
// "Performs preprocessing equivalent to UTS 46 transitional processing
// if `transitional` is `true`. If `transitional` is `false`, merely
// lets the input pass through as-is (for call site convenience)."

use vstd::prelude::*;
use vstd::seq::Seq;

#[path = "uts46.rs"]
mod uts46_v;

use uts46_v::AsciiDenyList;
use uts46_v::Hyphens;
use uts46_v::bit_is_set;
use uts46_v::deny_list_bits;
use uts46_v::ldh_pred;
use uts46_v::upper_case_pred;

verus! {

/* ============================================================
 * map_transitional (deprecated.rs:25-62) as a pure char core
 * ============================================================ */

/// The per-character transitional mapping, in accumulator form: the
/// deprecated transitional deviations of UTS 46 mapping (sharp s lower and
/// upper double to "ss", final sigma normalizes to sigma, the zero-width
/// non-joiner/joiner drop, everything else passes through unchanged).
pub open spec fn map_char_pushes(c: char, acc: Seq<char>) -> (r: Seq<char>) {
    if c == '\u{df}' || c == '\u{1e9e}' {
        acc.push('s').push('s')
    } else if c == '\u{3c2}' {
        acc.push('\u{3c3}')
    } else if c == '\u{200c}' || c == '\u{200d}' {
        acc
    } else {
        acc.push(c)
    }
}

/// The transitional trigger characters (exactly the chars with a
/// non-identity mapping above).
pub open spec fn is_transitional_char(c: char) -> (r: bool) {
    c == '\u{df}'
        || c == '\u{1e9e}'
        || c == '\u{3c2}'
        || c == '\u{200c}'
        || c == '\u{200d}'
}

/// A non-trigger char maps to itself (single-char chunk).
proof fn lemma_map_char_self(c: char)
    requires
        !is_transitional_char(c),
    ensures
        map_char_pushes(c, Seq::empty()) == seq![c],
{
}

/// The full-mapping accumulator model over input positions [j, len).
pub open spec fn map_all(input: Seq<char>, j: int, acc: Seq<char>) -> (r: Seq<char>)
    decreases (input.len() as int) - j
{
    if j >= (input.len() as int) {
        acc
    } else {
        map_all(input, j + 1, map_char_pushes(input[j], acc))
    }
}

/// The full map_transitional model: identity without the flag, the
/// per-character transitional mapping with it.
pub open spec fn map_transitional_model(
    input: Seq<char>,
    transitional: bool,
) -> (r: Seq<char>) {
    if !transitional {
        input
    } else {
        map_all(input, 0, Seq::empty())
    }
}

/// Origin: deprecated.rs:25-62 `map_transitional`, monomorphized to a
/// char-slice core returning a fresh Vec<char> (the Cow borrow/owned
/// ownership split has no value-level semantics; see the file ledger).
/// The exec below is a single full-mapping loop, output-equal to the
/// upstream scan-then-rebuild structure because every non-trigger char
/// maps to itself.
/// Upstream doc (deprecated.rs:20-22):
///   Performs preprocessing equivalent to UTS 46 transitional processing
///   if `transitional` is `true`. If `transitional` is `false`, merely
///   lets the input pass through as-is (for call site convenience).
pub fn map_transitional_chars(input: &[char], transitional: bool) -> (r: Vec<char>)
    ensures
        r@ == map_transitional_model(input@, transitional),
{
    /* Origin Rust: if !transitional { return Cow::Borrowed(domain); } --
       the passthrough core copies the input (a value-identical fresh
       vector; the borrowed ownership channel is ledger-blocked). */
    let mut out: Vec<char> = Vec::new();
    if !transitional {
        let mut q: usize = 0;
        while q < input.len()
            invariant
                q <= input.len(),
                (out@.len() as int) == (q as int),
                forall |k: int|
                    0 <= k < (out@.len() as int) ==> (out@[k] == input@[k]),
            decreases (input.len() as int) - (q as int)
        {
            let c = input[q];
            let ghost pa = out@;
            out.push(c);
            proof {
                vstd::seq::lemma_seq_push_index_same(pa, c, (pa.len() as int));
            }
            q += 1;
        }
        proof {
            // the copy is the input view, elementwise and by length
            assert forall |k: int|
                0 <= k < (input@.len() as int) implies (out@[k] == input@[k]) by {}
            vstd::seq::lemma_seq_ext_equal(out@, input@);
        }
        // model side: !transitional keeps the input as-is
        assert(map_transitional_model(input@, transitional) == input@);
    } else {
        /* Origin Rust: the upstream iterator scans for the first trigger
           char and rebuilds from there; here the whole input is mapped in
           one loop (output-equal: the scan prefix is an identity copy). */
        let mut q: usize = 0;
        while q < input.len()
            invariant
                q <= input.len(),
                map_all(input@, 0, Seq::empty())
                    == map_all(input@, q as int, out@),
            decreases (input.len() as int) - (q as int)
        {
            let c = input[q];
            let ghost pre = out@;
            proof {
                // one recursion step of the model
                assert(map_all(input@, q as int, pre)
                    == map_all(
                        input@,
                        q as int + 1,
                        map_char_pushes(input@[q as int], pre),
                    )) by {
                    reveal_with_fuel(map_all, 1);
                }
            }
            /* Origin Rust: the match of the upstream tail loop
               (deprecated.rs:41-51):
                 'ss' | 'SS' => s.push_str("ss")
                 'ss-final' => s.push('sigma')
                 ZWNJ | ZWJ => {}
                 _ => s.push(c) */
            if c == '\u{df}' || c == '\u{1e9e}' {
                out.push('s');
                out.push('s');
            } else if c == '\u{3c2}' {
                out.push('\u{3c3}');
            } else if c == '\u{200c}' || c == '\u{200d}' {
            } else {
                proof {
                    lemma_map_char_self(c);
                }
                out.push(c);
            }
            proof {
                // each arm pushed exactly the model chunk
                assert(map_char_pushes(input@[q as int], pre) == out@);
                assert(map_all(input@, 0, Seq::empty())
                    == map_all(input@, q as int + 1, out@));
            }
            q += 1;
        }
        proof {
            // recursion end: the accumulator is the full model
            assert(map_all(input@, input@.len() as int, out@) == out@) by {
                reveal_with_fuel(map_all, 1);
            }
        }
        assert(map_transitional_model(input@, transitional) == out@);
    }
    out
}

/* ============================================================
 * Config (deprecated.rs:131-248) and Idna (deprecated.rs:64-75)
 * ============================================================ */

/// Origin: deprecated.rs:132-140 `pub struct Config` (four flag fields,
/// upstream private; the attribute trivia is in the file ledger).
pub struct Config {
    use_std3_ascii_rules: bool,
    transitional_processing: bool,
    verify_dns_length: bool,
    check_hyphens: bool,
}

/* Spec accessors for the (upstream-private) flag fields; the fields stay
   private like upstream (deprecated.rs:135-140), and spec consumers go
   through these views (kept closed so fields do not leak into unfolding). */
pub closed spec fn cfg_use_std3_ascii_rules(c: &Config) -> bool {
    c.use_std3_ascii_rules
}

pub closed spec fn cfg_transitional_processing(c: &Config) -> bool {
    c.transitional_processing
}

pub closed spec fn cfg_verify_dns_length(c: &Config) -> bool {
    c.verify_dns_length
}

pub closed spec fn cfg_check_hyphens(c: &Config) -> bool {
    c.check_hyphens
}


/// Origin: deprecated.rs:142-153 `impl Default`, the beStrict=false
/// defaults of the WHATWG URL Standard.
/// Upstream doc (deprecated.rs:142):
///   The defaults are that of _beStrict=false_ in the WHATWG URL Standard
impl Config {
    /// The `impl Default for Config` (deprecated.rs:143-153) as a core fn
    /// (external trait impls are not verifiable faces; semantics identical).
    pub fn default_() -> (r: Self)
        ensures
            cfg_use_std3_ascii_rules(&r) == false,
            cfg_transitional_processing(&r) == false,
            cfg_verify_dns_length(&r) == false,
            cfg_check_hyphens(&r) == false,
    {
        Self {
            use_std3_ascii_rules: false,
            transitional_processing: false,
            verify_dns_length: false,
            check_hyphens: false,
        }
    }
}

/// Origin: deprecated.rs:155-232 `impl Config` (the four documented
/// setters, the retained-obsolete panic setter, and the two mode
/// mappings).
impl Config {
    /// Origin: deprecated.rs:161-165. The STD3 setter.
    /// Upstream doc (deprecated.rs:156-160):
    ///   Whether to enforce STD3 or WHATWG URL Standard ASCII deny list.
    ///   `true` for STD3, `false` for no deny list.
    ///   Note that `true` rejects pseudo-hosts used by various TXT record-based protocols.
    pub fn use_std3_ascii_rules(mut self, value: bool) -> (r: Self)
        ensures
            cfg_use_std3_ascii_rules(&r) == value,
            cfg_transitional_processing(&r) == cfg_transitional_processing(&self),
            cfg_verify_dns_length(&r) == cfg_verify_dns_length(&self),
            cfg_check_hyphens(&r) == cfg_check_hyphens(&self),
    {
        self.use_std3_ascii_rules = value;
        self
    }

    /// Origin: deprecated.rs:171-175. The transitional-processing setter.
    /// Upstream doc (deprecated.rs:167-170):
    ///   Whether to enable (deprecated) transitional processing.
    ///   Note that Firefox, Safari, and Chrome do not use transitional
    ///   processing.
    pub fn transitional_processing(mut self, value: bool) -> (r: Self)
        ensures
            cfg_use_std3_ascii_rules(&r) == cfg_use_std3_ascii_rules(&self),
            cfg_transitional_processing(&r) == value,
            cfg_verify_dns_length(&r) == cfg_verify_dns_length(&self),
            cfg_check_hyphens(&r) == cfg_check_hyphens(&self),
    {
        self.transitional_processing = value;
        self
    }

    /// Origin: deprecated.rs:182-186. The verify-dns-length setter.
    /// Upstream doc (deprecated.rs:177-181):
    ///   Whether the _VerifyDNSLength_ operation should be performed
    ///   by `to_ascii`.
    ///   For compatibility with previous behavior, even when set to `true`,
    ///   the trailing root label dot is allowed contrary to the spec.
    pub fn verify_dns_length(mut self, value: bool) -> (r: Self)
        ensures
            cfg_use_std3_ascii_rules(&r) == cfg_use_std3_ascii_rules(&self),
            cfg_transitional_processing(&r) == cfg_transitional_processing(&self),
            cfg_verify_dns_length(&r) == value,
            cfg_check_hyphens(&r) == cfg_check_hyphens(&self),
    {
        self.verify_dns_length = value;
        self
    }

    /// Origin: deprecated.rs:198-202. The hyphen-check setter.
    /// Upstream doc (deprecated.rs:188-197):
    ///   Whether to enforce STD3 rules for hyphen placement.
    ///   `true` to deny hyphens in the first and last positions.
    ///   `false` to not enforce hyphen placement.
    ///   Note that for backward compatibility this is not the same as
    ///   UTS 46 _CheckHyphens_, which also disallows hyphens in the
    ///   third and fourth positions.
    ///   Note that `true` rejects real-world names, including some GitHub user pages.
    pub fn check_hyphens(mut self, value: bool) -> (r: Self)
        ensures
            cfg_use_std3_ascii_rules(&r) == cfg_use_std3_ascii_rules(&self),
            cfg_transitional_processing(&r) == cfg_transitional_processing(&self),
            cfg_verify_dns_length(&r) == cfg_verify_dns_length(&self),
            cfg_check_hyphens(&r) == value,
    {
        self.check_hyphens = value;
        self
    }

    /// Origin: deprecated.rs:210-214. The retained-obsolete setter with its
    /// documented panic domain.
    /// Upstream doc (deprecated.rs:204-208):
    ///   Obsolete method retained to ease migration. The argument must be `false`.
    ///   Panics
    ///   If the argument is `true`.
    //
    // Verus note: upstream asserts !value ("IDNA 2008 rules are no longer
    // supported") and panics on `true`; here the documented panic domain is
    // transcribed as `requires` (contract transcription, not weakening: the
    // # Panics section of the upstream doc is exactly this precondition).
    pub fn use_idna_2008_rules(self, value: bool) -> (r: Self)
        requires
            !value,
        ensures
            cfg_use_std3_ascii_rules(&r) == cfg_use_std3_ascii_rules(&self),
            cfg_transitional_processing(&r) == cfg_transitional_processing(&self),
            cfg_verify_dns_length(&r) == cfg_verify_dns_length(&self),
            cfg_check_hyphens(&r) == cfg_check_hyphens(&self),
    {
        self
    }

    /// Origin: deprecated.rs:217-222 `deny_list` (private upstream):
    /// STD3 when the flag is set, the plain upper-case deny list otherwise.
    /// Upstream doc (deprecated.rs:156-160 quoted above).
    pub fn deny_list(&self) -> (r: AsciiDenyList)
        ensures
            forall |k: u8| #![trigger bit_is_set(deny_list_bits(&r), k)] k < 128
                ==> (bit_is_set(deny_list_bits(&r), k)
                    == (if cfg_use_std3_ascii_rules(&self) { ldh_pred(k) } else { upper_case_pred(k) })),
    {
        if self.use_std3_ascii_rules {
            AsciiDenyList::std3()
        } else {
            AsciiDenyList::empty()
        }
    }

    /// Origin: deprecated.rs:225-231 `hyphens` (private upstream): the
    /// first/last-position check when the flag is set, Allow otherwise.
    pub fn hyphens(&self) -> (r: Hyphens)
        ensures
            r == (if cfg_check_hyphens(&self) { Hyphens::CheckFirstLast } else { Hyphens::Allow }),
    {
        if self.check_hyphens {
            Hyphens::CheckFirstLast
        } else {
            Hyphens::Allow
        }
    }
}

/// Origin: deprecated.rs:65-69 `pub struct Idna` (the config carrier; its
/// to_ascii/to_unicode methods are ledger-blocked with the Uts46 pipeline).
pub struct Idna {
    config: Config,
}

/// Spec accessor for the (upstream-private) config field.
pub closed spec fn idna_config(id: &Idna) -> Config {
    id.config
}

impl Idna {
    /// Origin: deprecated.rs:71-74 `Idna::new`.
    pub fn new(config: Config) -> (r: Idna)
        ensures
            cfg_use_std3_ascii_rules(&idna_config(&r))
                == cfg_use_std3_ascii_rules(&config),
            cfg_transitional_processing(&idna_config(&r))
                == cfg_transitional_processing(&config),
            cfg_verify_dns_length(&idna_config(&r))
                == cfg_verify_dns_length(&config),
            cfg_check_hyphens(&idna_config(&r)) == cfg_check_hyphens(&config),
    {
        Idna { config }
    }
}

} // verus!

fn main() {}
