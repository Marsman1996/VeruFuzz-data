//! `unicode-segmentation` library mirror (crate root) -- formal verification deliverable
//!
//! Upstream: https://github.com/unicode-rs/unicode-segmentation
//!   pin e445e101b129862148127c9e41ab4486b0125232 (the code/ tree is untouched)
//!
//! Mirror strategy (this crate's specifics -- UAX#29 semantics + generated giant
//! tables):
//! - `tables.rs`: data tables kept verbatim + #[verifier::external]; the four table
//!   lookups external_body + axiomatic contracts (ASCII model / anchor
//!   classification / bounds containment); all axioms validated in full on the
//!   upstream pin tree by out/verus-bugfinder/tables_equiv.
//! - The segmentation logic layer (the rule matrices and state-machine pure fns of
//!   grapheme/word/sentence, plus the pure small faces of each iterator) is this
//!   round's **obligation face**: transcribed verbatim and proved by Verus.
//! - The deep-water zones (the chunked GraphemeCursor state machine, the
//!   UWordBounds forward/backward main loops, and the SentenceBreaks::next
//!   main loop) are ledgered as blocked (see out/bug-finder-summary.md);
//!   the verbatim bodies stay, with no fabricated contracts.
//!
//! Consumption: this file is the module assembly root; the harness files
//! include it via `#[path = "../src/<file>.rs"]` mod declarations; copying this
//! mirror's spec is forbidden.

#![allow(unused)]
use vstd::prelude::*;
use vstd::prelude::SpecOrd;
use vstd::string::StringSliceAdditionalSpecFns;

pub mod grapheme;
pub mod sentence;
pub mod tables;
pub mod word;

fn main() {}
