//! verified/src/lib.rs -- module-tree mirror of code/src/lib.rs (pin 2fcf2a7),
//!
//! - [Origin Rust: `#![doc = include_str!...]` / cfg_attr / clippy allow]
//!   The doc embedding and lint attributes carry no verification
//!   semantics, so they are not mirrored.
//! - [Origin Rust: `mod tests` / `mod tests128` (#[cfg(test)])]
//!   The verification form of the UTs lives in verified/harness/
//!   (reference organization; #[path] does not copy the src side).
//! - [Origin Rust: `pub mod reexports` (serde feature gated)]
//!   The default feature set has no serde; not mirrored (matching the
//!   UT inventory's exclusion policy).
//! - [Origin Rust: `pub mod prelude`] -- a pure re-export declaration
//!   layer with no standalone semantics;
//!   the translated verification takes the re-exported sip/sip128
//!   modules (the ::Hasher as _ trait imports are done by the harness
//!   side's own `use`) as the source of truth; the prelude is not
//!   mirrored.

#[path = "common.rs"]
pub mod common;

#[path = "sip.rs"]
pub mod sip;

#[path = "sip128.rs"]
pub mod sip128;
