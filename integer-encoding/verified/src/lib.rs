//! verified/src/lib.rs -- the module-assembly mirror of the upstream
//! code/src/lib.rs (a KVerus migrate artifact)
//!
//! Upstream lib.rs (pin e0a10d0):
//!   mod fixed; mod fixed_tests; mod varint; mod varint_tests; mod reader; mod writer;
//!   pub use fixed::FixedInt; pub use varint::VarInt; ...
//!   (the async-feature cfg items are out of this verification round;
//!    no default feature)
//!
//! Mirror side:
//!   mod fixed / varint / reader / writer keep the upstream structure (after the
//!    per-type monomorphization, see each file's header ledger);
//!   the contents of the upstream *_tests modules land in verified/harness/
//!    (reference-style organization).
//! No fn main -- driven by the harness files via #[path].

pub mod fixed;
pub mod varint;
pub mod reader;
pub mod writer;
