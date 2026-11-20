//! tpm-core 0.1.4 message-header type wrappers (src/types.rs) --
//! Verus translation.
//!
//! Upstream module doc (types.rs:1-9, abridged): "At the moment only
//! `buf` uses TpmTag and TpmRc; callers do not yet use them. ...
//! This is kept for the TpmRc case: the return code and command code
//! share the same offset in the header, and if the two are mixed up
//! with the same bare u32, no check will catch it."

use vstd::prelude::*;

verus! {

// ------------------------------------------------------------------
// TpmTag (types.rs:11-46)
// ------------------------------------------------------------------

/// Origin Rust: /// Tag field in the TPM message header.
/// #[derive(Clone, Copy)]
/// pub enum TpmTag {
///     RquCommand, Tpm2NoSessions, Tpm2Sessions, Null,
/// } (src/types.rs:11-22 with per-variant doc lines; variant docs:
/// "TPM_TAG_RQU_COMMAND = 193 (TPM 1.2 command)",
/// "TPM2_ST_NO_SESSIONS = 0x8001", "TPM2_ST_SESSIONS = 0x8002",
/// "0 -- explicitly allowed by tpm_buf_reset() for an unfinalized
/// buffer")
#[derive(Clone, Copy)]
pub enum TpmTag {
    RquCommand,
    Tpm2NoSessions,
    Tpm2Sessions,
    Null,
}

/// spec twin of TpmTag::code (the wire value of each tag variant).
pub open spec fn tag_code(t: TpmTag) -> u16 {
    match t {
        TpmTag::RquCommand => 193u16,
        TpmTag::Tpm2NoSessions => 0x8001u16,
        TpmTag::Tpm2Sessions => 0x8002u16,
        TpmTag::Null => 0u16,
    }
}

/// spec twin of TpmTag::from_code (the wire parse face).
pub open spec fn tag_from_code(c: u16) -> Option<TpmTag> {
    if c == 193u16 {
        Option::Some(TpmTag::RquCommand)
    } else if c == 0x8001u16 {
        Option::Some(TpmTag::Tpm2NoSessions)
    } else if c == 0x8002u16 {
        Option::Some(TpmTag::Tpm2Sessions)
    } else if c == 0u16 {
        Option::Some(TpmTag::Null)
    } else {
        Option::None
    }
}

impl TpmTag {
    /// Origin Rust: pub fn code(self) -> u16 (src/types.rs:24-31; match
    /// arms 193 / 0x8001 / 0x8002 / 0)
    pub exec fn code(self) -> (c: u16)
        ensures
            c == tag_code(self),
    {
        match self {
            TpmTag::RquCommand => 193u16,
            TpmTag::Tpm2NoSessions => 0x8001u16,
            TpmTag::Tpm2Sessions => 0x8002u16,
            TpmTag::Null => 0u16,
        }
    }

    /// Origin Rust: /// Parse a value from the wire.
    /// pub fn from_code(c: u16) -> Option<TpmTag> (src/types.rs:32-45)
    pub exec fn from_code(c: u16) -> (r: Option<TpmTag>)
        ensures
            r == tag_from_code(c),
    {
        if c == 193u16 {
            Some(TpmTag::RquCommand)
        } else if c == 0x8001u16 {
            Some(TpmTag::Tpm2NoSessions)
        } else if c == 0x8002u16 {
            Some(TpmTag::Tpm2Sessions)
        } else if c == 0u16 {
            Some(TpmTag::Null)
        } else {
            None
        }
    }
}

/// Wire roundtrip: parsing the code of any tag variant yields the same
/// variant (upstream: from_code and code are mutual inverses on the
/// closed variant set).
proof fn lemma_tag_roundtrip(t: TpmTag)
    ensures
        tag_from_code(tag_code(t)) == Option::Some(t),
{
    match t {
        TpmTag::RquCommand => assert(tag_code(t) == 193u16),
        TpmTag::Tpm2NoSessions => assert(tag_code(t) == 0x8001u16),
        TpmTag::Tpm2Sessions => assert(tag_code(t) == 0x8002u16),
        TpmTag::Null => assert(tag_code(t) == 0u16),
    }
}

/// Wire injectivity preface: the four variant codes are pairwise
/// distinct, so code() separates variants (the caller-side membership
/// face of from_code's None arm).
proof fn lemma_tag_codes_distinct(t: TpmTag, u: TpmTag)
    requires
        tag_code(t) == tag_code(u),
    ensures
        t == u,
{
    match t {
        TpmTag::RquCommand => match u {
            TpmTag::RquCommand => {
            }
            TpmTag::Tpm2NoSessions => assert(193u16 != 0x8001u16),
            TpmTag::Tpm2Sessions => assert(193u16 != 0x8002u16),
            TpmTag::Null => assert(193u16 != 0u16),
        },
        TpmTag::Tpm2NoSessions => match u {
            TpmTag::RquCommand => assert(0x8001u16 != 193u16),
            TpmTag::Tpm2NoSessions => {
            }
            TpmTag::Tpm2Sessions => assert(0x8001u16 != 0x8002u16),
            TpmTag::Null => assert(0x8001u16 != 0u16),
        },
        TpmTag::Tpm2Sessions => match u {
            TpmTag::RquCommand => assert(0x8002u16 != 193u16),
            TpmTag::Tpm2NoSessions => assert(0x8002u16 != 0x8001u16),
            TpmTag::Tpm2Sessions => {
            }
            TpmTag::Null => assert(0x8002u16 != 0u16),
        },
        TpmTag::Null => match u {
            TpmTag::RquCommand => assert(0u16 != 193u16),
            TpmTag::Tpm2NoSessions => assert(0u16 != 0x8001u16),
            TpmTag::Tpm2Sessions => assert(0u16 != 0x8002u16),
            TpmTag::Null => {
            }
        },
    }
}

// ------------------------------------------------------------------
// TpmRc (types.rs:47-70)
// ------------------------------------------------------------------

/// Origin Rust: /// TPM return code (the third field in the header, sharing one offset with the ordinal).
/// /// A newtype rather than an enum: the return-code space is open (including vendor-defined values), ...
/// #[derive(Clone, Copy)]
/// pub struct TpmRc(pub u32); (src/types.rs:47-52)
#[derive(Clone, Copy)]
pub struct TpmRc {
    pub value: u32,
}

impl TpmRc {
    /// Origin Rust: pub const SUCCESS: u32 = 0x0000_0000; (types.rs:54)
    pub const SUCCESS: u32 = 0x0000_0000;
    /// Origin Rust: pub const WARN_RETRY: u32 = 0x0000_0800;
    ///   doc: `TPM_WARN_RETRY` (types.rs:55-56)
    pub const WARN_RETRY: u32 = 0x0000_0800;
    /// Origin Rust: pub const WARN_DOING_SELFTEST: u32 = 0x0000_0802;
    ///   doc: `TPM_WARN_DOING_SELFTEST` (types.rs:57-58)
    pub const WARN_DOING_SELFTEST: u32 = 0x0000_0802;
    /// Origin Rust: pub const ERR_DEACTIVATED: u32 = 0x0000_0006;
    ///   doc: `TPM_ERR_DEACTIVATED` (types.rs:59-60)
    pub const ERR_DEACTIVATED: u32 = 0x0000_0006;
    /// Origin Rust: pub const ERR_DISABLED: u32 = 0x0000_0007;
    ///   doc: `TPM_ERR_DISABLED` (types.rs:61-62)
    pub const ERR_DISABLED: u32 = 0x0000_0007;
    /// Origin Rust: pub const ERR_FAILEDSELFTEST: u32 = 0x0000_001C;
    ///   doc: `TPM_ERR_FAILEDSELFTEST` (types.rs:63-64)
    pub const ERR_FAILEDSELFTEST: u32 = 0x0000_001C;
    /// Origin Rust: pub const ERR_INVALID_POSTINIT: u32 = 38;
    ///   doc: `TPM_ERR_INVALID_POSTINIT` (types.rs:65-66)
    pub const ERR_INVALID_POSTINIT: u32 = 38;

    /// Origin Rust: pub fn is_success(self) -> bool {
    ///     self.0 == 0u32
    /// } (src/types.rs:67-69; the tuple field is spelled `value` in
    /// the twin: Verus named-struct face of the upstream tuple
    /// newtype, same single-field shape)
    pub exec fn is_success(self) -> (r: bool)
        ensures
            r == (self.value == 0u32),
    {
        self.value == 0u32
    }
}

// ------------------------------------------------------------------
// Size constants (types.rs:71-78)
// ------------------------------------------------------------------

/// Origin Rust: /// `TPM_BUFSIZE`
/// pub const TPM_BUFSIZE: usize = 4096; (types.rs:71-72)
pub const TPM_BUFSIZE: usize = 4096;
/// Origin Rust: /// `TPM2_SPACE_BUFFER_SIZE`
/// pub const TPM2_SPACE_BUFFER_SIZE: usize = 16384; (types.rs:73-74)
pub const TPM2_SPACE_BUFFER_SIZE: usize = 16384;
/// Origin Rust: /// `TPM_MAX_RNG_DATA`
/// pub const TPM_MAX_RNG_DATA: usize = 128; (types.rs:75-76)
pub const TPM_MAX_RNG_DATA: usize = 128;
/// Origin Rust: /// `TPM_RETRY`
/// pub const TPM_RETRY: u32 = 50; (types.rs:77-78)
pub const TPM_RETRY: u32 = 50;

} // verus!
