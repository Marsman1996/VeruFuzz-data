//! `url` crate mirror -- src/host.rs (first verus batch subset)
//!
//! Upstream: https://github.com/servo/rust-url (pin 00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a)
//! crate root at `code/url/` (SUBDIR=url; code/ tree untouched).
//! This file is the same-name mirror of `src/host.rs`, restricted to the data-model
//! face consumed by the Url read API: the `HostInternal` tag enum (host.rs:23-41)
//! and the `Host` carrier enum (host.rs:43-64). The host *parsing* face
//! (parse_cow/parse_opaque_cow/parse_ipv4addr/parse_ipv6addr/ends_in_a_number,
//! host.rs:92-512) is parser-dependent and is scheduled for a later batch.
//!
//! Lossy-abstraction ledger (per item, verus vs upstream):
//! 1. Upstream `HostInternal::Ipv4(Ipv4Addr)` / `Host::Ipv4(Ipv4Addr)` carry a
//!    `std::net::Ipv4Addr`, which has no vstd spec; the mirror carries the address
//!    as its `u32` bit pattern (`Ipv4Addr::from(u32)` round-trip is the identity,
//!    the decimal octets are `(v >> 24) & 0xFF`, ... `v & 0xFF`).
//! 2. Upstream `HostInternal::Ipv6(Ipv6Addr)` / `Host::Ipv6(Ipv6Addr)` carry a
//!    `std::net::Ipv6Addr`; the mirror carries the eight `u16` segments exactly as
//!    `Ipv6Addr::new(pieces[0], .., pieces[7])` (host.rs:509-511 and the `segments()`
//!    face are both the segment tuple, so no information is lost).
//! 3. Upstream `Host<S>` is generic over the domain string type (`&str` borrowed by
//!    `Url::host`, `String` owned by `Host::parse`); the mirror specializes S to a
//!    byte payload `Vec<u8>` (the content of the upstream `&str`/`String`), following
//!    the same String-has-no-vstd-spec ruling as the form_urlencoded mirror.
//! 4. `Cow`/`Display`/`PartialEq` impls (host.rs:66-212) are outside the verus
//!    surface (fmt layer, generic PartialEq); their content behavior is carried by
//!    the callers' ensures instead.
//! 5. `From<Host<Cow<'_, str>>> for HostInternal` (host.rs:32-41) is an impl-From
//!    constructor; the mirror is the same-name free fn `host_to_internal` over the
//!    specialized S (the Cow layer is flattened away by ruling 3).

use vstd::prelude::*;
use vstd::seq::Seq;

verus! {

/// Origin Rust derive (host.rs:24): #[derive(Copy, Clone, Debug, Eq, PartialEq)]
///   (Eq/PartialEq derives are dropped: a derived PartialEq makes exec `==` go
///    through the opaque trait spec while spec `==` stays the datatype equality;
///    all comparisons in the mirror use the datatype equality or explicit matches,
///    which the derive would make ambiguous to the solver)
#[derive(Copy, Clone, Debug)]
pub enum HostInternal {
    None,
    Domain,
    Ipv4(u32),
    Ipv6([u16; 8]),
}

/// Upstream doc (host.rs:43-51):
///   The host name of an URL.
///   A DNS domain name, as '.' dot-separated labels.
///   Non-ASCII labels are encoded in punycode per IDNA if this is the host of
///   a special URL, or percent encoded for non-special URLs. Hosts for
///   non-special URLs are also called opaque hosts.
/// Origin Rust derive (host.rs:45): #[derive(Clone, Debug, Eq, Ord, PartialOrd, Hash)]
///   (Eq/Ord/PartialOrd/Hash derives dropped for the same datatype-equality reason
///    as HostInternal; Clone is kept for the Domain(Vec<u8>) payload)
#[derive(Clone, Debug)]
pub enum Host {
    /// Origin Rust: Domain(S)  (host.rs:51; S specialized to the byte payload, ledger 3)
    Domain(Vec<u8>),
    /// Origin Rust: Ipv4(Ipv4Addr)  (host.rs:56)
    /// Upstream doc (host.rs:53-56):
    ///   An IPv4 address.
    ///   `Url::host_str` returns the serialization of this address,
    ///   as four decimal integers separated by `.` dots.
    Ipv4(u32),
    /// Origin Rust: Ipv6(Ipv6Addr)  (host.rs:63)
    /// Upstream doc (host.rs:58-63):
    ///   An IPv6 address.
    ///   `Url::host_str` returns the serialization of that address between `[` and `]` brackets,
    ///   in the format per RFC 5952 *A Recommendation
    ///   for IPv6 Address Text Representation*: lowercase hexadecimal with maximal `::` compression.
    Ipv6([u16; 8]),
}

/// Origin Rust: impl From<Host<Cow<'_, str>>> for HostInternal (host.rs:32-41)
///   match host {
///     Host::Domain(ref s) if s.is_empty() => Self::None,
///     Host::Domain(_) => Self::Domain,
///     Host::Ipv4(address) => Self::Ipv4(address),
///     Host::Ipv6(address) => Self::Ipv6(address),
///   }
pub exec fn host_to_internal(host: &Host) -> (r: HostInternal)
    ensures
        (r == HostInternal::None) == (match host {
            Host::Domain(d) => d.view().len() == 0,
            _ => false,
        }),
        (r == HostInternal::Domain) == (match host {
            Host::Domain(d) => d.view().len() > 0,
            _ => false,
        }),
        (match host {
            Host::Ipv4(a) => r == HostInternal::Ipv4(*a),
            _ => true,
        }),
        (match host {
            Host::Ipv6(a) => r == HostInternal::Ipv6(*a),
            _ => true,
        }),
{
    match host {
        Host::Domain(s) => {
            if s.len() == 0 {
                HostInternal::None
            } else {
                HostInternal::Domain
            }
        }
        Host::Ipv4(a) => HostInternal::Ipv4(*a),
        Host::Ipv6(a) => HostInternal::Ipv6(*a),
    }
}

}
