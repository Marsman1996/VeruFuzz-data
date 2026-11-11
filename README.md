# Verification targets database
This directory contains several libraries that are configured to be verified using VeruFuzz.

## Dataset

Each crate is verified at the tip of its GitHub upstream; the resolved HEAD is pinned in `fetch.conf` as a reproducible evidence chain. `Version` is the latest crates.io release (reference only; the upstream tip may be ahead of it). `Commit` is the actually-verified pin.

| Library | Version | Commit |
| ------------- | -------- | ------ |
| [base64](https://github.com/marshallpierce/rust-base64) | 0.23.1 | [5b98ee1](https://github.com/marshallpierce/rust-base64/commit/5b98ee180cc7c2a64af6cb12c724b1721550e0d0) |
| [base64ct](https://github.com/RustCrypto/formats) | 1.8.3 | [4c5fadb](https://github.com/RustCrypto/formats/commit/4c5fadb155ebc05c4a8a3abc05e4e64a6a100614) |
| [bit-vec](https://github.com/contain-rs/bit-vec) | 0.10.1 | [cd5b439](https://github.com/contain-rs/bit-vec/commit/cd5b4392be151fb507f3bdbf71ce1e73885dbc28) |
| [bitflags](https://github.com/bitflags/bitflags) | 2.13.2 | [8384f6f](https://github.com/bitflags/bitflags/commit/8384f6f6e1fd1ab3f448ccf17d400a9e1d6a5280) |
| [byteorder](https://github.com/BurntSushi/byteorder) | 1.5.0 | [5a82625](https://github.com/BurntSushi/byteorder/commit/5a82625fae462e8ba64cec8146b24a372b4d75c6) |
| [crc](https://github.com/mrhooray/crc-rs) | 3.4.0 | [1894aa9](https://github.com/mrhooray/crc-rs/commit/1894aa9f184d44cf1226aeb3048a3e91fc1b8df4) |
| [data-encoding](https://github.com/ia0/data-encoding) | 2.11.1 | [53e2ff6](https://github.com/ia0/data-encoding/commit/53e2ff65eb3157a7b113b8a1a8b3fc89ce898dbf) |
| [data-url](https://github.com/servo/rust-url) | 0.3.2 | [00a6ce5](https://github.com/servo/rust-url/commit/00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a) |
| [form_urlencoded](https://github.com/servo/rust-url) | 1.2.2 | [00a6ce5](https://github.com/servo/rust-url/commit/00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a) |
| [generational-arena](https://github.com/fitzgen/generational-arena) | 0.2.9 | [6dbc29e](https://github.com/fitzgen/generational-arena/commit/6dbc29e573aa192a2c7ae9c7f968eb8853311294) |
| [glob](https://github.com/rust-lang/glob) | 0.3.4 | [057cef2](https://github.com/rust-lang/glob/commit/057cef2824f5a96f738e52d7d8ca3e024381bcc6) |
| [hex](https://github.com/KokaKiwi/rust-hex) | 0.4.3 | [e25a870](https://github.com/KokaKiwi/rust-hex/commit/e25a8701f7f6b5ec4acedffcb4a45cfb69cc34eb) |
| [humantime](https://github.com/chronotope/humantime) | 2.4.0 | [997ff56](https://github.com/chronotope/humantime/commit/997ff566cc731e3ece5c792c8b83dd78e459f202) |
| [idna](https://github.com/servo/rust-url) | 1.1.0 | [00a6ce5](https://github.com/servo/rust-url/commit/00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a) |
| [integer-encoding](https://github.com/dermesser/integer-encoding-rs) | 4.1.0 | [e0a10d0](https://github.com/dermesser/integer-encoding-rs/commit/e0a10d01e86a38d0df177676c62f9a10c845ab53) |
| [num-integer](https://github.com/rust-num/num-integer) | 0.1.47 | [765fd9b](https://github.com/rust-num/num-integer/commit/765fd9b3eb9397471d41b9f613e530f6d9d6383f) |
| [percent-encoding](https://github.com/servo/rust-url) | 2.3.2 | [00a6ce5](https://github.com/servo/rust-url/commit/00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a) |
| [semver](https://github.com/dtolnay/semver) | 1.0.28 | [280ebcb](https://github.com/dtolnay/semver/commit/280ebcb6edac3aa4cdc545dbff8a26c5ac4861fe) |
| [siphasher](https://github.com/jedisct1/rust-siphash) | 1.0.4 | [2fcf2a7](https://github.com/jedisct1/rust-siphash/commit/2fcf2a742340824ee23328e6eba4bc7ea0e52613) |
| [slab](https://github.com/tokio-rs/slab) | 0.4.12 | [7d1d8ab](https://github.com/tokio-rs/slab/commit/7d1d8ab00a7b8b1978b4bf21d9ae9633ac8c0b05) |
| [strsim](https://github.com/rapidfuzz/strsim-rs) | 0.11.1 | [dacc84c](https://github.com/rapidfuzz/strsim-rs/commit/dacc84c0dc61eff0ee0ff66962bcf2e17018ad26) |
| [unicode-segmentation](https://github.com/unicode-rs/unicode-segmentation) | 1.13.3 | [e445e10](https://github.com/unicode-rs/unicode-segmentation/commit/e445e101b129862148127c9e41ab4486b0125232) |
| [untrusted](https://github.com/briansmith/untrusted) | 0.9.0 | [b7c4aea](https://github.com/briansmith/untrusted/commit/b7c4aea36ca2ddcec71c323fb7b27d5724d73f3a) |
| [url](https://github.com/servo/rust-url) | 2.5.8 | [00a6ce5](https://github.com/servo/rust-url/commit/00a6ce58d02f4e0d43c5ca0702c0bedb8b1ebf3a) |

## File Structure

Typically, each library is in a separate subdirectory, which holds a crate-local `README.md` with per-crate notes and, used in order, a `fetch.conf` and a `verified/` directory:

1. `fetch.conf` records `NAME`, `VERSION` (the release the `Version` column references; not used for fetching), `REPO` (GitHub clone URL), and — written back on first fetch — `COMMIT` (the pinned commit SHA; the evidence chain) and `SUBDIR` (the crate's location inside its repository when it is not at the repo root, e.g. `percent_encoding` inside `servo/rust-url`).
2. `./fetch.sh <dir>` (at the database root) clones `REPO` and checks out the pinned `COMMIT` (pinned rebuilds are deterministic: the commit tree is materialized byte-exactly via `git archive`). On the first fetch of an unpinned directory it shallow-clones the tip and writes the resolved HEAD back into `COMMIT`. It then produces two git-ignored artifacts: `.upstream/` (the local clone, evidence) and `code/` (the whole upstream tree of the pinned commit; no `.git` inside). `./fetch.sh all` does this for every library listed above; `--latest` moves the pin to the remote tip (re-clones).
3. `verified/` holds the Verus verification artifacts.

Notes:
- `code/` always holds the full repository tree so workspace inheritance keeps working for workspace carriers (`servo/rust-url`, `RustCrypto/formats`, `contain-rs/bit-vec`, `ia0/data-encoding`); to build such a crate run e.g. `cargo build -p <NAME>` from `code/`, or pass `--manifest-path code/$SUBDIR/Cargo.toml`.
