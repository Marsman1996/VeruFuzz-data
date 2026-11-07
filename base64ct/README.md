# base64ct 1.8.3

- upstream: [RustCrypto/formats](https://github.com/RustCrypto/formats) @ [4c5fadb](https://github.com/RustCrypto/formats/commit/4c5fadb155ebc05c4a8a3abc05e4e64a6a100614) (`COMMIT` pin in `fetch.conf`; `../fetch.sh base64ct --latest` follows the tip)
- source: `../code/` — whole upstream tree at the pinned commit (byte-exact `git archive`, git-ignored); this crate lives in upstream subdir `base64ct/` (workspace carrier: build with `cargo build -p base64ct` from `../code/`, or `--manifest-path ../code/base64ct/Cargo.toml`)
