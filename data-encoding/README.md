# data-encoding 2.11.1

- upstream: [ia0/data-encoding](https://github.com/ia0/data-encoding) @ [53e2ff6](https://github.com/ia0/data-encoding/commit/53e2ff65eb3157a7b113b8a1a8b3fc89ce898dbf) (`COMMIT` pin in `fetch.conf`; `../fetch.sh data-encoding --latest` follows the tip)
- source: `../code/` — whole upstream tree at the pinned commit (byte-exact `git archive`, git-ignored); this crate lives in upstream subdir `lib/` (workspace carrier: build with `cargo build -p data-encoding` from `../code/`, or `--manifest-path ../code/lib/Cargo.toml`)
