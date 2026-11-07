#!/usr/bin/env bash
# fetch.sh -- clone a crate's upstream GitHub repository (tip of the
# default branch, or the commit pinned in fetch.conf) and materialize
# it into ./<crate-dir>/code.
#
# Why GitHub tip instead of a crates.io release: a bug found during
# verification may already be fixed upstream, so we verify the current
# commit rather than a possibly stale release tarball. The resolved
# HEAD is written back into fetch.conf as COMMIT=<sha> on first fetch,
# so afterwards the pin stays reproducible; ./fetch.sh <dir> --latest
# moves the pin to the new tip.
#
# Generic per-crate fetcher. Each crate directory under database/
# only carries a small config file `fetch.conf` (shell-sourceable):
#
#   database/<dir>/
#     fetch.conf    # NAME / VERSION / REPO (required);
#                   # COMMIT / SUBDIR (written back on first fetch)
#     .upstream/    # created here: local git clone of REPO (evidence)
#     code/         # created here: whole upstream tree of the pinned
#                   # commit (git archive output; no .git inside)
#     verified/     # crate-local verification artifacts (not managed here)
#
# code/ is a byte-exact subtree of the pinned commit (repo root at
# code/ root). For crates that live in a subdirectory of their repo
# (workspace carriers such as servo/rust-url, RustCrypto/formats,
# contain-rs/bit-vec, ia0/data-encoding), fetch.conf records the
# location in SUBDIR and commands must be run with that in mind, e.g.
# `cargo build -p <NAME>` from code/ or --manifest-path code/$SUBDIR.
# Nothing upstream is modified, relocated or pruned: workspace
# inheritance and path deps keep working.
#
# Usage:
#   ./fetch.sh <dir> [--latest]   # use fetch.conf of database/<dir>
#   ./fetch.sh all [--latest]     # fetch every crate under database/
#
# Notes:
# - Idempotent: an existing clone whose HEAD equals the pinned COMMIT
#   (and an already materialized code/) is left untouched.
# - The COMMIT SHA in fetch.conf is the evidence chain.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

usage() {
  echo "usage: $(basename "$0") <crate-dir|all> [--latest]" >&2
  exit 2
}

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
  usage
fi
TARGET="$1"
REFRESH=0
if [ $# -eq 2 ]; then
  [ "$2" = "--latest" ] || usage
  REFRESH=1
fi

# "all" fetches every crate directory that carries a fetch.conf.
# Each crate runs in a fresh invocation (forwarding only the optional
# --latest flag), and failures are collected so one bad crate does
# not block the rest (exit code stays 1).
if [ "${TARGET}" = "all" ]; then
  status=0
  shift
  shopt -s nullglob
  for conf in "${SCRIPT_DIR}"/*/fetch.conf; do
    d="$(basename "$(dirname "$conf")")"
    echo "=== fetching ${d} ==="
    if ! "$0" "$d" "$@"; then
      echo "FAILED: ${d}" >&2
      status=1
    fi
  done
  shopt -u nullglob
  [ "${status}" -eq 0 ] || echo "fetch all: some crates failed" >&2
  exit "${status}"
fi

DIR="${SCRIPT_DIR}/${TARGET}"
CONF="${DIR}/fetch.conf"
[ -f "${CONF}" ] || { echo "missing config: ${CONF}" >&2; exit 2; }

# shellcheck source=/dev/null
source "${CONF}"
: "${NAME:?NAME required}"
: "${REPO:?REPO required (GitHub clone URL)}"
VERSION="${VERSION:-?}"
COMMIT="${COMMIT:-}"
SUBDIR="${SUBDIR:-}"

UPSTREAM="${DIR}/.upstream"
CODE_DIR="${DIR}/code"

# Write a KEY=VALUE line back into fetch.conf (idempotent, portable:
# awk prefix match instead of sed -i, whose in-place flag differs).
set_field() {
  local key="$1" val="$2"
  if grep -q "^${key}=" "${CONF}"; then
    awk -v k="${key}" -v v="${val}" '
      index($0, k"=") == 1 { print k"="v; next }
      { print }' "${CONF}" > "${CONF}.tmp"
    mv "${CONF}.tmp" "${CONF}"
  else
    printf '%s=%s\n' "${key}" "${val}" >> "${CONF}"
  fi
}

# Exact package name declared in the [package] table of manifest $1
# (section-aware: [dependencies]/[[bin]] tables also use `name =`).
package_name() {
  awk -F'"' '
  /^[[:space:]]*\[/  { in_pkg = ($0 ~ /^[[:space:]]*\[package\][[:space:]]*$/) }
  in_pkg && /^[[:space:]]*name[[:space:]]*=/ { print $2; exit }
  ' "$1" 2>/dev/null
}

# Crate names are dash/underscore interchangeable when matching.
name_matches() {
  local got="$1" want="$2" alt
  alt="$(printf '%s' "${want}" | tr '_-' '-_')"
  [ "${got}" = "${want}" ] || [ "${got}" = "${alt}" ]
}

# Locate the crate inside the cloned repo; prints the in-repo subpath
# (empty when the crate is at the repo root), or returns 1 (not found)
# / 2 (ambiguous).
detect_subdir() {
  local root="$1" want="$2" m d got n=0 found=""
  if name_matches "$(package_name "${root}/Cargo.toml" 2>/dev/null)" "${want}"; then
    echo ""
    return 0
  fi
  while IFS= read -r m; do
    got="$(package_name "${m}")"
    if name_matches "${got}" "${want}"; then
      n=$((n + 1))
      d="$(dirname "${m}")"
      found="${d#"${root}/"}"
    fi
  done < <(find "${root}" -name Cargo.toml -not -path '*/.git/*' -not -path '*/target/*' | LC_ALL=C sort)
  if [ "${n}" -eq 1 ]; then
    echo "${found}"
    return 0
  fi
  if [ "${n}" -eq 0 ]; then
    echo "ERROR: no manifest declaring package '${want}' in ${REPO}" >&2
  else
    echo "ERROR: ${n} manifests declare package '${want}' in ${REPO} -- pin SUBDIR manually" >&2
  fi
  return 1
}

# --latest discards everything and follows the remote tip again.
if [ "${REFRESH}" -eq 1 ]; then
  rm -rf "${UPSTREAM}" "${CODE_DIR}"
  COMMIT=""
fi

# Idempotent fast path: pin already recorded, clone already on it,
# and code/ materialized. (The crate manifest may sit in SUBDIR --
# workspace carriers have no manifest at repo root.)
if [ -d "${UPSTREAM}" ] && [ -d "${CODE_DIR}" ] && [ -n "${COMMIT}" ] \
   && [ -f "${CODE_DIR}/${SUBDIR:+${SUBDIR}/}Cargo.toml" ] \
   && [ "$(git -C "${UPSTREAM}" rev-parse HEAD)" = "${COMMIT}" ]; then
  echo "fetch skipped: ${CODE_DIR} already pinned at ${COMMIT} (use --latest to follow the tip)"
  exit 0
fi

if [ -d "${UPSTREAM}" ]; then
  HEAD_SHA="$(git -C "${UPSTREAM}" rev-parse HEAD)"
  if [ -z "${COMMIT}" ]; then
    # Clone exists but no pin yet (should not normally happen): pin it.
    COMMIT="${HEAD_SHA}"
    set_field COMMIT "${COMMIT}"
    echo "pinned ${NAME} at existing clone HEAD ${COMMIT}"
  elif [ "${HEAD_SHA}" != "${COMMIT}" ]; then
    echo "checking out pinned ${COMMIT} in existing clone ..."
    git -C "${UPSTREAM}" checkout -q "${COMMIT}" || {
      echo "ERROR: pinned commit ${COMMIT} not reachable in existing clone of ${REPO}" >&2
      echo "       (upstream force-pushed? re-run with --latest to re-pin)" >&2
      exit 1
    }
  fi
else
  if [ -n "${COMMIT}" ] && [ "${REFRESH}" -eq 0 ]; then
    # Pinned rebuild: full clone so the pin can be checked out and
    # archived byte-exactly (no lazy-fetch surprises), independent of
    # how far upstream has drifted since.
    echo "cloning ${REPO} for pinned commit ${COMMIT} ..."
    git clone --quiet "${REPO}" "${UPSTREAM}"
    git -C "${UPSTREAM}" checkout -q "${COMMIT}" || {
      echo "ERROR: pinned commit ${COMMIT} not found in ${REPO}" >&2
      echo "       (rewritten away? re-run with --latest to re-pin)" >&2
      exit 1
    }
  else
    echo "cloning tip of ${REPO} ..."
    git clone --quiet --depth 1 "${REPO}" "${UPSTREAM}"
    COMMIT="$(git -C "${UPSTREAM}" rev-parse HEAD)"
    set_field COMMIT "${COMMIT}"
    echo "pinned ${NAME} at tip ${COMMIT}"
  fi
fi

# Where inside the repo does this crate live? (workspace carriers such
# as servo/rust-url or RustCrypto/formats hold several crates)
if [ -z "${SUBDIR}" ]; then
  SUBDIR="$(detect_subdir "${UPSTREAM}" "${NAME}")" || exit 1
  set_field SUBDIR "${SUBDIR}"
fi

# Materialize the whole pinned tree into code/ (git archive, no .git),
# byte-exact as upstream published it.
rm -rf "${CODE_DIR}"
mkdir -p "${CODE_DIR}"
git -C "${UPSTREAM}" archive "${COMMIT}" | tar -x -C "${CODE_DIR}"

# Sanity: the crate manifest must sit where SUBDIR says it is.
CRATE_MANIFEST="${CODE_DIR}/${SUBDIR:+${SUBDIR}/}Cargo.toml"
[ -f "${CRATE_MANIFEST}" ] || {
  echo "ERROR: expected crate manifest at ${CRATE_MANIFEST}" >&2
  exit 1
}
name_matches "$(package_name "${CRATE_MANIFEST}")" "${NAME}" || {
  echo "ERROR: ${CRATE_MANIFEST} declares package '$(package_name "${CRATE_MANIFEST}")', expected '${NAME}'" >&2
  exit 1
}

echo "fetched ${NAME} (upstream ref v${VERSION}) @ ${COMMIT}${SUBDIR:+ (subdir: ${SUBDIR})} into ${CODE_DIR}"
echo "done."
