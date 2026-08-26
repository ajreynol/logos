#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/get-eo-compiler.sh [OPTION]...

Download and build everything scripts/install-cpc.sh needs in order to
regenerate the Lean sources of this repository from the Eunoia definition of a
calculus:

  * the ethos source tree, and ethos-eoc built from the standalone project in
    its plugins/ directory
  * the Eunoia signature of CPC, taken from the cvc5 source tree

Both are placed under deps/ (see --deps-dir) and the resulting paths and
versions are recorded in deps/eoc-env.sh, which scripts/install-cpc.sh reads so
that it can then be run with no arguments at all.

ethos-eoc is always compiled here rather than downloaded. No release of ethos
publishes it, and it reads its Lean and Eunoia templates out of the source tree
it was built from, so that tree has to be fetched either way.

Only the proofs/eo part of cvc5 is extracted: what the compiler consumes is the
signature, which is Eunoia source, not a cvc5 binary.

Options:
  --ethos-version REF  git ref of cvc5/ethos to build (default: main)
  --cvc5-version REF   git ref of cvc5/cvc5 to take the CPC signature from
                       (default: main)
  --deps-dir DIR       where to put everything (default: <repo>/deps)
  --jobs N             parallel compile jobs (default: all processors)
  --keep-tmp           keep the downloaded archives instead of deleting them
  -h, --help           show this message

Requires cmake >= 3.12, a C++17 compiler, the GMP development headers, tar, and
either wget or curl. On Debian and Ubuntu the GMP headers are libgmp-dev; on
macOS with Homebrew they are gmp.

Examples:
  scripts/get-eo-compiler.sh
  scripts/get-eo-compiler.sh --ethos-version b9fc583f --cvc5-version cvc5-1.2.0
USAGE
}

ETHOS_VERSION="main"
CVC5_VERSION="main"
DEPS_DIR=""
JOBS=""
KEEP_TMP=0

while [ $# -gt 0 ]; do
  case "$1" in
    --ethos-version) ETHOS_VERSION="${2:?--ethos-version requires a value}"; shift 2 ;;
    --ethos-version=*) ETHOS_VERSION="${1#*=}"; shift ;;
    --cvc5-version) CVC5_VERSION="${2:?--cvc5-version requires a value}"; shift 2 ;;
    --cvc5-version=*) CVC5_VERSION="${1#*=}"; shift ;;
    --deps-dir) DEPS_DIR="${2:?--deps-dir requires a value}"; shift 2 ;;
    --deps-dir=*) DEPS_DIR="${1#*=}"; shift ;;
    --jobs) JOBS="${2:?--jobs requires a value}"; shift 2 ;;
    --jobs=*) JOBS="${1#*=}"; shift ;;
    --keep-tmp) KEEP_TMP=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unrecognized option $1" >&2; usage >&2; exit 2 ;;
  esac
done

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
DEPS_DIR="${DEPS_DIR:-${repo_root}/deps}"

if [ -z "${JOBS}" ]; then
  if command -v nproc >/dev/null 2>&1; then
    JOBS="$(nproc)"
  elif command -v sysctl >/dev/null 2>&1; then
    JOBS="$(sysctl -n hw.logicalcpu 2>/dev/null || echo 4)"
  else
    JOBS=4
  fi
fi

# Download $1 to $2, as contrib/get-ethos-checker does in cvc5.
download() {
  if command -v wget >/dev/null 2>&1; then
    wget -c -O "$2" "$1"
  elif command -v curl >/dev/null 2>&1; then
    curl -Lf "$1" -o "$2"
  else
    echo "Neither wget nor curl is installed; cannot download $1." >&2
    exit 1
  fi
}

# Extract the members of archive $1 matching pattern $3 into $2, dropping the
# leading directory that a GitHub archive wraps everything in. BSD tar matches
# a pattern given as an operand, GNU tar wants --wildcards for the same.
extract() {
  local archive="$1" dest="$2" pattern="${3:-}"
  mkdir -p "${dest}"
  if [ -z "${pattern}" ]; then
    tar --strip-components 1 -xzf "${archive}" -C "${dest}"
  elif tar --version 2>/dev/null | grep -qi 'gnu tar'; then
    tar --strip-components 1 -xzf "${archive}" -C "${dest}" --wildcards "${pattern}"
  else
    tar --strip-components 1 -xzf "${archive}" -C "${dest}" "${pattern}"
  fi
}

for tool in cmake tar; do
  command -v "${tool}" >/dev/null 2>&1 || {
    echo "${tool} is required but was not found on PATH." >&2
    exit 1
  }
done

TMP_DIR="${DEPS_DIR}/tmp"
ETHOS_DIR="${DEPS_DIR}/ethos"
CVC5_DIR="${DEPS_DIR}/cvc5"
BUILD_DIR="${ETHOS_DIR}/build-eoc"
mkdir -p "${TMP_DIR}"

echo "==> Downloading ethos ${ETHOS_VERSION}"
download "https://github.com/cvc5/ethos/archive/${ETHOS_VERSION}.tar.gz" \
  "${TMP_DIR}/ethos.tgz"
rm -rf "${ETHOS_DIR}"
extract "${TMP_DIR}/ethos.tgz" "${ETHOS_DIR}"

DRIVER="${ETHOS_DIR}/tools/eoc/driver.py"
if [ ! -f "${DRIVER}" ]; then
  echo "error: ${DRIVER} is missing from the ethos tree." >&2
  echo "The Eunoia compiler driver was added to ethos in #229; a ref older" >&2
  echo "than that cannot be used here. Pass a newer --ethos-version." >&2
  exit 1
fi

echo "==> Downloading the CPC signature from cvc5 ${CVC5_VERSION}"
download "https://github.com/cvc5/cvc5/archive/${CVC5_VERSION}.tar.gz" \
  "${TMP_DIR}/cvc5.tgz"
rm -rf "${CVC5_DIR}"
extract "${TMP_DIR}/cvc5.tgz" "${CVC5_DIR}" '*/proofs/eo/*'

CPC_SIGNATURE="${CVC5_DIR}/proofs/eo/cpc/Cpc.eo"
if [ ! -f "${CPC_SIGNATURE}" ]; then
  echo "error: ${CPC_SIGNATURE} was not found in the cvc5 archive." >&2
  exit 1
fi

echo "==> Building ethos-eoc with ${JOBS} jobs"
if ! cmake -S "${ETHOS_DIR}/plugins" -B "${BUILD_DIR}" -DCMAKE_BUILD_TYPE=Release; then
  echo >&2
  echo "error: configuring ethos-eoc failed. It needs cmake >= 3.12, a C++17" >&2
  echo "compiler and the GMP development headers (libgmp-dev on Debian and" >&2
  echo "Ubuntu, gmp on Homebrew)." >&2
  exit 1
fi
cmake --build "${BUILD_DIR}" --parallel "${JOBS}" --target ethos-eoc

ETHOS_EOC="${BUILD_DIR}/ethos-eoc"
if [ ! -x "${ETHOS_EOC}" ]; then
  echo "error: the build reported success but ${ETHOS_EOC} is not there." >&2
  exit 1
fi

# The binary is left where it was built on purpose. It resolves its templates
# against the source tree that configured it, so moving it apart from
# ${ETHOS_DIR} would only work with ETHOS_PLUGIN_ROOT set to point back.

echo "==> Recording what was installed in ${DEPS_DIR}/eoc-env.sh"
cat > "${DEPS_DIR}/eoc-env.sh" <<ENV
# Written by scripts/get-eo-compiler.sh. Read by scripts/install-cpc.sh so that
# it can be run with no arguments. Edit by re-running get-eo-compiler.sh rather
# than by hand.
#
# ethos ${ETHOS_VERSION}, cvc5 ${CVC5_VERSION}
EOC_ETHOS_DIR="${ETHOS_DIR}"
EOC_ETHOS_EOC="${ETHOS_EOC}"
EOC_BUILD_DIR="${BUILD_DIR}"
EOC_SIGNATURE="${CPC_SIGNATURE}"
EOC_DEFS="${ETHOS_DIR}/plugins/model_smt/cpc_defs.eo"
EOC_LEAN_CONFIG="${ETHOS_DIR}/plugins/lean_meta/cpc_termination.lean"
EOC_ETHOS_VERSION="${ETHOS_VERSION}"
EOC_CVC5_VERSION="${CVC5_VERSION}"
ENV

if [ "${KEEP_TMP}" = "0" ]; then
  rm -rf "${TMP_DIR}"
fi

cat <<DONE

==> Done.

  ethos      ${ETHOS_DIR} (${ETHOS_VERSION})
  ethos-eoc  ${ETHOS_EOC}
  signature  ${CPC_SIGNATURE} (cvc5 ${CVC5_VERSION})

Regenerate the Lean sources of this repository with:

  scripts/install-cpc.sh              # the Cpc package
  scripts/install-cpc.sh --mini       # the CpcMini package

Both read ${DEPS_DIR}/eoc-env.sh, so neither needs to be told where any of the
above is. Add deps/ to .gitignore if it is not there already.
DONE
