#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/build.sh [LAKE-BUILD-OPTION|TARGET]...

Build Logos with the pinned Lean toolchain. If Lean's bundled Clang/LLVM cannot
run on an older Linux host, use compatible host tools automatically.

Examples:
  scripts/build.sh logos
  scripts/build.sh Logos.Parser Cpc.Parser
USAGE
}

case "${1:-}" in
  -h|--help) usage; exit 0 ;;
esac

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

# shellcheck source=lean-toolchain-env.sh
source "${script_dir}/lean-toolchain-env.sh"
logos_configure_lean_toolchain

exec lake build "$@"
