#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/build-all-cpc-rules.sh [options]

Build every CPC proof rule under Cpc/Proofs/Rules and show Lake's verbose
build progress.

All rules are built in a single `lake build` invocation, so Lake already
compiles them in parallel across all cores. This Lake version has no -j/--jobs
flag, so -jN here instead caps Lean's program-wide thread pool via
LEAN_NUM_THREADS (use it to limit, not raise, parallelism). Omit it for all
cores.

Options:
  -jN, --jobs N  Set LEAN_NUM_THREADS=N for this build.
  --clean        Run `lake clean` before building all rules.
  --clean-only   Run `lake clean` and exit without building.
  -h, --help     Show this help.

Examples:
  scripts/build-all-cpc-rules.sh
  scripts/build-all-cpc-rules.sh -j12
  scripts/build-all-cpc-rules.sh --clean
  scripts/build-all-cpc-rules.sh --clean-only
USAGE
}

die() {
  echo "error: $*" >&2
  exit 1
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"

do_clean=false
build=true
jobs=""

while [ "$#" -gt 0 ]; do
  case "$1" in
    --clean) do_clean=true ;;
    --clean-only) do_clean=true; build=false ;;
    -j) jobs="${2:-}"; shift ;;
    -j*) jobs="${1#-j}" ;;
    --jobs) jobs="${2:-}"; shift ;;
    --jobs=*) jobs="${1#--jobs=}" ;;
    -h|--help) usage; exit 0 ;;
    *) usage >&2; die "unknown argument: $1" ;;
  esac
  shift
done

if [ -n "${jobs}" ]; then
  case "${jobs}" in
    *[!0-9]*|'') die "invalid job count: ${jobs}" ;;
  esac
  export LEAN_NUM_THREADS="${jobs}"
fi

rules_dir="${repo_root}/Cpc/Proofs/Rules"
[ -d "${rules_dir}" ] || die "rules directory not found: ${rules_dir}"

cd "${repo_root}"

if [ "${do_clean}" = true ]; then
  echo "==> Cleaning build artifacts (lake clean)"
  lake clean
fi

if [ "${build}" != true ]; then
  exit 0
fi

# Collect every rule module from its source file.
modules=()
while IFS= read -r file; do
  rel_file="${file#"${repo_root}/"}"
  module="${rel_file%.lean}"
  module="${module//\//.}"
  modules+=("${module}")
done < <(find "${rules_dir}" -maxdepth 1 -type f -name '*.lean' | sort)

[ "${#modules[@]}" -gt 0 ] || die "no rule files found under ${rules_dir}"

echo "Rules directory: Cpc/Proofs/Rules"
echo "Rule count: ${#modules[@]}"
echo

# Build every rule in a single Lake invocation so targets compile in parallel,
# filtering the verbose output the same way build-cpc-rule.sh does.
lake --verbose --no-ansi build "${modules[@]}" 2>&1 | awk '
  {
    line = $0

    if (match(line, /\[[0-9]+\/[0-9]+\][[:space:]]+(Building|Compiling|Built|Replayed)[[:space:]]+Cpc[^[:space:]]*/)) {
      progress = substr(line, RSTART, RLENGTH)
      split(progress, parts, /[[:space:]]+/)

      step = parts[1]
      status = parts[2]
      target = parts[3]

      file = target
      gsub(/\./, "/", file)
      file = file ".lean"

      if (status == "Building" || status == "Compiling") {
        label = "compiling"
      } else {
        label = tolower(status)
      }

      annotation = step " " label " " file
      if (annotation != last_annotation) {
        print "==> " annotation
        last_annotation = annotation
      }
    }

    if (line ~ /^trace: \.> /) {
      fflush()
      next
    }

    print line
    fflush()
  }
'
