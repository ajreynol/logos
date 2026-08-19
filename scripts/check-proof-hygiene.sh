#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

readonly forbidden_pattern="(^|[^[:alnum:]_'])(sorry|admit|axiom)([^[:alnum:]_']|$)"
readonly source_dirs=(Cpc CpcMini)

for source_dir in "${source_dirs[@]}"; do
  if [ ! -d "${source_dir}" ]; then
    echo "error: source directory not found: ${source_dir}" >&2
    exit 1
  fi
done

source_files=()
while IFS= read -r -d '' source_file; do
  source_files+=("${source_file}")
done < <(find "${source_dirs[@]}" -type f -name '*.lean' -print0)

if [ "${#source_files[@]}" -eq 0 ]; then
  echo "error: no Lean source files found under Cpc or CpcMini" >&2
  exit 1
fi

grep_status=0
LC_ALL=C grep -nHE "${forbidden_pattern}" "${source_files[@]}" || grep_status=$?

case "${grep_status}" in
  0)
    echo "error: forbidden proof escape hatch found in Cpc or CpcMini" >&2
    echo "Remove every standalone 'sorry', 'admit', and 'axiom' token, including occurrences in comments." >&2
    exit 1
    ;;
  1)
    ;;
  *)
    echo "error: failed to scan Lean source files" >&2
    exit "${grep_status}"
    ;;
esac

echo "Proof hygiene check passed (${#source_files[@]} Lean source files checked)."
