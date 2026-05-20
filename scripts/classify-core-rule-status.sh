#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
tmp_file="$(mktemp "${TMPDIR:-/tmp}/core-rule-status.XXXXXX")"

trap 'rm -f "${tmp_file}"' EXIT

"${script_dir}/classify-rule-status.py" \
  "${repo_root}/Cpc" \
  --filter-file "${script_dir}/core-rules.txt" \
  > "${tmp_file}"

cat "${tmp_file}"

printf '\nsummary\n'
awk -F '\t' '
  NR == 1 && $1 == "rule" && $2 == "status" { next }
  NF >= 2 && !seen[$1]++ {
    counts[$2]++
    total++
  }
  END {
    printf "Proven\t%d\n", counts["Proven"] + 0
    printf "Unproven\t%d\n", counts["Unproven"] + 0
    printf "OutOfScope\t%d\n", counts["OutOfScope"] + 0
    printf "Total\t%d\n", total + 0
  }
' "${tmp_file}"
