#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"

"${script_dir}/classify-rule-status.py" \
  "${repo_root}/Cpc" \
  --filter-file "${script_dir}/core-rules.txt"
