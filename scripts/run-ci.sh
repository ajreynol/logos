#!/usr/bin/env bash

set -euo pipefail

echo "Building logos executable..."
lake build logos

echo "Compiling Cpc.Spec..."
lake build Cpc.Spec

echo "Compiling Cpc.Lemmas..."
lake build Cpc.Lemmas

shopt -s nullglob
examples=(examples/*.cpc.lean)

if [ "${#examples[@]}" -eq 0 ]; then
  echo "No regression examples found under examples/." >&2
  exit 1
fi

echo "Running ${#examples[@]} regression examples..."
for example in "${examples[@]}"; do
  echo "::group::${example}"
  if ! output="$(lake exe logos "${example}" 2>&1)"; then
    printf '%s\n' "${output}"
    echo "Regression run failed for ${example}" >&2
    exit 1
  fi

  printf '%s\n' "${output}"
  result="$(printf '%s\n' "${output}" | awk 'NF { line = $0 } END { print line }')"
  if [ "${result}" != "true" ]; then
    echo "Expected ${example} to evaluate to true, got: ${result}" >&2
    exit 1
  fi
  echo "::endgroup::"
done

echo "All CI checks passed."
