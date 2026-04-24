#!/usr/bin/env bash

set -euo pipefail

echo "Building logos executable..."
lake build logos

echo "Compiling Cpc.Spec..."
lake build Cpc.Spec

# expensive (~5mins)
#echo "Compiling Cpc.Proofs.Rules.Chain_resolution..."
#lake build Cpc.Proofs.Rules.Chain_resolution

# expensive to compile and not currently used in CI checks, so skipping for now
#echo "Compiling Cpc.Proofs.Checker..."
#lake build Cpc.Proofs.Checker

echo "Compiling CpcMini.Proofs.Checker..."
lake build CpcMini.Proofs.Checker

echo "Compiling CpcMini.Examples.TestSimpleCheckerAssumptions..."
lake build CpcMini.Examples.TestSimpleCheckerAssumptions

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
