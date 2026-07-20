#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

run_regressions() {
  echo "Building logos executable..."
  lake build logos

  shopt -s nullglob
  local examples=(examples/*.cpc.lean)

  if [ "${#examples[@]}" -eq 0 ]; then
    echo "No regression examples found under examples/." >&2
    exit 1
  fi

  echo "Running ${#examples[@]} regression examples..."
  local example output result
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
}

run_cpc_examples() {
  shopt -s nullglob
  local examples=(Cpc/Examples/*.lean)

  if [ "${#examples[@]}" -eq 0 ]; then
    echo "No Cpc examples found under Cpc/Examples/." >&2
    exit 1
  fi

  local example module
  local modules=()
  for example in "${examples[@]}"; do
    module="${example%.lean}"
    modules+=("${module//\//.}")
  done

  echo "Compiling ${#modules[@]} Cpc example modules..."
  lake build "${modules[@]}"
}

run_cpc_proofs() {
  local targets=(
    Cpc.Spec
    Cpc.Proofs.Rules.Refl
    Cpc.Proofs.Rules.Contra
    Cpc.Proofs.Rules.Trans
    Cpc.Proofs.TypePreservation.Nonvacuity
  )

  echo "Compiling representative Cpc proof targets..."
  lake build "${targets[@]}"

  # Expensive and not currently used in CI checks:
  # Cpc.Proofs.Rules.Chain_resolution
  # Cpc.Proofs.Checker
}

run_cpcmini() {
  local targets=(
    CpcMini.Proofs.Checker
    CpcMini.Proofs.TypePreservation.Nonvacuity
    CpcMini.Examples.TestSimpleCheckerAssumptions
  )

  echo "Compiling CpcMini proof and example targets..."
  lake build "${targets[@]}"
}

group="${1:-all}"
case "${group}" in
  regressions)
    run_regressions
    ;;
  cpc-examples)
    run_cpc_examples
    ;;
  cpc-proofs)
    run_cpc_proofs
    ;;
  cpcmini)
    run_cpcmini
    ;;
  all)
    run_regressions
    run_cpc_examples
    run_cpc_proofs
    run_cpcmini
    ;;
  *)
    echo "Usage: $0 [all|regressions|cpc-examples|cpc-proofs|cpcmini]" >&2
    exit 2
    ;;
esac

echo "CI group '${group}' passed."
