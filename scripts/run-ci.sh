#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

# Examples that Logos accepts as CPC derivations but whose terms fall outside the
# SMT-LIB fragment that Cpc/SmtModel.lean defines, so that the side conditions of
# correct___eo_is_refutation cannot be discharged for them. The s-expression
# executables report `incomplete` and exit 2 for these; see the Correctness
# section of README.md.
#
#   examples/sexp/test-declare-sort.cpc  declares a sort of arity 1, and the
#   specification has no counterpart for a sort constructor applied to a sort.
incomplete_example() {
  case "$1" in
    examples/sexp/test-declare-sort.cpc) return 0 ;;
    *) return 1 ;;
  esac
}

# Run every example in a directory through a checker executable, requiring its
# final nonempty output line and its exit status to match what is expected.
run_examples() {
  local exe="$1" dir="$2" pattern="$3" expected="$4"

  shopt -s nullglob
  local examples=("${dir}"/${pattern})

  if [ "${#examples[@]}" -eq 0 ]; then
    echo "No examples found under ${dir}/." >&2
    exit 1
  fi

  echo "Running ${#examples[@]} examples from ${dir} through ${exe}..."
  local example output result status want want_status
  for example in "${examples[@]}"; do
    echo "::group::${example}"

    want="${expected}"
    want_status=0
    if incomplete_example "${example}"; then
      want="incomplete"
      want_status=2
    fi

    set +e
    output="$(lake exe "${exe}" "${example}" 2>&1)"
    status=$?
    set -e

    printf '%s\n' "${output}"
    if [ "${status}" -ne "${want_status}" ]; then
      echo "Expected ${example} to exit with status ${want_status}, got ${status}" >&2
      exit 1
    fi
    result="$(printf '%s\n' "${output}" | awk 'NF { line = $0 } END { print line }')"
    if [ "${result}" != "${want}" ]; then
      echo "Expected ${example} to report ${want}, got: ${result}" >&2
      exit 1
    fi
    echo "::endgroup::"
  done
}

run_proof_hygiene() {
  echo "Checking Cpc and CpcMini for proof escape hatches..."
  bash scripts/check-proof-hygiene.sh
}

run_regressions() {
  echo "Checking the generated parser tables against the signature..."
  python3 scripts/check-parser-tables.py

  echo "Checking parser tests..."
  lake build Logos.Parser
  lake env lean test/Parser.lean

  echo "Checking checker diagnostics..."
  lake build Cpc.Diagnostics
  lake env lean test/CheckerDiagnostics.lean

  echo "Building the CPC executables..."
  lake build logos logos-native

  # Proofs in the Lean term syntax, checked by logos-native.
  run_examples logos-native examples '*.cpc.lean' true
  # The same proofs in s-expression syntax, checked by logos (Cpc.Parser).
  run_examples logos examples/sexp '*.cpc' correct
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
    Cpc.ApiChecks
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
  # Cpc.ApiCorrect  (correctness of the executable; imports Cpc.Proofs.Checker)
}

run_cpcmini() {
  local targets=(
    CpcMini.Proofs.Checker
    CpcMini.ApiCorrect
    CpcMini.Proofs.TypePreservation.Nonvacuity
    CpcMini.Examples.TestSimpleCheckerAssumptions
  )

  echo "Compiling CpcMini proof and example targets..."
  lake build "${targets[@]}"

  echo "Building the CpcMini executables..."
  lake build logos-mini logos-mini-native
  run_examples logos-mini examples/sexp-mini '*.cpc' correct
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
  proof-hygiene)
    run_proof_hygiene
    ;;
  all)
    run_proof_hygiene
    run_regressions
    run_cpc_examples
    run_cpc_proofs
    run_cpcmini
    ;;
  *)
    echo "Usage: $0 [all|regressions|cpc-examples|cpc-proofs|cpcmini|proof-hygiene]" >&2
    exit 2
    ;;
esac

echo "CI group '${group}' passed."
