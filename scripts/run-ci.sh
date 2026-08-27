#!/usr/bin/env bash

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

configure_lean_toolchain() {
  # shellcheck source=lean-toolchain-env.sh
  source "${script_dir}/lean-toolchain-env.sh"
  logos_configure_lean_toolchain
}

# Examples that Logos accepts as CPC derivations but whose terms fall outside the
# SMT-LIB fragment that Cpc/SmtModel.lean defines, so that the side conditions of
# correct___eo_is_refutation cannot be discharged for them. The `logos`
# executable reports `incomplete` and exits 2 for these; see the Correctness
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

# Compile the cached signature and require the package $1 to be exactly what
# comes out. Remaining arguments select the package the way install-cpc.sh
# does, so they are also what regenerating it takes.
check_regeneration() {
  local package="$1"
  shift
  if bash install/install-cpc.sh --cached --check "$@"; then
    return 0
  fi
  cat >&2 <<MSG

${package} is not what install/defs/Cpc.eo compiles to, so it no longer follows
the signature it is generated from. Either it was edited by hand where it is
generated, or it was regenerated from a signature that was never recorded.

Regenerate it from the cached signature with

  install/install-cpc.sh --cached${*:+ $*}

or, if the signature has moved on and the packages should follow it, record
the new one and regenerate from that:

  install/install-cpc.sh --signature <cvc5>/proofs/eo/cpc/Cpc.eo --update-cache
MSG
  exit 1
}

# The generated packages against the signature they came from, which this
# repository keeps a copy of. Needs the Eunoia compiler and nothing from cvc5;
# pass "skip" to pass silently where the compiler has not been set up, which is
# what running every group locally wants.
run_regeneration() {
  if [ ! -f install/deps/eoc-env.sh ]; then
    if [ "${1:-}" = "skip" ]; then
      echo "Skipping the regeneration check: install/deps/eoc-env.sh is not"
      echo "there, so the Eunoia compiler has not been set up. Run"
      echo "install/get-eo-compiler.sh once to include this check."
      return 0
    fi
    echo "The Eunoia compiler has not been set up: install/deps/eoc-env.sh" >&2
    echo "is not there. Run install/get-eo-compiler.sh first." >&2
    exit 1
  fi

  echo "Checking that Cpc is what the cached signature compiles to..."
  check_regeneration Cpc
  echo "Checking that CpcMini is what the cached signature compiles to..."
  check_regeneration CpcMini --mini
}

run_regressions() {
  echo "Checking the generated parser tables against the signature..."
  python3 scripts/check-parser-tables.py

  echo "Checking parser tests..."
  lake build Logos.Parser Cpc.Parser
  lake env lean test/Parser.lean
  lake env lean test/CpcParser.lean

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
    CpcMini.Proofs.TypePreservation.Nonvacuity
  )

  echo "Compiling the CpcMini proofs..."
  lake build "${targets[@]}"
}

group="${1:-all}"
case "${group}" in
  regressions)
    configure_lean_toolchain
    run_regressions
    ;;
  cpc-proofs)
    configure_lean_toolchain
    run_cpc_proofs
    ;;
  cpcmini)
    configure_lean_toolchain
    run_cpcmini
    ;;
  proof-hygiene)
    run_proof_hygiene
    ;;
  regeneration)
    run_regeneration
    ;;
  all)
    run_proof_hygiene
    run_regeneration skip
    configure_lean_toolchain
    run_regressions
    run_cpc_proofs
    run_cpcmini
    ;;
  *)
    echo "Usage: $0 [all|regressions|cpc-proofs|cpcmini|proof-hygiene|regeneration]" >&2
    exit 2
    ;;
esac

echo "CI group '${group}' passed."
