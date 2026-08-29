#!/usr/bin/env bash
#
# Modularity invariants of the checker layer, checked textually.
#
# These hold today and each one has drifted at least once, so they are checked
# rather than documented.  Nothing here builds anything: it is a grep pass over
# a dozen files and runs in well under a second.
#
# What is checked, and why it matters, is in docs/modularity.md.

set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
cd "${repo_root}"

fail=0
note() { printf '  %s\n' "$*"; }
bad()  { printf '  FAIL: %s\n' "$*" >&2; fail=1; }

# The hand-written checker layer, in dependency order.  A file added to the
# layer belongs in this list.
core_files() {
  local pkg="$1"
  printf '%s\n' \
    "${pkg}/Proofs/Common.lean" \
    "${pkg}/Proofs/Assumptions.lean" \
    "${pkg}/Proofs/RuleSupport/Contract.lean" \
    "${pkg}/Proofs/CheckerState.lean" \
    "${pkg}/Proofs/Invariants/Stability.lean" \
    "${pkg}/Proofs/CheckerCore.lean" \
    "${pkg}/Proofs/Checker.lean"
}

# 1. The two packages' soundness proofs are the same file.
#
# Cpc and CpcMini kept hand-maintained copies that diverged by 376 lines,
# because CpcMini did not need one invariant.  They were unforked; this is what
# keeps them that way.  It is also the property that makes Checker.lean a
# candidate for a shared template rather than a per-package file.
echo "Checking that Cpc and CpcMini share one Checker.lean..."
if diff -q \
     <(sed 's/\bCpcMini\./@PKG@./g' CpcMini/Proofs/Checker.lean) \
     <(sed 's/\bCpc\./@PKG@./g' Cpc/Proofs/Checker.lean) >/dev/null; then
  note "Cpc/Proofs/Checker.lean and CpcMini/Proofs/Checker.lean agree."
else
  bad "Cpc/Proofs/Checker.lean and CpcMini/Proofs/Checker.lean have diverged."
  bad "They are meant to be one file modulo the package name. Diff them with:"
  bad "  diff <(sed 's/\\bCpcMini\\./@PKG@./g' CpcMini/Proofs/Checker.lean) \\"
  bad "       <(sed 's/\\bCpc\\./@PKG@./g' Cpc/Proofs/Checker.lean)"
fi

# 2. The soundness proof names no rule and no operator.
#
# It is stated about a calculus it does not mention: adding a rule to the
# calculus must not require editing it.
echo "Checking that Checker.lean is calculus-agnostic..."
for pkg in Cpc CpcMini; do
  f="${pkg}/Proofs/Checker.lean"
  n=$(grep -c 'CRule\.' "${f}" || true)
  [ "${n}" = "0" ] || bad "${f} names ${n} CRule constructor(s); it must name none."
  n=$(grep -c 'UserOp' "${f}" || true)
  [ "${n}" = "0" ] || bad "${f} names ${n} UserOp(s); it must name none."
  n=$(grep -c 'AssumptionStability\|assumptionStability\|StableAssumption' "${f}" || true)
  [ "${n}" = "0" ] || bad "${f} names the stability invariant ${n} time(s). Use the checkerExtraInvariant slot."
done
[ "${fail}" = "0" ] && note "Checker.lean names no rule, no operator, no calculus-specific invariant."

# 3. The state machine names no invariant.
#
# CheckerState.lean is the layer a new checker reuses unchanged; an invariant
# appearing there is a commitment leaking out of CheckerCore.lean.
echo "Checking that CheckerState.lean carries no invariant..."
for pkg in Cpc CpcMini; do
  f="${pkg}/Proofs/CheckerState.lean"
  n=$(grep -c 'Invariant' "${f}" || true)
  [ "${n}" = "0" ] || bad "${f} mentions 'Invariant' ${n} time(s); invariants belong in CheckerCore.lean or Invariants/."
done

# 4. The checker layer depends on exactly one signature symbol.
#
# `and` is irreducible: the checker folds the proof state into an and-chain and
# soundness is stated about it.  `not`, `eq` and `imp` were removed and live in
# Proofs/CommonBoolOps.lean, which the checker does not import.  A new operator
# appearing here is a new requirement on every consumer's signature.
echo "Checking the checker layer's operator dependency..."
for pkg in Cpc CpcMini; do
  ops=$(cat $(core_files "${pkg}") 2>/dev/null \
          | grep -o 'UserOp\.[a-zA-Z_0-9]*' | sort -u | sed 's/UserOp\.//' | tr '\n' ' ')
  ops="${ops% }"
  if [ "${ops}" = "and" ]; then
    note "${pkg}: and"
  else
    bad "${pkg} checker layer depends on operators: ${ops:-<none>} (expected exactly: and)"
    bad "  A rule-only lemma probably landed in the checker layer; move it to Proofs/CommonBoolOps.lean."
  fi
done

echo
if [ "${fail}" = "0" ]; then
  echo "Checker modularity check passed."
else
  echo "Checker modularity check FAILED. See docs/modularity.md for what these invariants are for." >&2
  exit 1
fi
