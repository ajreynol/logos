#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: scripts/install-cpc.sh [OPTION]...

Compile a Eunoia signature with ethos-eoc and install the Lean files it
generates into a package of this repository, by default Cpc.

What is generated is the signature-wide part of the package: the checker, the
term and operator datatypes, the parser configuration, the SMT-LIB semantics
modules, the spec, the rule lemmas, and one file per proof rule. What is
hand-written -- everything under Proofs/ other than RuleLemmas.lean and
Rules/, and the Api and Diagnostics modules -- is left alone.

Existing files under Proofs/Rules/ are preserved, since those are where the
proofs of this repository live and the compiler only ever emits a statement
with `sorry` for a body. A rule that has no file yet gets that stub, which is
what makes a newly added rule of the calculus visible here as an obligation.
Pass --overwrite-rules to replace them instead, which discards proofs.

Where the compiler and the signature come from:

  * with no --ethos or --signature, from deps/eoc-env.sh, written by
    scripts/get-eo-compiler.sh -- run that first and this needs no arguments
  * otherwise from whatever those options name, so that a signature being
    worked on locally can be compiled without downloading anything

Options:
  --signature PATH     the Eunoia signature to compile
                       (default: the CPC signature recorded in deps/eoc-env.sh)
  --ethos PATH         an ethos source tree containing tools/eoc/driver.py
                       (default: the one recorded in deps/eoc-env.sh)
  --package NAME       the package under this repository to install into
                       (default: Cpc)
  --mini               shorthand for the reduced package: --package CpcMini
                       --no-parser --no-partial and the five rules below,
                       unless those are given explicitly
  --rules RULE...      compile only these rules; everything up to the next
                       option is taken as a rule name
                       (default: the whole signature)
  --no-parser          do not generate or install Parser.lean, and delete a
                       stale one from the package
  --no-partial         rewrite `partial def` to `def` in the installed package
  --overwrite-rules    replace existing files under Proofs/Rules/ instead of
                       preserving them
  --defs PATH          the signature of the input written in the deep
                       embedding, read by the model-smt stage
  --lean-config PATH   why each recursive program of the input terminates,
                       read by the lean-meta stage
  --build-dir DIR      the ethos-eoc build tree
  --out-dir DIR        where to stage what the compiler publishes before it is
                       installed (default: <deps>/eoc-out)
  --deps-dir DIR       where deps/eoc-env.sh is (default: <repo>/deps)
  --jobs N             parallel compile jobs if ethos-eoc has to be built
  -h, --help           show this message

Examples:
  scripts/install-cpc.sh
  scripts/install-cpc.sh --mini
  scripts/install-cpc.sh --signature ~/cvc5/proofs/eo/cpc/Cpc.eo
  scripts/install-cpc.sh --package CpcMini --no-parser --rules symm refl trans
USAGE
}

SIGNATURE=""
ETHOS_DIR=""
PACKAGE=""
MINI=0
declare -a RULES=()
RULES_GIVEN=0
NO_PARSER=0
NO_PARTIAL=0
OVERWRITE_RULES=0
DEFS=""
LEAN_CONFIG=""
BUILD_DIR=""
OUT_DIR=""
DEPS_DIR=""
JOBS=""

while [ $# -gt 0 ]; do
  case "$1" in
    --signature) SIGNATURE="${2:?--signature requires a value}"; shift 2 ;;
    --signature=*) SIGNATURE="${1#*=}"; shift ;;
    --ethos) ETHOS_DIR="${2:?--ethos requires a value}"; shift 2 ;;
    --ethos=*) ETHOS_DIR="${1#*=}"; shift ;;
    --package) PACKAGE="${2:?--package requires a value}"; shift 2 ;;
    --package=*) PACKAGE="${1#*=}"; shift ;;
    --mini) MINI=1; shift ;;
    --rules)
      shift
      RULES_GIVEN=1
      while [ $# -gt 0 ] && [ "${1#-}" = "$1" ]; do
        RULES+=("$1")
        shift
      done
      ;;
    --no-parser) NO_PARSER=1; shift ;;
    --no-partial) NO_PARTIAL=1; shift ;;
    --overwrite-rules) OVERWRITE_RULES=1; shift ;;
    --defs) DEFS="${2:?--defs requires a value}"; shift 2 ;;
    --defs=*) DEFS="${1#*=}"; shift ;;
    --lean-config) LEAN_CONFIG="${2:?--lean-config requires a value}"; shift 2 ;;
    --lean-config=*) LEAN_CONFIG="${1#*=}"; shift ;;
    --build-dir) BUILD_DIR="${2:?--build-dir requires a value}"; shift 2 ;;
    --build-dir=*) BUILD_DIR="${1#*=}"; shift ;;
    --out-dir) OUT_DIR="${2:?--out-dir requires a value}"; shift 2 ;;
    --out-dir=*) OUT_DIR="${1#*=}"; shift ;;
    --deps-dir) DEPS_DIR="${2:?--deps-dir requires a value}"; shift 2 ;;
    --deps-dir=*) DEPS_DIR="${1#*=}"; shift ;;
    --jobs) JOBS="${2:?--jobs requires a value}"; shift 2 ;;
    --jobs=*) JOBS="${1#*=}"; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unrecognized option $1" >&2; usage >&2; exit 2 ;;
  esac
done

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
DEPS_DIR="${DEPS_DIR:-${repo_root}/deps}"

# What get-eo-compiler.sh installed, if it has been run. Anything named on the
# command line wins over it.
ENV_FILE="${DEPS_DIR}/eoc-env.sh"
if [ -f "${ENV_FILE}" ]; then
  # shellcheck source=/dev/null
  source "${ENV_FILE}"
fi

ETHOS_DIR="${ETHOS_DIR:-${EOC_ETHOS_DIR:-}}"
SIGNATURE="${SIGNATURE:-${EOC_SIGNATURE:-}}"

if [ -z "${ETHOS_DIR}" ] || [ -z "${SIGNATURE}" ]; then
  echo "error: no ethos tree or signature to work from." >&2
  echo "Run scripts/get-eo-compiler.sh first, or name them with --ethos and" >&2
  echo "--signature. See --help." >&2
  exit 1
fi

DRIVER="${ETHOS_DIR}/tools/eoc/driver.py"
[ -f "${DRIVER}" ] || { echo "error: ${DRIVER} not found." >&2; exit 1; }
[ -f "${SIGNATURE}" ] || { echo "error: signature ${SIGNATURE} not found." >&2; exit 1; }

# The mini package is the same install with a different name, no parser, no
# `partial`, and a handful of rules. Each is still settable on its own.
if [ "${MINI}" = "1" ]; then
  PACKAGE="${PACKAGE:-CpcMini}"
  NO_PARSER=1
  NO_PARTIAL=1
  if [ "${RULES_GIVEN}" = "0" ]; then
    RULES=(symm contra refl scope trans)
    RULES_GIVEN=1
  fi
fi
PACKAGE="${PACKAGE:-Cpc}"

DEFS="${DEFS:-${EOC_DEFS:-${ETHOS_DIR}/plugins/model_smt/cpc_defs.eo}}"
LEAN_CONFIG="${LEAN_CONFIG:-${EOC_LEAN_CONFIG:-${ETHOS_DIR}/plugins/lean_meta/cpc_termination.lean}}"
BUILD_DIR="${BUILD_DIR:-${EOC_BUILD_DIR:-${ETHOS_DIR}/build-eoc}}"
OUT_DIR="${OUT_DIR:-${DEPS_DIR}/eoc-out}"
DEST_DIR="${repo_root}/${PACKAGE}"

[ -f "${DEFS}" ] || { echo "error: --defs file ${DEFS} not found." >&2; exit 1; }
[ -f "${LEAN_CONFIG}" ] || { echo "error: --lean-config file ${LEAN_CONFIG} not found." >&2; exit 1; }

# The signature-wide files the lean subcommand of driver.py publishes, in
# module dependency order, as "<name under out/lean> <destination relative to
# the package>". out/lean is the package with the leading Proofs component
# dropped, so RuleLemmas.lean goes back under Proofs/ and so do the per-rule
# files, which are handled separately below. This list has to cover everything
# the driver writes apart from Rules/; a file added there but not here is
# silently left behind.
LEAN_OUTPUTS=(
  "Logos.lean Logos.lean"
  "LogosTerm.lean LogosTerm.lean"
  "Parser.lean Parser.lean"
  "SmtEval.lean SmtEval.lean"
  "SmtModelDefs.lean SmtModelDefs.lean"
  "SmtValueOrder.lean SmtValueOrder.lean"
  "SmtModel.lean SmtModel.lean"
  "Spec.lean Spec.lean"
  "RuleLemmas.lean Proofs/RuleLemmas.lean"
)

# sed -i takes an argument on BSD and not on GNU; giving it a suffix and
# deleting the backup is what both accept.
sed_in_place() {
  sed -i.bak -e "$1" "$2"
  rm -f "$2.bak"
}

# The name of the calculus as the generated files spell it, read off the first
# import of the generated checker. Lean allows an `all` modifier before the
# module name, which is kept out of the captured name.
detect_generated_calc() {
  local logos_file="$1/Logos.lean" import_line
  [ -f "${logos_file}" ] || return 1
  import_line="$(grep -m1 '^import ' "${logos_file}" || true)"
  if [[ "${import_line}" =~ ^import[[:space:]]+(all[[:space:]]+)?([^.]+)\. ]]; then
    printf '%s\n' "${BASH_REMATCH[2]}"
    return 0
  fi
  return 1
}

# The calculus name driver.py derives from a file name, which is the file name
# up to its first dot in upper camel case. Keep in sync with input_base_name
# and lean_calc_name in tools/eoc/driver.py. Only a fallback: the name is read
# out of the generated files when they are there.
calc_name_of() {
  local stem calc="" part head rest
  stem="$(basename "$1")"
  stem="${stem%%.*}"
  for part in $(printf '%s' "${stem}" | tr -cs '[:alnum:]' ' '); do
    # Upper camel case, spelled without ${x^} so that bash 3.2 can run this.
    head="$(printf '%s' "${part}" | cut -c1 | tr '[:lower:]' '[:upper:]')"
    rest="$(printf '%s' "${part}" | cut -c2-)"
    calc+="${head}${rest}"
  done
  [ -n "${calc}" ] || calc="EoCalc"
  [[ "${calc}" =~ ^[[:alpha:]] ]] || calc="Calc${calc}"
  printf '%s\n' "${calc}"
}

echo "==> Compiling ${SIGNATURE}"
echo "    ethos    ${ETHOS_DIR}"
echo "    package  ${DEST_DIR}"

driver_args=(lean --build-dir "${BUILD_DIR}" --final-out-dir "${OUT_DIR}"
             --defs "${DEFS}" --lean-config "${LEAN_CONFIG}")
if [ -x "${BUILD_DIR}/ethos-eoc" ]; then
  driver_args+=(--no-build)
else
  echo "    ethos-eoc is not built yet; building it into ${BUILD_DIR}"
  [ -n "${JOBS}" ] && driver_args+=(--jobs "${JOBS}")
fi
[ "${NO_PARSER}" = "1" ] && driver_args+=(--no-parser)
if [ "${RULES_GIVEN}" = "1" ]; then
  if [ "${#RULES[@]}" -eq 0 ]; then
    echo "error: --rules was given with no rule names. Drop it to compile the" >&2
    echo "whole signature." >&2
    exit 2
  fi
  driver_args+=("${SIGNATURE}" "${RULES[@]}")
else
  driver_args+=(--all "${SIGNATURE}")
fi

python3 "${DRIVER}" "${driver_args[@]}"

LEAN_DIR="${OUT_DIR}/lean"
[ -d "${LEAN_DIR}" ] || { echo "error: the compiler published nothing in ${LEAN_DIR}." >&2; exit 1; }

echo "==> Installing generated Lean files into ${DEST_DIR}"
mkdir -p "${DEST_DIR}" "${DEST_DIR}/Proofs" "${DEST_DIR}/Proofs/Rules"
for entry in "${LEAN_OUTPUTS[@]}"; do
  read -r src dest <<< "${entry}"
  if [ "${NO_PARSER}" = "1" ] && [ "${src}" = "Parser.lean" ]; then
    rm -f "${DEST_DIR}/${dest}"
    continue
  fi
  if [ ! -f "${LEAN_DIR}/${src}" ]; then
    echo "error: ${LEAN_DIR}/${src} was not generated." >&2
    exit 1
  fi
  echo "    ${src} -> ${PACKAGE}/${dest}"
  cp "${LEAN_DIR}/${src}" "${DEST_DIR}/${dest}"
done

copied=0
preserved=0
if [ -d "${LEAN_DIR}/Rules" ]; then
  shopt -s nullglob
  for file in "${LEAN_DIR}"/Rules/*.lean; do
    rule_dest="${DEST_DIR}/Proofs/Rules/$(basename "${file}")"
    if [ "${OVERWRITE_RULES}" = "0" ] && [ -e "${rule_dest}" ]; then
      preserved=$((preserved + 1))
      continue
    fi
    cp "${file}" "${rule_dest}"
    copied=$((copied + 1))
  done
  shopt -u nullglob
  echo "    Rules/*.lean -> ${PACKAGE}/Proofs/Rules/ (${copied} written, ${preserved} existing preserved)"
fi

# The generated files import each other under the name the compiler gave the
# calculus, which is the name of the signature file. Point them at the package
# they were just installed into, which for CpcMini is not that name.
SRC_CALC="$(detect_generated_calc "${LEAN_DIR}" || calc_name_of "${SIGNATURE}")"
if [ "${SRC_CALC}" != "${PACKAGE}" ]; then
  echo "==> Rewriting imports from ${SRC_CALC} to ${PACKAGE}"
  while IFS= read -r -d '' file; do
    sed_in_place \
      "s/import \\(all \\)\\{0,1\\}${SRC_CALC}\\./import \\1${PACKAGE}\\./g" \
      "${file}"
  done < <(find "${DEST_DIR}" -type f -name '*.lean' -print0)
fi

if [ "${NO_PARTIAL}" = "1" ]; then
  echo "==> Rewriting partial def to def in ${PACKAGE}"
  while IFS= read -r -d '' file; do
    sed_in_place 's/partial def /def /g' "${file}"
  done < <(find "${DEST_DIR}" -type f -name '*.lean' -print0)
fi

cat <<DONE

==> Done. ${PACKAGE} regenerated from ${SIGNATURE}.

${copied} rule file(s) written, ${preserved} preserved. Build with:

  scripts/build.sh ${PACKAGE}

A preserved rule file whose statement the calculus has changed will fail to
build; a newly written one has \`sorry\` for a proof. Review with git diff
before committing.
DONE
