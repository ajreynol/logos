#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install/install-cpc.sh [OPTION]...

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

The signature to compile is always named with --signature. It is not
something install/get-eo-compiler.sh fetches, so any signature reachable on
this machine -- a cvc5 checkout, or one being worked on locally -- can be
compiled without downloading anything.

A copy of the signature the packages here were last compiled from is kept in
this repository as a single file, install/defs/Cpc.eo, with every (include ...)
of the original spliced in and its comments dropped. --cached compiles that
copy, which is how the packages can be regenerated, and checked, without a
cvc5 checkout at all; it is what CI does.

An install of Cpc or CpcMini rewrites that copy itself, so the two cannot
drift: what a full run compiled is what gets recorded. An install that selects
rules with --rules compiles a reduced calculus, and one into another package
says nothing about these two, so neither records anything and both say so.
--no-update-cache leaves the copy alone whatever the run; --update-cache
rewrites it without installing anything and needs no compiler.

The compiler comes from install/deps/eoc-env.sh, which
install/get-eo-compiler.sh writes, unless --ethos names another ethos tree.

Options:
  --signature PATH     the Eunoia signature to compile, e.g.
                       <cvc5>/proofs/eo/cpc/Cpc.eo. Required unless --cached
                       names the copy kept here instead
  --ethos PATH         an ethos source tree containing tools/eoc/driver.py
                       (default: the one install/deps/eoc-env.sh records).
                       Also redirects --build-dir, --defs and --lean-config to
                       that tree, so a local checkout is never mixed with
                       install/deps/
  --cached             compile the copy of the signature kept in this
                       repository instead of naming one with --signature
  --update-cache       do not install: rewrite that copy from the signature
                       named by --signature, splicing in every file it
                       includes and dropping every comment, and exit. No
                       compiler is needed for this
  --no-update-cache    do not record the compiled signature in that copy,
                       which a full install of Cpc or CpcMini otherwise does
  --cache PATH         where that copy lives
                       (default: <install>/defs/Cpc.eo)
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
  --check              do not install anything: compile, compare against the
                       package, and exit 0 only if it is already up to date,
                       1 if an install would change it. Every other option
                       means the same under --check as without it
  --defs PATH          the signature of the input written in the deep
                       embedding, read by the model-smt stage
  --lean-config PATH   why each recursive program of the input terminates,
                       read by the lean-meta stage
  --build-dir DIR      the ethos-eoc build tree
  --out-dir DIR        where to stage what the compiler publishes before it is
                       installed (default: <deps>/eoc-out)
  --deps-dir DIR       where eoc-env.sh is (default: <install>/deps)
  --jobs N             parallel compile jobs if ethos-eoc has to be built
  -h, --help           show this message

Examples:
  install/install-cpc.sh --signature ~/cvc5/proofs/eo/cpc/Cpc.eo
  install/install-cpc.sh --signature ~/cvc5/proofs/eo/cpc/Cpc.eo --update-cache
  install/install-cpc.sh --cached
  install/install-cpc.sh --cached --check
  install/install-cpc.sh --signature ~/cvc5/proofs/eo/cpc/Cpc.eo --mini
  install/install-cpc.sh --signature ~/sig.eo --package Mine --no-parser \
    --rules symm refl trans
USAGE
}

# A leading ~ in --option=VALUE is not the shell's to expand: it does that at
# the start of a word, and there the word starts with --option. So the tilde
# arrives here as a character, and every option that takes a path expands it
# the way the shell would have. ~user is left alone, since resolving that needs
# more than $HOME.
expand_tilde() {
  case "$1" in
    "~") printf '%s\n' "${HOME}" ;;
    "~/"*) printf '%s\n' "${HOME}/${1#\~/}" ;;
    *) printf '%s\n' "$1" ;;
  esac
}

SIGNATURE=""
CACHED=0
UPDATE_CACHE=0
NO_UPDATE_CACHE=0
CACHE_FILE=""
ETHOS_DIR=""
ETHOS_GIVEN=0
PACKAGE=""
MINI=0
declare -a RULES=()
RULES_GIVEN=0
NO_PARSER=0
NO_PARTIAL=0
OVERWRITE_RULES=0
CHECK=0
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
    --cached) CACHED=1; shift ;;
    --update-cache) UPDATE_CACHE=1; shift ;;
    --no-update-cache) NO_UPDATE_CACHE=1; shift ;;
    --cache) CACHE_FILE="${2:?--cache requires a value}"; shift 2 ;;
    --cache=*) CACHE_FILE="${1#*=}"; shift ;;
    --ethos) ETHOS_DIR="${2:?--ethos requires a value}"; ETHOS_GIVEN=1; shift 2 ;;
    --ethos=*) ETHOS_DIR="${1#*=}"; ETHOS_GIVEN=1; shift ;;
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
    --check) CHECK=1; shift ;;
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

# --mini selects rules of its own further down, so whether this run was asked
# to compile a reduced calculus is a question about the command line and has to
# be answered while that is still what RULES_GIVEN says.
RULES_ASKED_FOR="${RULES_GIVEN}"

# Every option above that takes a path, whether it arrived as --option VALUE or
# as --option=VALUE.
SIGNATURE="$(expand_tilde "${SIGNATURE}")"
CACHE_FILE="$(expand_tilde "${CACHE_FILE}")"
ETHOS_DIR="$(expand_tilde "${ETHOS_DIR}")"
DEFS="$(expand_tilde "${DEFS}")"
LEAN_CONFIG="$(expand_tilde "${LEAN_CONFIG}")"
BUILD_DIR="$(expand_tilde "${BUILD_DIR}")"
OUT_DIR="$(expand_tilde "${OUT_DIR}")"
DEPS_DIR="$(expand_tilde "${DEPS_DIR}")"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/.." && pwd)"
DEPS_DIR="${DEPS_DIR:-${script_dir}/deps}"
CACHE_FILE="${CACHE_FILE:-${repo_root}/install/defs/Cpc.eo}"

# What get-eo-compiler.sh installed, if it has been run. Anything named on the
# command line wins over it.
ENV_FILE="${DEPS_DIR}/eoc-env.sh"
if [ -f "${ENV_FILE}" ]; then
  # shellcheck source=/dev/null
  source "${ENV_FILE}"
fi

# --ethos names a tree that is not the one install/deps/eoc-env.sh describes,
# so the recorded build directory, defs and lean config belong to another ethos
# and must not be used as defaults for it. Deriving them from the named tree
# instead is what keeps a local-checkout run from silently mixing the two:
# the binary under the recorded build dir resolves its templates against the
# tree it was configured from, so a mixed run compiles with the wrong
# templates and still exits 0.
if [ "${ETHOS_GIVEN}" = "1" ]; then
  EOC_BUILD_DIR=""
  EOC_DEFS=""
  EOC_LEAN_CONFIG=""
fi

ETHOS_DIR="${ETHOS_DIR:-${EOC_ETHOS_DIR:-}}"

# Where the signature $1 sits, for the header of the cached copy: the path it
# has inside the checkout it came from, which is the same path in any copy of
# that project, or its name when it is not in one. What is deliberately not
# here is the commit -- see signature_version.
signature_location() {
  local dir sig top
  dir="$(cd "$(dirname "$1")" && pwd)"
  sig="${dir}/$(basename "$1")"
  if top="$(git -C "${dir}" rev-parse --show-toplevel 2>/dev/null)"; then
    printf '%s\n' "${sig#"${top}"/}"
  else
    printf '%s\n' "$(basename "${sig}")"
  fi
}

# The version of the checkout the signature $1 came from, for the terminal and
# not for the file. It is what identifies the signature to a person, but
# writing it into the copy would make the copy depend on which checkout it was
# made from rather than on the calculus: two people flattening the same
# signature from two checkouts would then produce two different files, and an
# install would rewrite a line that says nothing about what it compiles to.
# Empty when there is no checkout to name.
signature_version() {
  local dir sha
  dir="$(cd "$(dirname "$1")" && pwd)"
  git -C "${dir}" rev-parse --show-toplevel >/dev/null 2>&1 || return 0
  sha="$(git -C "${dir}" rev-parse HEAD 2>/dev/null)" || return 0
  if [ -n "$(git -C "${dir}" status --porcelain -- "${dir}" 2>/dev/null)" ]; then
    printf '%s, with uncommitted changes under %s\n' "${sha}" "$(basename "${dir}")"
  else
    printf '%s\n' "${sha}"
  fi
}

# Write the signature $1 to $2 as a single file: every (include "...") replaced
# by the text of the file it names, depth first, each file written only the
# first time it is reached, and every comment dropped. Writing a file once is
# what makes the result equivalent to the original rather than a redeclaration
# of everything the tree shares: ethos also reads a file only the first time it
# is named, see markIncluded in its src/state.cpp. Which lines name a file is
# decided the way driver.py decides it, see INCLUDE_RE and strip_comment there,
# so the copy contains the files a compilation of the original would have read
# and no others.
flatten_signature() {
  python3 - "$1" "$2" "$(signature_location "$1")" <<'PY'
import os
import re
import sys

INCLUDE_RE = re.compile(r'^\(include\s+"([^"]+)"\s*\)')
# Anything else that names another file. Splicing cannot represent it, and
# leaving it in place would resolve it against the copy's own directory, so
# stop instead of writing a file that quietly means something else.
UNSPLICEABLE_RE = re.compile(r"^\((include|reference)\b")

HEADER = """\
; This file is generated by install/install-cpc.sh --update-cache. Do not edit
; it, and do not read it as the upstream signature: it is a copy of one.
;
; It is the Eunoia signature that the Cpc and CpcMini packages of this
; repository were compiled from, written as a single file: every
; (include "...") of the original replaced by the text of the file it names,
; each file appearing once and in the order ethos reads them, and the comments
; of the original dropped. Compiling this produces the same Lean as compiling
; the original tree, so a regeneration needs nothing but this repository. Read
; the original for the prose; what is here is what the compiler acts on, which
; is also what makes a diff of this file a diff of the calculus.
;
; Read from:
;   %s
;
; Which checkout that was, and at what commit, is deliberately not written
; here: this file is then a function of the signature and of nothing else, so
; regenerating from another copy of the same calculus leaves it alone rather
; than rewriting a line that says nothing about what it compiles to. The
; commit belongs in the message of whatever commit updates this file.
;
; scripts/run-ci.sh regeneration compiles it and fails if what comes out
; differs from what is committed under Cpc/ and CpcMini/, which is what makes
; a generated package that no longer matches the signature visible.
"""


def strip_comments(text):
    """The lines of `text` with every comment removed, and with the lines that
    leaves empty dropped along with the ones that already were.

    A `;` inside a string literal or a |quoted symbol| is content rather than
    the start of a comment, and a line that begins inside either is passed
    through untouched, since its blankness and its trailing spaces are content
    too. `""` is how a string literal spells a quote, so it does not end one.
    """
    lines = []
    line = []
    quote = ""
    quoted_at_start = False
    index = 0
    length = len(text)

    def end_line():
        joined = "".join(line)
        if quoted_at_start or quote:
            lines.append(joined)
        elif joined.strip():
            lines.append(joined.rstrip())

    while index < length:
        char = text[index]
        if char == "\n":
            end_line()
            del line[:]
            quoted_at_start = bool(quote)
            index += 1
            continue
        if not quote:
            if char == ";":
                newline = text.find("\n", index)
                index = length if newline < 0 else newline
                continue
            if char in '"|':
                quote = char
        elif char == quote:
            if char == '"' and text[index + 1 : index + 2] == '"':
                line.append(char)
                index += 1
                char = text[index]
            else:
                quote = ""
        line.append(char)
        index += 1
    end_line()
    if quote:
        sys.exit("error: a %s left open at the end of the file." % quote)
    return lines


source, dest, location = sys.argv[1], sys.argv[2], sys.argv[3]
root = os.path.realpath(source)
base = os.path.dirname(root)
seen = set()
out = []


def name_of(path):
    return os.path.relpath(path, base)


def visit(path, named_by):
    real = os.path.realpath(path)
    if not os.path.isfile(real):
        sys.exit("error: %s includes %s, which is not there." % (named_by, path))
    if real in seen:
        out.append("; (%s is included above)\n" % name_of(real))
        return
    seen.add(real)
    out.append("\n; ==== %s ====\n" % name_of(real))
    with open(real) as handle:
        text = handle.read()
    for line in strip_comments(text):
        command = line.strip()
        match = INCLUDE_RE.match(command)
        if match:
            visit(os.path.join(os.path.dirname(real), match.group(1)), name_of(real))
            continue
        if UNSPLICEABLE_RE.match(command):
            sys.exit("error: %s: cannot splice `%s` into one file." % (name_of(real), command))
        out.append(line + "\n")


visit(root, os.path.basename(root))
with open(dest, "w") as handle:
    handle.write(HEADER % location)
    handle.write("".join(out))
PY
}

if [ "${CACHED}" = "1" ] && [ "${UPDATE_CACHE}" = "1" ]; then
  echo "error: --update-cache writes the cached signature from the one named" >&2
  echo "by --signature, so there is nothing for --cached to say to it." >&2
  exit 2
fi
if [ "${UPDATE_CACHE}" = "1" ] && [ "${CHECK}" = "1" ]; then
  echo "error: --update-cache writes the cached signature and --check writes" >&2
  echo "nothing at all. Give one or the other." >&2
  exit 2
fi

# --cached is --signature with the one path this repository keeps filled in.
if [ "${CACHED}" = "1" ]; then
  if [ -n "${SIGNATURE}" ]; then
    echo "error: --cached and --signature name two different signatures." >&2
    echo "Give one or the other." >&2
    exit 2
  fi
  if [ ! -f "${CACHE_FILE}" ]; then
    echo "error: there is no cached signature at ${CACHE_FILE}." >&2
    echo "Write one with --signature <path> --update-cache." >&2
    exit 1
  fi
  SIGNATURE="${CACHE_FILE}"
fi

if [ -z "${SIGNATURE}" ]; then
  echo "error: no signature to compile. Name one with --signature, e.g." >&2
  echo "  install/install-cpc.sh --signature ~/cvc5/proofs/eo/cpc/Cpc.eo" >&2
  echo "or compile the copy kept in this repository with --cached." >&2
  exit 2
fi
[ -f "${SIGNATURE}" ] || { echo "error: signature ${SIGNATURE} not found." >&2; exit 1; }

# Nothing below this is needed to record a signature: the copy is made out of
# the signature alone, so --update-cache works on a machine that has never run
# get-eo-compiler.sh.
if [ "${UPDATE_CACHE}" = "1" ]; then
  echo "==> Writing ${SIGNATURE} to ${CACHE_FILE} as a single file"
  mkdir -p "$(dirname "${CACHE_FILE}")"
  flatten_signature "${SIGNATURE}" "${CACHE_FILE}"
  echo "    $(grep -c '^; ==== ' "${CACHE_FILE}") file(s) spliced in, $(wc -l < "${CACHE_FILE}") lines"
  version="$(signature_version "${SIGNATURE}")"
  cat <<DONE

==> Done. The cached signature is now ${SIGNATURE}.
DONE
  if [ -n "${version}" ]; then
    cat <<DONE

It was read at commit
  ${version}
which the copy does not record: put that in the message of the commit that
updates it.
DONE
  fi
  cat <<DONE

Nothing was compiled and no package was installed. Check that the packages
match what was just recorded with:

  install/install-cpc.sh --cached --check
  install/install-cpc.sh --cached --mini --check
DONE
  exit 0
fi

if [ -z "${ETHOS_DIR}" ]; then
  echo "error: no ethos tree to work from. Run install/get-eo-compiler.sh" >&2
  echo "first, or name one with --ethos. See --help." >&2
  exit 1
fi

DRIVER="${ETHOS_DIR}/tools/eoc/driver.py"
[ -f "${DRIVER}" ] || { echo "error: ${DRIVER} not found." >&2; exit 1; }

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
PACKAGE_DIR="${DEST_DIR}"

# --check performs the whole install into a throwaway copy of the package and
# then compares, rather than reimplementing what an install would have done.
# Every step below runs unchanged against that copy, so the check cannot drift
# from the install it is checking: a file the install would not touch was
# copied verbatim and compares equal, and whatever differs at the end is
# exactly the set of changes an install would make.
if [ "${CHECK}" = "1" ]; then
  CHECK_DIR="$(mktemp -d "${TMPDIR:-/tmp}/install-cpc-check.XXXXXX")"
  trap 'rm -rf "${CHECK_DIR}"' EXIT INT TERM
  DEST_DIR="${CHECK_DIR}/${PACKAGE}"
  if [ -d "${PACKAGE_DIR}" ]; then
    cp -R "${PACKAGE_DIR}" "${DEST_DIR}"
  fi
fi

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
echo "    package  ${PACKAGE_DIR}"

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

if [ "${CHECK}" = "1" ]; then
  echo "==> Staging a copy of ${PACKAGE} to compare against"
else
  echo "==> Installing generated Lean files into ${DEST_DIR}"
fi
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
  [ "${CHECK}" = "1" ] || echo "    ${src} -> ${PACKAGE}/${dest}"
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
  [ "${CHECK}" = "1" ] || \
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

if [ "${CHECK}" = "1" ]; then
  staged="${CHECK_DIR}/staged.txt"
  current="${CHECK_DIR}/current.txt"
  ( cd "${DEST_DIR}" && find . -type f | sed 's|^\./||' | LC_ALL=C sort ) > "${staged}"
  if [ -d "${PACKAGE_DIR}" ]; then
    ( cd "${PACKAGE_DIR}" && find . -type f | sed 's|^\./||' | LC_ALL=C sort ) > "${current}"
  else
    : > "${current}"
  fi

  echo
  updates=0
  while IFS= read -r rel; do
    if [ ! -e "${PACKAGE_DIR}/${rel}" ]; then
      echo "  add     ${PACKAGE}/${rel}"
      updates=$((updates + 1))
    elif ! cmp -s "${DEST_DIR}/${rel}" "${PACKAGE_DIR}/${rel}"; then
      echo "  update  ${PACKAGE}/${rel}"
      updates=$((updates + 1))
    fi
  done < "${staged}"
  while IFS= read -r rel; do
    if [ ! -e "${DEST_DIR}/${rel}" ]; then
      echo "  remove  ${PACKAGE}/${rel}"
      updates=$((updates + 1))
    fi
  done < "${current}"

  if [ "${updates}" -eq 0 ]; then
    echo "==> ${PACKAGE} is up to date with ${SIGNATURE}."
    echo "Nothing was written."
    exit 0
  fi
  echo
  echo "==> ${PACKAGE} is NOT up to date with ${SIGNATURE}: ${updates} file(s)."
  echo "Nothing was written. Rerun without --check to apply."
  exit 1
fi

# CI compiles the cached copy, not whatever signature happens to be on the
# machine that ran the install, so the copy has to stay the signature the
# packages were generated from. A full install of Cpc or CpcMini is the thing
# that makes it so, and records it here rather than leaving that to be
# remembered as a second command.
#
# The two runs that must not: --rules installed a reduced calculus rather than
# the signature, and another package says nothing about these two. Recording
# either would repoint what CI compiles at a signature nothing here was built
# from. They report instead. --cached compiled the copy itself, so there is
# nothing to record either way.
cache_action=""
if [ "${CACHED}" = "0" ]; then
  fresh_cache="$(mktemp "${TMPDIR:-/tmp}/install-cpc-cache.XXXXXX")"
  if flatten_signature "${SIGNATURE}" "${fresh_cache}" &&
     ! cmp -s "${fresh_cache}" "${CACHE_FILE}"; then
    if [ "${NO_UPDATE_CACHE}" = "1" ]; then
      cache_action="skipped:--no-update-cache was given"
    elif [ "${RULES_ASKED_FOR}" = "1" ]; then
      cache_action="skipped:--rules compiled a reduced calculus"
    elif [ "${PACKAGE}" != "Cpc" ] && [ "${PACKAGE}" != "CpcMini" ]; then
      cache_action="skipped:${PACKAGE} is not a package the copy speaks for"
    else
      mkdir -p "$(dirname "${CACHE_FILE}")"
      cp "${fresh_cache}" "${CACHE_FILE}"
      cache_action="updated"
    fi
  fi
  rm -f "${fresh_cache}"
fi

cat <<DONE

==> Done. ${PACKAGE} regenerated from ${SIGNATURE}.

${copied} rule file(s) written, ${preserved} preserved. Build with:

  scripts/build.sh ${PACKAGE}

A preserved rule file whose statement the calculus has changed will fail to
build; a newly written one has \`sorry\` for a proof. Review with git diff
before committing.
DONE

case "${cache_action}" in
  updated)
    cat <<NOTE

==> ${CACHE_FILE#"${repo_root}/"} now records this signature.

That copy is what CI compiles, so commit it along with ${PACKAGE}.
NOTE
    version="$(signature_version "${SIGNATURE}")"
    [ -z "${version}" ] || cat <<NOTE

It was read at commit
  ${version}
which the copy does not record: put that in the commit message.
NOTE
    echo
    ;;
  skipped:*)
    cat <<NOTE

==> Note: the cached signature is not the one just compiled.

${CACHE_FILE#"${repo_root}/"} was left as it was, since ${cache_action#skipped:}.
It is what CI compiles. Record this signature there with:

  install/install-cpc.sh --signature ${SIGNATURE} --update-cache

NOTE
    ;;
esac
