#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install/install-cpc.sh [OPTION]... [SIGNATURE.eo]

Regenerate both packages of this repository, Cpc and CpcMini, from a Eunoia
signature:

  install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo

The run also records that signature in install/defs, which --cached then
compiles in place of naming one:

  install/install-cpc.sh --cached

Less commonly, what the packages are compiled *to* is what is being changed
rather than the calculus they are of. What each symbol of the signature means
is install/defs/Cpc.eos, and what the SMT-LIB symbols it is written against
mean is a configuration the compiler ships; either can be named:

  install/install-cpc.sh --cached --semantics ~/Cpc.eos
  install/install-cpc.sh --cached --smt-semantics ~/smt.eos

A run that names one regenerates the packages against a semantics other than
the pair the checked-in packages are of, so it is for trying a change to the
semantics out rather than for a normal update.

Options:
  --cached             compile the recorded copy of the signature
  --check              install nothing; report whether either package is out
                       of date and exit 1 if either is. Both are checked
  --ethos PATH         an ethos source tree to compile with
  --semantics PATH     what the symbols of the signature mean
                       (default: install/defs/Cpc.eos)
  --smt-semantics PATH what the symbols of SMT-LIB those are written against
                       mean (default: the one the compiler ships)
  -h, --help           show this message

Anything else is handed to install-sig.sh, which this runs once per package;
see install/install-sig.sh --help. --mini and --package are refused, since
which packages are installed is what this script decides.
USAGE
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
INSTALL_SIG="${script_dir}/install-sig.sh"
[ -f "${INSTALL_SIG}" ] || { echo "error: ${INSTALL_SIG} not found." >&2; exit 1; }

CHECK=0
SIGNATURE=""
want_signature=0
want_value=0
for arg in "$@"; do
  if [ "${want_signature}" = "1" ]; then
    SIGNATURE="${arg}"
    want_signature=0
    continue
  fi
  # The value of any other option that takes one, stepped over rather than
  # read: this loop is looking for the signature, and a semantics or an ethos
  # tree named as a separate word is not one however it is spelled.
  if [ "${want_value}" = "1" ]; then
    want_value=0
    continue
  fi
  case "${arg}" in
    -h|--help) usage; exit 0 ;;
    --check) CHECK=1 ;;
    --cached) SIGNATURE="the cached signature" ;;
    --signature) want_signature=1 ;;
    --signature=*) SIGNATURE="${arg#*=}" ;;
    --semantics|--smt-semantics|--lean-config|--cache|--ethos|--build-dir|--out-dir|--deps-dir)
      want_value=1 ;;
    --mini|--package|--package=*)
      echo "error: ${arg} asks for one package, and this script is the two of" >&2
      echo "them. Run install/install-sig.sh for a single package." >&2
      exit 2
      ;;
    -*) ;;
    *.eo) SIGNATURE="${arg}" ;;
  esac
done

if [ -z "${SIGNATURE}" ]; then
  echo "error: no signature to compile. Name one, e.g." >&2
  echo "  install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo" >&2
  echo "or compile the copy kept in this repository with --cached." >&2
  exit 2
fi

if [ "${CHECK}" = "1" ]; then
  cpc=0
  mini=0
  bash "${INSTALL_SIG}" --brief "$@" || cpc=1
  echo
  bash "${INSTALL_SIG}" --brief "$@" --mini || mini=1

  echo
  if [ "${cpc}" = "0" ] && [ "${mini}" = "0" ]; then
    echo "==> Cpc and CpcMini are both up to date with ${SIGNATURE}."
    echo "Nothing was written."
    exit 0
  fi
  if [ "${cpc}" = "1" ] && [ "${mini}" = "1" ]; then
    echo "==> Neither Cpc nor CpcMini is what ${SIGNATURE} compiles to."
  elif [ "${cpc}" = "1" ]; then
    echo "==> Cpc is not what ${SIGNATURE} compiles to. CpcMini is."
  else
    echo "==> CpcMini is not what ${SIGNATURE} compiles to. Cpc is."
  fi
  echo "Nothing was written. Rerun without --check to apply."
  exit 1
fi

# An install, where the second run has no business starting if the first did
# not finish: set -e stops here.
bash "${INSTALL_SIG}" --brief "$@"
echo
bash "${INSTALL_SIG}" --brief "$@" --mini

cat <<DONE

==> Done. Cpc and CpcMini regenerated from ${SIGNATURE}.

Build them with:

  scripts/build.sh Cpc CpcMini

A preserved rule file whose statement the calculus has changed will fail to
build; a newly written one has \`sorry\` for a proof. Review with git diff
before committing.
DONE
