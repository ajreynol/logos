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

Options:
  --cached             compile the recorded copy of the signature
  --check              install nothing; report whether either package is out
                       of date and exit 1 if either is. Both are checked
  --update-cache       record the signature; install nothing
  --ethos PATH         an ethos source tree to compile with
  --no-update-cache    leave the recorded copy as it is
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
UPDATE_CACHE=0
SIGNATURE=""
want_signature=0
for arg in "$@"; do
  if [ "${want_signature}" = "1" ]; then
    SIGNATURE="${arg}"
    want_signature=0
    continue
  fi
  case "${arg}" in
    -h|--help) usage; exit 0 ;;
    --check) CHECK=1 ;;
    --update-cache) UPDATE_CACHE=1 ;;
    --cached) SIGNATURE="the cached signature" ;;
    --signature) want_signature=1 ;;
    --signature=*) SIGNATURE="${arg#*=}" ;;
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

# Recording the signature is one act, not one per package.
if [ "${UPDATE_CACHE}" = "1" ]; then
  exec bash "${INSTALL_SIG}" "$@"
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
