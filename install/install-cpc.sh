#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: install/install-cpc.sh [OPTION]... [SIGNATURE.eo]

Compile a Eunoia signature into both generated packages of this repository,
Cpc and CpcMini. It is install-sig.sh run twice -- once for the full calculus
and once with --mini -- which is what keeps the two packages descriptions of
the same signature rather than of whichever one each was last built from.

The signature is a path ending in .eo, or --cached for the copy this
repository keeps in install/defs:

  install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo
  install/install-cpc.sh --cached

Every option is handed to install-sig.sh, so anything it understands means the
same here; see install/install-sig.sh --help for all of them. The ones this is
usually run with:

  --cached             compile the copy of the signature kept in install/defs
  --check              do not install: report whether either package is out of
                       date and exit 1 if either is. Both are checked whatever
                       the first one says, so that one run names everything
                       that is stale rather than the first thing it meets
  --update-cache       do not install: record the signature in install/defs
  --ethos PATH         an ethos source tree to compile with
  -h, --help           show this message

--mini and --package are refused rather than passed through, since which
packages are installed is what this script is for. Reach for install-sig.sh
directly to install one package, a reduced calculus, or a package of your own.
USAGE
}

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
INSTALL_SIG="${script_dir}/install-sig.sh"
[ -f "${INSTALL_SIG}" ] || { echo "error: ${INSTALL_SIG} not found." >&2; exit 1; }

CHECK=0
UPDATE_CACHE=0
HAVE_SIGNATURE=0
for arg in "$@"; do
  case "${arg}" in
    -h|--help) usage; exit 0 ;;
    --check) CHECK=1 ;;
    --update-cache) UPDATE_CACHE=1 ;;
    --cached) HAVE_SIGNATURE=1 ;;
    --signature|--signature=*) HAVE_SIGNATURE=1 ;;
    --mini|--package|--package=*)
      echo "error: ${arg} asks for one package, and this script is the two of" >&2
      echo "them. Run install/install-sig.sh for a single package." >&2
      exit 2
      ;;
    -*) ;;
    *.eo) HAVE_SIGNATURE=1 ;;
  esac
done

if [ "${HAVE_SIGNATURE}" = "0" ]; then
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
  status=0
  bash "${INSTALL_SIG}" "$@" || status=1
  echo
  bash "${INSTALL_SIG}" "$@" --mini || status=1
  exit "${status}"
fi

# An install, where the second run has no business starting if the first did
# not finish: set -e stops here.
bash "${INSTALL_SIG}" "$@"
echo
bash "${INSTALL_SIG}" "$@" --mini
