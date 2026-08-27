# Regenerating the calculus

`Cpc` and `CpcMini` are compiled from the Eunoia definition of CPC rather than
written by hand. This directory is what does that:

```text
install/install-cpc.sh       regenerate Cpc and CpcMini from a signature
install/install-sig.sh       compile one signature into one package
install/get-eo-compiler.sh   fetch and build the compiler
install/defs/Cpc.cached.eo   the signature they compile, kept in git
install/deps/                the Ethos tree and the compiler, ignored by git
```

## Usage

```bash
install/get-eo-compiler.sh                          # once
install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo  # regenerate both packages
scripts/build.sh Cpc CpcMini                        # check the result
```

Passing the signature is the whole of a normal update. It can be any Eunoia
signature reachable on the machine, including one being edited; `Cpc.eo`
includes the rest of `proofs/eo` by relative path, so it has to sit in a
complete copy of that subtree. The run records what it compiled in
`install/defs/Cpc.cached.eo`.

With no signature to hand, `--cached` compiles that recorded copy:

```bash
install/install-cpc.sh --cached          # regenerate both from it
install/install-cpc.sh --cached --check  # ask whether both still match it
```

The options most often added to either of those:

```text
--check              install nothing; exit 1 if either package is out of date
--ethos PATH         compile with an Ethos checkout you already have
--overwrite-rules    replace existing rule files instead of preserving them
```

Both scripts take `--help` for the rest.

Requirements: `cmake` >= 3.12, a C++17 compiler, the GMP development headers
(`libgmp-dev` on Debian and Ubuntu, `gmp` on Homebrew), `python3`, `tar`, and
either `wget` or `curl`.

## What is generated and what is not

The signature-wide modules of the package, and one file per proof rule:

```text
Cpc/Logos.lean       Cpc/SmtModelDefs.lean   Cpc/Spec.lean
Cpc/LogosTerm.lean   Cpc/SmtValueOrder.lean  Cpc/Proofs/RuleLemmas.lean
Cpc/Parser.lean      Cpc/SmtModel.lean       Cpc/Proofs/Rules/<Rule>.lean
Cpc/SmtEval.lean
```

Everything else is hand-written and is left alone: `Cpc/Api*.lean`,
`Cpc/Diagnostics.lean`, and everything under `Cpc/Proofs/` other than
`RuleLemmas.lean` and `Rules/`.

Rule files are preserved. The compiler emits each rule as its statement with
`sorry` for a proof, and the proofs live in those same files, so an existing
file is kept and only a rule with no file yet gets the stub:

* a rule newly added to CPC appears as a `sorry` stub to discharge
* a rule whose *statement* changed keeps its old file and fails to build, which
  is how a proof needing attention shows up — build after an install to find
  them
* a reinstall over an up-to-date tree changes nothing

`--check` reports what an install would write and writes nothing, exiting 1 if
anything at all would change. It performs the install into a throwaway copy and
compares, so every other option means the same under `--check` as without it.

## The cached signature

`install/defs/Cpc.cached.eo` is the signature the packages were compiled from,
kept here as a single file: every `(include "...")` replaced by the text of the
file it names, each file appearing once, and comments dropped. It compiles to
the same Lean as the original tree, byte for byte, so `--cached` needs nothing
outside this repository — which is what the `regeneration` CI group uses to
check that the generated packages still match their signature.

An install of `Cpc` and `CpcMini` records the signature it compiled, and is the
only thing that writes the copy, so it and the packages stay in step. Two runs
record nothing and say so: `--rules`, which compiles a reduced calculus, and
`--package`, which installs something these two are not.

The header of the file names the path the signature had, not the checkout or
the commit; the scripts print the commit they read, for the message of the
commit that updates the copy.

`install/defs/` is not the `--defs` option, which names Ethos's `cpc_defs.eo`
and arrives with the compiler under `install/deps/`.

## install-sig.sh

`install-cpc.sh` is `install-sig.sh` run twice, once plain and once `--mini`.
Reach for `install-sig.sh` directly for one package, a reduced calculus, or a
package of your own; `install-cpc.sh` refuses `--mini` and `--package` rather
than pass them on.

`--rules` selects more than which rule files are installed: the compiler builds
the whole package around only the rules given, so the signature-wide modules
describe a calculus containing just those. Running
`install/install-sig.sh --rules symm` against `Cpc` therefore guts the package
rather than refreshing one rule. Use it with `--package` or `--mini`.

`--mini` is the same install into `CpcMini` with `--no-parser`, the five rules
`symm contra refl scope trans`, imports rewritten to `CpcMini`, and
`partial def` rewritten to `def`. Each of those is available on its own.

`--ethos` redirects the whole tree and not just the driver: the build
directory, the `--defs` file and the `--lean-config` file all come from the
tree it names, in preference to what `install/deps/eoc-env.sh` recorded.

## Pinning

The Ethos commit is not an option. It is hardcoded as `ETHOS_VERSION` in
`get-eo-compiler.sh`, currently `b9fc583f5a4838fcfcaade2d31f8cdc5f19c62a6` —
"Add core Eunoia compiler infrastructure (#229)". To move it, edit that line
and re-run both scripts.

The signature is pinned by copy: `install/defs/Cpc.cached.eo` is the one the
packages were compiled from, and `--cached` compiles exactly that.
