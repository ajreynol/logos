# Regeneration scripts for the Logos repository

Two scripts to copy into `scripts/` of <https://github.com/ajreynol/logos>.
They replace `tools/eoc/cpc/install_logos` and `install_logos_mini` in the
ethos tree with an equivalent that runs from Logos and drives ethos through its
public interface, `tools/eoc/driver.py`. Nothing in them depends on an
unreleased ethos branch: everything they use has been part of ethos `main`
since [#229](https://github.com/cvc5/ethos/pull/229).

```text
scripts/get-eo-compiler.sh   fetch and build the compiler and the signature
scripts/install-cpc.sh       compile a signature and install the Lean it emits
```

They are layered. `get-eo-compiler.sh` puts an ethos tree, an `ethos-eoc` built
from it, and the CPC signature under `deps/`, and records where each landed in
`deps/eoc-env.sh`. `install-cpc.sh` reads that file, so once the first has run
the second needs no arguments. The second is also usable on its own, against a
signature and an ethos checkout you already have.

## Usage

```bash
scripts/get-eo-compiler.sh          # once, and again to pick up new versions
scripts/install-cpc.sh              # regenerate the Cpc package
scripts/install-cpc.sh --mini       # regenerate the CpcMini package
scripts/build.sh Cpc CpcMini        # check the result
```

Working against a signature you are editing, with no download:

```bash
scripts/install-cpc.sh \
  --ethos ~/ethos \
  --signature ~/cvc5/proofs/eo/cpc/Cpc.eo
```

Add `deps/` to `.gitignore`. Both scripts take `--help`.

## What is generated and what is not

`install-cpc.sh` writes the signature-wide modules of the package and one file
per proof rule:

```text
Cpc/Logos.lean             Cpc/SmtModelDefs.lean      Cpc/Spec.lean
Cpc/LogosTerm.lean         Cpc/SmtValueOrder.lean     Cpc/Proofs/RuleLemmas.lean
Cpc/Parser.lean            Cpc/SmtModel.lean          Cpc/Proofs/Rules/<Rule>.lean
Cpc/SmtEval.lean
```

Everything else is hand-written and is never touched: `Cpc/Api*.lean`,
`Cpc/Diagnostics.lean`, and everything under `Cpc/Proofs/` other than
`RuleLemmas.lean` and `Rules/`, which is where `CheckerCore.lean`,
`RuleSupport/`, `Canonical/` and the rest live.

`out/lean` as the compiler publishes it is the package with the leading
`Proofs` component dropped, which is why `RuleLemmas.lean` is installed as
`Proofs/RuleLemmas.lean` and `Rules/<Rule>.lean` as `Proofs/Rules/<Rule>.lean`.
The `LEAN_OUTPUTS` table near the top of `install-cpc.sh` is that mapping; it
has to cover everything `driver.py` publishes apart from `Rules/`, and a file
added there but not here is silently left behind.

### Rule files are preserved

The compiler emits each rule as its theorem statement with `sorry` for a proof.
The proofs of this repository are in those same files, so an existing one is
kept and only a rule with no file yet gets the stub. That is what makes a rule
newly added to CPC show up here as an obligation, and it means a reinstall over
an up-to-date tree changes nothing at all.

`--overwrite-rules` replaces them instead. It discards proofs; it is for
inspecting what the compiler currently emits, not for a normal update.

A rule whose *statement* changed in the calculus keeps its old file and so
fails to build. That is the intended signal: the proof has to be revisited.
Find them by building after an install.

### The `--mini` package

`--mini` is the same install into `CpcMini` with `--no-parser`, the five rules
`symm contra refl scope trans`, and two rewrites: imports from the generated
calculus name to `CpcMini`, and `partial def` to `def`. Each of those is
available on its own if the reduced package ever needs a different shape.

## Why the compiler is built rather than downloaded

`ethos-eoc` is not published by any ethos release — the CI upload step ships
only the `ethos` checker binary. It also reads its Lean and Eunoia templates
out of the source tree it was configured against, so that tree has to be
fetched whether or not a binary is available. `driver.py` additionally copies
one file, `SmtEval.lean`, verbatim from `plugins/lean_meta/` rather than from
the build output.

The build is the standalone project in `plugins/`, which leaves the ordinary
ethos build untouched:

```bash
cmake -S plugins -B build-eoc -DCMAKE_BUILD_TYPE=Release
cmake --build build-eoc --target ethos-eoc
```

It needs cmake >= 3.12, a C++17 compiler and the GMP development headers
(`libgmp-dev` on Debian and Ubuntu, `gmp` on Homebrew). It takes about a
minute.

If a prebuilt binary is ever wanted, the templates can be relocated with
`ETHOS_PLUGIN_ROOT`, and the plugins' scratch output with
`ETHOS_PLUGIN_OUTPUT_DIR`; neither is needed for the layout these scripts set
up.

## What is taken from cvc5

Only `proofs/eo`, which is the Eunoia source of the calculus. The compiler
consumes the signature, not a cvc5 binary, so `get-eo-compiler.sh` extracts
that subtree from the archive and nothing else. A cvc5 binary is needed only to
regenerate `examples/`, which these scripts deliberately leave alone — that is
the `cpc_gen_logos.sh` path and it is a separate concern.

## Pinning

Both default to `main`. `get-eo-compiler.sh --ethos-version REF
--cvc5-version REF` takes any git ref, and the refs used are recorded in
`deps/eoc-env.sh`. Pin them in CI so that a regeneration is reproducible.

## Verified

Against ethos `main` at `b9fc583f` and the CPC signature of cvc5 at
`40a4bb7e43`, `install-cpc.sh` reproduces the `Cpc` and `CpcMini` packages of
this repository as of commit `351b8e0a` byte for byte, with all 591 rule files
preserved. Reinstalling over an up-to-date tree changes nothing; deleting one
rule file and reinstalling restores exactly that file, as a `sorry` stub.

### A naming difference to be aware of

Commit `4d4084a5` moved two spots away from what ethos `main` emits, in both
cases by renaming a generated binder:

```text
Cpc/Logos.lean     | t => ...        became   | x1 => ...
Cpc/SmtModel.lean  __smtx_seq_nth_wrong moved earlier in the file
```

The same pattern is in `Cpc/Proofs/Rules/Scope.lean`, whose statement binds
`(x1 : Term) (s : CState)` where ethos `main` emits `(A : Term) (root :
CState)`. The two are alpha-equivalent, so nothing is wrong with either, but it
means this repository is being kept in sync with an ethos that names generated
binders differently from `main`. Until that change is on `main`, an install run
against `main` will put the `main` spelling back in those places.

Whether that matters is a question for whoever owns the ethos side. If those
names are meant to be `x1`, the ethos change wants upstreaming; if not, the two
edits above will be reverted by the next install.
