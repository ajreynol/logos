# Regeneration scripts

The `Cpc` and `CpcMini` packages are compiled from the Eunoia definition of CPC,
not written by hand. Two scripts do that compilation and install the result:

```text
scripts/get-eo-compiler.sh   fetch and build the compiler and the signature
scripts/install-cpc.sh       compile a signature and install the Lean it emits
```

They drive Ethos through its public interface, `tools/eoc/driver.py`, and
replace the older `tools/eoc/cpc/install_logos` and `install_logos_mini`
scripts that lived in the Ethos tree and reached back into this repository.
Nothing they use depends on an unreleased Ethos branch: `driver.py` and the
`lean_meta` templates have been on Ethos `main` since
[#229](https://github.com/cvc5/ethos/pull/229).

The two are layered. `get-eo-compiler.sh` puts an Ethos tree, an `ethos-eoc`
built from it, and the CPC signature under `deps/`, and records where each
landed in `deps/eoc-env.sh`. `install-cpc.sh` reads that file, so once the first
has run the second needs no arguments. The second is also usable on its own,
against a signature and an Ethos checkout you already have.

`deps/` is ignored by git.

## Usage

```bash
scripts/get-eo-compiler.sh          # once, and again to pick up a new signature
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

`--ethos` redirects the whole tree, not just the driver: the build directory,
the `--defs` file and the `--lean-config` file are all taken from the tree it
names, in preference to whatever `deps/eoc-env.sh` recorded. That matters
because `ethos-eoc` resolves its templates against the source tree it was
configured from, so a run that mixed the two would compile against the wrong
templates and still exit 0.

Both scripts take `--help`.

Requirements: `cmake` >= 3.12, a C++17 compiler, the GMP development headers
(`libgmp-dev` on Debian and Ubuntu, `gmp` on Homebrew), `python3`, `tar`, and
either `wget` or `curl`.

## What is generated and what is not

`install-cpc.sh` writes the signature-wide modules of the package and one file
per proof rule:

```text
Cpc/Logos.lean             Cpc/SmtModelDefs.lean      Cpc/Spec.lean
Cpc/LogosTerm.lean         Cpc/SmtValueOrder.lean     Cpc/Proofs/RuleLemmas.lean
Cpc/Parser.lean            Cpc/SmtModel.lean          Cpc/Proofs/Rules/<Rule>.lean
Cpc/SmtEval.lean
```

Everything else is hand-written and is not generated over: `Cpc/Api*.lean`,
`Cpc/Diagnostics.lean`, and everything under `Cpc/Proofs/` other than
`RuleLemmas.lean` and `Rules/`, which is where `CheckerCore.lean`,
`RuleSupport/`, `Canonical/` and the rest live.

Two `sed` passes do run over *every* `.lean` file in the package, hand-written
ones included: the import rewrite below, and the `partial def` rewrite that
`--no-partial` asks for. Neither matches anything in the hand-written files
today, but they are not excluded by construction.

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

### `--rules` compiles a reduced calculus

`--rules` does not merely select which rule files to install. The compiler
builds the whole package around only the rules it was given, so the
signature-wide modules it publishes describe a calculus containing just those
rules — `Logos.lean` loses the `__eo_cmd_step` cases of every other rule,
`Spec.lean` and `SmtModel.lean` shrink to match.

`install-cpc.sh` installs those reduced modules over the full ones. Running
`scripts/install-cpc.sh --rules symm` against `Cpc` therefore guts the package
rather than refreshing one rule. Use `--rules` with `--package`/`--mini` to
build a deliberately reduced package, and a full run for `Cpc`.

### The `--mini` package

`--mini` is the same install into `CpcMini` with `--no-parser`, the five rules
`symm contra refl scope trans`, and two rewrites: imports from the generated
calculus name to `CpcMini`, and `partial def` to `def`. Each of those is
available on its own if the reduced package ever needs a different shape.

## Why the compiler is built rather than downloaded

`ethos-eoc` is not published by any Ethos release — the CI upload step ships
`build/src`, which is the ordinary `ethos` checker binary; `ethos-eoc` is a
target of the separate `plugins/` project. It also reads its Lean and Eunoia
templates out of the source tree it was configured against, so that tree has to
be fetched whether or not a binary is available. `driver.py` additionally
copies one file, `SmtEval.lean`, verbatim from `plugins/lean_meta/` rather than
from the build output.

The build is the standalone project in `plugins/`, which leaves the ordinary
Ethos build untouched:

```bash
cmake -S plugins -B build-eoc -DCMAKE_BUILD_TYPE=Release
cmake --build build-eoc --target ethos-eoc
```

It takes about a minute.

If a prebuilt binary is ever wanted, the templates can be relocated with
`ETHOS_PLUGIN_ROOT`, and the plugins' scratch output with
`ETHOS_PLUGIN_OUTPUT_DIR`; neither is needed for the layout these scripts set
up.

## What is taken from cvc5, and why no cvc5 binary is needed

Only `proofs/eo` — 51 `.eo` files, about 640K — which is the Eunoia source of
the calculus. `Cpc.eo` includes the rest of that subtree by relative path, so
the subtree is extracted and nothing else in the cvc5 archive is.

The compiler consumes that *source text*. It never runs cvc5, and none of these
scripts needs a cvc5 binary or a cvc5 build. The dependency is on the cvc5
repository purely because that is where CPC is maintained. On Ethos `main`,
`tools/eoc/driver.py` does not mention cvc5 at all; the `--cvc5`/`--skip-cvc5`
options that exist on Ethos development branches belong to the `vc`/`batch`
subcommands, which generate SMT-LIB or SyGuS verification conditions and
optionally solve them. The `lean` pipeline these scripts use never touches
them.

A cvc5 binary is needed only to regenerate `examples/`, which these scripts
deliberately leave alone — that is the `cpc_gen_logos.sh` path and it is a
separate concern.

## Pinning

The Ethos commit is **not** an option. It is hardcoded as `ETHOS_VERSION` in
`get-eo-compiler.sh`, so what the compiler emits changes only when someone
moves the pin deliberately. It is currently
`b9fc583f5a4838fcfcaade2d31f8cdc5f19c62a6` — "Add core Eunoia compiler
infrastructure (#229)". To move it, edit that line and re-run both scripts.

The signature defaults to cvc5 `main` and is selectable:
`get-eo-compiler.sh --cvc5-version REF` takes any git ref. Both refs are
recorded in `deps/eoc-env.sh`.

## Verified

Against the pinned Ethos commit and the CPC signature of cvc5 `main`, on
2026-08-25:

* `get-eo-compiler.sh` completes from a clean `deps/`: it fetches Ethos,
  extracts `proofs/eo` from the cvc5 archive, builds `ethos-eoc`, and writes
  `deps/eoc-env.sh`.
* `install-cpc.sh` with no arguments compiles the whole signature, installs the
  nine signature-wide modules, and preserves all 591 existing rule files
  (`0 written, 591 existing preserved`).
* `install-cpc.sh --mini` installs `CpcMini`, preserves its 5 rule files, and
  applies both rewrites.
* Deleting one rule file and reinstalling restores exactly that file, as a
  `sorry` stub.
* Output is byte-identical to a build against the `ethosEoc3` development
  branch, i.e. the pin loses nothing relative to the branch this repository was
  last regenerated from.
* A signature declaring a symbol the `--defs` file gives no model semantics for
  fails loudly (`no model semantics found for <symbol>`) and installs nothing.

### Current drift from the committed packages

A full reinstall today does not reproduce the committed tree exactly. Four
files differ, all of them benign — the committed tree predates some template
changes on Ethos `main`:

```text
Cpc/Logos.lean             12 lines   native_str_indexof_rec drops an unused
                                      `len` parameter; one comment expanded
Cpc/Spec.lean              94 lines   the same 32 definitions, with one mutual
                                      block emitted in a different position
Cpc/SmtEval.lean            2 lines   comment added
Cpc/Proofs/RuleLemmas.lean  2 lines   two comments added
```

`CpcMini` differs in the corresponding three files. Nothing is added or
removed from either package; regenerating and committing the result is a
mechanical update whenever someone wants the two back in step.
