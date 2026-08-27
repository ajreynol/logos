# Regenerating the calculus

The `Cpc` and `CpcMini` packages are compiled from the Eunoia definition of
CPC, not written by hand. This directory is everything that compilation takes:

```text
install/install-cpc.sh       regenerate Cpc and CpcMini from a signature
install/install-sig.sh       compile one signature into one package
install/get-eo-compiler.sh   fetch and build the compiler
install/defs/Cpc.cached.eo          the signature they compile, kept in git
install/deps/                the Ethos tree and the compiler built from it
```

The scripts drive Ethos through its public interface, `tools/eoc/driver.py`.
Nothing they use depends on an unreleased Ethos branch: `driver.py` and the
`lean_meta` templates have been on Ethos `main` since
[#229](https://github.com/cvc5/ethos/pull/229).

They are layered, and split along two lines. `get-eo-compiler.sh` sets up the
*compiler*; `install-sig.sh` compiles a *signature* into *a* package, and takes
every option there is for saying which signature, which package and which
rules; `install-cpc.sh` is the one to reach for day to day, and is
`install-sig.sh` run twice, for the two packages this repository generates.
Running it rather than the two runs by hand is what keeps `Cpc` and `CpcMini`
descriptions of the same signature.

`get-eo-compiler.sh` puts an Ethos tree and an `ethos-eoc` built from it under
`install/deps/`, and records where each landed in `install/deps/eoc-env.sh`. It
fetches nothing else — in particular no signature, and nothing from cvc5.
`install-sig.sh` reads that file, so the signature is the only thing it has to
be told. It is also usable against an Ethos checkout you already have, via
`--ethos`.

`install/deps/` is ignored by git. `install/defs/` is not: see [The cached
signature](#the-cached-signature).

## Usage

```bash
install/get-eo-compiler.sh                            # once
install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo    # both packages
scripts/build.sh Cpc CpcMini                          # check the result
```

The signature is any Eunoia signature reachable on the machine, so one being
edited is compiled the same way as one from a checkout. A bare path ending in
`.eo` is taken as the signature, which is what the runs above do; `--signature
PATH` spells the same thing out, and is what to use after `--rules`, since that
reads every following word as a rule name. The alternative to
naming one is `--cached`, which compiles the copy this repository keeps of the
signature the packages came from:

```bash
install/install-cpc.sh --cached          # regenerate both from that copy
install/install-cpc.sh --cached --check  # ask whether both still match it
```

One package at a time, a reduced calculus, or a package of your own is what
`install-sig.sh` is for; `install-cpc.sh` refuses `--mini` and `--package`
rather than pass them on, since which packages get installed is the whole of
what it decides.

Working against an Ethos checkout you already have, with no download at all:

```bash
install/install-sig.sh \
  --ethos ~/ethos \
  --signature ~/cvc5/proofs/eo/cpc/Cpc.eo
```

`--ethos` redirects the whole tree, not just the driver: the build directory,
the `--defs` file and the `--lean-config` file are all taken from the tree it
names, in preference to what `install/deps/eoc-env.sh` recorded. That matters
because `ethos-eoc` resolves its templates against the source tree it was
configured from, so a run that mixed the two would compile against the wrong
templates and still exit 0.

Both scripts take `--help`.

Requirements: `cmake` >= 3.12, a C++17 compiler, the GMP development headers
(`libgmp-dev` on Debian and Ubuntu, `gmp` on Homebrew), `python3`, `tar`, and
either `wget` or `curl`.

## What is generated and what is not

`install-sig.sh` writes the signature-wide modules of the package and one file
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
The `LEAN_OUTPUTS` table near the top of `install-sig.sh` is that mapping; it
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

`install-sig.sh` installs those reduced modules over the full ones. Running
`install/install-sig.sh --rules symm` against `Cpc` therefore guts the package
rather than refreshing one rule. Use `--rules` with `--package`/`--mini` to
build a deliberately reduced package, and a full run for `Cpc`.

### `--check` asks whether anything is out of date

`--check` compiles the signature, works out exactly what an install would
write, and installs nothing. It exits 0 only if the package already matches,
and 1 if anything at all would change, listing what:

```console
$ install/install-sig.sh --signature ~/cvc5/proofs/eo/cpc/Cpc.eo --check
  update  Cpc/Logos.lean
  add     Cpc/Proofs/Rules/NewRule.lean

==> Cpc is NOT up to date with ~/cvc5/proofs/eo/cpc/Cpc.eo: 2 file(s).
Nothing was written. Rerun without --check to apply.
```

It works by performing the whole install into a throwaway copy of the package
and comparing, so it reports what an install would actually do rather than a
separate opinion about it. Every other option means the same thing under
`--check` as without it, `--mini` and `--rules` included.

Note what this does and does not treat as out of date, which follows from rule
files being preserved:

* an existing rule file is up to date whatever its *proof* says, since an
  install would not touch it — a changed rule *statement* is caught by
  building, not by this
* a rule the calculus has that the package has no file for is out of date, as
  an install would write the `sorry` stub for it
* a `Parser.lean` that `--no-parser` would delete counts as out of date

### The `--mini` package

`--mini` is the same install into `CpcMini` with `--no-parser`, the five rules
`symm contra refl scope trans`, and two rewrites: imports from the generated
calculus name to `CpcMini`, and `partial def` to `def`. Each of those is
available on its own if the reduced package ever needs a different shape.

## The cached signature

`install/defs/Cpc.cached.eo` is a copy of the signature the packages here were
compiled from, kept in this repository as a *single file*: every
`(include "...")` of the original replaced by the text of the file it names,
each file appearing once and in the order Ethos reads them, and the comments
of the original dropped. Compiling it produces the same Lean as compiling the
original tree, byte for byte, so it is the signature and not a summary of one.

Comments go because the upstream file is where the prose belongs, and a copy
that carried it would turn every rewording upstream into a diff here. What is
left is what the compiler acts on, so a diff of this file is a diff of the
calculus. Two things are added rather than removed: a header saying what the
copy is, and a `; ==== <file> ====` line at each splice, so the tree the copy
was made of is still legible in it.

The header names the path the signature had — `proofs/eo/cpc/Cpc.eo` — and
deliberately not the checkout or the commit. That keeps the file a function of
the *signature* and of nothing else: flatten the same calculus from two cvc5
checkouts sitting at different commits and you get the same bytes, so an
install rewrites this file only when the calculus itself moved. Recording the
commit instead would have every regeneration churn a line that says nothing
about what the file compiles to, and would make two people's copies of the
same calculus conflict. Both scripts print the commit they read, for the
message of the commit that updates the copy — which is where a version that
cannot go stale belongs.

It exists because the signature otherwise lives in someone's cvc5 checkout,
which makes "is the generated code still what the signature says?" a question
nobody can answer from this repository alone. With the copy here, `--check`
answers it with no cvc5 anywhere in sight, which is what the `regeneration` CI
group does:

```bash
install/install-cpc.sh --cached --check
```

The flattening follows the same rules the compiler does. A file is spliced in
the first time it is reached and afterwards left as a comment saying so, which
is what Ethos does with a repeated `(include ...)` too (`markIncluded` in its
`src/state.cpp`), and which lines count as an include is decided the way
`driver.py` decides it. That is what keeps the copy equivalent to the tree
rather than a redeclaration of everything the tree shares. Comment stripping
knows what a comment is: a `;` inside a string literal or a `|quoted symbol|`
is content, and a line that begins inside either is passed through as it
stands.

Do not read `install/defs/` as the `--defs` option, which is a different file:
that one is Ethos's `cpc_defs.eo`, the deep-embedding definitions the
model-smt stage reads, and it arrives with the compiler under `install/deps/`.
What is here is the signature itself.

### Keeping it current

An install rewrites it, so there is no second command to remember:

```bash
install/install-cpc.sh ~/cvc5/proofs/eo/cpc/Cpc.eo
```

regenerates both packages *and* records the signature it compiled. What the packages
were generated from and what CI compiles are then the same thing by
construction rather than by anyone's discipline.

Two runs deliberately do not record anything, because neither compiled the
signature the packages follow:

* `--rules` installed a *reduced* calculus, not the signature
* `--package Mine` says nothing about `Cpc` or `CpcMini`

Both end by saying the copy was left alone and what to run to record the
signature anyway. `--no-update-cache` asks for that on a run that would
otherwise record, and `--cached` compiled the copy itself, so it has nothing
to record.

`--update-cache` is the standalone form: it rewrites the copy and installs
nothing. It reads only the signature, so it needs no compiler and no
`install/deps/` — a machine that has never run `get-eo-compiler.sh` can still
record one.

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

## The relationship to cvc5

Neither script depends on cvc5. Nothing is downloaded from it and nothing is
run from it.

The CPC signature happens to be maintained in the cvc5 repository, at
`proofs/eo/cpc/Cpc.eo`, so that is the usual thing to point `--signature` at.
What the compiler consumes is Eunoia *source text*, not a solver: no cvc5
binary and no cvc5 build is involved. Note that `Cpc.eo` includes the rest of
`proofs/eo` by relative path, so `--signature` needs to name a file sitting in
a complete copy of that subtree. `install/defs/Cpc.cached.eo` is that subtree written
as one file, which is why `--cached` needs nothing outside this repository.

## Pinning

The Ethos commit is **not** an option. It is hardcoded as `ETHOS_VERSION` in
`get-eo-compiler.sh`, so what the compiler emits changes only when someone
moves the pin deliberately. It is currently
`b9fc583f5a4838fcfcaade2d31f8cdc5f19c62a6` — "Add core Eunoia compiler
infrastructure (#229)". To move it, edit that line and re-run both scripts.

The signature is pinned by copy rather than by version: `install/defs/Cpc.cached.eo`
is the one the packages were compiled from, and `--cached` compiles exactly
that. `--signature` is still whatever you point it at, so a run against a
checkout compiles that checkout; what the copy fixes is the version everything
is *checked* against, which is why moving to a newer signature means running
`--update-cache` as well.
