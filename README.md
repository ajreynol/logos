# Logos Checker

## A Verified Proof Checker for SMT Solvers

Logos is a verified proof checker for SMT written in Lean.
It is an executable checker whose soundness is proven in Lean against a correctness
specification, which depends on a complete definition of SMT-LIB semantics in Lean.
See [Correctness](#correctness) below for what that proof establishes and what it still assumes.

Logos has a fully functional CPC parser, meaning that it accepts the same syntax for proofs as Ethos
(see [docs/parser.md](docs/parser.md)).
However, Logos does not support arbitrary Eunoia signatures.
Instead,
the proof rules currently used by Logos are automatically generated from the current definition of the Cooperating Proof Calculus (CPC)
(https://github.com/cvc5/cvc5/blob/main/proofs/eo/cpc/Cpc.eo).
This compilation depends on plugins of the proof checker Ethos (https://github.com/cvc5/ethos).
The definition of Logos is intended to evolve and remain in sync with the definition of Cpc
as further reasoning capabilities are added to cvc5.
See [Regenerating the calculus](#regenerating-the-calculus) for how to rerun that compilation.

## Building the Logos checker

```bash
scripts/build.sh logos
```

The build script uses the Lean version pinned in `lean-toolchain`. On older
Linux systems, it also detects when the Clang/LLVM binaries bundled with Lean
cannot run against the host's glibc and automatically uses the host C compiler
and archiver instead while retaining Lean's bundled link libraries. A direct
Lake build is equivalent on supported hosts:

```bash
lake build logos
```

If a direct build fails with errors such as `GLIBC_2.27 not found` or
`GLIBC_2.29 not found` from the toolchain's `bin/clang`, use the build script.
It performs the equivalent of selecting the host tools with `LEAN_CC` and
`LEAN_AR`, and also preserves the link-library paths from the Lean toolchain:

```bash
scripts/build.sh logos
```

This requires a working host C toolchain (GCC or Clang plus `ar`). Do not replace
the system `libm.so.6` or glibc in place; use a newer container or build the
pinned Lean toolchain locally if the host compiler fallback is unavailable.
Official x86-64 Lean binaries require glibc 2.26 or newer; check the host with
`getconf GNU_LIBC_VERSION`.

There are two checker executables:

- `logos` checks CPC proofs in s-expression syntax.
- `logos-native` checks CPC proofs expressed as Lean evaluation scripts.

The first build of a CPC executable takes roughly 3.5 minutes currently.

`CpcMini` is a cut-down calculus used to develop and test the proofs; it has no
parser and no executable of its own.

To run the same checks as CI locally, use:

```bash
bash scripts/run-ci.sh
```

To build every CPC proof rule, use:

```bash
scripts/build-all-cpc-rules.sh
```

The script builds one rule target at a time by default to keep peak memory
bounded. On machines with more RAM, `--batch-size 2` (or a larger value) trades
memory for speed. `--all-at-once` enables the previous maximum-parallelism mode
and may exhaust memory.

To remove Lake build artifacts, use either of these equivalent commands:

```bash
scripts/clean-build.sh
lake clean
```

## Regenerating the calculus

The `Cpc` package is compiled from the Eunoia definition of CPC rather than
written by hand. Two scripts do that; see
[`scripts/README.md`](scripts/README.md) for the full description.

```bash
scripts/get-eo-compiler.sh                                     # once: build the compiler
scripts/install-cpc.sh --signature <cvc5>/proofs/eo/cpc/Cpc.eo # regenerate Cpc
scripts/build.sh Cpc                                           # check the result
```

The first script sets up the compiler only, under `deps/`, which is ignored by
git. The signature to compile against is named on each run, so any copy of
`Cpc.eo` reachable on the machine can be used, including one being edited. What
is consumed is the Eunoia source of the signature; no cvc5 *binary* or build is
involved.

Regeneration rewrites the signature-wide modules of the package but preserves
the existing per-rule proofs under `Proofs/Rules/`. A rule newly added to CPC
appears as a `sorry` stub, and a rule whose statement changed keeps its old
proof and therefore fails to build — both are the intended signal that a proof
needs attention.

## Using the Logos checker

The standard `logos` executable reads the s-expression (Eunoia) syntax emitted by
`cvc5 --dump-proofs --proof-format=cpc`:

```bash
lake exe logos examples/sexp/test-simple.cpc
```

After building, it can be run directly without invoking Lake:

```bash
./.lake/build/bin/logos examples/sexp/test-simple.cpc
```

The executable accepts exactly one proof path and reports one of three outcomes:

| output        | status | meaning                                                                     |
| ------------- | ------ | --------------------------------------------------------------------------- |
| `correct`     | 0      | the proof's assumptions are unsatisfiable, by `correct___logos_check_proof` |
| `incorrect`   | 1      | Logos does not accept the proof as a refutation                             |
| `incomplete`  | 2      | Logos accepts the proof, but it mentions something the specification of SMT-LIB semantics does not model, so the correctness theorem does not apply to it |

Parse and usage errors also exit with status 1. An `incomplete` run explains on
stderr which assumption or command took the proof outside the specified
fragment; see [Correctness](#correctness).

For example, a CPC proof may contain:

```
(declare-const x Int)
(declare-const y Int)
(assume @p0 (= y x))
(assume @p1 (not (= x y)))
(step @p2 :rule symm :premises (@p1))
(step @p3 :rule contra :premises (@p0 @p2))
```

The parser accepts the same proof syntax as Ethos.  Its structure, the commands and term
syntax it supports, and how it lexes literals are described in
[docs/parser.md](docs/parser.md).

Note that Logos has not (yet) been optimized for performance, so it is significantly slower
than performant proof checkers for SMT.

Logos also accepts proofs written directly as Lean evaluation scripts, as emitted by
`cvc5 --dump-proofs --proof-format=cpc-logos`.  These are checked by the `logos-native`
executable; that format is described in
[docs/lean-native-proofs.md](docs/lean-native-proofs.md).

## Correctness

Logos is verified: its soundness is stated and proven in Lean against a specification of
SMT-LIB semantics, so a proof it accepts implies that the assumptions of that
proof are indeed unsatisfiable.
The specification is in two parts. First, the file `./Cpc/SmtModel.lean` formalizes a model semantics of SMT-LIB.
Second, the file `./Cpc/Spec.lean` defines a correspondence between Eunoia terms and SMT-LIB terms
and a definition of satisfiability for Eunoia terms.

The SMT-LIB formalization `./cpc/SmtModel.lean`
includes several non-standard extensions of SMT-LIB (e.g. the theory of sets and the theory of sequences).
It additionally contains operators that are helpful in defining the semantics of existing operators.
This includes total versions of partial arithmetic operators.

The correctness proof for the checker lives in `Cpc/Proofs/Checker.lean`,
whose final theorem `correct___eo_is_refutation` states that
a successfully checked proof in Logos implies that the input assumptions to that proof are indeed unsatisfiable.
This theorem intentionally has two explicit assumptions that state that the given proof uses only terms that
have a corresponding SMT-LIB semantics.
That theorem is proven, as are the correctness proofs of the individual proof rules it relies on.
There are no `sorry`s in the soundness proof or its dependencies.

### From the theorem to the executable

`correct___eo_is_refutation` is stated about an assumption term `F`, a command
list, and two side conditions (`TranslatableAssumptionList F` and
`CmdListTranslationOk`, defined in `Cpc/Proofs/Assumptions.lean`, which restrict
the proof to terms the SMT-LIB formalization gives a meaning to). Three further
files connect that statement to what the executable actually runs, so that the
`correct` it prints is the theorem's conclusion rather than an informal argument
about it:

- `Cpc/Api.lean` is everything `logos` does with a proof file, as one function
  `Eo.logos_check_proof : String -> Except String Verdict`: parse the text, then
  run the three checks that compute the theorem's components — the assumption
  term `F`, the refutation check, and the two side conditions.
- `Cpc/ApiChecks.lean` proves that each check gives the component it stands for.
  In particular it proves that folding the guarded assumption push over the
  parser's list builds the same state as `__eo_invoke_assume_list` on the
  corresponding `and`-chain, which is what lets the executable use a fold
  (constant stack) rather than a recursion over the chain.
- `Cpc/ApiCorrect.lean` assembles those into `correct___logos_check_proof`,
  stated about the text of a proof file:

  ```lean
  theorem correct___logos_check_proof (input : String) (assums : List Term) (cmds : CCmdList)
      (hParse : parseProof input = Except.ok (assums, cmds))
      (hCorrect : logos_check_proof input = Except.ok Verdict.correct) :
      eo_satisfiability (logos_assumption_term assums) false
  ```

  That is: if the parser reads the assumptions `assums` out of `input`, and
  `logos` prints `correct` for `input`, then their conjunction is unsatisfiable.
  `Main.lean` only reads the file, prints the verdict and picks an exit status.

The side conditions are not re-implemented for the executable to run: they are
the predicates of `Cpc/Proofs/Assumptions.lean`, and that file also derives the
`Decidable` instances that decide them, so the per-rule conditions the rule
proofs assume and the ones the executable checks are one definition, written
down once.

Note that the side conditions are *checked at run time*: computing them needs
the specification's `__eo_to_smt`, so the executable links the specification
layer, even though the checker itself never consults it (the proof rules remain
untyped syntactic manipulations, and the semantics is not used as an oracle).
A proof that Logos accepts but whose side conditions fail is reported as
`incomplete` rather than `correct` — `examples/sexp/test-declare-sort.cpc` is
one, since it declares a sort of arity 1 and the specification has no
counterpart for a sort constructor applied to a sort.

What is still outside the theorem: the s-expression reader and the parser
(`Logos/Parser.lean`, `Cpc/Parser.lean`) are unverified, so the assumptions the
theorem talks about are whatever they read out of the file, and Logos does not
compare them against an original input problem (`include` and `reference` are
ignored).

The proof of the core checker is agnostic to the proof rules being used, i.e.
the core definition of Logos and its correctness does not depend on the particular rules of the calculus.
The proofs of correctness of each proof rule are contained in `Cpc/Proofs/Rules/`.
The dispatcher which case splits on these rules is in `Cpc/Proofs/RuleLemmas.lean`,
which is also auto-generated based on the calculus.

`scripts/cpc-loc-summary.py` reports the size of each of these pieces — the specification, the
checker, the parser and the correctness proof — in lines of code.
