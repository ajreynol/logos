# Logos Checker

## A Verified Proof Checker for SMT Solvers

Logos is a verified proof checker for SMT written in Lean.
It is an executable checker whose soundness is proven in Lean against a correctness
specification, which depends on a complete definition of SMT-LIB semantics in Lean.
See [Correctness](#correctness) below for what that proof establishes and what it still assumes.

Logos has a fully functional CPC parser, meaning that it accepts the same syntax for proofs as Ethos.
However, Logos does not support arbitrary Eunoia signatures.
Instead,
the proof rules currently used by Logos are automatically generated from the current definition of the Cooperating Proof Calculus (CPC)
(https://github.com/cvc5/cvc5/blob/main/proofs/eo/cpc/Cpc.eo).
This compilation depends on plugins of the proof checker Ethos (https://github.com/cvc5/ethos),
available on a development branch.
The definition of Logos is intended to evolve and remain in sync with the definition of Cpc
as further reasoning capabilities are added to cvc5.

## Building the Logos checker

```bash
lake build logos
```

The four checker executables follow one naming convention:

- `logos` checks CPC proofs in s-expression syntax.
- `logos-native` checks CPC proofs expressed as Lean evaluation scripts.
- `logos-mini` checks CpcMini proofs in s-expression syntax.
- `logos-mini-native` checks CpcMini proofs expressed as Lean evaluation scripts.

The first build of a CPC executable takes roughly 3.5 minutes currently.

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

The corresponding CpcMini executable is `logos-mini`; it reads the examples in
`examples/sexp-mini/` and uses the same output and exit-code convention.

### Checking Lean-native proofs

The `-native` executables check proofs written directly as Lean evaluation scripts, as emitted by
`cvc5 --dump-proofs --proof-format=cpc-logos`.  That format is described in
[docs/lean-native-proofs.md](docs/lean-native-proofs.md).

Note that Logos has not (yet) been optimized for performance, so it is significantly slower
that performant proof checkers for SMT.

This parser is split into two parts.
`Logos/Parser.lean` is signature-independent: it reads the command and term grammar and
resolves premise references, but knows nothing about any particular operator or proof rule.
Everything signature-specific is a `Logos.Parser.Config`, and those are auto-generated from
the calculus alongside `Cpc/Logos.lean` — `Cpc/Parser.lean` lists the 196 operator
declarations and 591 proof rules of CPC, and `CpcMini/Parser.lean` the corresponding subset.

Because the configurations are generated, an operator's surface syntax comes from its Eunoia
declaration metadata.  The generic `.argList` arity implements Eunoia's `:arg-list` attribute:
the surface arguments are gathered with the declared n-ary helper and passed as the annotated
operator's single argument.  `scripts/check-parser-tables.py` checks that the generated tables
cover every operator and proof rule.  Generic arity behavior is tested separately; it is not
inferred from calculus-specific term types.  Both checks run in the `regressions` CI group.

The parser supports the commands `declare-const`, `declare-fun`, `declare-sort`,
`declare-type`, `declare-datatypes`, `define`, `assume`, `assume-push`, `step` and `step-pop`.
`include` and `reference` commands are ignored: Logos has the signature built in and does not
check the proof against the original input problem.
A `declare-sort` of arity `n` (equivalently, a `declare-type` with `n` arguments) declares a
symbol of type `(-> Type … Type)`, so that arity `0` declares an uninterpreted sort; the
function type is built from the signature's own `->`, as it is for `declare-fun`.
A `define` with parameters is a macro, since Eunoia has no lambda: its body is kept as an
s-expression and read again wherever the defined symbol is applied, with the parameters bound
to the arguments given there.  Consequently a parameter's declared type is not used, an error
in the body is reported at the use site, and a recursive `define` is rejected.  A `define`
without parameters is read where it is given, as before.
An expression headed by `_` uses indexed-operator syntax when a matching indexed declaration
exists (for example, `(_ extract 1 0)`); otherwise `_` is a higher-order application marker,
so `(_ BitVec 4)` is equivalent to `(BitVec 4)`.
Parameterized operators also accept Eunoia's flat application syntax, which is what cvc5 emits:
for example, `(extract 1 0 x)` is equivalent to `((_ extract 1 0) x)`.  SMT-LIB type
ascriptions such as `(as set.empty (Set Int))` supply the ascribed sort as the operator index.
Term-level `let` uses parallel bindings whose names are scoped to its body.
A name may be declared more than once, as SMT-LIB allows, and a proof's own symbol may
carry the name of one of the signature's operators; every declaration of a name is kept,
and a use of it means the reading the calculus gives a type to (`Config.wellTyped`, which
`Cpc.Parser` decides with `__eo_typeof`).  A name with only one reading is never rejected
this way, so a partially applied operator, which has no type, still parses.  A `let`
binding and a macro parameter shadow instead of overloading.
Datatypes may be mutually recursive; parametric datatypes (a non-zero arity, or a `par` body)
are rejected, since Logos has no representation for them.
The conclusion printed on a `step` is ignored, since Logos recomputes it from the rule.

Literals are lexed by `Logos.Parser.Literal.ofString`, which a configuration only has to map
into its own term language: integers (`12`, `-12`), rationals in both fractional and decimal
form (`1/2`, `-1.25`), bit-vectors in binary and hexadecimal (`#b0110`, `#x1f`) and strings
with the SMT-LIB `""` escape.  A string literal's `\u{d…}` and `\ud₃d₂d₁d₀` escapes are
decoded as well, since they belong to the SMT-LIB theory of strings rather than to its
syntax: `"\u{a}"` is one character, not six.  A malformed escape stands for its own
characters, as in Ethos; a well-formed one naming a surrogate is rejected, since Lean has
no `Char` for it.

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
ignored). The Lean-native front end is also not yet covered: `MainNative.lean`
and the `#eval` scripts cvc5 emits for it go through the generated
`Eo.logos_invoke_assume`, which pushes an input assumption without the
Boolean-typed-and-closed guard that `__eo_invoke_assume_list` applies; the
guarded push the theorem is stated against is `Eo.logos_invoke_input_assume`.

The proof of the core checker is agnostic to the proof rules being used, i.e.
the core definition of Logos and its correctness does not depend on the particular rules of the calculus.
The proofs of correctness of each proof rule are contained in `Cpc/Proofs/Rules/`.
The dispatcher which case splits on these rules is in `Cpc/Proofs/RuleLemmas.lean`,
which is also auto-generated based on the calculus.

`scripts/cpc-loc-summary.py` reports the size of each of these pieces — the specification, the
checker, the parser and the correctness proof — in lines of code.
