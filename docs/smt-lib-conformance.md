# Conformance to SMT-LIB

Logos's soundness theorem is stated against `Cpc/SmtModel.lean`, a formalization
of SMT-LIB semantics written independently of the checker. Most of that
formalization is faithful, and the places where it is not are known, small and
listed here.

**None of them is a gap in the proof.** The theorem is proven, and it says what
it says about the semantics it is stated against. What this page records is that
the semantics admits a slightly narrower class of models than SMT-LIB does, so
`correct` claims slightly less than the words *these assumptions are
unsatisfiable* are normally taken to mean. Every deviation below is confined to
quantified or nonlinear reasoning; on the quantifier-free linear fragments the
two agree.

## What `correct` means, exactly

Unsatisfiability in the specification is *false under every well-formed model*
(`smt_satisfiability`, `Cpc/SmtModel.lean:2176`), where a model assigns each
symbol a value of the right SMT type (`model_wf`, `Cpc/SmtModel.lean:2164`), and
the values available at a type are the inhabitants of `SmtValue` at that type.

That value inductive is where the narrowing happens. Every model of this
semantics is an SMT-LIB model, but not every SMT-LIB model is one of these — so

> SMT-LIB says unsatisfiable **⟹** Logos says unsatisfiable, and not the reverse.

The consequence worth stating plainly: a formula that is satisfiable in SMT-LIB
only by a model this semantics cannot express is treated here as
unsatisfiable. Nothing in the checker will notice, because the restriction is in
what a model *is*, not in what a term means, so no `incomplete` verdict fires.
The channel by which that could produce a wrong `correct` is a CPC rule that is
sound for this model class and unsound for SMT-LIB's: its Lean proof would go
through, and proofs using it would be accepted.

| deviation | this semantics | SMT-LIB | where it bites |
| --- | --- | --- | --- |
| arrays are almost constant | a default plus finitely many overrides | the full function space | quantifiers over arrays or indices |
| `Real` is the rationals | ℚ | ℝ | nonlinear real arithmetic |
| uninterpreted sorts are infinite | one countably infinite domain per sort | any nonempty cardinality | quantified cardinality constraints |
| sets are finite | finite sets only | (an extension; cvc5 admits infinite sets) | quantifiers over set membership |

## Arrays are almost-constant maps

An array value is `SmtMap`, which is `default T v` overridden at finitely many
points by `cons k v m` (`Cpc/SmtModelDefs.lean`). So every array in every model
is constant except at finitely many indices, where SMT-LIB's `ArraysEx`
interprets `(Array I E)` as the whole function space from `I` to `E`.

It bites where a formula forces an array that is not almost constant:

```smt2
(declare-const a (Array Int Int))
(assert (forall ((i Int)) (= (select a i) i)))
```

satisfiable in SMT-LIB by the identity, and false under every model here.

It does not bite on quantifier-free array formulas, where a satisfiable formula
has an almost-constant model — the same property array decision procedures are
built on.

## `Real` is interpreted as the rationals

`SmtValue.Rational` carries a Lean `Rat` (`Cpc/SmtEval.lean:28`), and it is the
only numeric value at type `Real`. The reals of every model are therefore exactly
ℚ, and quantification over `Real` ranges over ℚ.

It bites in nonlinear arithmetic, where a solution may be irrational:

```smt2
(declare-const x Real)
(assert (= (* x x) 2.0))
```

satisfiable in SMT-LIB, and false under every model here.

It does not bite on linear real arithmetic, where a satisfiable formula always
has a rational solution.

## Uninterpreted sorts are assumed infinite

A value of an uninterpreted sort is `UValue i n` for a natural `n`
(`Cpc/SmtModelDefs.lean`), and every such value has type `USort i`
(`Cpc/SmtModel.lean:1644`), so each uninterpreted sort is interpreted as a
countably infinite domain. SMT-LIB allows any nonempty cardinality, finite
included. The write-up states the assumption; nothing enforces or checks it.

It bites on quantified cardinality constraints:

```smt2
(declare-sort U 0)
(declare-const x U) (declare-const y U) (declare-const z U)
(assert (forall ((a U) (b U) (c U)) (or (= a b) (= a c) (= b c))))
```

which bounds `U` at two elements: satisfiable in SMT-LIB, false under every model
here. Quantifier-free formulas are unaffected, since a satisfiable one always has
an infinite model.

## Sets are finite

Sets share the map representation, and a set value is canonical only when its
default is `false` (`__smtx_value_canonical`, `Cpc/SmtModel.lean:1903`), so every
set in every model is finite. Sets are a non-standard extension rather than
SMT-LIB proper, and the operators the semantics carries — union, intersection,
difference, singleton, membership, subset — preserve finiteness, so this is
reachable only through quantified membership constraints such as
`(forall ((i Int)) (set.member i S))`.

## A coverage limit, not a semantic one: parametric datatypes

Parametric datatypes are refused, not mismodeled. Both the sort list and a `par`
body are rejected during parsing (`Logos/Parser.lean:685`, `Logos/Parser.lean:776`)
with `parametric datatype ... is not supported`, and the run exits 1 without a
verdict. `SmtDatatypeDecl` carries no type parameter, so there is nothing for
such a declaration to translate to.

This costs coverage and nothing else: a proof over parametric datatypes is not
checked, rather than checked against the wrong meaning.

A parametric *sort* is refused later and more gently: `(declare-sort U 1)` parses,
and an application of it has no counterpart in the specification, so the side
conditions fail and the run reports `incomplete` rather than `correct`.
`test/regress/sexp/test-declare-sort.cpc` is that case.

## What is faithful, and is easy to assume otherwise

- **Division by zero, `mod` by zero and real division by zero** are
  underspecified exactly as SMT-LIB requires: each evaluates by applying a
  model-dependent function (`@div_by_zero`, `@mod_by_zero`, `@qdiv_by_zero`), so
  models disagreeing about `(div 1 0)` are all admitted, and nothing here fixes a
  value for it.
- **Out-of-bounds `seq.nth`** is underspecified the same way, through
  `@oob_seq_nth`.
- **The character alphabet** is SMT-LIB's, code points `0` to `196607`
  (`native_char_valid`, `Cpc/SmtEval.lean:36`).
- **Uninterpreted functions** get the full function space, not the almost-constant
  restriction arrays carry.
- **Sequences** are finite, which is what SMT-LIB says they are.

## Where this is written down elsewhere

Each deviation is stated in passing in the write-up,
[`smt-model-definitions.pdf`](smt-model-definitions.pdf) — arrays under the type
constructors and again where maps are defined, the rational assumption where
values are introduced, and the cardinality assumption where uninterpreted sort
values are. The parser's refusal is in [`parser.md`](parser.md). This page is the
collected list; the write-up is where the definitions and their reasoning are.
