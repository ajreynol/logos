# Modularity of the Logos checker

Logos is one checker for one calculus, CPC. But most of its soundness argument
is not about CPC: it is about a stack machine that pushes assumptions and proven
facts, and about invariants that machine maintains. This document records how
far that separation has been taken, what a *second* consumer has to supply, and
what is left to do.

It has two audiences:

- Logos maintainers — the TODO list at the end.
- Anyone building a Logos-like checker for a different calculus (e.g.
  [eudaimonia](https://github.com/ajreynol/eudaimonia)) — the contract in
  [What a new checker supplies](#what-a-new-checker-supplies). Start from
  `CpcMini`, not `Cpc`.

## Current layering

Hand-written proof, in lines, after the split described below. "Reusable" means
a new calculus can take the file essentially as-is.

| layer | files | Cpc | CpcMini | reusable? |
| --- | --- | ---: | ---: | --- |
| checker | `Proofs/{Checker,CheckerState,CheckerCore}.lean`, `Proofs/Invariants/Stability.lean`, `Proofs/RuleSupport/Contract.lean`, `Proofs/Assumptions.lean` | 4,474 | 4,229 | yes, except `Assumptions.lean` |
| common | `Proofs/{Common,CommonBoolOps,TermCompat}.lean` | 1,388 | 804 | mostly |
| translation | `Proofs/Translation*` | 33,463 | 5,194 | no — signature-specific |
| type preservation | `Proofs/TypePreservation*` | 17,700 | 5,638 | no — signature-specific |
| canonical models | `Proofs/Canonical*` | 10,083 | 228 | no — signature-specific |
| closedness / var-model | `Proofs/Closed*` | 32,274 | 0 | only if you have binder rules |
| rule support | `Proofs/RuleSupport/*` | 352,795 | 259 | no — rule-specific |
| rules | `Proofs/Rules/*` | 279,000 (591 files) | 1,209 (5 files) | no |

Everything else — `Logos.lean`, `LogosTerm.lean`, `SmtEval.lean`,
`SmtModel*.lean`, `SmtValueOrder.lean`, `Spec.lean`, `Parser.lean`,
`Proofs/RuleLemmas.lean`, and one stub per rule — is emitted by `ethos-eoc`;
see `install/install-sig.sh`.

**Read that table before planning work.** The checker layer is 4.2K of
CpcMini's ~17.5K hand-written lines (24%), and 4.5K of Cpc's ~730K (0.6%). The
checker layer is now in good shape; the cost of a new checker is dominated by
the *semantics* layer. See TODO 5.

### Module order

```
Proofs/Common.lean            core semantics predicates (eo_interprets, eo_has_bool_type)
Proofs/Assumptions.lean       input-problem + per-command side conditions
Proofs/RuleSupport/Contract.lean   the checker/rule contract
Proofs/CheckerState.lean      the state machine — no invariant is named here
Proofs/Invariants/Stability.lean   the one optional invariant
Proofs/CheckerCore.lean       the invariants, the bundle, the rule bridge
     ↑ (generated) Proofs/RuleLemmas.lean, Proofs/Rules/*.lean
Proofs/Checker.lean           preservation + correct___eo_is_refutation
```

`Proofs/CommonBoolOps.lean` and the rest of `Proofs/RuleSupport/` hang off
`Contract.lean` on the rule side and are deliberately *not* in the checker's
transitive imports.

## What a new checker inherits

`Proofs/Checker.lean` — the ~25 preservation theorems and
`correct___eo_is_refutation` — is **byte-identical between `Cpc` and `CpcMini`**
modulo the package name. It contains:

- zero references to any `CRule` constructor;
- zero references to the stability invariant, or to any other calculus-specific
  invariant;
- three `Term` constructors only: `Stuck`, `Bool`, `Boolean`.

`CheckerState.lean` contains zero occurrences of the string `Invariant`.

The evidence that this is real, not aspirational: `CpcMini` uses Cpc's
`Checker.lean` verbatim while differing in rule set (5 rules vs 591), in
signature, *and* in which invariants its rules require.

## What a new checker supplies

### 1. Signature symbols

The checker layer hard-codes a small number of SMT-LIB symbols. Eunoia does not
guarantee these exist; your signature must declare them.

- **`and`**, and not merely the symbol: it must be declared right-associative
  with nil `true`. `stateAssumes` / `statePushes` / `stateProvens` fold the
  checker stack with it (`Proofs/CheckerState.lean`);
  `__eo_invoke_assume_list` parses the input problem as an `and`-chain
  terminated by `true`; `__eo_nil` carries a hard-coded arm
  `| (Term.UOp UserOp.and), T => Term.Boolean true`, which
  `__eo_mk_premise_list` relies on for *every* `:list`-premise rule; and the
  conclusion `eo_satisfiability F false` is a statement about that chain.
- **The Bool literals `true` / `false`.** `Term.Boolean` is a builtin `Term`
  constructor so it always exists, but the checker fixes its meaning: `false`
  is the refutation target (`__eo_state_is_refutation` is literally
  `check_proven false`), and `true` is the unit of the assumption conjunction.

`not`, `=` and `imp` are **not** required by the checker. They are used only by
rule proofs, and live in `Proofs/CommonBoolOps.lean`, outside the checker's
transitive imports. A signature declaring none of them can delete that module
without touching anything else.

`imp` was the last to go and was pure accident: `CheckerState.lean` carried five
`eo_interprets_imp_*` lemmas that **nothing in the checker used** — in Cpc they
were one-line forwarders to the `RuleProofs` versions in `Common.lean`, and in
CpcMini they had no users anywhere. Deleting them, and moving Cpc's originals
to `CommonBoolOps.lean`, left the core naming exactly one operator.

**The core of both packages now depends on a single signature symbol: `and`.**

Nothing currently *checks* these requirements — see TODO 8.

### 2. The SMT semantics side

`__eo_to_smt` must send `and` to `SmtTerm.and` and `Bool` to `SmtType.Bool`.
The checker layer's entire SMT surface is `SmtTerm.and`, `SmtTerm.Boolean`,
`SmtType.Bool` and the `None` cases. A signature that declared `and` but
translated it to something else would break soundness silently at that seam:
nothing cross-checks it.

### 3. The semantics layer

`Translation/`, `TypePreservation/`, `Canonical/` — proofs about the generated
`__eo_to_smt` and `__smtx_typeof` for *your* operators. This is the bulk of the
work and it scales with how many SMT theories you take on: 228 lines of
`Canonical/` in CpcMini against 10,083 in Cpc.

### 4. `cmdTranslationOk`

`Proofs/Assumptions.lean`. Seed it from **CpcMini's** 44-line version, whose
`cmdTranslationOk` is generic (`| CCmd.step _ args _ => cArgListTranslationOk args`)
and names no rule. Cpc's 257-line version is a hand-maintained specialization —
see TODO 1.

### 5. Optionally, an extra invariant

If your rules need something of the proof state beyond "well-typed, translatable,
locally true", supply it through the slot in
`Proofs/Invariants/Stability.lean`:

```lean
abbrev checkerExtraInvariant (M : SmtModel) (s : CState) : Prop := ...
abbrev cmdExtraOk            (M : SmtModel) (c : CCmd)    : Prop := ...
abbrev CmdListExtraOk        (M : SmtModel) (cs : CCmdList) : Prop := ...
abbrev extraAssumptionListOk (M : SmtModel) (F : Term)    : Prop := ...
```

plus `invoke_cmd_preserves_extraInvariant_nonstuck`. `Checker.lean` is written
against those four names and never mentions what they stand for. A calculus with
no extra invariant points `checkerExtraInvariant` at `fun _ _ => True`.

In CPC the slot holds variable stability, which exists so binder-sensitive rules
(`instantiate`, `skolemize`, `alpha_equiv`) can be given premise truth in a
variable-variant model via `RulePremiseEvidence.true_in_var_model`. CpcMini
defines `StableWhenTrueInAnyVarModel := True` and pays nothing.

**The slot is coupled to `RuleSupport/Contract.lean`.** Adding
`true_in_var_model` to `RulePremiseEvidence` is exactly what makes an extra
invariant load-bearing. Those two choices are made together, up front.

## TODO

Ordered by value to a second consumer.

### 1. Make `cmdTranslationOk` per-rule and generated

`Cpc/Proofs/Assumptions.lean` is a 257-line hand-maintained table naming 32
individual CPC rules. It is the **only** hand-written non-rule file that
mentions a rule, and it appears in the hypothesis of the top-level
`correct___eo_is_refutation`.

Have the rule stub template emit
`def cmd_step_<rule>_args_ok : CArgList → Prop := fun _ => True`, let the proof
author strengthen it in the rule file, and have `ethos-eoc` generate
`cmdTranslationOk` as a dispatch — exactly as it already generates
`cmd_step_proven_facts_of_invariants`. Then no hand-written file in the checker
layer names a rule.

The masks cannot be inferred from the signature: the kind
(`term`/`list`/`type`/`wfTerm`/`wfElem`) is discovered while proving the rule.
So it must be *declared* in the rule file, not derived.

Needs an eoc template change, and a `Decidable` instance per rule so
`Cpc/ApiChecks.lean` can keep discharging it with `decide`.

### 2. Promote the checker layer to eoc templates

`Checker.lean`, `CheckerState.lean`, `RuleSupport/Contract.lean` and a generic
`Assumptions.lean` should be *seeded* into a new package and then owned by it —
the install-once, preserve-if-present treatment that `Proofs/Rules/*.lean`
already gets in `install/install-sig.sh` (see the loop near line 652). Today
they are hand-maintained per package, and they drifted: before being unforked,
Cpc's and CpcMini's `Checker.lean` differed by 376 lines purely because CpcMini
did not need one invariant.

`Checker.lean` needs no parameterization beyond the package name — 25 `Term`
references, zero `CRule`, zero `UserOp`.

### 3. Split `CheckerCore.lean` per invariant

It still holds four invariants, the bundle, and the rule bridge in one file
(1,123 / 1,005 lines). Splitting into `Invariants/{Type,Translation,LocalTruth}.lean`
plus a bundle module would let a consumer replace the *translation* invariant —
relevant if your specification is not "translate to SMT-LIB and interpret".

Low risk: the same split was done for `Stability.lean` by computing the
declaration reference graph, and it had zero generic→invariant violations, so no
proof needed fixing.

### 4. Generalize the extra-invariant slot

`checkerExtraInvariant` is a single slot. A calculus needing two extra invariants
must conjoin them by hand. Making it a list, or documenting the conjunction
idiom, is cheap. Low value until someone hits it.

### 5. Make the semantics layer cheaper — the biggest lever

Cpc: semantics layer 93,530 lines against a 4,474-line checker layer. Whatever
else is done to the checker has bounded returns; **this** is what a new consumer
pays.

Two directions:

- Have `ethos-eoc` emit the translation and type-preservation proofs alongside
  `__eo_to_smt`. They are largely mechanical case analyses over the operator set,
  which is exactly what the compiler already enumerates.
- Share the SMT-LIB half properly. `SmtModel.lean` is a formalization of
  *SMT-LIB*, not of CPC, yet each package gets its own pruned copy (2,186 lines
  in Cpc, 743 in CpcMini). A real shared library with per-package pruning as an
  optimization would let two consumers share the theory proofs.

This is the item most worth coordinating with eudaimonia before they start: if
their signature differs substantially from CPC's, this is the cost they will
actually feel.

### 6. Move calculus-independent material into `Logos/`

The `Logos` library is 1,069 lines (`Sexp.lean`, `Parser.lean`). Everything
reusable lives in per-package files instead, because `Term`, `CState` and
`CRule` are generated per package.

Two routes. **(a)** Keep per-package files but generate them from shared
templates — this is TODO 2, and is cheap. **(b)** Parameterize the proofs over
an abstract `Term` — expensive, because `CheckerCore.lean` also depends on the
translation layer and on `UserOp.and`. Recommend (a); do not start with (b).

### 7. Add a fast soundness check to CI — **done**

`Cpc.Proofs.Checker` and `Cpc.ApiCorrect` are deliberately excluded from CI
(`scripts/run-ci.sh`, "Expensive and not currently used in CI checks") because
they need all 591 rule files — roughly two hours. **Changes to `Checker.lean`
are therefore not verified by CI at all.**

`scripts/check-checker-soundness.sh` closes that gap, and now runs inside the
`cpc-proofs` group. It typechecks `Checker.lean` *and* `ApiCorrect.lean` against
the already-built `Proofs/CheckerCore` with the two generated bridge theorems
(`cmd_step_proven_facts_of_invariants`,
`cmd_step_pop_proven_facts_of_invariants`) stubbed by `sorry`. Whole thing runs
in **1.7 seconds** and catches everything except the rule proofs themselves.

Two details that make it trustworthy rather than decorative:

- it reads the two stubbed signatures *out of* `Proofs/RuleLemmas.lean` rather
  than hard-coding them, so a change to the compiler's template fails the check
  instead of silently testing the wrong statement;
- it ends with a canary — a declaration that must be rejected — so the harness
  cannot degrade into a no-op that always passes.

Verified against an injected error: replacing a hypothesis in one proof step of
`Checker.lean` makes it exit 1.

### 8. Check the signature contract explicitly

Nothing verifies the requirements in
[Signature symbols](#1-signature-symbols). A signature without `and`, or with
`and` not declared right-assoc-nil `true`, fails deep inside generated files
with confusing errors. Either check it in `install-sig.sh` or put a Lean-level
`example` in the seeded template that fails with a message naming the missing
symbol.

Now cheap, because the list is one symbol plus the Bool literals.

### 9. Split `Closed/Support.lean`

7,917 lines in one file, now reached only through `Invariants/Stability.lean`.
It mixes generic closedness machinery with binder/variable-model stability. A
calculus without binders pays nothing for it today, so this is low priority —
but it is a monolith and the natural next `Invariants/` tenant.

### 10. Organize `RuleSupport/`

352,795 lines in one flat directory. Rule-specific, so off the critical path for
modularity, but it is the bulk of the repository and would benefit from
theory-level structure.

### 11. Guard the properties this work established — **done**

`scripts/check-proof-modularity.sh`, CI group `proof-modularity`. Textual, no
toolchain, well under a second. Each invariant it checks had drifted at least
once:

- `Cpc/Proofs/Checker.lean` and `CpcMini/Proofs/Checker.lean` are identical
  modulo the package name — they diverged by 376 lines before being unforked;
- `Checker.lean` names no `CRule` constructor, no `UserOp`, and no
  calculus-specific invariant;
- `Proofs/CheckerState.lean` contains no occurrence of `Invariant`;
- the checker layer names exactly one `UserOp`, namely `and`.

### 12. Cross-check the soundness proof against the Eudaimonia template

**Not yet — Eudaimonia is in active development.** Recorded so it is not lost.

Once Eudaimonia's `templates/pkg/Proofs/Checker.lean.in` carries content rather
than a description, the same identity check that keeps `Cpc` and `CpcMini` in
agreement should extend across the two repositories: the template and both
Logos packages should be one file modulo the calculus name. That is what would
make the template *the* soundness proof rather than a copy of it, and it is the
natural end state of TODO 2.

Two things block it today, both on the Eudaimonia side and both deliberate:

- `templates/pkg/Proofs/Checker.lean.in` and `CheckerCore.lean.in` are 22-line
  stubs carrying a description of what belongs in them, so there is nothing to
  compare against.
- `scripts/get-eo-compiler.sh` runs with `DEV_MODE=1`, building the head of the
  `ethosEoc3` branch rather than a pinned commit, so a cross-repository check
  would be comparing against a moving target. Their roadmap has leaving
  development mode as its own item.

Revisit when both are resolved. Until then the in-repo check (TODO 11) covers
the property that matters most, which is that Logos does not re-fork its own
soundness proof.

## Cross-reference: the Eudaimonia roadmap

`~/eudiamonia/TODO.md` §4b measures the same tree independently and reaches
compatible conclusions. Two of its findings are worth importing here.

**Syntactic independence is not semantic independence.** Compilation
*configures the model*: `SmtModel.lean` is 743 lines in CpcMini and 2,186 in
Cpc, and `Spec.lean` 105 against 475. So a proof file that never names an
operator is still *stated about* an `SmtModel` that varies with the signature.
`Checker.lean` being byte-identical across the two packages therefore buys
**template** reuse, not library reuse — the two files are the same text about
two different types. That is exactly what TODO 2 proposes and what TODO 6(b)
would have to fix; the roadmap is right that stabilizing the SMT-LIB model as a
fixed base which signatures *extend* is the prerequisite for real sharing. It
matches TODO 5 here and should be sequenced first.

**`Term` has no per-operator constructors.** Operators live in the
`UserOp`/`UserOp1`/`UserOp2`/`UserOp3` enums and `Term` is uniform, so core
proofs never pattern-match an individual operator. Parameterizing `Term` over
the op enums with a small class supplying the required operators is therefore
much cheaper than abstracting the term algebra — and since the core is now down
to `and` alone, that class has one member. The roadmap's advice to try it on
`Proofs/Invariants/Stability.lean` first (one operator, self-contained) is
sound.

Two corrections to send back: the required-builtin list in the Eudaimonia
README (`and`, `imp`, `eq`, `not`, `Bool`, `true`, `false`) is stale — `eq` and
`not` were removed, and `imp` since — and the 108 differing lines it measures in
`Invariants/Stability.lean` are necessity rather than duplication: Cpc carries
the real `StableWhenTrueInAnyVarModel` machinery while CpcMini defines it
`True`.

## A note on mechanical file splitting

Several TODOs above involve splitting large Lean files. When doing that
programmatically, a declaration scanner must handle: multi-line `/-- … -/`
docstrings, `@[attr]` on the *same* line as the declaration, `set_option … in`
prefixes, and dotted names (`RulePremiseEvidence.instCoeFun` must not be
conflated with `RulePremiseEvidence`). Each of those, missed, produces a file
that either fails to parse or — worse — silently duplicates a declaration into
both outputs.

Assert an exact line partition (`moved + kept + header + trailer == original`),
and afterwards diff every declaration body against the original. Both checks are
cheap and catch what the compiler will not.
