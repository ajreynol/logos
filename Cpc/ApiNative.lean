module

public import Cpc.Api
import all Cpc.Api

@[expose] public section

/-!
# What the `logos-native` executable computes

`Cpc/Api.lean` is the pipeline of the `logos` executable, from the text of an
s-expression proof file to a `Verdict`.  This module is the same pipeline for
the Lean-native front end (`MainNative.lean`, `docs/lean-native-proofs.md`),
whose input is a Lean script that builds a checker state one command at a time
and evaluates a predicate on it:

```
def s0 : NativeState := logos_native_init_state
def s1 : NativeState := (logos_native_invoke_assume s0 t4)
def s2 : NativeState := (logos_native_invoke_cmd s1 (CCmd.step ...))
#eval!
(logos_native_state_is_refutation s2)
```

The two front ends differ only in where the assumptions and the commands come
from: `logos` gets them from `Cpc/Parser.lean`, and here the script names them
one call at a time.  Everything downstream of that is the same, and is meant to
stay the same -- the three checks of `logos_verdict` are run here too, on the
same definitions:

| component of `correct___eo_is_refutation` | in `logos_verdict`                       | here                       |
| ----------------------------------------- | ---------------------------------------- | -------------------------- |
| `eo_is_refutation F pf`                    | `logos_check_refutation`                 | `NativeState.state`        |
| `TranslatableAssumptionList F`             | `logos_check_translatableAssumptionList` | `NativeState.translationOk` |
| `CmdListTranslationOk pf`                  | `logos_check_cmdListTranslationOk`       | `NativeState.translationOk` |

`logos_native_verdict_eq_verdict` below proves that a script of the shape above
computes exactly `logos_verdict` of the assumptions and commands it names, and
`correct___logos_native_verdict` (`Cpc/ApiCorrect.lean`) turns that into the
soundness statement.  What the script's *shape* is remains unchecked, and is the
counterpart here of the unverified parser on the `logos` side.

The generated API of `Cpc/Logos.lean` -- `logos_invoke_assume`,
`logos_invoke_cmd`, `logos_state_is_refutation` -- runs the checker alone: its
`logos_invoke_assume` pushes an input assumption with no well-formedness guard,
and no translation side condition is evaluated anywhere.  It is kept for scripts
written against it, but a `true` from it is weaker than a `true` from
`logos_native_state_is_refutation`; see `docs/lean-native-proofs.md`.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The state a script threads

A checker state, plus the running conjunction of the translation side conditions
of the assumptions and commands that built it.  The checker state alone is what
`Cpc/Logos.lean` threads; the extra field is what lets the two side conditions of
`correct___eo_is_refutation` be decided incrementally, without the script having
to hand back the list of everything it has done.
-/
structure NativeState where
  /-- The checker state, as `__eo_invoke_cmd_list` would have built it. -/
  state : CState
  /-- Every assumption and command so far satisfies its translation side condition. -/
  translationOk : Bool
deriving Repr, Inhabited

/-- The empty state: no assumptions, no commands, nothing yet to translate. -/
def logos_native_init_state : NativeState :=
  { state := logos_init_state, translationOk := true }

/--
Push an input assumption.

The checker state is advanced by `logos_invoke_input_assume`, which applies the
same well-formedness guard as `__eo_invoke_assume_list` -- the assumption must be
Boolean-typed and closed, or the state goes `Stuck`.  This is what
`logos_invoke_assume` (`Cpc/Logos.lean`) omits, and what `checkerTypeInvariant`
and `StableAssumptionList` need.

`decide (eoHasSmtTranslation A)` is the same check `logos_check_translatableAssumptionList`
makes of each parsed assumption.
-/
def logos_native_invoke_assume (s : NativeState) (A : Term) : NativeState :=
  { state := logos_invoke_input_assume s.state A,
    translationOk := s.translationOk && decide (eoHasSmtTranslation A) }

/--
Run one checker command.

`decide (cmdTranslationOk c)` is the per-command half of
`logos_check_cmdListTranslationOk`, decided by the same instance of
`Cpc/Proofs/Assumptions.lean`, so the per-rule masks the rule proofs assume are
checked here too.
-/
def logos_native_invoke_cmd (s : NativeState) (c : CCmd) : NativeState :=
  { state := __eo_invoke_cmd s.state c,
    translationOk := s.translationOk && decide (cmdTranslationOk c) }

/-- The verdict for a state a script built: `logos_verdict`, read off the state. -/
def logos_native_verdict (s : NativeState) : Verdict :=
  if !__eo_state_is_refutation s.state then Verdict.incorrect
  else if !s.translationOk then Verdict.incomplete
  else Verdict.correct

/--
What a script evaluates: `true` exactly when the verdict is `correct`, i.e. when
`correct___logos_native_verdict` applies to it.

The `incorrect`/`incomplete` distinction the `logos` executable reports is
available from `logos_native_verdict`; a script reduced to one Boolean cannot
show it, so a proof Logos accepts but cannot translate reads as `false` here.
-/
def logos_native_state_is_refutation (s : NativeState) : Bool :=
  logos_native_verdict s == Verdict.correct

/-! ## The shape a script is assumed to have

Nothing checks that a script builds its state this way; `MainNative.lean`
elaborates whatever the file says.  These definitions are what the theorems below
are stated about, and they are what the scripts under `test/regress/*.cpc.lean`
(and the ones cvc5 emits) do write.
-/

/-- Run a list of commands from a state, as `__eo_invoke_cmd_list` does. -/
def logos_native_invoke_cmd_list (s : NativeState) : CCmdList -> NativeState
  | CCmdList.nil => s
  | CCmdList.cons c cmds => logos_native_invoke_cmd_list (logos_native_invoke_cmd s c) cmds

/-- The state a script that assumes `assums` and then runs `cmds` ends in. -/
def logos_native_run (assums : List Term) (cmds : CCmdList) : NativeState :=
  logos_native_invoke_cmd_list (assums.foldl logos_native_invoke_assume logos_native_init_state) cmds

/-! ## The script computes `logos_verdict`

Each field is tracked separately: the checker state is the one
`logos_check_refutation` folds, and the flag is the conjunction of the two
translation checks.
-/

private theorem state_foldl_assume (assums : List Term) :
    ∀ s : NativeState,
      (assums.foldl logos_native_invoke_assume s).state
        = assums.foldl logos_invoke_input_assume s.state := by
  induction assums with
  | nil => intro s; rfl
  | cons A assums ih => intro s; rw [List.foldl_cons, ih, List.foldl_cons]; rfl

private theorem translationOk_foldl_assume (assums : List Term) :
    ∀ s : NativeState,
      (assums.foldl logos_native_invoke_assume s).translationOk
        = (s.translationOk && logos_check_translatableAssumptionList assums) := by
  induction assums with
  | nil => intro s; simp [logos_check_translatableAssumptionList]
  | cons A assums ih =>
    intro s
    rw [List.foldl_cons, ih]
    simp [logos_native_invoke_assume, logos_check_translatableAssumptionList,
      Bool.and_assoc]

private theorem state_invoke_cmd_list :
    ∀ (cmds : CCmdList) (s : NativeState),
      (logos_native_invoke_cmd_list s cmds).state = __eo_invoke_cmd_list s.state cmds := by
  intro cmds
  induction cmds with
  | nil => intro s; rfl
  | cons c cmds ih => intro s; rw [logos_native_invoke_cmd_list, ih]; rfl

/-- `CmdListTranslationOk` of a `cons` splits, so `decide` of it splits too. -/
private theorem check_cmdListTranslationOk_cons (c : CCmd) (cmds : CCmdList) :
    logos_check_cmdListTranslationOk (CCmdList.cons c cmds)
      = (decide (cmdTranslationOk c) && logos_check_cmdListTranslationOk cmds) := by
  rw [Bool.eq_iff_iff]
  simp only [logos_check_cmdListTranslationOk, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h; cases h with | cons _ _ hc hcs => exact ⟨hc, hcs⟩
  · intro h; exact CmdListTranslationOk.cons c cmds h.1 h.2

private theorem translationOk_invoke_cmd_list :
    ∀ (cmds : CCmdList) (s : NativeState),
      (logos_native_invoke_cmd_list s cmds).translationOk
        = (s.translationOk && logos_check_cmdListTranslationOk cmds) := by
  intro cmds
  induction cmds with
  | nil => intro s; simp [logos_native_invoke_cmd_list, logos_check_cmdListTranslationOk,
      CmdListTranslationOk.nil]
  | cons c cmds ih =>
    intro s
    rw [logos_native_invoke_cmd_list, ih, check_cmdListTranslationOk_cons]
    simp [logos_native_invoke_cmd, Bool.and_assoc]

/--
A script that assumes `assums` and then runs `cmds` reports exactly what `logos`
reports for the same assumptions and commands.
-/
theorem logos_native_verdict_eq_verdict (assums : List Term) (cmds : CCmdList) :
    logos_native_verdict (logos_native_run assums cmds) = logos_verdict assums cmds := by
  have hstate : (logos_native_run assums cmds).state
      = __eo_invoke_cmd_list (assums.foldl logos_invoke_input_assume logos_init_state) cmds := by
    rw [logos_native_run, state_invoke_cmd_list, state_foldl_assume]; rfl
  have hok : (logos_native_run assums cmds).translationOk
      = (logos_check_translatableAssumptionList assums
          && logos_check_cmdListTranslationOk cmds) := by
    rw [logos_native_run, translationOk_invoke_cmd_list, translationOk_foldl_assume]
    simp [logos_native_init_state]
  unfold logos_native_verdict logos_verdict logos_check_refutation
  rw [hstate, hok]
  cases __eo_state_is_refutation
      (__eo_invoke_cmd_list (assums.foldl logos_invoke_input_assume logos_init_state) cmds) <;>
    cases logos_check_translatableAssumptionList assums <;>
      cases logos_check_cmdListTranslationOk cmds <;> rfl

/-- `logos_native_state_is_refutation` is the verdict being `correct`. -/
theorem logos_native_state_is_refutation_eq_correct (s : NativeState) :
    logos_native_state_is_refutation s = true ↔ logos_native_verdict s = Verdict.correct := by
  simp [logos_native_state_is_refutation]

end Eo
