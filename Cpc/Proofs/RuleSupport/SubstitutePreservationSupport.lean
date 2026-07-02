import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# Combined substitution preservation support

This module is a staging point for merging the two structural preservation
proofs for substitution mode (`isr = false`):

* EO type preservation of `__substitute_simul_rec`;
* SMT-translatability preservation of `__substitute_simul_rec`.

The main theorem below currently packages the existing two engines. The intended
next step is to move their shared structural induction here and turn the old
single-purpose theorems into projections, then delete the duplicated engines.
-/

namespace SubstitutePreservationSupport

private abbrev substResult (F xs ts bvs : Term) : Term :=
  __substitute_simul_rec (Term.Boolean false) F xs ts bvs

/--
Size-recursive form of combined substitution preservation under an arbitrary
bound-variable accumulator.

`SubstActualsHaveSmtTypes` is the stronger, instantiate-facing side condition:
it implies the exact EO entry type facts consumed by the older type-preservation
theorem and also carries the SMT-translation/type facts consumed by the older
translatability theorem.
-/
theorem substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck_lt
    (n : Nat) (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hLt : sizeOf F < n)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy : __eo_typeof (substResult F xs ts bvs) ≠ Term.Stuck) :
    __eo_typeof (substResult F xs ts bvs) = __eo_typeof F ∧
      RuleProofs.eo_has_smt_translation (substResult F xs ts bvs) := by
  have hEntryTypes : SubstituteSupport.SubstEntryPreservesTypes xs ts :=
    SubstActualsHaveSmtTypes.entry_eo_type_eq hActuals
  by_cases hApply : ∃ f a, F = Term.Apply f a
  · rcases hApply with ⟨f, a, rfl⟩
    refine ⟨?_, ?_⟩
    · exact
        SubstituteSupport.substitute_simul_rec_typeof_eq_of_typeof_ne_stuck_lt
          n (Term.Apply f a) xs ts bvs
          hLt hXsEnv hBvsEnv hFTrans hTs hEntryTypes hTy
    · exact
        SubstituteTranslatabilitySupport.substitute_simul_has_smt_translation_of_typeof_ne_stuck_lt
          n (Term.Apply f a) xs ts bvs
          hLt hXsEnv hBvsEnv hFTrans hTs hActuals hTy
  · by_cases hVar : ∃ name T, F = Term.Var name T
    · rcases hVar with ⟨name, T, rfl⟩
      exact ⟨
        SubstituteSupport.substitute_simul_rec_var_any_typeof_eq
          name T xs ts bvs hXsEnv hBvsEnv hTs hEntryTypes hFTrans,
        substitute_simul_var_any_has_smt_translation_of_typeof_ne_stuck
          name T xs ts bvs hXsEnv hBvsEnv hFTrans hTs hTy⟩
    · by_cases hStuck : F = Term.Stuck
      · subst F
        exact False.elim
          ((RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck hFTrans) rfl)
      · have hNotApply : ∀ f a, F ≠ Term.Apply f a := by
          intro f a hEq
          exact hApply ⟨f, a, hEq⟩
        have hNotVar : ∀ name T, F ≠ Term.Var name T := by
          intro name T hEq
          exact hVar ⟨name, T, hEq⟩
        exact ⟨
          SubstituteSupport.substitute_simul_rec_atom_typeof_eq_of_typeof_ne_stuck
            _ xs ts bvs hXsEnv hBvsEnv hTs
            hNotApply hNotVar hStuck
            hTy,
          substitute_simul_atom_has_smt_translation_of_typeof_ne_stuck
            _ xs ts bvs hXsEnv hBvsEnv hTs
            hNotApply hNotVar hStuck
            hFTrans hTy⟩

/--
Combined substitution preservation under an arbitrary bound-variable
accumulator.
-/
theorem substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy : __eo_typeof (substResult F xs ts bvs) ≠ Term.Stuck) :
    __eo_typeof (substResult F xs ts bvs) = __eo_typeof F ∧
      RuleProofs.eo_has_smt_translation (substResult F xs ts bvs) :=
  substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck_lt
    (sizeOf F + 1) F xs ts bvs
    (by omega) hXsEnv hBvsEnv hFTrans hTs hActuals hTy

/-- Projection of the combined theorem: EO type preservation. -/
theorem substitute_simul_preserves_type_of_typeof_ne_stuck
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy : __eo_typeof (substResult F xs ts bvs) ≠ Term.Stuck) :
    __eo_typeof (substResult F xs ts bvs) = __eo_typeof F :=
  (substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
    F xs ts bvs hXsEnv hBvsEnv hFTrans hTs hActuals hTy).1

/-- Projection of the combined theorem: SMT-translatability preservation. -/
theorem substitute_simul_preserves_translation_of_typeof_ne_stuck
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy : __eo_typeof (substResult F xs ts bvs) ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation (substResult F xs ts bvs) :=
  (substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
    F xs ts bvs hXsEnv hBvsEnv hFTrans hTs hActuals hTy).2

/--
Instantiate-facing combined preservation for a Boolean-typed substitution result.
-/
theorem substitute_simul_preserves_type_and_translation_of_typeof_bool
    (F xs ts : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
      __eo_typeof F ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) := by
  have hBodyTrans :
      RuleProofs.eo_has_smt_translation F :=
    forall_body_has_smt_translation_of_has_smt_translation xs F hForall
  rcases forall_binders_env_of_has_smt_translation xs F hForall with
    ⟨_binderVars, hXsEnv⟩
  exact
    substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
      F xs ts Term.__eo_List_nil
      (EoVarEnvPerm.of_exact hXsEnv)
      (EoVarEnvPerm.of_exact EoVarEnv.nil)
      hBodyTrans hTs hActuals
      (by
        intro hStuck
        rw [hStuck] at hTy
        cases hTy)

/-- Instantiate-facing projection: SMT-translatability of the substitution. -/
theorem substitute_simul_has_smt_translation_of_typeof_bool
    (F xs ts : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) :=
  (substitute_simul_preserves_type_and_translation_of_typeof_bool
    F xs ts hForall hTs hActuals hTy).2

/--
Instantiate-facing projection: the substitution result has SMT Boolean type.
-/
theorem substitute_simul_has_bool_type_of_typeof_bool
    (F xs ts : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) :=
  RuleProofs.eo_typeof_bool_implies_has_bool_type
    (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)
    (substitute_simul_has_smt_translation_of_typeof_bool F xs ts
      hForall hTs hActuals hTy)
    hTy

end SubstitutePreservationSupport
