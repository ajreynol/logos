import Cpc.Proofs.RuleSupport.SubstitutePreservationTernaryCore

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open TypedListSubstitutionSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstitutePreservationSupport

private theorem eo_typeof_ite_arg_types_of_ne_stuck
    {C X Y : Term}
    (h : __eo_typeof_ite C X Y ≠ Term.Stuck) :
    C = Term.Bool ∧ X ≠ Term.Stuck ∧ Y ≠ Term.Stuck ∧ Y = X := by
  cases C <;> cases X <;> cases Y <;>
    simp_all [__eo_typeof_ite, __eo_requires, __eo_eq, native_ite,
      native_teq]

theorem substitute_simul_ite_preserves_type_and_translation_of_typeof_ne_stuck
    (c x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecC :
      RuleProofs.eo_has_smt_translation c ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) c xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) c xs ts bvs) =
          __eo_typeof c ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) c xs ts bvs))
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.ite c x y xs ts bvs hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        ite_args_have_smt_translation_of_has_smt_translation h)
      (fun C X Y hApp => by
        change
          __eo_typeof_ite (__eo_typeof C) (__eo_typeof X)
              (__eo_typeof Y) ≠
            Term.Stuck at hApp
        rcases eo_typeof_ite_arg_types_of_ne_stuck hApp with
          ⟨hC, hX, hY, _hYX⟩
        constructor
        · intro hCStuck
          rw [hCStuck] at hC
          cases hC
        · exact ⟨hX, hY⟩)
      (fun C₁ X₁ Y₁ C₂ X₂ Y₂ hC hX hY => by
        change
          __eo_typeof_ite (__eo_typeof C₁) (__eo_typeof X₁)
              (__eo_typeof Y₁) =
            __eo_typeof_ite (__eo_typeof C₂) (__eo_typeof X₂)
              (__eo_typeof Y₂)
        rw [hC, hX, hY])
      (fun C X Y hCTrans hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt X)
                (__eo_to_smt Y)) ≠
            SmtType.None
        change
          __eo_typeof_ite (__eo_typeof C) (__eo_typeof X)
              (__eo_typeof Y) ≠
            Term.Stuck at hApp
        rcases eo_typeof_ite_arg_types_of_ne_stuck hApp with
          ⟨hCTy, _hXNe, _hYNe, hYTy⟩
        have hCSmt :
            __smtx_typeof (__eo_to_smt C) = SmtType.Bool := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation C hCTrans
          rw [hCTy] at hMatch
          exact hMatch
        have hXSmt :=
          TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
        have hYSmt :=
          TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
        have hXNN :
            __eo_to_smt_type (__eo_typeof X) ≠ SmtType.None :=
          eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
        rw [typeof_ite_eq, hCSmt, hXSmt, hYSmt, hYTy]
        simpa [__smtx_typeof_ite, native_ite, native_Teq] using hXNN)
      hRecC hRecX hRecY


end SubstitutePreservationSupport
