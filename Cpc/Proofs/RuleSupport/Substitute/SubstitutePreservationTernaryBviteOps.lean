import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationTernaryCore

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

private theorem eo_typeof_bvite_arg_types_of_ne_stuck
    {C X Y : Term}
    (h : __eo_typeof_bvite C X Y ≠ Term.Stuck) :
    C = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
      X ≠ Term.Stuck ∧ Y ≠ Term.Stuck ∧ Y = X := by
  have hXNN : X ≠ Term.Stuck := by
    intro hX
    subst X
    exact h rfl
  have hYNN : Y ≠ Term.Stuck := by
    intro hY
    subst Y
    apply h
    cases X <;> rfl
  have hCTy :
      C = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    cases C <;> simp [__eo_typeof_bvite, hXNN, hYNN] at h ⊢
    case Apply f w =>
      cases f <;> simp [__eo_typeof_bvite, hXNN, hYNN] at h ⊢
      case UOp op =>
        cases op <;> simp [__eo_typeof_bvite, hXNN, hYNN] at h ⊢
        case BitVec =>
          cases w <;> simp [__eo_typeof_bvite, hXNN, hYNN] at h ⊢
          case Numeral n =>
            by_cases hn : n = 1
            · subst n
              rfl
            · exfalso
              apply h
              simp [__eo_typeof_bvite, __eo_requires, __eo_eq, native_ite,
                native_teq, native_not, hn]
  have hReq :
      __eo_requires (__eo_eq X Y) (Term.Boolean true) X ≠
        Term.Stuck := by
    rw [hCTy] at h
    cases X <;> cases Y <;>
      simp_all [__eo_typeof_bvite, __eo_requires, __eo_eq, native_ite,
        native_teq]
  have hYX : Y = X :=
    support_eq_of_eo_eq_true X Y
      (support_eo_requires_cond_eq_of_non_stuck hReq)
  exact ⟨hCTy, hXNN, hYNN, hYX⟩

theorem substitute_simul_bvite_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (c x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) x) y)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecC :
      RuleProofs.eo_has_smt_translation c ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) c xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) c xs ts bvs) =
          __eo_typeof c ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) c xs ts bvs))
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) x) y)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.bvite c x y xs ts bvs hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        bvite_args_have_smt_translation_of_has_smt_translation h)
      (fun C X Y hApp => by
        change
          __eo_typeof_bvite (__eo_typeof C) (__eo_typeof X)
              (__eo_typeof Y) ≠
            Term.Stuck at hApp
        rcases eo_typeof_bvite_arg_types_of_ne_stuck hApp with
          ⟨hC, hX, hY, _hYX⟩
        constructor
        · intro hCStuck
          rw [hCStuck] at hC
          cases hC
        · exact ⟨hX, hY⟩)
      (fun C₁ X₁ Y₁ C₂ X₂ Y₂ hC hX hY => by
        change
          __eo_typeof_bvite (__eo_typeof C₁) (__eo_typeof X₁)
              (__eo_typeof Y₁) =
            __eo_typeof_bvite (__eo_typeof C₂) (__eo_typeof X₂)
              (__eo_typeof Y₂)
        rw [hC, hX, hY])
      (fun C X Y hCTrans hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.ite
                (SmtTerm.eq (__eo_to_smt C) (SmtTerm.Binary 1 1))
                (__eo_to_smt X) (__eo_to_smt Y)) ≠
            SmtType.None
        change
          __eo_typeof_bvite (__eo_typeof C) (__eo_typeof X)
              (__eo_typeof Y) ≠
            Term.Stuck at hApp
        rcases eo_typeof_bvite_arg_types_of_ne_stuck hApp with
          ⟨hCTy, _hXNe, _hYNe, hYTy⟩
        have hCSmt :
            __smtx_typeof (__eo_to_smt C) = SmtType.BitVec 1 := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation C hCTrans
          rw [hCTy] at hMatch
          simpa [__eo_to_smt_type, native_ite] using hMatch
        have hCondTy :
            __smtx_typeof
                (SmtTerm.eq (__eo_to_smt C) (SmtTerm.Binary 1 1)) =
              SmtType.Bool := by
          rw [typeof_eq_eq, hCSmt, smt_typeof_binary_one_one]
          simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
            native_Teq]
        have hXSmt :=
          TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
        have hYSmt :=
          TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
        have hXNN :
            __eo_to_smt_type (__eo_typeof X) ≠ SmtType.None :=
          eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
        rw [typeof_ite_eq, hCondTy, hXSmt, hYSmt, hYTy]
        simpa [__smtx_typeof_ite, native_ite, native_Teq] using hXNN)
      hRecC hRecX hRecY


end SubstitutePreservationSupport
