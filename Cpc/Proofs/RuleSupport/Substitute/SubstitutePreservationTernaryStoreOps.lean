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

private theorem eo_typeof_store_arg_types_of_ne_stuck
    {A I E : Term}
    (h : __eo_typeof_store A I E ≠ Term.Stuck) :
    ∃ U T,
      A = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T ∧
        I = U ∧ E = T ∧ I ≠ Term.Stuck ∧ E ≠ Term.Stuck := by
  have hINN : I ≠ Term.Stuck := by
    intro hI
    subst I
    exact h rfl
  have hENN : E ≠ Term.Stuck := by
    intro hE
    subst E
    apply h
    cases I <;> rfl
  have hAShape :
      ∃ U T, A = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T := by
    cases A <;> simp [__eo_typeof_store, hINN, hENN] at h ⊢
    case Apply f T =>
      cases f <;> simp [__eo_typeof_store, hINN, hENN] at h ⊢
      case Apply g U =>
        cases g <;> simp [__eo_typeof_store, hINN, hENN] at h ⊢
        case UOp op =>
          cases op <;> simp [__eo_typeof_store, hINN, hENN] at h ⊢
  rcases hAShape with ⟨U, T, hA⟩
  have hReq :
      __eo_requires (__eo_and (__eo_eq U I) (__eo_eq T E))
          (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) ≠
        Term.Stuck := by
    rw [hA] at h
    simpa [__eo_typeof_store, hINN, hENN] using h
  have hAnd :
      __eo_and (__eo_eq U I) (__eo_eq T E) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReq
  have hUI :
      __eo_eq U I = Term.Boolean true :=
    (eo_and_eq_true_cases hAnd).1
  have hTE :
      __eo_eq T E = Term.Boolean true :=
    (eo_and_eq_true_cases hAnd).2
  have hI : I = U :=
    support_eq_of_eo_eq_true U I hUI
  have hE : E = T :=
    support_eq_of_eo_eq_true T E hTE
  exact ⟨U, T, hA, hI, hE, hINN, hENN⟩

theorem substitute_simul_store_preserves_type_and_translation_of_typeof_ne_stuck
    (arr idx val xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) arr) idx)
          val))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) arr) idx)
            val)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecArr :
      RuleProofs.eo_has_smt_translation arr ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) arr xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) arr xs ts bvs) =
          __eo_typeof arr ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) arr xs ts bvs))
    (hRecIdx :
      RuleProofs.eo_has_smt_translation idx ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) idx xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) idx xs ts bvs) =
          __eo_typeof idx ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) idx xs ts bvs))
    (hRecVal :
      RuleProofs.eo_has_smt_translation val ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) val xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) val xs ts bvs) =
          __eo_typeof val ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) val xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) arr) idx)
            val)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) arr) idx)
          val) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) arr) idx)
            val)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.store arr idx val xs ts bvs hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        store_args_have_smt_translation_of_has_smt_translation h)
      (fun A I E hApp => by
        change
          __eo_typeof_store (__eo_typeof A) (__eo_typeof I)
              (__eo_typeof E) ≠
            Term.Stuck at hApp
        rcases eo_typeof_store_arg_types_of_ne_stuck hApp with
          ⟨U, T, hA, _hI, _hE, hINN, hENN⟩
        constructor
        · intro hAStuck
          rw [hAStuck] at hA
          cases hA
        · exact ⟨hINN, hENN⟩)
      (fun A₁ I₁ E₁ A₂ I₂ E₂ hA hI hE => by
        change
          __eo_typeof_store (__eo_typeof A₁) (__eo_typeof I₁)
              (__eo_typeof E₁) =
            __eo_typeof_store (__eo_typeof A₂) (__eo_typeof I₂)
              (__eo_typeof E₂)
        rw [hA, hI, hE])
      (fun A I E hATrans hITrans hETrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.store (__eo_to_smt A) (__eo_to_smt I)
                (__eo_to_smt E)) ≠
            SmtType.None
        change
          __eo_typeof_store (__eo_typeof A) (__eo_typeof I)
              (__eo_typeof E) ≠
            Term.Stuck at hApp
        rcases eo_typeof_store_arg_types_of_ne_stuck hApp with
          ⟨U, T, hATy, hITy, hETy, _hINN, _hENN⟩
        have hASmt :
            __smtx_typeof (__eo_to_smt A) =
              __eo_to_smt_type
                (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation A hATrans
          rw [hATy] at hMatch
          exact hMatch
        have hISmt :
            __smtx_typeof (__eo_to_smt I) = __eo_to_smt_type U := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation I hITrans
          rw [hITy] at hMatch
          exact hMatch
        have hESmt :
            __smtx_typeof (__eo_to_smt E) = __eo_to_smt_type T := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation E hETrans
          rw [hETy] at hMatch
          exact hMatch
        have hArrayNN :
            __eo_to_smt_type
                (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) ≠
              SmtType.None := by
          simpa [hATy] using
            eo_to_smt_typeof_ne_none_of_has_smt_translation A hATrans
        have hArraySmt :
            __eo_to_smt_type
                (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) =
              SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T) := by
          cases hUSmt : __eo_to_smt_type U <;>
            cases hTSmt : __eo_to_smt_type T <;>
            simp [TranslationProofs.eo_to_smt_type_array,
              __smtx_typeof_guard, native_ite, native_and, native_Teq,
              hUSmt, hTSmt] at hArrayNN ⊢
        rw [typeof_store_eq, hASmt, hISmt, hESmt, hArraySmt]
        simp [__smtx_typeof_store, native_ite, native_Teq])
      hRecArr hRecIdx hRecVal


end SubstitutePreservationSupport
