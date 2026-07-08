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

private theorem eo_typeof_str_substr_arg_types_of_ne_stuck
    {S I N : Term}
    (h : __eo_typeof_str_substr S I N ≠ Term.Stuck) :
    ∃ T,
      S = Term.Apply (Term.UOp UserOp.Seq) T ∧
        I = Term.UOp UserOp.Int ∧ N = Term.UOp UserOp.Int := by
  cases S <;> simp [__eo_typeof_str_substr] at h ⊢
  case Apply f T =>
    cases f <;> simp [__eo_typeof_str_substr] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_substr] at h ⊢
      case Seq =>
        cases I <;> simp [__eo_typeof_str_substr] at h ⊢
        case UOp opI =>
          cases opI <;> simp [__eo_typeof_str_substr] at h ⊢
          case Int =>
            cases N <;> simp [__eo_typeof_str_substr] at h ⊢
            case UOp opN =>
              cases opN <;> simp [__eo_typeof_str_substr] at h ⊢

theorem substitute_simul_str_substr_preserves_type_and_translation_of_typeof_ne_stuck
    (s start len xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) start)
          len))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) start)
            len)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecS :
      RuleProofs.eo_has_smt_translation s ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) s xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) s xs ts bvs) =
          __eo_typeof s ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) s xs ts bvs))
    (hRecStart :
      RuleProofs.eo_has_smt_translation start ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) start xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) start xs ts bvs) =
          __eo_typeof start ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) start xs ts bvs))
    (hRecLen :
      RuleProofs.eo_has_smt_translation len ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) len xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) len xs ts bvs) =
          __eo_typeof len ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) len xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) start)
            len)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) start)
          len) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) start)
            len)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_substr s start len xs ts bvs hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
          (eoOp := UserOp.str_substr) (smtOp := SmtTerm.str_substr)
          (by rfl) str_substr_args_have_smt_translation_of_non_none h)
      (fun S I N hApp => by
        change
          __eo_typeof_str_substr (__eo_typeof S) (__eo_typeof I)
              (__eo_typeof N) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_substr_arg_types_of_ne_stuck hApp with
          ⟨T, hS, hI, hN⟩
        constructor
        · intro hSStuck
          rw [hSStuck] at hS
          cases hS
        · constructor
          · intro hIStuck
            rw [hIStuck] at hI
            cases hI
          · intro hNStuck
            rw [hNStuck] at hN
            cases hN)
      (fun S₁ I₁ N₁ S₂ I₂ N₂ hS hI hN => by
        change
          __eo_typeof_str_substr (__eo_typeof S₁) (__eo_typeof I₁)
              (__eo_typeof N₁) =
            __eo_typeof_str_substr (__eo_typeof S₂) (__eo_typeof I₂)
              (__eo_typeof N₂)
        rw [hS, hI, hN])
      (fun S I N hSTrans hITrans hNTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_substr (__eo_to_smt S) (__eo_to_smt I)
                (__eo_to_smt N)) ≠
            SmtType.None
        change
          __eo_typeof_str_substr (__eo_typeof S) (__eo_typeof I)
              (__eo_typeof N) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_substr_arg_types_of_ne_stuck hApp with
          ⟨T, hSTy, hITy, hNTy⟩
        have hSSmt :
            __smtx_typeof (__eo_to_smt S) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation S hSTrans
          rw [hSTy] at hMatch
          exact hMatch
        have hISmt :
            __smtx_typeof (__eo_to_smt I) = SmtType.Int := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation I hITrans
          rw [hITy] at hMatch
          simpa using hMatch
        have hNSmt :
            __smtx_typeof (__eo_to_smt N) = SmtType.Int := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation N hNTrans
          rw [hNTy] at hMatch
          simpa using hMatch
        have hSeqNN :
            __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
              SmtType.None := by
          simpa [hSTy] using
            eo_to_smt_typeof_ne_none_of_has_smt_translation S hSTrans
        have hSeqSmt :
            __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) =
              SmtType.Seq (__eo_to_smt_type T) := by
          cases hTSmt : __eo_to_smt_type T <;>
            simp [TranslationProofs.eo_to_smt_type_seq,
              __smtx_typeof_guard, native_ite, native_Teq, hTSmt] at hSeqNN ⊢
        rw [typeof_str_substr_eq, hSSmt, hISmt, hNSmt, hSeqSmt]
        simp [__smtx_typeof_str_substr])
      hRecS hRecStart hRecLen


end SubstitutePreservationSupport
