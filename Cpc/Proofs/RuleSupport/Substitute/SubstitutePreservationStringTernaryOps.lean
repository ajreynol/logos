module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationTernaryCore
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationTernaryCore

public section

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

private theorem eo_typeof_str_replace_args_not_stuck_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_replace A B C ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck ∧ C ≠ Term.Stuck := by
  cases A <;> cases B <;> cases C <;>
    simp [__eo_typeof_str_replace] at h ⊢

private theorem eo_typeof_str_replace_arg_types_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_replace A B C ≠ Term.Stuck) :
    ∃ T,
      A = Term.Apply (Term.UOp UserOp.Seq) T ∧
        B = Term.Apply (Term.UOp UserOp.Seq) T ∧
          C = Term.Apply (Term.UOp UserOp.Seq) T := by
  cases A <;> try simp [__eo_typeof_str_replace] at h
  case Apply fA aA =>
    cases fA <;> try simp at h
    case UOp opA =>
      cases opA <;> try simp at h
      case Seq =>
        cases B <;> try simp at h
        case Apply fB aB =>
          cases fB <;> try simp at h
          case UOp opB =>
            cases opB <;> try simp at h
            case Seq =>
              cases C <;> try simp at h
              case Apply fC aC =>
                cases fC <;> try simp at h
                case UOp opC =>
                  cases opC <;> try simp at h
                  case Seq =>
                    have hCond :
                        __eo_and (__eo_eq aA aB) (__eo_eq aA aC) =
                          Term.Boolean true :=
                      support_eo_requires_cond_eq_of_non_stuck h
                    rcases eo_and_boolean_true_split hCond with ⟨hAB, hAC⟩
                    have hBA : aB = aA := support_eq_of_eo_eq_true aA aB hAB
                    have hCA : aC = aA := support_eq_of_eo_eq_true aA aC hAC
                    subst aB
                    subst aC
                    simp

theorem substitute_simul_str_replace_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s old new xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) old)
          new))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) old)
            new)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecS :
      RuleProofs.eo_has_smt_translation s ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) =
          __eo_typeof s ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs))
    (hRecOld :
      RuleProofs.eo_has_smt_translation old ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) old xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) old xs ts bvs) =
          __eo_typeof old ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) old xs ts bvs))
    (hRecNew :
      RuleProofs.eo_has_smt_translation new ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) new xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) new xs ts bvs) =
          __eo_typeof new ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) new xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) old)
            new)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) old)
          new) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) old)
            new)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_replace s old new xs ts bvs hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
          (eoOp := UserOp.str_replace) (smtOp := SmtTerm.str_replace)
          (by rfl)
          (fun hNN =>
            seq_triop_args_have_smt_translation_of_non_none
              (typeof_str_replace_eq (__eo_to_smt s) (__eo_to_smt old)
                (__eo_to_smt new))
              hNN)
          h)
      (fun S O N hApp => by
        change
          __eo_typeof_str_replace (__eo_typeof S) (__eo_typeof O)
              (__eo_typeof N) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_replace_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ O₁ N₁ S₂ O₂ N₂ hS hO hN => by
        change
          __eo_typeof_str_replace (__eo_typeof S₁) (__eo_typeof O₁)
              (__eo_typeof N₁) =
            __eo_typeof_str_replace (__eo_typeof S₂) (__eo_typeof O₂)
              (__eo_typeof N₂)
        rw [hS, hO, hN])
      (fun S O N hSTrans hOTrans hNTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_replace (__eo_to_smt S) (__eo_to_smt O)
                (__eo_to_smt N)) ≠
            SmtType.None
        change
          __eo_typeof_str_replace (__eo_typeof S) (__eo_typeof O)
              (__eo_typeof N) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_replace_arg_types_of_ne_stuck hApp with
          ⟨T, hSTy, hOTy, hNTy⟩
        have hSSmt :
            __smtx_typeof (__eo_to_smt S) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation S hSTrans
          rw [hSTy] at hMatch
          exact hMatch
        have hOSmt :
            __smtx_typeof (__eo_to_smt O) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation O hOTrans
          rw [hOTy] at hMatch
          exact hMatch
        have hNSmt :
            __smtx_typeof (__eo_to_smt N) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation N hNTrans
          rw [hNTy] at hMatch
          exact hMatch
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
        rw [typeof_str_replace_eq, hSSmt, hOSmt, hNSmt, hSeqSmt]
        simp [__smtx_typeof_seq_op_3, native_ite, native_Teq])
      hRecS hRecOld hRecNew

theorem substitute_simul_str_replace_all_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s old new xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) old)
          new))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) old)
            new)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecS :
      RuleProofs.eo_has_smt_translation s ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) =
          __eo_typeof s ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs))
    (hRecOld :
      RuleProofs.eo_has_smt_translation old ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) old xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) old xs ts bvs) =
          __eo_typeof old ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) old xs ts bvs))
    (hRecNew :
      RuleProofs.eo_has_smt_translation new ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) new xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) new xs ts bvs) =
          __eo_typeof new ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) new xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) old)
            new)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) old)
          new) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) s) old)
            new)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_replace_all s old new xs ts bvs hXsEnv hBvsEnv hTs
      hFTrans hTy
      (fun h =>
        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
          (eoOp := UserOp.str_replace_all) (smtOp := SmtTerm.str_replace_all)
          (by rfl)
          (fun hNN =>
            seq_triop_args_have_smt_translation_of_non_none
              (typeof_str_replace_all_eq (__eo_to_smt s) (__eo_to_smt old)
                (__eo_to_smt new))
              hNN)
          h)
      (fun S O N hApp => by
        change
          __eo_typeof_str_replace (__eo_typeof S) (__eo_typeof O)
              (__eo_typeof N) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_replace_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ O₁ N₁ S₂ O₂ N₂ hS hO hN => by
        change
          __eo_typeof_str_replace (__eo_typeof S₁) (__eo_typeof O₁)
              (__eo_typeof N₁) =
            __eo_typeof_str_replace (__eo_typeof S₂) (__eo_typeof O₂)
              (__eo_typeof N₂)
        rw [hS, hO, hN])
      (fun S O N hSTrans hOTrans hNTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_replace_all (__eo_to_smt S) (__eo_to_smt O)
                (__eo_to_smt N)) ≠
            SmtType.None
        change
          __eo_typeof_str_replace (__eo_typeof S) (__eo_typeof O)
              (__eo_typeof N) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_replace_arg_types_of_ne_stuck hApp with
          ⟨T, hSTy, hOTy, hNTy⟩
        have hSSmt :
            __smtx_typeof (__eo_to_smt S) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation S hSTrans
          rw [hSTy] at hMatch
          exact hMatch
        have hOSmt :
            __smtx_typeof (__eo_to_smt O) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation O hOTrans
          rw [hOTy] at hMatch
          exact hMatch
        have hNSmt :
            __smtx_typeof (__eo_to_smt N) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation N hNTrans
          rw [hNTy] at hMatch
          exact hMatch
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
        rw [typeof_str_replace_all_eq, hSSmt, hOSmt, hNSmt, hSeqSmt]
        simp [__smtx_typeof_seq_op_3, native_ite, native_Teq])
      hRecS hRecOld hRecNew

private theorem eo_typeof_str_indexof_args_not_stuck_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_indexof A B C ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck ∧ C ≠ Term.Stuck := by
  cases A <;> cases B <;> cases C <;>
    simp [__eo_typeof_str_indexof] at h ⊢

private theorem eo_typeof_str_indexof_arg_types_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_indexof A B C ≠ Term.Stuck) :
    ∃ T,
      A = Term.Apply (Term.UOp UserOp.Seq) T ∧
        B = Term.Apply (Term.UOp UserOp.Seq) T ∧
          C = Term.UOp UserOp.Int := by
  cases A <;> try simp [__eo_typeof_str_indexof] at h
  case Apply fA aA =>
    cases fA <;> try simp at h
    case UOp opA =>
      cases opA <;> try simp at h
      case Seq =>
        cases B <;> try simp at h
        case Apply fB aB =>
          cases fB <;> try simp at h
          case UOp opB =>
            cases opB <;> try simp at h
            case Seq =>
              cases C <;> try simp at h
              case UOp opC =>
                cases opC <;> try simp at h
                case Int =>
                  have hCond : __eo_eq aA aB = Term.Boolean true :=
                    support_eo_requires_cond_eq_of_non_stuck h
                  have hBA : aB = aA := support_eq_of_eo_eq_true aA aB hCond
                  subst aB
                  simp

theorem substitute_simul_str_indexof_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s needle start xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) needle)
          start))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) needle)
            start)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecS :
      RuleProofs.eo_has_smt_translation s ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) =
          __eo_typeof s ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs))
    (hRecNeedle :
      RuleProofs.eo_has_smt_translation needle ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) needle xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) needle xs ts bvs) =
          __eo_typeof needle ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) needle xs ts bvs))
    (hRecStart :
      RuleProofs.eo_has_smt_translation start ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) start xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) start xs ts bvs) =
          __eo_typeof start ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) start xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) needle)
            start)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) needle)
          start) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) needle)
            start)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_indexof s needle start xs ts bvs hXsEnv hBvsEnv hTs
      hFTrans hTy
      (fun h =>
        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
          (eoOp := UserOp.str_indexof) (smtOp := SmtTerm.str_indexof)
          (by rfl) str_indexof_args_have_smt_translation_of_non_none h)
      (fun S N I hApp => by
        change
          __eo_typeof_str_indexof (__eo_typeof S) (__eo_typeof N)
              (__eo_typeof I) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_indexof_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ N₁ I₁ S₂ N₂ I₂ hS hN hI => by
        change
          __eo_typeof_str_indexof (__eo_typeof S₁) (__eo_typeof N₁)
              (__eo_typeof I₁) =
            __eo_typeof_str_indexof (__eo_typeof S₂) (__eo_typeof N₂)
              (__eo_typeof I₂)
        rw [hS, hN, hI])
      (fun S N I hSTrans hNTrans hITrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_indexof (__eo_to_smt S) (__eo_to_smt N)
                (__eo_to_smt I)) ≠
            SmtType.None
        change
          __eo_typeof_str_indexof (__eo_typeof S) (__eo_typeof N)
              (__eo_typeof I) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_indexof_arg_types_of_ne_stuck hApp with
          ⟨T, hSTy, hNTy, hITy⟩
        have hSSmt :
            __smtx_typeof (__eo_to_smt S) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation S hSTrans
          rw [hSTy] at hMatch
          exact hMatch
        have hNSmt :
            __smtx_typeof (__eo_to_smt N) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation N hNTrans
          rw [hNTy] at hMatch
          exact hMatch
        have hISmt :
            __smtx_typeof (__eo_to_smt I) = SmtType.Int := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation I hITrans
          rw [hITy] at hMatch
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
        rw [typeof_str_indexof_eq, hSSmt, hNSmt, hISmt, hSeqSmt]
        simp [__smtx_typeof_str_indexof, native_ite, native_Teq])
      hRecS hRecNeedle hRecStart

private theorem eo_typeof_str_update_args_not_stuck_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_update A B C ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck ∧ C ≠ Term.Stuck := by
  cases A <;> cases B <;> cases C <;>
    simp [__eo_typeof_str_update] at h ⊢

private theorem eo_typeof_str_update_arg_types_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_update A B C ≠ Term.Stuck) :
    ∃ T,
      A = Term.Apply (Term.UOp UserOp.Seq) T ∧
        B = Term.UOp UserOp.Int ∧
          C = Term.Apply (Term.UOp UserOp.Seq) T := by
  cases A <;> try simp [__eo_typeof_str_update] at h
  case Apply fA aA =>
    cases fA <;> try simp at h
    case UOp opA =>
      cases opA <;> try simp at h
      case Seq =>
        cases B <;> try simp at h
        case UOp opB =>
          cases opB <;> try simp at h
          case Int =>
            cases C <;> try simp at h
            case Apply fC aC =>
              cases fC <;> try simp at h
              case UOp opC =>
                cases opC <;> try simp at h
                case Seq =>
                  have hCond : __eo_eq aA aC = Term.Boolean true :=
                    support_eo_requires_cond_eq_of_non_stuck h
                  have hCA : aC = aA := support_eq_of_eo_eq_true aA aC hCond
                  subst aC
                  simp

theorem substitute_simul_str_update_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s idx repl xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) s) idx)
          repl))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) s) idx)
            repl)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecS :
      RuleProofs.eo_has_smt_translation s ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs) =
          __eo_typeof s ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) s xs ts bvs))
    (hRecIdx :
      RuleProofs.eo_has_smt_translation idx ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) idx xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) idx xs ts bvs) =
          __eo_typeof idx ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) idx xs ts bvs))
    (hRecRepl :
      RuleProofs.eo_has_smt_translation repl ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs) =
          __eo_typeof repl ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) repl xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) s) idx)
            repl)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) s) idx)
          repl) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) s) idx)
            repl)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_update s idx repl xs ts bvs hXsEnv hBvsEnv hTs
      hFTrans hTy
      (fun h =>
        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
          (eoOp := UserOp.str_update) (smtOp := SmtTerm.str_update)
          (by rfl) str_update_args_have_smt_translation_of_non_none h)
      (fun S I R hApp => by
        change
          __eo_typeof_str_update (__eo_typeof S) (__eo_typeof I)
              (__eo_typeof R) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_update_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ I₁ R₁ S₂ I₂ R₂ hS hI hR => by
        change
          __eo_typeof_str_update (__eo_typeof S₁) (__eo_typeof I₁)
              (__eo_typeof R₁) =
            __eo_typeof_str_update (__eo_typeof S₂) (__eo_typeof I₂)
              (__eo_typeof R₂)
        rw [hS, hI, hR])
      (fun S I R hSTrans hITrans hRTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_update (__eo_to_smt S) (__eo_to_smt I)
                (__eo_to_smt R)) ≠
            SmtType.None
        change
          __eo_typeof_str_update (__eo_typeof S) (__eo_typeof I)
              (__eo_typeof R) ≠
            Term.Stuck at hApp
        rcases eo_typeof_str_update_arg_types_of_ne_stuck hApp with
          ⟨T, hSTy, hITy, hRTy⟩
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
        have hRSmt :
            __smtx_typeof (__eo_to_smt R) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation R hRTrans
          rw [hRTy] at hMatch
          exact hMatch
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
        rw [typeof_str_update_eq, hSSmt, hISmt, hRSmt, hSeqSmt]
        simp [__smtx_typeof_str_update, native_ite, native_Teq])
      hRecS hRecIdx hRecRepl


end SubstitutePreservationSupport
