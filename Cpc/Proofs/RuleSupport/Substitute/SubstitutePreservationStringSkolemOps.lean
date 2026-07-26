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

private theorem eo_typeof_strings_occur_index_arg_types_of_ne_stuck
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
                  have hBA : aB = aA :=
                    support_eq_of_eo_eq_true aA aB hCond
                  subst aB
                  simp

private theorem eo_typeof_strings_occur_index_args_not_stuck_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_indexof A B C ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck ∧ C ≠ Term.Stuck := by
  rcases eo_typeof_strings_occur_index_arg_types_of_ne_stuck h with
    ⟨T, hA, hB, hC⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · constructor
    · intro hStuck
      rw [hB] at hStuck
      cases hStuck
    · intro hStuck
      rw [hC] at hStuck
      cases hStuck

private theorem eo_typeof_strings_occur_index_re_arg_types_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_indexof_re A B C ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      B = Term.UOp UserOp.RegLan ∧
        C = Term.UOp UserOp.Int := by
  unfold __eo_typeof_str_indexof_re at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_strings_occur_index_re_args_not_stuck_of_ne_stuck
    {A B C : Term}
    (h : __eo_typeof_str_indexof_re A B C ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck ∧ C ≠ Term.Stuck := by
  rcases eo_typeof_strings_occur_index_re_arg_types_of_ne_stuck h with
    ⟨hA, hB, hC⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · constructor
    · intro hStuck
      rw [hB] at hStuck
      cases hStuck
    · intro hStuck
      rw [hC] at hStuck
      cases hStuck

theorem substitute_simul_strings_occur_index_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s needle count xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_occur_index) s)
            needle)
          count))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_strings_occur_index) s)
              needle)
            count)
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
    (hRecCount :
      RuleProofs.eo_has_smt_translation count ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) count xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) count xs ts bvs) =
          __eo_typeof count ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) count xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_strings_occur_index) s)
              needle)
            count)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_occur_index) s)
            needle)
          count) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_strings_occur_index) s)
              needle)
            count)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_strings_occur_index s needle count xs ts bvs
      hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        strings_occur_index_args_have_smt_translation_of_has_smt_translation h)
      (fun S N C hApp => by
        change
          __eo_typeof_str_indexof (__eo_typeof S) (__eo_typeof N)
              (__eo_typeof C) ≠
            Term.Stuck at hApp
        exact
          eo_typeof_strings_occur_index_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ N₁ C₁ S₂ N₂ C₂ hS hN hC => by
        change
          __eo_typeof_str_indexof (__eo_typeof S₁) (__eo_typeof N₁)
              (__eo_typeof C₁) =
            __eo_typeof_str_indexof (__eo_typeof S₂) (__eo_typeof N₂)
              (__eo_typeof C₂)
        rw [hS, hN, hC])
      (fun S N C hSTrans hNTrans hCTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm._at_strings_occur_index
                (__eo_to_smt S) (__eo_to_smt N) (__eo_to_smt C)) ≠
            SmtType.None
        change
          __eo_typeof_str_indexof (__eo_typeof S) (__eo_typeof N)
              (__eo_typeof C) ≠
            Term.Stuck at hApp
        rcases eo_typeof_strings_occur_index_arg_types_of_ne_stuck hApp with
          ⟨T, hSTy, hNTy, hCTy⟩
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
        have hCSmt :
            __smtx_typeof (__eo_to_smt C) = SmtType.Int := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation C hCTrans
          rw [hCTy] at hMatch
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
        rw [typeof_at_strings_occur_index_eq, hSSmt, hNSmt, hCSmt,
          hSeqSmt]
        simp [__smtx_typeof_str_indexof, native_ite, native_Teq])
      hRecS hRecNeedle hRecCount

theorem substitute_simul_strings_occur_index_re_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (s regex count xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) s)
            regex)
          count))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) s)
              regex)
            count)
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
    (hRecRegex :
      RuleProofs.eo_has_smt_translation regex ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs) =
          __eo_typeof regex ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) regex xs ts bvs))
    (hRecCount :
      RuleProofs.eo_has_smt_translation count ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) count xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) count xs ts bvs) =
          __eo_typeof count ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) count xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) s)
              regex)
            count)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) s)
            regex)
          count) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) s)
              regex)
            count)
          xs ts bvs) := by
  exact
    substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_strings_occur_index_re s regex count xs ts bvs
      hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        strings_occur_index_re_args_have_smt_translation_of_has_smt_translation
          h)
      (fun S R C hApp => by
        change
          __eo_typeof_str_indexof_re (__eo_typeof S) (__eo_typeof R)
              (__eo_typeof C) ≠
            Term.Stuck at hApp
        exact
          eo_typeof_strings_occur_index_re_args_not_stuck_of_ne_stuck hApp)
      (fun S₁ R₁ C₁ S₂ R₂ C₂ hS hR hC => by
        change
          __eo_typeof_str_indexof_re (__eo_typeof S₁) (__eo_typeof R₁)
              (__eo_typeof C₁) =
            __eo_typeof_str_indexof_re (__eo_typeof S₂) (__eo_typeof R₂)
              (__eo_typeof C₂)
        rw [hS, hR, hC])
      (fun S R C hSTrans hRTrans hCTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm._at_strings_occur_index_re
                (__eo_to_smt S) (__eo_to_smt R) (__eo_to_smt C)) ≠
            SmtType.None
        change
          __eo_typeof_str_indexof_re (__eo_typeof S) (__eo_typeof R)
              (__eo_typeof C) ≠
            Term.Stuck at hApp
        rcases
            eo_typeof_strings_occur_index_re_arg_types_of_ne_stuck hApp with
          ⟨hSTy, hRTy, hCTy⟩
        have hSSmt :=
          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hSTrans hSTy
        have hRSmt :=
          smt_typeof_eo_to_smt_reglan_of_typeof_reglan hRTrans hRTy
        have hCSmt :=
          smt_typeof_eo_to_smt_int_of_typeof_int hCTrans hCTy
        rw [typeof_at_strings_occur_index_re_eq, hSSmt, hRSmt, hCSmt]
        simp [native_ite, native_Teq])
      hRecS hRecRegex hRecCount

private theorem eo_typeof_strings_replace_all_result_arg_types_of_ne_stuck
    {A B C D : Term}
    (h : __eo_typeof__at_strings_replace_all_result A B C D ≠ Term.Stuck) :
    ∃ T,
      A = Term.Apply (Term.UOp UserOp.Seq) T ∧
        B = Term.Apply (Term.UOp UserOp.Seq) T ∧
          C = Term.Apply (Term.UOp UserOp.Seq) T ∧
            D = Term.UOp UserOp.Int := by
  cases A <;>
    try simp [__eo_typeof__at_strings_replace_all_result] at h
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
                    cases D <;> try simp at h
                    case UOp opD =>
                      cases opD <;> try simp at h
                      case Int =>
                        have hCond :
                            __eo_and (__eo_eq aA aB) (__eo_eq aA aC) =
                              Term.Boolean true :=
                          support_eo_requires_cond_eq_of_non_stuck h
                        rcases eo_and_boolean_true_split hCond with
                          ⟨hAB, hAC⟩
                        have hBA : aB = aA :=
                          support_eq_of_eo_eq_true aA aB hAB
                        have hCA : aC = aA :=
                          support_eq_of_eo_eq_true aA aC hAC
                        subst aB
                        subst aC
                        simp

private theorem eo_typeof_strings_replace_all_result_args_not_stuck_of_ne_stuck
    {A B C D : Term}
    (h : __eo_typeof__at_strings_replace_all_result A B C D ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧
      B ≠ Term.Stuck ∧ C ≠ Term.Stuck ∧ D ≠ Term.Stuck := by
  rcases eo_typeof_strings_replace_all_result_arg_types_of_ne_stuck h with
    ⟨T, hA, hB, hC, hD⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · constructor
    · intro hStuck
      rw [hB] at hStuck
      cases hStuck
    · constructor
      · intro hStuck
        rw [hC] at hStuck
        cases hStuck
      · intro hStuck
        rw [hD] at hStuck
        cases hStuck

private theorem eo_typeof_strings_replace_re_all_result_arg_types_of_ne_stuck
    {A B C D : Term}
    (h :
      __eo_typeof__at_strings_replace_re_all_result A B C D ≠
        Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      B = Term.UOp UserOp.RegLan ∧
        C = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
          D = Term.UOp UserOp.Int := by
  unfold __eo_typeof__at_strings_replace_re_all_result at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_strings_replace_re_all_result_args_not_stuck_of_ne_stuck
    {A B C D : Term}
    (h :
      __eo_typeof__at_strings_replace_re_all_result A B C D ≠
        Term.Stuck) :
    A ≠ Term.Stuck ∧
      B ≠ Term.Stuck ∧ C ≠ Term.Stuck ∧ D ≠ Term.Stuck := by
  rcases
      eo_typeof_strings_replace_re_all_result_arg_types_of_ne_stuck h with
    ⟨hA, hB, hC, hD⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · constructor
    · intro hStuck
      rw [hB] at hStuck
      cases hStuck
    · constructor
      · intro hStuck
        rw [hC] at hStuck
        cases hStuck
      · intro hStuck
        rw [hD] at hStuck
        cases hStuck

theorem substitute_simul_strings_replace_all_result_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (source pattern replacement count xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.UOp UserOp._at_strings_replace_all_result)
                source)
              pattern)
            replacement)
          count))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_strings_replace_all_result)
                  source)
                pattern)
              replacement)
            count)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecSource :
      RuleProofs.eo_has_smt_translation source ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) source xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) source xs ts bvs) =
          __eo_typeof source ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec
              (Term.Boolean isRename) source xs ts bvs))
    (hRecPattern :
      RuleProofs.eo_has_smt_translation pattern ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) pattern xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) pattern xs ts bvs) =
          __eo_typeof pattern ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec
              (Term.Boolean isRename) pattern xs ts bvs))
    (hRecReplacement :
      RuleProofs.eo_has_smt_translation replacement ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) replacement xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) replacement xs ts bvs) =
          __eo_typeof replacement ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec
              (Term.Boolean isRename) replacement xs ts bvs))
    (hRecCount :
      RuleProofs.eo_has_smt_translation count ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) count xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) count xs ts bvs) =
          __eo_typeof count ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec
              (Term.Boolean isRename) count xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_strings_replace_all_result)
                  source)
                pattern)
              replacement)
            count)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.UOp UserOp._at_strings_replace_all_result)
                source)
              pattern)
            replacement)
          count) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_strings_replace_all_result)
                  source)
                pattern)
              replacement)
            count)
          xs ts bvs) := by
  exact
    substitute_simul_quaternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_strings_replace_all_result
      source pattern replacement count xs ts bvs
      hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        strings_replace_all_result_args_have_smt_translation_of_has_smt_translation
          h)
      (fun S P R C hApp => by
        change
          __eo_typeof__at_strings_replace_all_result
              (__eo_typeof S) (__eo_typeof P) (__eo_typeof R)
              (__eo_typeof C) ≠
            Term.Stuck at hApp
        exact
          eo_typeof_strings_replace_all_result_args_not_stuck_of_ne_stuck
            hApp)
      (fun S₁ P₁ R₁ C₁ S₂ P₂ R₂ C₂ hS hP hR hC => by
        change
          __eo_typeof__at_strings_replace_all_result
              (__eo_typeof S₁) (__eo_typeof P₁) (__eo_typeof R₁)
              (__eo_typeof C₁) =
            __eo_typeof__at_strings_replace_all_result
              (__eo_typeof S₂) (__eo_typeof P₂) (__eo_typeof R₂)
              (__eo_typeof C₂)
        rw [hS, hP, hR, hC])
      (fun S P R C hSTrans hPTrans hRTrans hCTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_replace_all
                (SmtTerm.str_substr
                  (__eo_to_smt S)
                  (SmtTerm._at_strings_occur_index
                    (__eo_to_smt S) (__eo_to_smt P) (__eo_to_smt C))
                  (SmtTerm.str_len (__eo_to_smt S)))
                (__eo_to_smt P) (__eo_to_smt R)) ≠
            SmtType.None
        change
          __eo_typeof__at_strings_replace_all_result
              (__eo_typeof S) (__eo_typeof P) (__eo_typeof R)
              (__eo_typeof C) ≠
            Term.Stuck at hApp
        rcases
            eo_typeof_strings_replace_all_result_arg_types_of_ne_stuck
              hApp with
          ⟨T, hSTy, hPTy, hRTy, hCTy⟩
        have hSSmt :
            __smtx_typeof (__eo_to_smt S) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation S hSTrans
          rw [hSTy] at hMatch
          exact hMatch
        have hPSmt :
            __smtx_typeof (__eo_to_smt P) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation P hPTrans
          rw [hPTy] at hMatch
          exact hMatch
        have hRSmt :
            __smtx_typeof (__eo_to_smt R) =
              __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation R hRTrans
          rw [hRTy] at hMatch
          exact hMatch
        have hCSmt :
            __smtx_typeof (__eo_to_smt C) = SmtType.Int := by
          have hMatch :=
            TranslationProofs.eo_to_smt_typeof_matches_translation C hCTrans
          rw [hCTy] at hMatch
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
        rw [typeof_str_replace_all_eq, typeof_str_substr_eq,
          typeof_at_strings_occur_index_eq, typeof_str_len_eq,
          hSSmt, hPSmt, hRSmt, hCSmt, hSeqSmt]
        simp [__smtx_typeof_seq_op_3, __smtx_typeof_str_substr,
          __smtx_typeof_str_indexof, __smtx_typeof_seq_op_1_ret,
          native_ite, native_Teq])
      hRecSource hRecPattern hRecReplacement hRecCount

theorem substitute_simul_strings_replace_re_all_result_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (source regex replacement count xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.UOp UserOp._at_strings_replace_re_all_result)
                source)
              regex)
            replacement)
          count))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_strings_replace_re_all_result)
                  source)
                regex)
              replacement)
            count)
          xs ts bvs) ≠
        Term.Stuck)
    (hRecSource :
      RuleProofs.eo_has_smt_translation source ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) source xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) source xs ts bvs) =
          __eo_typeof source ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec
              (Term.Boolean isRename) source xs ts bvs))
    (hRecRegex :
      RuleProofs.eo_has_smt_translation regex ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) regex xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) regex xs ts bvs) =
          __eo_typeof regex ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec
              (Term.Boolean isRename) regex xs ts bvs))
    (hRecReplacement :
      RuleProofs.eo_has_smt_translation replacement ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) replacement xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) replacement xs ts bvs) =
          __eo_typeof replacement ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec
              (Term.Boolean isRename) replacement xs ts bvs))
    (hRecCount :
      RuleProofs.eo_has_smt_translation count ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) count xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec
              (Term.Boolean isRename) count xs ts bvs) =
          __eo_typeof count ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec
              (Term.Boolean isRename) count xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_strings_replace_re_all_result)
                  source)
                regex)
              replacement)
            count)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.UOp UserOp._at_strings_replace_re_all_result)
                source)
              regex)
            replacement)
          count) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply
            (Term.Apply
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_strings_replace_re_all_result)
                  source)
                regex)
              replacement)
            count)
          xs ts bvs) := by
  exact
    substitute_simul_quaternary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_strings_replace_re_all_result
      source regex replacement count xs ts bvs
      hXsEnv hBvsEnv hTs hFTrans hTy
      (fun h =>
        strings_replace_re_all_result_args_have_smt_translation_of_has_smt_translation
          h)
      (fun S R P C hApp => by
        change
          __eo_typeof__at_strings_replace_re_all_result
              (__eo_typeof S) (__eo_typeof R) (__eo_typeof P)
              (__eo_typeof C) ≠
            Term.Stuck at hApp
        exact
          eo_typeof_strings_replace_re_all_result_args_not_stuck_of_ne_stuck
            hApp)
      (fun S₁ R₁ P₁ C₁ S₂ R₂ P₂ C₂ hS hR hP hC => by
        change
          __eo_typeof__at_strings_replace_re_all_result
              (__eo_typeof S₁) (__eo_typeof R₁) (__eo_typeof P₁)
              (__eo_typeof C₁) =
            __eo_typeof__at_strings_replace_re_all_result
              (__eo_typeof S₂) (__eo_typeof R₂) (__eo_typeof P₂)
              (__eo_typeof C₂)
        rw [hS, hR, hP, hC])
      (fun S R P C hSTrans hRTrans hPTrans hCTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_replace_re_all
                (SmtTerm.str_substr
                  (__eo_to_smt S)
                  (SmtTerm._at_strings_occur_index_re
                    (__eo_to_smt S) (__eo_to_smt R) (__eo_to_smt C))
                  (SmtTerm.str_len (__eo_to_smt S)))
                (__eo_to_smt R) (__eo_to_smt P)) ≠
            SmtType.None
        change
          __eo_typeof__at_strings_replace_re_all_result
              (__eo_typeof S) (__eo_typeof R) (__eo_typeof P)
              (__eo_typeof C) ≠
            Term.Stuck at hApp
        rcases
            eo_typeof_strings_replace_re_all_result_arg_types_of_ne_stuck
              hApp with
          ⟨hSTy, hRTy, hPTy, hCTy⟩
        have hSSmt :=
          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hSTrans hSTy
        have hRSmt :=
          smt_typeof_eo_to_smt_reglan_of_typeof_reglan hRTrans hRTy
        have hPSmt :=
          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hPTrans hPTy
        have hCSmt :=
          smt_typeof_eo_to_smt_int_of_typeof_int hCTrans hCTy
        rw [typeof_str_replace_re_all_eq, typeof_str_substr_eq,
          typeof_at_strings_occur_index_re_eq, typeof_str_len_eq,
          hSSmt, hRSmt, hPSmt, hCSmt]
        simp [__smtx_typeof_str_substr, __smtx_typeof_seq_op_1_ret,
          native_ite, native_Teq])
      hRecSource hRecRegex hRecReplacement hRecCount


end SubstitutePreservationSupport
