import Cpc.Proofs.RuleSupport.SubstitutePreservationBinaryArithArrayHelpers
import Cpc.Proofs.RuleSupport.TypedListSubstitutionSupport

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

theorem eo_typeof_str_concat_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_concat A B ≠ Term.Stuck) :
    ∃ T,
      A = Term.Apply (Term.UOp UserOp.Seq) T ∧
        B = Term.Apply (Term.UOp UserOp.Seq) T := by
  cases A <;> simp [__eo_typeof_str_concat] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_concat] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_concat] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_concat] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_concat] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_concat] at h ⊢
            case Seq =>
              exact
                support_eq_of_eo_eq_true x y
                  (support_eo_requires_cond_eq_of_non_stuck h)

theorem eo_typeof_str_concat_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_concat A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_str_concat_arg_types_of_ne_stuck h with
    ⟨T, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_seq_binop_non_none_of_eo_seq_type_non_none
    {T : Term}
    (hT :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
        SmtType.None) :
    __smtx_typeof_seq_op_2
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T))
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)) ≠
      SmtType.None := by
  rw [TranslationProofs.eo_to_smt_type_seq] at hT ⊢
  have hElemNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hT
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hT
  have hSeq :=
    TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hElemNN
  rw [hSeq]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]

theorem smt_seq_binop_ret_non_none_of_eo_seq_type_non_none
    {T : Term} {ret : SmtType}
    (hT :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
        SmtType.None)
    (hRet : ret ≠ SmtType.None) :
    __smtx_typeof_seq_op_2_ret
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T))
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)) ret ≠
      SmtType.None := by
  rw [TranslationProofs.eo_to_smt_type_seq] at hT ⊢
  have hElemNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hT
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hT
  have hSeq :=
    TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hElemNN
  rw [hSeq]
  simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, hRet]

theorem smt_str_concat_non_none_of_eo_typeof_str_concat_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_str_concat (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.str_concat (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_str_concat_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hXTyNN :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
        SmtType.None := by
    simpa [hXTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
  rw [typeof_str_concat_eq, hXSmt, hYSmt, hXTy, hYTy]
  exact smt_seq_binop_non_none_of_eo_seq_type_non_none hXTyNN

theorem eo_typeof_str_contains_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ T,
      A = Term.Apply (Term.UOp UserOp.Seq) T ∧
        B = Term.Apply (Term.UOp UserOp.Seq) T := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              exact
                support_eq_of_eo_eq_true x y
                  (support_eo_requires_cond_eq_of_non_stuck h)

theorem eo_typeof_str_contains_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_str_contains_arg_types_of_ne_stuck h with
    ⟨T, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_str_contains_non_none_of_eo_typeof_str_contains_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_str_contains (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_str_contains_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hXTyNN :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
        SmtType.None := by
    simpa [hXTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
  rw [typeof_str_contains_eq, hXSmt, hYSmt, hXTy, hYTy]
  exact
    smt_seq_binop_ret_non_none_of_eo_seq_type_non_none hXTyNN
      (by simp)

private theorem smt_typeof_eo_to_smt_seq_of_typeof_seq_elem_eq
    {X U : Term} {T : SmtType}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.Apply (Term.UOp UserOp.Seq) U)
    (hU : __eo_to_smt_type U = T) :
    __smtx_typeof (__eo_to_smt X) = SmtType.Seq T := by
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hXNN :
      __smtx_typeof (__eo_to_smt X) ≠ SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hXTrans
  rw [hXTy] at hMatch
  cases hUSmt : __eo_to_smt_type U <;>
    simp [TranslationProofs.eo_to_smt_type_seq, __smtx_typeof_guard,
      native_ite, native_Teq, hUSmt] at hMatch hU ⊢
  case None =>
    exact False.elim (hXNN hMatch)
  all_goals
    simpa [← hU] using hMatch

theorem smt_seq_bool_binop_non_none_of_original_type_eq
    (eoOp : UserOp)
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hTranslate :
      ∀ X Y,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) X) Y) =
          smtOp (__eo_to_smt X) (__eo_to_smt Y))
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof X) (__smtx_typeof Y) SmtType.Bool)
    (x y X Y : Term)
    (hOrigTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (hOrigXTrans : RuleProofs.eo_has_smt_translation x)
    (hOrigYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hXTyEq : __eo_typeof X = __eo_typeof x)
    (hYTyEq : __eo_typeof Y = __eo_typeof y) :
    __smtx_typeof (smtOp (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hOrigNN :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate x y]
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hOrigTrans
  rcases
      seq_binop_args_of_non_none_ret
        (op := smtOp) (R := SmtType.Bool)
        (hSmtType (__eo_to_smt x) (__eo_to_smt y)) hOrigNN with
    ⟨T, hOrigXSmt, hOrigYSmt⟩
  rcases
      TranslationProofs.eo_typeof_eq_seq_of_smt_seq_from_ih
        x
        (fun _ =>
          TranslationProofs.eo_to_smt_typeof_matches_translation
            x hOrigXTrans)
        hOrigXSmt with
    ⟨UX, hOrigXTy, hUX⟩
  rcases
      TranslationProofs.eo_typeof_eq_seq_of_smt_seq_from_ih
        y
        (fun _ =>
          TranslationProofs.eo_to_smt_typeof_matches_translation
            y hOrigYTrans)
        hOrigYSmt with
    ⟨UY, hOrigYTy, hUY⟩
  have hXTy :
      __eo_typeof X = Term.Apply (Term.UOp UserOp.Seq) UX :=
    hXTyEq.trans hOrigXTy
  have hYTy :
      __eo_typeof Y = Term.Apply (Term.UOp UserOp.Seq) UY :=
    hYTyEq.trans hOrigYTy
  have hXSmt :
      __smtx_typeof (__eo_to_smt X) = SmtType.Seq T :=
    smt_typeof_eo_to_smt_seq_of_typeof_seq_elem_eq
      hXTrans hXTy hUX
  have hYSmt :
      __smtx_typeof (__eo_to_smt Y) = SmtType.Seq T :=
    smt_typeof_eo_to_smt_seq_of_typeof_seq_elem_eq
      hYTrans hYTy hUY
  rw [hSmtType, hXSmt, hYSmt]
  simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]

theorem seq_bool_binop_has_translation_of_original_type_eq
    (eoOp : UserOp)
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hTranslate :
      ∀ X Y,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) X) Y) =
          smtOp (__eo_to_smt X) (__eo_to_smt Y))
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof X) (__smtx_typeof Y) SmtType.Bool)
    (x y X Y : Term)
    (hOrigTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (hOrigXTrans : RuleProofs.eo_has_smt_translation x)
    (hOrigYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hXTyEq : __eo_typeof X = __eo_typeof x)
    (hYTyEq : __eo_typeof Y = __eo_typeof y) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) X) Y) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [hTranslate X Y]
  exact
    smt_seq_bool_binop_non_none_of_original_type_eq
      eoOp smtOp hTranslate hSmtType x y X Y hOrigTrans
      hOrigXTrans hOrigYTrans hXTrans hYTrans hXTyEq hYTyEq

theorem smt_seq_char_bool_binop_non_none_of_original_type_eq
    (eoOp : UserOp)
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hTranslate :
      ∀ X Y,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) X) Y) =
          smtOp (__eo_to_smt X) (__eo_to_smt Y))
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          native_ite
            (native_Teq (__smtx_typeof X) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof Y) (SmtType.Seq SmtType.Char))
              SmtType.Bool SmtType.None)
            SmtType.None)
    (x y X Y : Term)
    (hOrigTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (hOrigXTrans : RuleProofs.eo_has_smt_translation x)
    (hOrigYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hXTyEq : __eo_typeof X = __eo_typeof x)
    (hYTyEq : __eo_typeof Y = __eo_typeof y) :
    __smtx_typeof (smtOp (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hOrigNN :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate x y]
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hOrigTrans
  have hOrigArgsSmt :=
    seq_char_binop_args_of_non_none (op := smtOp) (ret := SmtType.Bool)
      (hSmtType (__eo_to_smt x) (__eo_to_smt y)) hOrigNN
  have hOrigXTy :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    TranslationProofs.eo_typeof_eq_seq_char_of_smt_seq_char_from_ih
      x
      (fun _ =>
        TranslationProofs.eo_to_smt_typeof_matches_translation x hOrigXTrans)
      hOrigArgsSmt.1
  have hOrigYTy :
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    TranslationProofs.eo_typeof_eq_seq_char_of_smt_seq_char_from_ih
      y
      (fun _ =>
        TranslationProofs.eo_to_smt_typeof_matches_translation y hOrigYTrans)
      hOrigArgsSmt.2
  have hXTy :
      __eo_typeof X =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    hXTyEq.trans hOrigXTy
  have hYTy :
      __eo_typeof Y =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
    hYTyEq.trans hOrigYTy
  have hXSmt :=
    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hXTrans hXTy
  have hYSmt :=
    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hYTrans hYTy
  rw [hSmtType (__eo_to_smt X) (__eo_to_smt Y), hXSmt, hYSmt]
  simp [native_ite, native_Teq]

theorem seq_char_bool_binop_has_translation_of_original_type_eq
    (eoOp : UserOp)
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hTranslate :
      ∀ X Y,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) X) Y) =
          smtOp (__eo_to_smt X) (__eo_to_smt Y))
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          native_ite
            (native_Teq (__smtx_typeof X) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof Y) (SmtType.Seq SmtType.Char))
              SmtType.Bool SmtType.None)
            SmtType.None)
    (x y X Y : Term)
    (hOrigTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (hOrigXTrans : RuleProofs.eo_has_smt_translation x)
    (hOrigYTrans : RuleProofs.eo_has_smt_translation y)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hXTyEq : __eo_typeof X = __eo_typeof x)
    (hYTyEq : __eo_typeof Y = __eo_typeof y) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) X) Y) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [hTranslate X Y]
  exact
    smt_seq_char_bool_binop_non_none_of_original_type_eq
      eoOp smtOp hTranslate hSmtType x y X Y hOrigTrans
      hOrigXTrans hOrigYTrans hXTrans hYTrans hXTyEq hYTyEq

theorem eo_typeof_str_at_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_at A B ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Seq) T ∧
      B = Term.UOp UserOp.Int := by
  cases A <;> cases B <;> simp [__eo_typeof_str_at] at h ⊢
  case Apply.UOp f n op =>
    cases f <;> simp [__eo_typeof_str_at] at h ⊢
    case UOp opF =>
      cases opF <;> cases op <;> simp [__eo_typeof_str_at] at h ⊢

theorem eo_typeof_str_at_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_at A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_str_at_arg_types_of_ne_stuck h with
    ⟨T, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_str_at_non_none_of_eo_seq_type_non_none
    {T : Term}
    (hT :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
        SmtType.None) :
    __smtx_typeof_str_at
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T))
        SmtType.Int ≠
      SmtType.None := by
  cases hSmtT : __eo_to_smt_type T <;>
    simp [TranslationProofs.eo_to_smt_type_seq, __smtx_typeof_str_at,
      __smtx_typeof_guard, native_ite, native_Teq, hSmtT] at hT ⊢

theorem smt_str_at_non_none_of_eo_typeof_str_at_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_str_at (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.str_at (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_str_at_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hXTyNN :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
        SmtType.None := by
    simpa [hXTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
  rw [typeof_str_at_eq, hXSmt, hYSmt, hXTy, hYTy]
  exact smt_str_at_non_none_of_eo_seq_type_non_none hXTyNN

theorem eo_typeof_seq_nth_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_seq_nth A B ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Seq) T ∧
      B = Term.UOp UserOp.Int := by
  cases A <;> cases B <;> simp [__eo_typeof_seq_nth] at h ⊢
  case Apply.UOp f n op =>
    cases f <;> simp [__eo_typeof_seq_nth] at h ⊢
    case UOp opF =>
      cases opF <;> cases op <;> simp [__eo_typeof_seq_nth] at h ⊢

theorem eo_typeof_seq_nth_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_seq_nth A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_seq_nth_arg_types_of_ne_stuck h with
    ⟨T, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_seq_nth_non_none_of_eo_typeof_seq_nth_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_seq_nth (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.seq_nth (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_seq_nth_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hSeqNN :
      __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Seq (__eo_to_smt_type T)) ≠
        SmtType.None := by
    have hXTyNN :
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
          SmtType.None := by
      simpa [hXTy] using
        eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
    simpa [TranslationProofs.eo_to_smt_type_seq] using hXTyNN
  have hElemNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hSeqNN
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hSeqNN
  have hSeqGuard :
      __smtx_typeof_guard (__eo_to_smt_type T)
          (SmtType.Seq (__eo_to_smt_type T)) =
        SmtType.Seq (__eo_to_smt_type T) :=
    TranslationProofs.smtx_typeof_guard_of_non_none _ _ hElemNN
  have hXSeqTy :
      __smtx_typeof (__eo_to_smt X) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [hXSmt, hXTy, TranslationProofs.eo_to_smt_type_seq, hSeqGuard]
  have hSeqWf :
      __smtx_type_wf (SmtType.Seq (__eo_to_smt_type T)) = true :=
    Smtm.smt_term_seq_type_wf_of_non_none
      (__eo_to_smt X) hXTrans hXSeqTy
  have hElemWf :
      __smtx_type_wf (__eo_to_smt_type T) = true :=
    seq_type_wf_component_of_wf hSeqWf
  rw [typeof_seq_nth_eq, hXSeqTy, hYSmt, hYTy]
  simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf, hElemWf,
    hElemNN, native_ite]

theorem eo_typeof_seq_unit_arg_not_stuck_of_ne_stuck
    {A : Term}
    (h : __eo_typeof_seq_unit A ≠ Term.Stuck) :
    A ≠ Term.Stuck := by
  cases A <;> simp [__eo_typeof_seq_unit] at h ⊢

theorem smt_seq_unit_non_none_of_has_smt_translation_type_eq
    (A X : Term)
    (hAppTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.seq_unit) A))
    (hATrans : RuleProofs.eo_has_smt_translation A)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTyEq : __eo_typeof X = __eo_typeof A) :
    __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt X)) ≠ SmtType.None := by
  have hOrig :
      __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt A)) ≠
        SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hAppTrans
    change
      __smtx_typeof (SmtTerm.seq_unit (__eo_to_smt A)) ≠
        SmtType.None at hAppTrans
    exact hAppTrans
  have hXMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation A hATrans
  have hSmtTy :
      __smtx_typeof (__eo_to_smt X) =
        __smtx_typeof (__eo_to_smt A) := by
    rw [hXMatch, hAMatch, hXTyEq]
  simpa [typeof_seq_unit_eq_closed, hSmtTy] using hOrig

end SubstitutePreservationSupport
