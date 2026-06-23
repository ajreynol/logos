import Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem str_re_consume_translation_facts
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) ∧
      RuleProofs.eo_has_smt_translation side ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side) := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation strIn
      side (by simpa [strIn] using hEqTrans) with
    ⟨hStrInTrans, hSideTrans⟩
  rcases str_in_re_args_smt_types_of_has_translation s r hStrInTrans with
    ⟨hSTy, hRTy⟩
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      simpa [strIn] using hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  exact ⟨hStrInTrans, hSideTrans, hSTy, hRTy, by
    simpa [strIn] using hEqBool⟩

theorem str_re_consume_terms_ne_stuck
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    s ≠ Term.Stuck ∧ r ≠ Term.Stuck ∧ side ≠ Term.Stuck := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, hSideTrans, hSTy, hRTy, _hEqBool⟩
  have hSTrans : RuleProofs.eo_has_smt_translation s := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSTy]
    simp
  have hRTrans : RuleProofs.eo_has_smt_translation r := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hRTy]
    simp
  exact ⟨
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans,
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans,
    RuleProofs.term_ne_stuck_of_has_smt_translation side hSideTrans⟩

theorem str_membership_str_str_in_re (s r : Term) :
    __str_membership_str
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) =
      s := by
  rfl

theorem str_membership_re_str_in_re (s r : Term) :
    __str_membership_re
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) =
      r := by
  rfl

theorem str_membership_rebuild_str_in_re
    (s r : Term)
    (hS : s ≠ Term.Stuck)
    (hR : r ≠ Term.Stuck) :
    __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_in_re)
          (__str_membership_str
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__str_membership_re
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r := by
  simp [str_membership_str_str_in_re, str_membership_re_str_in_re]
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s ≠ Term.Stuck := by
    cases s <;> simp [__eo_mk_apply] at hS ⊢
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.str_in_re) s =
        Term.Apply (Term.UOp UserOp.str_in_re) s :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.str_in_re) s
      hInnerNe
  have hOuterNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r ≠
        Term.Stuck := by
    cases r <;> simp [__eo_mk_apply] at hR ⊢
  rw [hInnerEq]
  exact eo_mk_apply_eq_apply_of_ne_stuck
    (Term.Apply (Term.UOp UserOp.str_in_re) s) r hOuterNe

theorem eo_ite_result_cases
    (c t e z : Term)
    (hNe : __eo_ite c t e ≠ Term.Stuck)
    (hEq : __eo_ite c t e = z) :
    (c = Term.Boolean true ∧ t = z) ∨
      (c = Term.Boolean false ∧ e = z) := by
  rcases eo_ite_cases_of_ne_stuck c t e hNe with hCond | hCond
  · left
    exact ⟨hCond, by simpa [hCond, eo_ite_true] using hEq⟩
  · right
    exact ⟨hCond, by simpa [hCond, eo_ite_false] using hEq⟩

theorem eo_ite_false_result_cases
    (c e : Term)
    (hNe : __eo_ite c (Term.Boolean false) e ≠ Term.Stuck)
    (hEq : __eo_ite c (Term.Boolean false) e = Term.Boolean false) :
    c = Term.Boolean true ∨ e = Term.Boolean false := by
  rcases eo_ite_result_cases c (Term.Boolean false) e
      (Term.Boolean false) hNe hEq with hThen | hElse
  · exact Or.inl hThen.1
  · exact Or.inr hElse.2

theorem eo_and_eq_true_local
    (a b : Term)
    (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;>
    try simp [__eo_and] at h
  case Boolean.Boolean x y =>
    simpa [__eo_and, SmtEval.native_and] using h
  case Binary.Binary w1 n1 w2 n2 =>
    simp [__eo_requires, native_ite, native_teq, native_not] at h
    split at h <;> cases h

theorem str_re_consume_input_eval
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    ∃ ss rv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hRTy, _hEqBool⟩
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  refine ⟨ss, rv, hSEval, hREval, ?_⟩
  change __smtx_model_eval M
      (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv)
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval, hREval]

theorem str_re_consume_str_flatten_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hFlatNe : __str_flatten (__str_nary_intro s) ≠ Term.Stuck) :
    ∃ ss flatSs,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M
          (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
        SmtValue.Seq flatSs ∧
      __smtx_typeof
          (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro s)) =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
        (SmtValue.Seq ss) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, _hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, _rv, hSEval, _hREval, _hStrInEval⟩
  rcases str_flatten_nary_intro_eval_rel M hM s ss hSTy hSEval
      hFlatNe with
    ⟨flatSs, hFlatEval, hFlatTy, hFlatList, hFlatRel⟩
  exact ⟨ss, flatSs, hSEval, hFlatEval, hFlatTy, hFlatList, hFlatRel⟩

theorem str_re_consume_re_flatten_false_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hFlatNe :
      __re_flatten (Term.Boolean false) (Term.Boolean true) r ≠
        Term.Stuck) :
    ∃ rv flatRv,
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
      __smtx_model_eval M
          (__eo_to_smt
            (__re_flatten (Term.Boolean false) (Term.Boolean true) r)) =
        SmtValue.RegLan flatRv ∧
      __smtx_typeof
          (__eo_to_smt
            (__re_flatten (Term.Boolean false) (Term.Boolean true) r)) =
        SmtType.RegLan ∧
      RuleProofs.smt_value_rel (SmtValue.RegLan flatRv)
        (SmtValue.RegLan rv) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, _hSTy, hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨_ss, rv, _hSEval, hREval, _hStrInEval⟩
  rcases re_flatten_false_eval_rel M hM (Term.Boolean false)
      (Term.Boolean true) r rv rfl hRTy hREval hFlatNe with
    ⟨flatRv, hFlatEval, hFlatTy, hFlatRel⟩
  exact ⟨rv, flatRv, hREval, hFlatEval, hFlatTy, hFlatRel⟩

theorem str_re_consume_re_flatten_true_rev_facts
    (r : Term)
    (hRevNe :
      __eo_list_rev (Term.UOp UserOp.re_concat)
          (__re_flatten (Term.Boolean true) (Term.Boolean true) r) ≠
        Term.Stuck) :
    __re_flatten (Term.Boolean true) (Term.Boolean true) r ≠ Term.Stuck ∧
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__re_flatten (Term.Boolean true) (Term.Boolean true) r) =
        Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.re_concat)
          (__eo_list_rev (Term.UOp UserOp.re_concat)
            (__re_flatten (Term.Boolean true) (Term.Boolean true) r)) =
        Term.Boolean true := by
  exact ⟨
    eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.re_concat)
      (__re_flatten (Term.Boolean true) (Term.Boolean true) r) hRevNe,
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.re_concat)
      (__re_flatten (Term.Boolean true) (Term.Boolean true) r) hRevNe,
    eo_list_rev_result_is_list_true_of_ne_stuck (Term.UOp UserOp.re_concat)
      (__re_flatten (Term.Boolean true) (Term.Boolean true) r) hRevNe⟩

theorem str_re_consume_side_smt_type
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    __smtx_typeof (__eo_to_smt side) = SmtType.Bool := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hRTy, _hEqBool⟩
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation strIn
      side (by simpa [strIn] using hEqTrans) with
    ⟨hSameTy, _hStrInNN⟩
  have hStrInTy :
      __smtx_typeof (__eo_to_smt strIn) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hSTy, hRTy, native_ite, native_Teq]
  rw [← hSameTy, hStrInTy]

theorem str_re_consume_side_eval_bool
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    ∃ b,
      __smtx_model_eval M (__eo_to_smt side) =
        SmtValue.Boolean b := by
  have hSideTy := str_re_consume_side_smt_type s r side hEqTrans
  have hSideEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt side)) =
        SmtType.Bool := by
    simpa [hSideTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt side) (by
        unfold term_has_non_none_type
        rw [hSideTy]
        simp)
  exact bool_value_canonical hSideEvalTy

theorem str_re_consume_model_rel_of_side_eq_str_in_re
    (M : SmtModel) (s r side : Term)
    (hSideEq :
      side =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  subst side
  exact RuleProofs.smt_value_rel_refl _

theorem str_re_consume_model_rel_of_consume_identity
    (M : SmtModel) (s r side : Term)
    (hSide : side = __str_re_consume s r)
    (hIdentity :
      __str_re_consume s r =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M s r side
  rw [hSide, hIdentity]

theorem str_re_consume_model_rel_of_side_false
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSideFalse : side = Term.Boolean false)
    (hInputFalse :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
        native_str_in_re (native_unpack_string ss) rv = false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, rv, hSEval, hREval, hStrInEval⟩
  have hNativeFalse := hInputFalse ss rv hSEval hREval
  subst side
  rw [hStrInEval, hNativeFalse]
  change RuleProofs.smt_value_rel
    (SmtValue.Boolean false)
    (__smtx_model_eval M (SmtTerm.Boolean false))
  rw [__smtx_model_eval.eq_1]
  exact RuleProofs.smt_value_rel_refl _

theorem native_str_in_re_eq_of_seq_reglan_rel
    {ss ss' : SmtSeq} {rv rv' : native_RegLan}
    (hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char)
    (hSeqRel :
      RuleProofs.smt_value_rel (SmtValue.Seq ss') (SmtValue.Seq ss))
    (hRegRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan rv') (SmtValue.RegLan rv)) :
    native_str_in_re (native_unpack_string ss') rv' =
      native_str_in_re (native_unpack_string ss) rv := by
  have hSeq : RuleProofs.smt_seq_rel ss' ss := by
    simpa [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel] using hSeqRel
  have hSeqEq : ss' = ss :=
    (RuleProofs.smt_seq_rel_iff_eq ss' ss).1 hSeq
  subst ss'
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSeqTy
  exact smt_value_rel_reglan_valid_eq hRegRel hValid

theorem str_re_consume_model_rel_of_side_str_in_re_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r side s' r' : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSideEq :
      side = Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s') r')
    (hSideRel :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          ∃ ss' rv',
            __smtx_model_eval M (__eo_to_smt s') = SmtValue.Seq ss' ∧
            __smtx_model_eval M (__eo_to_smt r') = SmtValue.RegLan rv' ∧
            RuleProofs.smt_value_rel (SmtValue.Seq ss') (SmtValue.Seq ss) ∧
            RuleProofs.smt_value_rel (SmtValue.RegLan rv')
              (SmtValue.RegLan rv)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, _hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, rv, hSEval, hREval, hStrInEval⟩
  rcases hSideRel ss rv hSEval hREval with
    ⟨ss', rv', hSEval', hREval', hSeqRel, hRegRel⟩
  have hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hNativeEq :
      native_str_in_re (native_unpack_string ss') rv' =
        native_str_in_re (native_unpack_string ss) rv :=
    native_str_in_re_eq_of_seq_reglan_rel hSeqTy hSeqRel hRegRel
  subst side
  rw [hStrInEval]
  change RuleProofs.smt_value_rel
    (SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv))
    (__smtx_model_eval M
      (SmtTerm.str_in_re (__eo_to_smt s') (__eo_to_smt r')))
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval',
    hREval']
  simpa [hNativeEq] using
    RuleProofs.smt_value_rel_refl
      (SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv))

theorem str_re_consume_model_rel_of_side_native_eval
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSideEval :
      ∀ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
          __smtx_model_eval M (__eo_to_smt side) =
            SmtValue.Boolean
              (native_str_in_re (native_unpack_string ss) rv)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, rv, hSEval, hREval, hStrInEval⟩
  rw [hStrInEval, hSideEval ss rv hSEval hREval]
  exact RuleProofs.smt_value_rel_refl _

theorem str_re_consume_model_rel_of_re_none_result
    (M : SmtModel) (hM : model_total_typed M)
    (s side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.UOp UserOp.re_none)))
          side))
    (hSideFalse : side = Term.Boolean false) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.UOp UserOp.re_none))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_false M hM s
    (Term.UOp UserOp.re_none) side hEqTrans hSideFalse
  intro ss rv _hSEval hREval
  change __smtx_model_eval M SmtTerm.re_none = SmtValue.RegLan rv at hREval
  rw [__smtx_model_eval.eq_104] at hREval
  cases hREval
  exact native_str_in_re_re_none (native_unpack_string ss)

theorem str_re_consume_model_rel_of_re_all_result
    (M : SmtModel) (hM : model_total_typed M)
    (s side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.UOp UserOp.re_all)))
          side))
    (hSideEq :
      side =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String []))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.UOp UserOp.re_all))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_translation_facts s (Term.UOp UserOp.re_all) side
      hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, _hRTy, _hEqBool⟩
  apply str_re_consume_model_rel_of_side_native_eval M hM s
    (Term.UOp UserOp.re_all) side hEqTrans
  intro ss rv hSEval hREval
  have hSeqTy :
      __smtx_typeof_value (SmtValue.Seq ss) =
        SmtType.Seq SmtType.Char := by
    rw [← hSEval]
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSeqTy
  change __smtx_model_eval M SmtTerm.re_all = SmtValue.RegLan rv at hREval
  rw [__smtx_model_eval.eq_105] at hREval
  cases hREval
  have hInputTrue :
      native_str_in_re (native_unpack_string ss) native_re_all = true :=
    native_str_in_re_re_all (native_unpack_string ss) hValid
  rw [hSideEq, hInputTrue]
  change __smtx_model_eval M
      (SmtTerm.str_in_re (SmtTerm.String [])
        (SmtTerm.str_to_re (SmtTerm.String []))) =
    SmtValue.Boolean true
  have hEmptyValid : native_string_valid ([] : native_String) = true := by
    rfl
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
    __smtx_model_eval_str_to_re, native_unpack_string_pack_string,
    native_str_in_re, native_str_to_re, native_re_of_list,
    native_re_nullable, hEmptyValid]

theorem str_re_consume_rec_re_none_eq
    (s fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s (Term.UOp UserOp.re_none) fuel =
      Term.Boolean false := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec] at hS hFuel ⊢

theorem str_re_consume_rec_re_all_eq
    (s fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s (Term.UOp UserOp.re_all) fuel =
      Term.Apply
        (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String []))
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec] at hS hFuel ⊢

theorem str_re_consume_rec_re_none_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.UOp UserOp.re_none)))
          side))
    (hSide : side = __str_re_consume_rec s (Term.UOp UserOp.re_none) fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.UOp UserOp.re_none))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideFalse : side = Term.Boolean false := by
    rw [hSide, str_re_consume_rec_re_none_eq s fuel hS hFuel]
  exact str_re_consume_model_rel_of_re_none_result M hM s side hEqTrans
    hSideFalse

theorem str_re_consume_rec_re_all_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.UOp UserOp.re_all)))
          side))
    (hSide : side = __str_re_consume_rec s (Term.UOp UserOp.re_all) fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.UOp UserOp.re_all))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideEq :
      side =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String []))
          (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) := by
    rw [hSide, str_re_consume_rec_re_all_eq s fuel hS hFuel]
  exact str_re_consume_model_rel_of_re_all_result M hM s side hEqTrans
    hSideEq

theorem native_re_concat_left_empty_local (r : native_RegLan) :
    native_re_concat (native_str_to_re []) r = r := by
  cases r <;> simp [native_re_concat, native_str_to_re, native_re_of_list,
    native_re_mk_concat]

theorem native_re_concat_right_empty_local (r : native_RegLan) :
    native_re_concat r (native_str_to_re []) = r := by
  cases r <;> simp [native_re_concat, native_str_to_re, native_re_of_list,
    native_re_mk_concat]

theorem nativeListInRe_char_self_local
    (c : native_Char) (hc : native_char_valid c = true) :
    nativeListInRe [c] (SmtRegLan.char c) = true := by
  simp [nativeListInRe, native_re_deriv, native_re_nullable, hc]

theorem nativeListInRe_re_of_list_self_local :
    ∀ pat : native_String,
      native_string_valid pat = true ->
        nativeListInRe pat (native_re_of_list pat) = true
  | [], _ => by
      simp [native_re_of_list, nativeListInRe, native_re_nullable]
  | c :: cs, hValid => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hHead : nativeListInRe [c] (SmtRegLan.char c) = true :=
        nativeListInRe_char_self_local c hc
      have hTail : nativeListInRe cs (native_re_of_list cs) = true :=
        nativeListInRe_re_of_list_self_local cs hcs
      have hConcat :
          nativeListInRe (c :: cs)
              (native_re_mk_concat (SmtRegLan.char c)
                (native_re_of_list cs)) = true :=
        (nativeListInRe_mk_concat_true_iff_exists_append (c :: cs)
          (SmtRegLan.char c) (native_re_of_list cs)).2
          ⟨[c], cs, rfl, hHead, hTail⟩
      simpa [native_re_of_list] using hConcat

theorem native_str_in_re_str_to_re_self_local
    (pat : native_String)
    (hValid : native_string_valid pat = true) :
    native_str_in_re pat (native_str_to_re pat) = true := by
  simpa [native_str_in_re, hValid, native_str_to_re, nativeListInRe] using
    nativeListInRe_re_of_list_self_local pat hValid

theorem native_str_in_re_str_to_re_concat_left_local
    (xs ys : native_String) (r : native_RegLan)
    (hXsValid : native_string_valid xs = true) :
    native_str_in_re (xs ++ ys) (native_re_concat (native_str_to_re xs) r) =
      native_str_in_re ys r := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hMem
    by_cases hAppendValid : native_string_valid (xs ++ ys) = true
    · have hListMem :
          nativeListInRe (xs ++ ys)
              (native_re_mk_concat (native_str_to_re xs) r) = true := by
        simpa [native_str_in_re, hAppendValid, native_re_concat,
          nativeListInRe] using hMem
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append (xs ++ ys)
            (native_str_to_re xs) r).1 hListMem with
        ⟨left, right, hAppend, hLeft, hRight⟩
      have hLeftValid : native_string_valid left = true :=
        native_string_valid_append_left left right (by
          simpa [hAppend] using hAppendValid)
      have hLeftMem :
          native_str_in_re left (native_str_to_re xs) = true := by
        simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
      have hLeftEq : left = xs :=
        native_str_in_re_str_to_re_eq hLeftValid hLeftMem
      subst left
      have hRightEq : right = ys := by
        exact List.append_cancel_left hAppend
      subst right
      have hYsValid : native_string_valid ys = true :=
        native_string_valid_append_right xs ys hAppendValid
      simpa [native_str_in_re, hYsValid, nativeListInRe] using hRight
    · simp [native_str_in_re, hAppendValid] at hMem
  · intro hMem
    by_cases hYsValid : native_string_valid ys = true
    · have hAppendValid : native_string_valid (xs ++ ys) = true := by
        exact native_string_valid_append hXsValid hYsValid
      have hXsMem :
          native_str_in_re xs (native_str_to_re xs) = true :=
        native_str_in_re_str_to_re_self_local xs hXsValid
      exact native_str_in_re_re_concat_intro xs ys
        (native_str_to_re xs) r hXsMem hMem
    · simp [native_str_in_re, hYsValid] at hMem

theorem native_str_in_re_str_to_re_concat_singleton_false_local
    (c d : native_Char) (ys : native_String) (r : native_RegLan)
    (hNe : c ≠ d) :
    native_str_in_re (c :: ys)
        (native_re_concat (native_str_to_re [d]) r) =
      false := by
  by_cases hValid : native_string_valid (c :: ys) = true
  · apply Bool.eq_false_iff.mpr
    intro hMem
    have hListMem :
        nativeListInRe (c :: ys)
            (native_re_mk_concat (native_str_to_re [d]) r) = true := by
      simpa [native_str_in_re, hValid, native_re_concat, nativeListInRe]
        using hMem
    rcases
        (nativeListInRe_mk_concat_true_iff_exists_append (c :: ys)
          (native_str_to_re [d]) r).1 hListMem with
      ⟨left, right, hAppend, hLeft, _hRight⟩
    have hLeftValid : native_string_valid left = true :=
      native_string_valid_append_left left right (by
        simpa [hAppend] using hValid)
    have hLeftMem :
        native_str_in_re left (native_str_to_re [d]) = true := by
      simpa [native_str_in_re, hLeftValid, nativeListInRe] using hLeft
    have hLeftEq : left = [d] :=
      native_str_in_re_str_to_re_eq hLeftValid hLeftMem
    subst left
    cases hAppend
    exact hNe rfl
  · simp [native_str_in_re, hValid]

theorem native_unpack_string_pack_seq_concat_local
    (T : SmtType) (ss1 ss2 : SmtSeq) :
    native_unpack_string
        (native_pack_seq T
          (native_seq_concat (native_unpack_seq ss1) (native_unpack_seq ss2))) =
      native_unpack_string ss1 ++ native_unpack_string ss2 := by
  simp [native_unpack_string, native_seq_concat, Smtm.native_unpack_pack_seq,
    List.map_append]

theorem str_re_consume_model_rel_of_re_concat_empty_left
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
                r)))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let concat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) eps) r
  rcases str_re_consume_translation_facts s concat side (by
      simpa [eps, concat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hConcatTy, _hEqBool⟩
  have hConcatArgs :
      __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt eps) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt concat) ≠ SmtType.None
      rw [hConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt eps) (__eo_to_smt r)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hConcatArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hConcatArgs.2]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hEpsEval :
      __smtx_model_eval M (__eo_to_smt eps) =
        SmtValue.RegLan (native_str_to_re []) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [])) =
      SmtValue.RegLan (native_str_to_re [])
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
      native_unpack_string_pack_string]
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt concat) =
        SmtValue.RegLan (native_re_concat (native_str_to_re []) rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt eps) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat (native_str_to_re []) rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hEpsEval,
      hREval]
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              concat)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt concat)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hConcatEval, hREval, native_re_concat_left_empty_local]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_concat_empty_right
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat) r)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat) r)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let eps := Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])
  let concat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r) eps
  rcases str_re_consume_translation_facts s concat side (by
      simpa [eps, concat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hConcatTy, _hEqBool⟩
  have hConcatArgs :
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt eps) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt eps)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt concat) ≠ SmtType.None
      rw [hConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt r) (__eo_to_smt eps)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hConcatArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hConcatArgs.1]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hEpsEval :
      __smtx_model_eval M (__eo_to_smt eps) =
        SmtValue.RegLan (native_str_to_re []) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [])) =
      SmtValue.RegLan (native_str_to_re [])
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
      native_unpack_string_pack_string]
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt concat) =
        SmtValue.RegLan (native_re_concat rv (native_str_to_re [])) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt r) (__eo_to_smt eps)) =
      SmtValue.RegLan (native_re_concat rv (native_str_to_re []))
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hEpsEval,
      hREval]
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              concat)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt concat)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hConcatEval, hREval, native_re_concat_right_empty_local]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_rec_str_concat_re_concat_empty_left_eq
    (s1 s2 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
          r)
        fuel =
      __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        r fuel := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel ⊢

theorem str_re_consume_rec_non_str_concat_re_concat_empty_left_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hNotConcat :
      ∀ s1 s2 : Term,
        s ≠ Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2) :
    __str_re_consume_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
          r)
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec] at hS hFuel hNotConcat ⊢

theorem str_re_consume_rec_re_concat_empty_left_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
          r)
        fuel =
      __str_re_consume_rec s r fuel := by
  by_cases hConcat :
      ∃ s1 s2 : Term,
        s = Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  · rcases hConcat with ⟨s1, s2, hEq⟩
    subst s
    exact str_re_consume_rec_str_concat_re_concat_empty_left_eq s1 s2 r
      fuel hFuel
  · exact str_re_consume_rec_non_str_concat_re_concat_empty_left_eq s r fuel
      hS hFuel (by
        intro s1 s2 hEq
        exact hConcat ⟨s1, s2, hEq⟩)

theorem str_re_consume_rec_re_concat_empty_left_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
            r)
          fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_rec_re_concat_empty_left_eq s r fuel hS
      hFuel]
  apply str_re_consume_model_rel_of_re_concat_empty_left M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_str_concat_str_to_re_eq_true_eq
    (s1 s2 s3 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEq : __eo_eq s1 s3 = Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) s3))
          r)
        fuel =
      __str_re_consume_rec s2 r fuel := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hS3Ne hEq ⊢
  all_goals simp [hEq, eo_ite_true]

theorem str_re_consume_rec_str_concat_str_to_re_len_mismatch_eq
    (s1 s2 s3 r fuel : Term)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEqFalse : __eo_eq s1 s3 = Term.Boolean false)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) =
        Term.Boolean true) :
    __str_re_consume_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.str_to_re) s3))
          r)
        fuel =
      Term.Boolean false := by
  cases fuel <;> simp [__str_re_consume_rec] at hFuel hS3Ne hEqFalse hLen ⊢
  all_goals simp [hEqFalse, hLen, eo_ite_false, eo_ite_true]

theorem str_re_consume_string_singleton_of_seq_type_len_one
    (s : Term)
    (hTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hLen : __eo_is_eq (__eo_len s) (Term.Numeral 1) = Term.Boolean true) :
    ∃ c : native_Char, s = Term.String [c] := by
  cases s <;>
    simp [__eo_len, __eo_is_eq, native_teq, native_and, native_not,
      SmtEval.native_and, SmtEval.native_not] at hLen ⊢
  case String str =>
    have hNatLen : str.length = 1 := by
      have hInt : (str.length : Int) = 1 := by
        simpa [native_str_len] using hLen.symm
      exact_mod_cast hInt
    cases str with
    | nil =>
        simp at hNatLen
    | cons c cs =>
        cases cs with
        | nil =>
            exact ⟨c, rfl⟩
        | cons d rest =>
            exfalso
            simp at hNatLen
  case Binary w n =>
    exfalso
    change __smtx_typeof (SmtTerm.Binary w n) =
      SmtType.Seq SmtType.Char at hTy
    rw [__smtx_typeof.eq_5] at hTy
    cases hCond :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
      simp [native_ite, hCond] at hTy

theorem str_re_consume_model_rel_of_str_concat_str_to_re_prefix
    (M : SmtModel) (hM : model_total_typed M)
    (s1 s2 r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s1))
                r)))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s1))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let headRe := Term.Apply (Term.UOp UserOp.str_to_re) s1
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) headRe) r
  rcases str_re_consume_translation_facts sConcat rConcat side (by
      simpa [sConcat, headRe, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hConcatTy, hRConcatTy, _hEqBool⟩
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hConcatTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt headRe) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt headRe) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [hRConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt headRe) (__eo_to_smt r)) hNN
  have hS1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS1Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s1) (by
        unfold term_has_non_none_type
        rw [hS1Ty]
        simp)
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRConcatArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRConcatArgs.2]
        simp)
  rcases seq_value_canonical hS1EvalTy with ⟨ss1, hS1Eval⟩
  rcases seq_value_canonical hS2EvalTy with ⟨ss2, hS2Eval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hS1Valid : native_string_valid (native_unpack_string ss1) = true :=
    native_unpack_string_valid_of_typeof_seq_char (by
      simpa [hS1Eval] using hS1EvalTy)
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt sConcat) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
            (native_seq_concat (native_unpack_seq ss1)
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (__eo_to_smt s1) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
          (native_seq_concat (native_unpack_seq ss1)
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS1Eval,
      hS2Eval]
  have hHeadEval :
      __smtx_model_eval M (__eo_to_smt headRe) =
        SmtValue.RegLan (native_str_to_re (native_unpack_string ss1)) := by
    change __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt s1)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss1))
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hS1Eval]
  have hRConcatEval :
      __smtx_model_eval M (__eo_to_smt rConcat) =
        SmtValue.RegLan
          (native_re_concat (native_str_to_re (native_unpack_string ss1)) rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat (__eo_to_smt headRe) (__eo_to_smt r)) =
      SmtValue.RegLan
        (native_re_concat (native_str_to_re (native_unpack_string ss1)) rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, hHeadEval,
      hREval]
  have hNativeEq :
      native_str_in_re
          (native_unpack_string
            (native_pack_seq (__smtx_elem_typeof_seq_value ss1)
              (native_seq_concat (native_unpack_seq ss1)
                (native_unpack_seq ss2))))
          (native_re_concat (native_str_to_re (native_unpack_string ss1)) rv) =
        native_str_in_re (native_unpack_string ss2) rv := by
    rw [native_unpack_string_pack_seq_concat_local]
    exact native_str_in_re_str_to_re_concat_left_local
      (native_unpack_string ss1) (native_unpack_string ss2) rv hS1Valid
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) sConcat)
              rConcat)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt sConcat) (__eo_to_smt rConcat)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s2) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hConcatEval,
      hRConcatEval, hS2Eval, hREval, hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_rec_str_concat_str_to_re_eq_true_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s1 s2 s3 r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s3))
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s3))
            r)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEq : __eo_eq s1 s3 = Term.Boolean true)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s2) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s2 r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s3))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hS3Eq : s3 = s1 := eq_of_eo_eq_true s1 s3 hEq
  subst s3
  have hSideRec : side = __str_re_consume_rec s2 r fuel := by
    rw [hSide,
      str_re_consume_rec_str_concat_str_to_re_eq_true_eq s1 s2 s1 r fuel
        hFuel hS3Ne hEq]
  apply str_re_consume_model_rel_of_str_concat_str_to_re_prefix M hM s1
    s2 r side hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_str_concat_str_to_re_len_mismatch_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s1 s2 s3 r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_in_re)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.Apply (Term.UOp UserOp.str_to_re) s3))
                r)))
          side))
    (hSide :
      side =
        __str_re_consume_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_concat)
              (Term.Apply (Term.UOp UserOp.str_to_re) s3))
            r)
          fuel)
    (hFuel : fuel ≠ Term.Stuck)
    (hS3Ne : s3 ≠ Term.String [])
    (hEqFalse : __eo_eq s1 s3 = Term.Boolean false)
    (hLen :
      __eo_and (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
        (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) =
        Term.Boolean true) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_in_re)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_concat) s1) s2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re) s3))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let sConcat :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s1) s2
  let headRe := Term.Apply (Term.UOp UserOp.str_to_re) s3
  let rConcat := Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) headRe) r
  rcases str_re_consume_translation_facts sConcat rConcat side (by
      simpa [sConcat, headRe, rConcat] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hConcatTy, hRConcatTy, _hEqBool⟩
  rcases str_concat_args_of_seq_type s1 s2 SmtType.Char (by
      simpa [sConcat] using hConcatTy) with
    ⟨hS1Ty, hS2Ty⟩
  have hRConcatArgs :
      __smtx_typeof (__eo_to_smt headRe) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_concat (__eo_to_smt headRe) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt rConcat) ≠ SmtType.None
      rw [hRConcatTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
      (typeof_re_concat_eq (__eo_to_smt headRe) (__eo_to_smt r)) hNN
  have hS3Ty :
      __smtx_typeof (__eo_to_smt s3) = SmtType.Seq SmtType.Char := by
    have hNN : term_has_non_none_type
        (SmtTerm.str_to_re (__eo_to_smt s3)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt headRe) ≠ SmtType.None
      rw [hRConcatArgs.1]
      simp
    exact seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
      (typeof_str_to_re_eq (__eo_to_smt s3)) hNN
  rcases eo_and_eq_true_local
      (__eo_is_eq (__eo_len s1) (Term.Numeral 1))
      (__eo_is_eq (__eo_len s3) (Term.Numeral 1)) hLen with
    ⟨hS1Len, hS3Len⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s1 hS1Ty
      hS1Len with ⟨c, hS1Eq⟩
  rcases str_re_consume_string_singleton_of_seq_type_len_one s3 hS3Ty
      hS3Len with ⟨d, hS3Eq⟩
  subst s1
  subst s3
  have hCharNe : c ≠ d := by
    intro hcd
    subst d
    simp [__eo_eq, native_teq] at hEqFalse
  have hSideFalse : side = Term.Boolean false := by
    rw [hSide,
      str_re_consume_rec_str_concat_str_to_re_len_mismatch_eq
        (Term.String [c]) s2 (Term.String [d]) r fuel hFuel hS3Ne
        hEqFalse hLen]
  apply str_re_consume_model_rel_of_side_false M hM
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
      (Term.String [c])) s2)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.re_concat)
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [d])))
      r)
    side hEqTrans hSideFalse
  intro ss rv hSEval hREval
  have hS2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hS2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s2) (by
        unfold term_has_non_none_type
        rw [hS2Ty]
        simp)
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    simpa [headRe] using hRConcatArgs.2
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical hS2EvalTy with ⟨ss2, hS2Eval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rvTail, hRTailEval⟩
  have hConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat)
              (Term.String [c])) s2)) =
        SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
            (native_seq_concat (native_unpack_seq (native_pack_string [c]))
              (native_unpack_seq ss2))) := by
    change __smtx_model_eval M
        (SmtTerm.str_concat (SmtTerm.String [c]) (__eo_to_smt s2)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string [c]))
          (native_seq_concat (native_unpack_seq (native_pack_string [c]))
            (native_unpack_seq ss2)))
    simp [__smtx_model_eval, __smtx_model_eval_str_concat, hS2Eval]
  have hHeadEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [d]))) =
        SmtValue.RegLan (native_str_to_re [d]) := by
    change __smtx_model_eval M
        (SmtTerm.str_to_re (SmtTerm.String [d])) =
      SmtValue.RegLan (native_str_to_re [d])
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
      native_unpack_string_pack_string]
  have hRConcatEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [d])))
              r)) =
        SmtValue.RegLan (native_re_concat (native_str_to_re [d]) rvTail) := by
    change __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.str_to_re (SmtTerm.String [d])) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_concat (native_str_to_re [d]) rvTail)
    simp [__smtx_model_eval, __smtx_model_eval_re_concat,
      __smtx_model_eval_str_to_re, hRTailEval,
      native_unpack_string_pack_string]
  rw [hConcatEval] at hSEval
  rw [hRConcatEval] at hREval
  cases hSEval
  cases hREval
  rw [native_unpack_string_pack_seq_concat_local]
  simp [native_unpack_string_pack_string]
  exact native_str_in_re_str_to_re_concat_singleton_false_local c d
    (native_unpack_string ss2) rvTail hCharNe

theorem str_re_consume_model_rel_of_re_inter_all_right
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) r)
                (Term.UOp UserOp.re_all))))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) r)
              (Term.UOp UserOp.re_all)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let all := Term.UOp UserOp.re_all
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r) all
  rcases str_re_consume_translation_facts s inter side (by
      simpa [all, inter] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hInterTy, _hEqBool⟩
  have hInterArgs :
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt all) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_inter (__eo_to_smt r) (__eo_to_smt all)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt inter) ≠ SmtType.None
      rw [hInterTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
      (typeof_re_inter_eq (__eo_to_smt r) (__eo_to_smt all)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hInterArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hInterArgs.1]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hAllEval :
      __smtx_model_eval M (__eo_to_smt all) =
        SmtValue.RegLan native_re_all := by
    change __smtx_model_eval M SmtTerm.re_all =
      SmtValue.RegLan native_re_all
    rw [__smtx_model_eval.eq_105]
  have hInterEval :
      __smtx_model_eval M (__eo_to_smt inter) =
        SmtValue.RegLan (native_re_inter rv native_re_all) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt r) (__eo_to_smt all)) =
      SmtValue.RegLan (native_re_inter rv native_re_all)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hAllEval,
      hREval]
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char (by
      simpa [hSEval] using hSEvalTy)
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_inter rv native_re_all) =
        native_str_in_re (native_unpack_string ss) rv := by
    rw [native_str_in_re_re_inter, native_str_in_re_re_all _ hValid]
    simp
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              inter)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt inter)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hInterEval, hREval, hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_inter_all_left
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter)
                  (Term.UOp UserOp.re_all))
                r)))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter)
                (Term.UOp UserOp.re_all))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let all := Term.UOp UserOp.re_all
  let inter := Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) all) r
  rcases str_re_consume_translation_facts s inter side (by
      simpa [all, inter] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hInterTy, _hEqBool⟩
  have hInterArgs :
      __smtx_typeof (__eo_to_smt all) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_inter (__eo_to_smt all) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt inter) ≠ SmtType.None
      rw [hInterTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
      (typeof_re_inter_eq (__eo_to_smt all) (__eo_to_smt r)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hInterArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hInterArgs.2]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hAllEval :
      __smtx_model_eval M (__eo_to_smt all) =
        SmtValue.RegLan native_re_all := by
    change __smtx_model_eval M SmtTerm.re_all =
      SmtValue.RegLan native_re_all
    rw [__smtx_model_eval.eq_105]
  have hInterEval :
      __smtx_model_eval M (__eo_to_smt inter) =
        SmtValue.RegLan (native_re_inter native_re_all rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt all) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_inter native_re_all rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, hAllEval,
      hREval]
  have hValid :
      native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char (by
      simpa [hSEval] using hSEvalTy)
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_inter native_re_all rv) =
        native_str_in_re (native_unpack_string ss) rv := by
    rw [native_str_in_re_re_inter, native_str_in_re_re_all _ hValid]
    simp
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              inter)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt inter)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hInterEval, hREval, hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_union_none_right
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) r)
                (Term.UOp UserOp.re_none))))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) r)
              (Term.UOp UserOp.re_none)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let none := Term.UOp UserOp.re_none
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r) none
  rcases str_re_consume_translation_facts s union side (by
      simpa [none, union] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hUnionTy, _hEqBool⟩
  have hUnionArgs :
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt none) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_union (__eo_to_smt r) (__eo_to_smt none)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt union) ≠ SmtType.None
      rw [hUnionTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
      (typeof_re_union_eq (__eo_to_smt r) (__eo_to_smt none)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.1] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.1]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hNoneEval :
      __smtx_model_eval M (__eo_to_smt none) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_104]
  have hUnionEval :
      __smtx_model_eval M (__eo_to_smt union) =
        SmtValue.RegLan (native_re_union rv native_re_none) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt r) (__eo_to_smt none)) =
      SmtValue.RegLan (native_re_union rv native_re_none)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hNoneEval,
      hREval]
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_union rv native_re_none) =
        native_str_in_re (native_unpack_string ss) rv := by
    rw [native_str_in_re_re_union, native_str_in_re_re_none]
    simp
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              union)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt union)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hUnionEval, hREval, hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_model_rel_of_re_union_none_left
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union)
                  (Term.UOp UserOp.re_none))
                r)))
          side))
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union)
                (Term.UOp UserOp.re_none))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  let none := Term.UOp UserOp.re_none
  let union := Term.Apply (Term.Apply (Term.UOp UserOp.re_union) none) r
  rcases str_re_consume_translation_facts s union side (by
      simpa [none, union] using hEqTrans) with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hUnionTy, _hEqBool⟩
  have hUnionArgs :
      __smtx_typeof (__eo_to_smt none) = SmtType.RegLan ∧
        __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hNN : term_has_non_none_type
        (SmtTerm.re_union (__eo_to_smt none) (__eo_to_smt r)) := by
      unfold term_has_non_none_type
      change __smtx_typeof (__eo_to_smt union) ≠ SmtType.None
      rw [hUnionTy]
      simp
    exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
      (typeof_re_union_eq (__eo_to_smt none) (__eo_to_smt r)) hNN
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hUnionArgs.2] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hUnionArgs.2]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hNoneEval :
      __smtx_model_eval M (__eo_to_smt none) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_104]
  have hUnionEval :
      __smtx_model_eval M (__eo_to_smt union) =
        SmtValue.RegLan (native_re_union native_re_none rv) := by
    change __smtx_model_eval M
        (SmtTerm.re_union (__eo_to_smt none) (__eo_to_smt r)) =
      SmtValue.RegLan (native_re_union native_re_none rv)
    simp [__smtx_model_eval, __smtx_model_eval_re_union, hNoneEval,
      hREval]
  have hNativeEq :
      native_str_in_re (native_unpack_string ss)
          (native_re_union native_re_none rv) =
        native_str_in_re (native_unpack_string ss) rv := by
    rw [native_str_in_re_re_union, native_str_in_re_re_none]
    simp
  have hOrigReduced :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              union)))
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))) := by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt union)))
      (__smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval,
      hUnionEval, hREval, hNativeEq]
    exact RuleProofs.smt_value_rel_refl _
  exact RuleProofs.smt_value_rel_trans _ _ _ hOrigReduced hReducedRel

theorem str_re_consume_inter_re_all_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_inter s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_inter) r)
          (Term.UOp UserOp.re_all))
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_inter] at hS hFuel ⊢

theorem str_re_consume_union_re_none_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_union s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_union) r)
          (Term.UOp UserOp.re_none))
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_union] at hS hFuel ⊢

theorem str_re_consume_inter_re_all_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) r)
                (Term.UOp UserOp.re_all))))
          side))
    (hSide :
      side =
        __str_re_consume_inter s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter) r)
            (Term.UOp UserOp.re_all))
          fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) r)
              (Term.UOp UserOp.re_all)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_inter_re_all_eq s r fuel hS hFuel]
  apply str_re_consume_model_rel_of_re_inter_all_right M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_union_re_none_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) r)
                (Term.UOp UserOp.re_none))))
          side))
    (hSide :
      side =
        __str_re_consume_union s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union) r)
            (Term.UOp UserOp.re_none))
          fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) r)
              (Term.UOp UserOp.re_none)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_union_re_none_eq s r fuel hS hFuel]
  apply str_re_consume_model_rel_of_re_union_none_right M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_inter_re_all_left_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter)
                  (Term.UOp UserOp.re_all))
                r)))
          side))
    (_hSide :
      side =
        __str_re_consume_inter s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter)
              (Term.UOp UserOp.re_all))
            r)
          fuel)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter)
                (Term.UOp UserOp.re_all))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  exact str_re_consume_model_rel_of_re_inter_all_left M hM s r side
    hEqTrans hReducedRel

theorem str_re_consume_union_re_none_left_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union)
                  (Term.UOp UserOp.re_none))
                r)))
          side))
    (_hSide :
      side =
        __str_re_consume_union s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union)
              (Term.UOp UserOp.re_none))
            r)
          fuel)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M (__eo_to_smt side))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union)
                (Term.UOp UserOp.re_none))
              r))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  exact str_re_consume_model_rel_of_re_union_none_left M hM s r side
    hEqTrans hReducedRel

theorem str_re_consume_rec_re_inter_all_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_inter) r)
          (Term.UOp UserOp.re_all))
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec, __str_re_consume_inter] at hS hFuel ⊢

theorem str_re_consume_rec_re_union_none_eq
    (s r fuel : Term)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck) :
    __str_re_consume_rec s
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.re_union) r)
          (Term.UOp UserOp.re_none))
        fuel =
      __str_re_consume_rec s r fuel := by
  cases s <;> cases fuel <;>
    simp [__str_re_consume_rec, __str_re_consume_union] at hS hFuel ⊢

theorem str_re_consume_rec_re_inter_all_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_inter) r)
                (Term.UOp UserOp.re_all))))
          side))
    (hSide :
      side =
        __str_re_consume_rec s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_inter) r)
            (Term.UOp UserOp.re_all))
          fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_inter) r)
              (Term.UOp UserOp.re_all)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_rec_re_inter_all_eq s r fuel hS hFuel]
  apply str_re_consume_model_rel_of_re_inter_all_right M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_rec_re_union_none_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r fuel side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_union) r)
                (Term.UOp UserOp.re_none))))
          side))
    (hSide :
      side =
        __str_re_consume_rec s
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.re_union) r)
            (Term.UOp UserOp.re_none))
          fuel)
    (hS : s ≠ Term.Stuck)
    (hFuel : fuel ≠ Term.Stuck)
    (hReducedRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
        (__smtx_model_eval M
          (__eo_to_smt (__str_re_consume_rec s r fuel)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_union) r)
              (Term.UOp UserOp.re_none)))))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  have hSideRec :
      side = __str_re_consume_rec s r fuel := by
    rw [hSide, str_re_consume_rec_re_union_none_eq s r fuel hS hFuel]
  apply str_re_consume_model_rel_of_re_union_none_right M hM s r side
    hEqTrans
  simpa [hSideRec] using hReducedRel

theorem str_re_consume_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, _hSTy, _hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨_ss, _rv, _hSEval, _hREval, _hStrInEval⟩
  rcases str_re_consume_side_eval_bool M hM s r side hEqTrans with
    ⟨_sideBool, _hSideEval⟩
  by_cases hIdentity :
      __str_re_consume s r =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  · exact str_re_consume_model_rel_of_consume_identity M s r side hSide
      hIdentity
  sorry

private theorem str_in_re_consume_valid_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s r b : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b))
    (hProgNe :
      __eo_prog_str_in_re_consume
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b) ≠
        Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_in_re_consume
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b)) := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  let side := __str_re_consume s r
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) b
  change __eo_requires side b body ≠ Term.Stuck at hProgNe
  have hSideEqB : side = b :=
    eo_requires_eq_of_ne_stuck side b body hProgNe
  have hReqResult : __eo_requires side b body = body :=
    eo_requires_result_eq_of_ne_stuck side b body hProgNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side b body hProgNe
  subst b
  change StepRuleProperties M [] (__eo_requires side side body)
  rw [hReqResult]
  have hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    simpa [strIn, side, body] using hArgTrans
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      exact hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt strIn))
        (__smtx_model_eval M (__eo_to_smt side)) :=
    RuleProofs.str_re_consume_model_rel M hM s r side hEqTrans rfl hSideNe
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by simpa [strIn, side] using hEqBool)⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M strIn side hEqBool hRel

end RuleProofs

theorem cmd_step_str_in_re_consume_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_consume args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_consume args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_consume args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_consume args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp b =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply inApp r =>
                                  cases inApp with
                                  | Apply inOp str =>
                                      cases inOp with
                                      | UOp inOpName =>
                                          cases inOpName with
                                          | str_in_re =>
                                              have hProps :=
                                                RuleProofs.str_in_re_consume_valid_properties
                                                  M hM str r b (by
                                                    simpa using hA1Trans) (by
                                                    change
                                                      __eo_prog_str_in_re_consume
                                                        (Term.Apply
                                                          (Term.Apply (Term.UOp UserOp.eq)
                                                            (Term.Apply
                                                              (Term.Apply
                                                                (Term.UOp UserOp.str_in_re) str) r)) b) ≠
                                                        Term.Stuck at hProg
                                                    exact hProg)
                                              change StepRuleProperties M []
                                                (__eo_prog_str_in_re_consume
                                                  (Term.Apply
                                                    (Term.Apply (Term.UOp UserOp.eq)
                                                      (Term.Apply
                                                        (Term.Apply
                                                          (Term.UOp UserOp.str_in_re) str) r)) b))
                                              simpa [premiseTermList] using hProps
                                          | _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
