import Cpc.Proofs.RuleSupport.CoreSupport
import Cpc.Proofs.RuleSupport.ReConcatStarSupport
import Cpc.Proofs.RuleSupport.RegexSupport
import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

def NativeIncludes (sup sub : native_RegLan) : Prop :=
  ∀ str : native_String,
    native_string_valid str = true ->
      native_str_in_re str sub = true ->
        native_str_in_re str sup = true

theorem native_str_in_re_re_none (str : native_String) :
    native_str_in_re str native_re_none = false := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, native_re_none, nativeListInRe] using
      nativeListInRe_empty str
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_union
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, native_re_union, nativeListInRe] using
      nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem smt_value_rel_re_inter_self_comp_all_none (r : native_RegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter r (native_re_inter (native_re_comp r) native_re_all)))
      (SmtValue.RegLan native_re_none) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_inter r (native_re_inter (native_re_comp r) native_re_all))
        native_re_none) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
    native_str_in_re_re_comp, native_str_in_re_re_all _ hValid,
    native_str_in_re_re_none]
  cases hMem : native_str_in_re str r <;> simp [hValid]

theorem smt_value_rel_re_inter_subset_comp_all_none
    (r1 r2 : native_RegLan)
    (hSub : NativeIncludes r2 r1) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter r1 (native_re_inter (native_re_comp r2) native_re_all)))
      (SmtValue.RegLan native_re_none) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_inter r1 (native_re_inter (native_re_comp r2) native_re_all))
        native_re_none) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
    native_str_in_re_re_comp, native_str_in_re_re_all _ hValid,
    native_str_in_re_re_none]
  cases hMem1 : native_str_in_re str r1
  · simp [hValid]
  · have hMem2 : native_str_in_re str r2 = true :=
      hSub str hValid hMem1
    simp [hValid, hMem2]

theorem smt_value_rel_re_union_self_comp_none_all (r : native_RegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_union r (native_re_union (native_re_comp r) native_re_none)))
      (SmtValue.RegLan native_re_all) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_union r (native_re_union (native_re_comp r) native_re_none))
        native_re_all) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    native_str_in_re_re_comp, native_str_in_re_re_none,
    native_str_in_re_re_all _ hValid]
  cases hMem : native_str_in_re str r <;> simp [hValid]

theorem smt_value_rel_re_union_subset_comp_none_all
    (r1 r2 : native_RegLan)
    (hSub : NativeIncludes r1 r2) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_union r1 (native_re_union (native_re_comp r2) native_re_none)))
      (SmtValue.RegLan native_re_all) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_union r1 (native_re_union (native_re_comp r2) native_re_none))
        native_re_all) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    native_str_in_re_re_comp, native_str_in_re_re_none,
    native_str_in_re_re_all _ hValid]
  cases hMem2 : native_str_in_re str r2
  · simp [hValid]
  · have hMem1 : native_str_in_re str r1 = true :=
      hSub str hValid hMem2
    simp [hValid, hMem1]

theorem smtx_model_eval_re_mult_allchar :
    __smtx_model_eval_re_mult (SmtValue.RegLan native_re_allchar) =
      SmtValue.RegLan native_re_all := by
  simp [__smtx_model_eval_re_mult, native_re_mult, native_re_allchar,
    native_re_all, native_re_mk_star]

theorem smt_model_eval_reglan_of_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.RegLan) :
    ∃ r : native_RegLan,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact reglan_value_canonical hEvalTy

theorem re_inclusion_side_native_includes
    (M : SmtModel) (hM : model_total_typed M)
    (sup sub flatSup flatSub side : Term)
    (rvSup rvSub : native_RegLan)
    (hSupTy : __smtx_typeof (__eo_to_smt sup) = SmtType.RegLan)
    (hSubTy : __smtx_typeof (__eo_to_smt sub) = SmtType.RegLan)
    (hSupEval : __smtx_model_eval M (__eo_to_smt sup) = SmtValue.RegLan rvSup)
    (hSubEval : __smtx_model_eval M (__eo_to_smt sub) = SmtValue.RegLan rvSub)
    (hFlatSup :
      flatSup = __re_flatten (Term.Boolean false) (Term.Boolean true) sup)
    (hFlatSub :
      flatSub = __re_flatten (Term.Boolean false) (Term.Boolean true) sub)
    (hSide :
      side =
        __eo_ite (__eo_eq flatSup flatSub) (Term.Boolean true)
          (__str_re_includes_rec flatSup flatSub))
    (hSideTrue : side = Term.Boolean true) :
    NativeIncludes rvSup rvSub := by
  sorry

end RuleProofs
