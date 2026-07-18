module

public import Cpc.Proofs.RuleSupport.Cong.TupleBvSeq
import all Cpc.Proofs.RuleSupport.Cong.TupleBvSeq

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

attribute [local simp] native_streq native_and native_ite

theorem congTrueSpine_re_exp_eq_true
    (M : SmtModel) (hM : model_total_typed M) (n x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp1 UserOp1.re_exp n) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp1 UserOp1.re_exp n) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp1 UserOp1.re_exp n) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed_unary_uop_inv M UserOp1.re_exp n x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let I : SmtTerm := __eo_to_smt n
    let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp1 UserOp1.re_exp n) x)
        (Term.Apply (Term.UOp1 UserOp1.re_exp n) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_exp I X) ≠ SmtType.None := by
      simpa [I, X] using hTypes.2
    rcases re_exp_index_arg_of_non_none I X hLeftNN with
      ⟨k, hI, hXTy⟩
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.re_exp I X))
        (__smtx_model_eval M (SmtTerm.re_exp I Y))
    rw [__smtx_model_eval.eq_107, __smtx_model_eval.eq_107, hI,
      __smtx_model_eval.eq_2, hXEval, hYEval]
    exact smt_value_rel_re_exp_reglan_congr k hExt

theorem congTrueSpine_re_loop_eq_true
    (M : SmtModel) (hM : model_total_typed M) (lo hi x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_indexed2_unary_uop_inv M UserOp2.re_loop lo hi x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let L : SmtTerm := __eo_to_smt lo
    let H : SmtTerm := __eo_to_smt hi
    let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x)
        (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) y)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.re_loop L H X) ≠ SmtType.None := by
      simpa [L, H, X] using hTypes.2
    rcases re_loop_index_arg_of_non_none L H X hLeftNN with
      ⟨loN, hiN, hL, hH, hXTy⟩
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hYTy : __smtx_typeof Y = SmtType.RegLan := by
      rw [← hArgTy]
      exact hXTy
    rcases smt_eval_reglan_of_smt_type_reglan M hM X hXTy with
      ⟨rx, hXEval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y hYTy with
      ⟨ry, hYEval⟩
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X) (__smtx_model_eval M Y) :=
      smt_value_rel_of_eq_true_or_same M x y hArg
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hXEval, hYEval] at hRel
      simpa [__smtx_model_eval_eq] using hRel
    change
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.re_loop L H X))
        (__smtx_model_eval M (SmtTerm.re_loop L H Y))
    rw [__smtx_model_eval.eq_115, __smtx_model_eval.eq_115, hL, hH,
      __smtx_model_eval.eq_2, __smtx_model_eval.eq_2, hXEval, hYEval]
    exact smt_value_rel_re_loop_reglan_congr loN hiN hExt

private theorem congTrueSpine_reglan_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (nativeOp : native_RegLan -> native_RegLan -> native_RegLan)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          match __smtx_model_eval M a, __smtx_model_eval M b with
          | SmtValue.RegLan r₁, SmtValue.RegLan r₂ =>
              SmtValue.RegLan (nativeOp r₁ r₂)
          | _, _ => SmtValue.NotValue)
    (hExtOp :
      ∀ r₁ r₁' r₂ r₂',
        (∀ str, native_string_valid str = true ->
          native_str_in_re str r₁ = native_str_in_re str r₁') ->
        (∀ str, native_string_valid str = true ->
          native_str_in_re str r₂ = native_str_in_re str r₂') ->
        ∀ str,
          native_string_valid str = true ->
          native_str_in_re str (nativeOp r₁ r₂) =
            native_str_in_re str (nativeOp r₁' r₂'))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)
        hEqBool
    have hLeftNN : __smtx_typeof (smtOp X₁ X₂) ≠ SmtType.None := by
      rw [← hToSmt x₁ x₂]
      exact hTypes.2
    have hTerm : term_has_non_none_type (smtOp X₁ X₂) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs :=
      reglan_binop_args_of_non_none (op := smtOp) (hTy X₁ X₂) hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.RegLan := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₁ hArgs.1 with
      ⟨rx₁, hX₁Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2 with
      ⟨rx₂, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₁ hY₁Ty with
      ⟨ry₁, hY₁Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry₂, hY₂Eval⟩
    have hRel₁ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₁) (__smtx_model_eval M Y₁) :=
      smt_value_rel_of_eq_true_or_same M x₁ y₁ hArg₁
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt₁ : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx₁ = native_str_in_re str ry₁ := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₁
      rw [hX₁Eval, hY₁Eval] at hRel₁
      simpa [__smtx_model_eval_eq] using hRel₁
    have hExt₂ : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx₂ = native_str_in_re str ry₂ := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    have hExt : ∀ str,
        native_string_valid str = true ->
        native_str_in_re str (nativeOp rx₁ rx₂) =
          native_str_in_re str (nativeOp ry₁ ry₂) :=
      hExtOp rx₁ ry₁ rx₂ ry₂ hExt₁ hExt₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (smtOp X₁ X₂))
        (__smtx_model_eval M (smtOp Y₁ Y₂)) =
          SmtValue.Boolean true
    rw [hEval, hEval, hX₁Eval, hX₂Eval, hY₁Eval, hY₂Eval]
    simp [__smtx_model_eval_eq]
    intro s hs
    exact hExt s hs

theorem congTrueSpine_re_concat_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
        rhs) true :=
  congTrueSpine_reglan_binop_eq_true M hM UserOp.re_concat
    SmtTerm.re_concat native_re_concat
    (by intro a b; rfl)
    (by intro a b; exact typeof_re_concat_eq a b)
    (by intro a b; rw [__smtx_model_eval.eq_111]; rfl)
    (by
      intro r₁ r₁' r₂ r₂' h₁ h₂ str _hValid
      exact native_str_in_re_re_concat_congr str r₁ r₁' r₂ r₂' h₁ h₂)
    x₁ x₂ rhs

theorem congTypeSpine_re_concat_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.re_concat
    SmtTerm.re_concat
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_re_concat_eq, typeof_re_concat_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_re_union_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
        rhs) true :=
  congTrueSpine_reglan_binop_eq_true M hM UserOp.re_union
    SmtTerm.re_union native_re_union
    (by intro a b; rfl)
    (by intro a b; exact typeof_re_union_eq a b)
    (by intro a b; rw [__smtx_model_eval.eq_113]; rfl)
    (by
      intro r₁ r₁' r₂ r₂' h₁ h₂ str hValid
      rw [native_str_in_re_re_union, native_str_in_re_re_union,
        h₁ str hValid, h₂ str hValid])
    x₁ x₂ rhs

theorem congTypeSpine_re_union_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.re_union
    SmtTerm.re_union
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_re_union_eq, typeof_re_union_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_re_inter_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
        rhs) true :=
  congTrueSpine_reglan_binop_eq_true M hM UserOp.re_inter
    SmtTerm.re_inter native_re_inter
    (by intro a b; rfl)
    (by intro a b; exact typeof_re_inter_eq a b)
    (by intro a b; rw [__smtx_model_eval.eq_112]; rfl)
    (by
      intro r₁ r₁' r₂ r₂' h₁ h₂ str hValid
      rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
        h₁ str hValid, h₂ str hValid])
    x₁ x₂ rhs

theorem congTypeSpine_re_inter_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.re_inter
    SmtTerm.re_inter
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_re_inter_eq, typeof_re_inter_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_re_diff_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
      rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
        rhs) true :=
  congTrueSpine_reglan_binop_eq_true M hM UserOp.re_diff
    SmtTerm.re_diff native_re_diff
    (by intro a b; rfl)
    (by intro a b; exact typeof_re_diff_eq a b)
    (by intro a b; rw [__smtx_model_eval.eq_114]; rfl)
    (by
      intro r₁ r₁' r₂ r₂' h₁ h₂ str hValid
      rw [native_str_in_re_re_diff, native_str_in_re_re_diff,
        h₁ str hValid, h₂ str hValid])
    x₁ x₂ rhs

theorem congTypeSpine_re_diff_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.re_diff
    SmtTerm.re_diff
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_re_diff_eq, typeof_re_diff_eq, ha, hb])
    x₁ x₂ rhs

private theorem set_is_empty_arg_non_reg_of_non_none (x : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_empty) x)) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof (__eo_to_smt x) = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  let T :=
    __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (SmtTerm.set_empty T)) ≠
        SmtType.None := by
    change
      __smtx_typeof
          (SmtTerm.eq (__eo_to_smt x)
            (SmtTerm.set_empty T)) ≠
        SmtType.None at hNN
    simpa [T, typeof_eq_eq] using hNN
  have hEqArgs := cong_smtx_typeof_eq_non_none hEqNN
  refine ⟨__smtx_typeof (__eo_to_smt x), rfl, hEqArgs.2, ?_⟩
  intro hReg
  have hEmptyNN :
      __smtx_typeof (SmtTerm.set_empty T) ≠ SmtType.None := by
    rw [← hEqArgs.1]
    exact hEqArgs.2
  have hEmptyTy :
      __smtx_typeof (SmtTerm.set_empty T) = SmtType.Set T := by
    rw [smtx_typeof_set_empty_term_eq]
    exact smtx_typeof_guard_wf_of_non_none
      (SmtType.Set T) (SmtType.Set T) (by
        simpa [smtx_typeof_set_empty_term_eq] using hEmptyNN)
  have hSetReg : SmtType.Set T = SmtType.RegLan := by
    rw [← hEmptyTy, ← hEqArgs.1]
    exact hReg
  cases hSetReg

private theorem set_choose_arg_non_reg_of_non_none (x : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof (__eo_to_smt x) = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  let T :=
    __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))
  have hMapNN :
      term_has_non_none_type
        (SmtTerm.map_diff (__eo_to_smt x) (SmtTerm.set_empty T)) := by
    unfold term_has_non_none_type
    change
      __smtx_typeof
          (SmtTerm.map_diff (__eo_to_smt x) (SmtTerm.set_empty T)) ≠
        SmtType.None
    simpa [T] using hNN
  rcases map_diff_args_of_non_none hMapNN with hMap | hSet
  · rcases hMap with ⟨A, B, hX, _hEmpty, _hTy⟩
    exact ⟨SmtType.Map A B, hX, by simp, by simp⟩
  · rcases hSet with ⟨A, hX, _hEmpty, _hTy⟩
    exact ⟨SmtType.Set A, hX, by simp, by simp⟩

private theorem set_is_singleton_arg_non_reg_of_non_none (x : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_singleton) x)) ≠
      SmtType.None ->
      ∃ A,
        __smtx_typeof (__eo_to_smt x) = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  let T :=
    __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt x))
  let diff := SmtTerm.map_diff (__eo_to_smt x) (SmtTerm.set_empty T)
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (SmtTerm.set_singleton diff)) ≠
        SmtType.None := by
    change
      __smtx_typeof
          (SmtTerm.eq (__eo_to_smt x)
            (SmtTerm.set_singleton diff)) ≠
        SmtType.None at hNN
    simpa [T, diff, typeof_eq_eq] using hNN
  have hEqArgs := cong_smtx_typeof_eq_non_none hEqNN
  refine ⟨__smtx_typeof (__eo_to_smt x), rfl, hEqArgs.2, ?_⟩
  intro hReg
  have hSingletonNN :
      __smtx_typeof (SmtTerm.set_singleton diff) ≠ SmtType.None := by
    rw [← hEqArgs.1]
    exact hEqArgs.2
  have hSingletonTy :
      __smtx_typeof (SmtTerm.set_singleton diff) =
        SmtType.Set (__smtx_typeof diff) := by
    rw [smtx_typeof_set_singleton_term_eq]
    exact smtx_typeof_guard_wf_of_non_none
      (SmtType.Set (__smtx_typeof diff))
      (SmtType.Set (__smtx_typeof diff)) (by
        simpa [smtx_typeof_set_singleton_term_eq] using hSingletonNN)
  have hSetReg : SmtType.Set (__smtx_typeof diff) = SmtType.RegLan := by
    rw [← hSingletonTy, ← hEqArgs.1]
    exact hReg
  cases hSetReg

theorem congTrueSpine_set_choose_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.set_choose) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.set_choose) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.set_choose) x) rhs) true :=
  congTrueSpine_eotype_non_reg_unop_eq_true_of_eval_congr
    M hM UserOp.set_choose
    set_choose_arg_non_reg_of_non_none
    (by
      intro a b hSmt hEo hEval
      have hChooseTy :
          __eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) a) =
            __eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) b) := by
        change __eo_typeof_set_choose (__eo_typeof a) =
          __eo_typeof_set_choose (__eo_typeof b)
        rw [hEo]
      let T₁ :=
        __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt a))
      let T₂ :=
        __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt b))
      have hT : T₁ = T₂ := by
        dsimp [T₁, T₂]
        rw [hSmt]
      change
        __smtx_model_eval M
            (SmtTerm.map_diff (__eo_to_smt a) (SmtTerm.set_empty T₁)) =
          __smtx_model_eval M
            (SmtTerm.map_diff (__eo_to_smt b) (SmtTerm.set_empty T₂))
      rw [hT, smtx_model_eval_map_diff_term_eq,
        smtx_model_eval_map_diff_term_eq,
        hEval])
    x rhs

theorem congTrueSpine_set_is_singleton_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.set_is_singleton) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.set_is_singleton) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.set_is_singleton) x) rhs) true :=
  congTrueSpine_eotype_non_reg_unop_eq_true_of_eval_congr
    M hM UserOp.set_is_singleton
    set_is_singleton_arg_non_reg_of_non_none
    (by
      intro a b hSmt hEo hEval
      have hChooseTy :
          __eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) a) =
            __eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) b) := by
        change __eo_typeof_set_choose (__eo_typeof a) =
          __eo_typeof_set_choose (__eo_typeof b)
        rw [hEo]
      let T₁ :=
        __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt a))
      let T₂ :=
        __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt b))
      have hT : T₁ = T₂ := by
        dsimp [T₁, T₂]
        rw [hSmt]
      change
        __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt a)
              (SmtTerm.set_singleton
                (SmtTerm.map_diff (__eo_to_smt a)
                  (SmtTerm.set_empty T₁)))) =
          __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt b)
              (SmtTerm.set_singleton
                (SmtTerm.map_diff (__eo_to_smt b)
                  (SmtTerm.set_empty T₂))))
      rw [hT, smtx_model_eval_eq_term_eq, smtx_model_eval_eq_term_eq,
        smtx_model_eval_set_singleton_term_eq,
        smtx_model_eval_set_singleton_term_eq,
        smtx_model_eval_map_diff_term_eq,
        smtx_model_eval_map_diff_term_eq, hEval])
    x rhs

theorem congTrueSpine_set_is_empty_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs) true :=
  congTrueSpine_eotype_non_reg_unop_eq_true_of_eval_congr
    M hM UserOp.set_is_empty
    set_is_empty_arg_non_reg_of_non_none
    (by
      intro a b hSmt hEo hEval
      let T₁ :=
        __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt a))
      let T₂ :=
        __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt b))
      have hT : T₁ = T₂ := by
        dsimp [T₁, T₂]
        rw [hSmt]
      change
        __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt a) (SmtTerm.set_empty T₁)) =
          __smtx_model_eval M
            (SmtTerm.eq (__eo_to_smt b) (SmtTerm.set_empty T₂))
      rw [hT, smtx_model_eval_eq_term_eq, smtx_model_eval_eq_term_eq, hEval])
    x rhs

theorem congTypeSpine_set_is_empty_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.set_is_empty) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.set_is_empty) x) rhs) := by
  intro hTrans hSpine
  refine congTypeSpine_typecongr_eotype_unop_eq_has_bool_type
    UserOp.set_is_empty ?_ x rhs hTrans hSpine
  intro a b hSmt hEo
  let T₁ :=
    __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt a))
  let T₂ :=
    __eo_to_smt_set_elem_type (__smtx_typeof (__eo_to_smt b))
  have hT : T₁ = T₂ := by
    dsimp [T₁, T₂]
    rw [hSmt]
  change
    __smtx_typeof
        (SmtTerm.eq (__eo_to_smt a) (SmtTerm.set_empty T₁)) =
      __smtx_typeof
        (SmtTerm.eq (__eo_to_smt b) (SmtTerm.set_empty T₂))
  rw [hT, typeof_eq_eq, typeof_eq_eq, hSmt]

theorem set_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (a b : SmtTerm) :
    __smtx_typeof (op a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases set_binop_args_of_non_none (op := op) (hTy a b)
      hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Set T, SmtType.Set T, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem set_binop_ret_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (a b : SmtTerm) :
    __smtx_typeof (op a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases set_binop_ret_args_of_non_none (op := op) (T := R)
      (hTy a b) hTerm with
    ⟨T, hA, hB⟩
  exact ⟨SmtType.Set T, SmtType.Set T, hA, hB,
    by simp, by simp, by simp, by simp⟩

theorem congTrueSpine_set_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_sets_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (set_binop_args_non_reg_of_non_none smtOp hTy)
    hEval
    x₁ x₂ rhs

theorem congTypeSpine_set_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_sets_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_set_binop_ret_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType) (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM eoOp smtOp evalOp
    hToSmt
    (set_binop_ret_args_non_reg_of_non_none smtOp R hTy)
    hEval
    x₁ x₂ rhs

theorem congTypeSpine_set_binop_ret_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTy :
      ∀ a b,
        __smtx_typeof (smtOp a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type eoOp smtOp
    hToSmt
    (by
      intro a b a' b' ha hb
      rw [hTy a b, hTy a' b', ha, hb])
    x₁ x₂ rhs

private def arrayDeqDiffTerm (a b : SmtTerm) : SmtTerm :=
  __eo_to_smt_array_deq_diff a (__smtx_typeof a) b (__smtx_typeof b)

private def arrayDeqDiffType : SmtType -> SmtType -> SmtType
  | SmtType.Map aT aU, SmtType.Map bT bU =>
      native_ite (native_and (native_Teq aT bT) (native_Teq aU bU))
        aT SmtType.None
  | _, _ => SmtType.None

private theorem typeof_arrayDeqDiffTerm_eq (a b : SmtTerm) :
    __smtx_typeof (arrayDeqDiffTerm a b) =
      arrayDeqDiffType (__smtx_typeof a) (__smtx_typeof b) := by
  unfold arrayDeqDiffTerm
  cases hA : __smtx_typeof a <;> cases hB : __smtx_typeof b <;>
    simp [__eo_to_smt_array_deq_diff, typeof_map_diff_eq,
      __smtx_typeof_map_diff, arrayDeqDiffType, hA, hB]

private theorem array_deq_diff_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (arrayDeqDiffTerm a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  refine ⟨__smtx_typeof a, __smtx_typeof b, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    unfold arrayDeqDiffTerm at hNN
    rw [h] at hNN
    simp [__eo_to_smt_array_deq_diff, TranslationProofs.smtx_typeof_none]
      at hNN
  · intro h
    unfold arrayDeqDiffTerm at hNN
    rw [h] at hNN
    cases __smtx_typeof a <;>
      simp [__eo_to_smt_array_deq_diff, TranslationProofs.smtx_typeof_none]
        at hNN
  · intro h
    unfold arrayDeqDiffTerm at hNN
    rw [h] at hNN
    simp [__eo_to_smt_array_deq_diff, TranslationProofs.smtx_typeof_none]
      at hNN
  · intro h
    unfold arrayDeqDiffTerm at hNN
    rw [h] at hNN
    cases __smtx_typeof a <;>
      simp [__eo_to_smt_array_deq_diff, TranslationProofs.smtx_typeof_none]
        at hNN

theorem congTypeSpine_array_deq_diff_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term._at_array_deq_diff x₁ x₂) ->
    CongTypeSpine (Term._at_array_deq_diff x₁ x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_array_deq_diff x₁ x₂) rhs) := by
  exact
    congTypeSpine_typecongr_binop_eq_has_bool_type
      UserOp._at_array_deq_diff arrayDeqDiffTerm
      (by intro a b; rfl)
      (by
        intro a b a' b' ha hb
        rw [typeof_arrayDeqDiffTerm_eq, typeof_arrayDeqDiffTerm_eq,
          ha, hb])
      x₁ x₂ rhs

theorem congTrueSpine_array_deq_diff_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_array_deq_diff x₁ x₂) rhs) ->
    CongTrueSpine M (Term._at_array_deq_diff x₁ x₂) rhs ->
    eo_interprets M (mkEq (Term._at_array_deq_diff x₁ x₂) rhs) true := by
  exact
    congTrueSpine_non_reg_binop_eq_true_of_eval_congr M hM
      UserOp._at_array_deq_diff arrayDeqDiffTerm
      (by intro a b; rfl)
      array_deq_diff_args_non_reg_of_non_none
      (by
        intro a b a' b' ha hb hea heb
        unfold arrayDeqDiffTerm
        cases hA : __smtx_typeof a <;> cases hB : __smtx_typeof b <;>
          rw [← ha, ← hb] <;>
          simp [__eo_to_smt_array_deq_diff, smtx_model_eval_map_diff_term_eq,
            hA, hB, hea, heb] at ha hb hea heb ⊢)
      x₁ x₂ rhs

private def setsDeqDiffTerm (a b : SmtTerm) : SmtTerm :=
  __eo_to_smt_sets_deq_diff a (__smtx_typeof a) b (__smtx_typeof b)

private def setsDeqDiffType : SmtType -> SmtType -> SmtType
  | SmtType.Set aT, SmtType.Set bT =>
      native_ite (native_Teq aT bT) aT SmtType.None
  | _, _ => SmtType.None

private theorem typeof_setsDeqDiffTerm_eq (a b : SmtTerm) :
    __smtx_typeof (setsDeqDiffTerm a b) =
      setsDeqDiffType (__smtx_typeof a) (__smtx_typeof b) := by
  unfold setsDeqDiffTerm
  cases hA : __smtx_typeof a <;> cases hB : __smtx_typeof b <;>
    simp [__eo_to_smt_sets_deq_diff, typeof_map_diff_eq,
      __smtx_typeof_map_diff, setsDeqDiffType, hA, hB]

private theorem sets_deq_diff_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (setsDeqDiffTerm a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  refine ⟨__smtx_typeof a, __smtx_typeof b, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    unfold setsDeqDiffTerm at hNN
    rw [h] at hNN
    simp [__eo_to_smt_sets_deq_diff, TranslationProofs.smtx_typeof_none]
      at hNN
  · intro h
    unfold setsDeqDiffTerm at hNN
    rw [h] at hNN
    cases __smtx_typeof a <;>
      simp [__eo_to_smt_sets_deq_diff, TranslationProofs.smtx_typeof_none]
        at hNN
  · intro h
    unfold setsDeqDiffTerm at hNN
    rw [h] at hNN
    simp [__eo_to_smt_sets_deq_diff, TranslationProofs.smtx_typeof_none]
      at hNN
  · intro h
    unfold setsDeqDiffTerm at hNN
    rw [h] at hNN
    cases __smtx_typeof a <;>
      simp [__eo_to_smt_sets_deq_diff, TranslationProofs.smtx_typeof_none]
        at hNN

theorem congTypeSpine_sets_deq_diff_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term._at_sets_deq_diff x₁ x₂) ->
    CongTypeSpine (Term._at_sets_deq_diff x₁ x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_sets_deq_diff x₁ x₂) rhs) := by
  exact
    congTypeSpine_typecongr_binop_eq_has_bool_type
      UserOp._at_sets_deq_diff setsDeqDiffTerm
      (by intro a b; rfl)
      (by
        intro a b a' b' ha hb
        rw [typeof_setsDeqDiffTerm_eq, typeof_setsDeqDiffTerm_eq, ha, hb])
      x₁ x₂ rhs

theorem congTrueSpine_sets_deq_diff_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_sets_deq_diff x₁ x₂) rhs) ->
    CongTrueSpine M (Term._at_sets_deq_diff x₁ x₂) rhs ->
    eo_interprets M (mkEq (Term._at_sets_deq_diff x₁ x₂) rhs) true := by
  exact
    congTrueSpine_non_reg_binop_eq_true_of_eval_congr M hM
      UserOp._at_sets_deq_diff setsDeqDiffTerm
      (by intro a b; rfl)
      sets_deq_diff_args_non_reg_of_non_none
      (by
        intro a b a' b' ha hb hea heb
        unfold setsDeqDiffTerm
        cases hA : __smtx_typeof a <;> cases hB : __smtx_typeof b <;>
          rw [← ha, ← hb] <;>
          simp [__eo_to_smt_sets_deq_diff, smtx_model_eval_map_diff_term_eq,
            hA, hB, hea, heb] at ha hb hea heb ⊢)
      x₁ x₂ rhs

private theorem smtx_model_eval_seq_diff_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_diff x y) =
      __smtx_model_eval_seq_diff (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem strings_deq_diff_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_diff a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  rcases seq_binop_args_of_non_none_ret (op := SmtTerm.seq_diff)
      (typeof_seq_diff_eq a b) hNN with ⟨A, ha, hb⟩
  exact ⟨SmtType.Seq A, SmtType.Seq A, ha, hb, by simp, by simp, by simp, by simp⟩

theorem congTypeSpine_strings_deq_diff_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term._at_strings_deq_diff x₁ x₂) ->
    CongTypeSpine (Term._at_strings_deq_diff x₁ x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_strings_deq_diff x₁ x₂) rhs) := by
  exact
    congTypeSpine_typecongr_binop_eq_has_bool_type
      UserOp._at_strings_deq_diff SmtTerm.seq_diff
      (by intro a b; rfl)
      (by
        intro a b a' b' ha hb
        rw [typeof_seq_diff_eq, typeof_seq_diff_eq, ha, hb])
      x₁ x₂ rhs

theorem congTrueSpine_strings_deq_diff_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_strings_deq_diff x₁ x₂) rhs) ->
    CongTrueSpine M (Term._at_strings_deq_diff x₁ x₂) rhs ->
    eo_interprets M (mkEq (Term._at_strings_deq_diff x₁ x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM
    UserOp._at_strings_deq_diff SmtTerm.seq_diff __smtx_model_eval_seq_diff
    (by intro a b; rfl)
    strings_deq_diff_args_non_reg_of_non_none
    (by intro a b; rw [smtx_model_eval_seq_diff_term_eq])
    x₁ x₂ rhs

def stringsStoiResultTerm (a b : SmtTerm) : SmtTerm :=
  SmtTerm.str_to_int (SmtTerm.str_substr a (SmtTerm.Numeral 0) b)

private def stringsStoiResultEval (a b : SmtValue) : SmtValue :=
  __smtx_model_eval_str_to_int
    (__smtx_model_eval_str_substr a (SmtValue.Numeral 0) b)

private theorem strings_stoi_result_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (stringsStoiResultTerm a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  rcases seq_char_unop_args_non_reg_of_non_none SmtTerm.str_to_int
      SmtType.Int (by intro x; exact typeof_str_to_int_eq x)
      (SmtTerm.str_substr a (SmtTerm.Numeral 0) b)
      (by simpa [stringsStoiResultTerm] using hNN) with
    ⟨A, hSubstrA, hANN, _hAReg⟩
  have hSubstrNN :
      __smtx_typeof (SmtTerm.str_substr a (SmtTerm.Numeral 0) b) ≠
        SmtType.None := by
    rw [hSubstrA]
    exact hANN
  rcases str_substr_args_non_reg_of_non_none a (SmtTerm.Numeral 0) b
      hSubstrNN with
    ⟨S, _Z, I, hA, _hZero, hB, hSNN, _hZNN, hINN, hSReg, _hZReg,
      hIReg⟩
  exact ⟨S, I, hA, hB, hSNN, hINN, hSReg, hIReg⟩

theorem congTrueSpine_strings_stoi_result_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs) true := by
  exact
    congTrueSpine_non_reg_binop_eq_true M hM
      UserOp._at_strings_stoi_result stringsStoiResultTerm
      stringsStoiResultEval
      (by intro a b; rfl)
      strings_stoi_result_args_non_reg_of_non_none
      (by
        intro a b
        rw [stringsStoiResultTerm, stringsStoiResultEval,
          __smtx_model_eval.eq_93, __smtx_model_eval.eq_79,
          __smtx_model_eval.eq_2])
      x₁ x₂ rhs

theorem congTypeSpine_strings_stoi_result_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term._at_strings_stoi_result x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term._at_strings_stoi_result x₁) x₂) rhs) := by
  exact
    congTypeSpine_typecongr_binop_eq_has_bool_type
      UserOp._at_strings_stoi_result stringsStoiResultTerm
      (by intro a b; rfl)
      (by
        intro a b a' b' ha hb
        rw [stringsStoiResultTerm, stringsStoiResultTerm,
          typeof_str_to_int_eq, typeof_str_to_int_eq,
          typeof_str_substr_eq, typeof_str_substr_eq, ha, hb])
      x₁ x₂ rhs

def stringsItosResultTerm (a b : SmtTerm) : SmtTerm :=
  SmtTerm.ite (SmtTerm.eq b (SmtTerm.Numeral 0))
    (SmtTerm.Numeral 0)
    (SmtTerm.str_to_int
      (SmtTerm.str_substr (SmtTerm.str_from_int a)
        (SmtTerm.Numeral 0) b))

private noncomputable def stringsItosResultEval (a b : SmtValue) : SmtValue :=
  __smtx_model_eval_ite
    (__smtx_model_eval_eq b (SmtValue.Numeral 0))
    (SmtValue.Numeral 0)
    (__smtx_model_eval_str_to_int
      (__smtx_model_eval_str_substr
        (__smtx_model_eval_str_from_int a) (SmtValue.Numeral 0) b))

private theorem strings_itos_result_args_non_reg_of_non_none
    (a b : SmtTerm) :
    __smtx_typeof (stringsItosResultTerm a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTermNN : term_has_non_none_type (stringsItosResultTerm a b) := by
    exact hNN
  rcases ite_args_of_non_none hTermNN with
    ⟨T, _hCondTy, _hZeroTy, hParsedTy, hTNN⟩
  have hParsedNN :
      term_has_non_none_type
        (SmtTerm.str_to_int
          (SmtTerm.str_substr (SmtTerm.str_from_int a)
            (SmtTerm.Numeral 0) b)) := by
    unfold term_has_non_none_type
    rw [hParsedTy]
    exact hTNN
  let prefixTerm :=
    SmtTerm.str_substr (SmtTerm.str_from_int a) (SmtTerm.Numeral 0) b
  have hPrefixTy :
      __smtx_typeof prefixTerm = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq prefixTerm) hParsedNN
  have hPrefixNN : term_has_non_none_type prefixTerm := by
    unfold term_has_non_none_type
    rw [hPrefixTy]
    simp
  rcases str_substr_args_of_non_none hPrefixNN with
    ⟨A, hFromIntTy, _hZeroInt, hBTy⟩
  have hFromIntNN :
      term_has_non_none_type (SmtTerm.str_from_int a) := by
    unfold term_has_non_none_type
    rw [hFromIntTy]
    simp
  have hATy : __smtx_typeof a = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
      (ret := SmtType.Seq SmtType.Char)
      (typeof_str_from_int_eq a) hFromIntNN
  exact ⟨SmtType.Int, SmtType.Int, hATy, hBTy,
    by simp, by simp, by simp, by simp⟩

theorem congTrueSpine_strings_itos_result_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs) true := by
  exact
    congTrueSpine_non_reg_binop_eq_true M hM
      UserOp._at_strings_itos_result stringsItosResultTerm
      stringsItosResultEval
      (by intro a b; rfl)
      strings_itos_result_args_non_reg_of_non_none
      (by
        intro a b
        simp only [stringsItosResultTerm, stringsItosResultEval,
          smtx_model_eval_ite_term_eq, smtx_model_eval_eq_term_eq,
          __smtx_model_eval.eq_2, __smtx_model_eval.eq_79,
          __smtx_model_eval.eq_93, __smtx_model_eval.eq_94])
      x₁ x₂ rhs

theorem congTypeSpine_strings_itos_result_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term._at_strings_itos_result x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term._at_strings_itos_result x₁) x₂) rhs) := by
  exact
    congTypeSpine_typecongr_binop_eq_has_bool_type
      UserOp._at_strings_itos_result stringsItosResultTerm
      (by intro a b; rfl)
      (by
        intro a b a' b' ha hb
        rw [stringsItosResultTerm, stringsItosResultTerm,
          typeof_ite_eq, typeof_ite_eq, typeof_eq_eq, typeof_eq_eq,
          typeof_str_to_int_eq, typeof_str_to_int_eq,
          typeof_str_substr_eq, typeof_str_substr_eq,
          typeof_str_from_int_eq, typeof_str_from_int_eq, ha, hb])
      x₁ x₂ rhs

def stringsNumOccurTerm (source pattern : SmtTerm) : SmtTerm :=
  SmtTerm.div
    (SmtTerm.neg (SmtTerm.str_len source)
      (SmtTerm.str_len
        (SmtTerm.str_replace_all source pattern
          (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
    (SmtTerm.str_len pattern)

private noncomputable def stringsNumOccurEval
    (M : SmtModel) (source pattern : SmtValue) : SmtValue :=
  smtEvalDiv M
    (__smtx_model_eval__
      (__smtx_model_eval_str_len source)
      (__smtx_model_eval_str_len
        (__smtx_model_eval_str_replace_all source pattern
          (SmtValue.Seq (SmtSeq.empty (SmtType.Seq SmtType.Char))))))
    (__smtx_model_eval_str_len pattern)

theorem strings_num_occur_args_non_reg_of_non_none
    (source pattern : SmtTerm) :
    __smtx_typeof (stringsNumOccurTerm source pattern) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof source = A ∧ __smtx_typeof pattern = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  let replacement :=
    SmtTerm.str_replace_all source pattern
      (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))
  let numerator :=
    SmtTerm.neg (SmtTerm.str_len source) (SmtTerm.str_len replacement)
  rcases int_binop_args_non_reg_of_non_none SmtTerm.div SmtType.Int
      (by intro x y; exact typeof_div_eq x y)
      numerator (SmtTerm.str_len pattern)
      (by simpa [stringsNumOccurTerm, numerator, replacement] using hNN) with
    ⟨_N, D, hNumerator, hDenominator, hNNumer, hDNN, _hNReg, _hDReg⟩
  have hPatternLenNN :
      __smtx_typeof (SmtTerm.str_len pattern) ≠ SmtType.None := by
    rw [hDenominator]
    exact hDNN
  rcases seq_unop_ret_args_non_reg_of_non_none SmtTerm.str_len SmtType.Int
      (by intro x; exact typeof_str_len_eq x) pattern hPatternLenNN with
    ⟨B, hPattern, hBNN, hBReg⟩
  have hNumeratorNN : __smtx_typeof numerator ≠ SmtType.None := by
    rw [hNumerator]
    exact hNNumer
  rcases arith_overload_binop_args_non_reg_of_non_none SmtTerm.neg
      (by intro x y; exact typeof_neg_eq x y)
      (SmtTerm.str_len source) (SmtTerm.str_len replacement)
      hNumeratorNN with
    ⟨_L, _R, hSourceLen, _hReplacementLen, hLNN, _hRNN, _hLReg, _hRReg⟩
  have hSourceLenNN :
      __smtx_typeof (SmtTerm.str_len source) ≠ SmtType.None := by
    rw [hSourceLen]
    exact hLNN
  rcases seq_unop_ret_args_non_reg_of_non_none SmtTerm.str_len SmtType.Int
      (by intro x; exact typeof_str_len_eq x) source hSourceLenNN with
    ⟨A, hSource, hANN, hAReg⟩
  exact ⟨A, B, hSource, hPattern, hANN, hBNN, hAReg, hBReg⟩

theorem congTrueSpine_strings_num_occur_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs ->
    eo_interprets M
      (mkEq (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp._at_strings_num_occur
    stringsNumOccurTerm (stringsNumOccurEval M)
    (by intro a b; rfl)
    strings_num_occur_args_non_reg_of_non_none
    (by
      intro a b
      rw [stringsNumOccurTerm, stringsNumOccurEval, __smtx_model_eval.eq_24,
        __smtx_model_eval.eq_13, smtx_eval_str_len_term_eq,
        smtx_eval_str_len_term_eq, smtx_eval_str_len_term_eq,
        __smtx_model_eval.eq_97, __smtx_model_eval.eq_76])
    x₁ x₂ rhs

theorem congTypeSpine_strings_num_occur_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x₁) x₂)
        rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type
    UserOp._at_strings_num_occur stringsNumOccurTerm
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [stringsNumOccurTerm, stringsNumOccurTerm, typeof_div_eq,
        typeof_div_eq, typeof_neg_eq, typeof_neg_eq, typeof_str_len_eq,
        typeof_str_len_eq, typeof_str_len_eq, typeof_str_len_eq,
        typeof_str_len_eq, typeof_str_len_eq, typeof_str_replace_all_eq,
        typeof_str_replace_all_eq, ha, hb])
    x₁ x₂ rhs

theorem congTrueSpine_str_replace_re_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.str_replace_re
      x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) y₁) y₂)
          y₃)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.str_replace_re X₁ X₂ X₃) ≠
        SmtType.None := by
      simpa [X₁, X₂, X₃] using hTypes.2
    have hTerm :
        term_has_non_none_type (SmtTerm.str_replace_re X₁ X₂ X₃) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs :=
      str_replace_re_args_of_non_none
        (op := SmtTerm.str_replace_re)
        (typeof_str_replace_re_eq X₁ X₂ X₃) hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ :=
      smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2.1
    have hY₃Ty : __smtx_typeof Y₃ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₃]
      exact hArgs.2.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    have hEval₃ : __smtx_model_eval M X₃ = __smtx_model_eval M Y₃ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₃ y₃
        (SmtType.Seq SmtType.Char) hArgs.2.2 hY₃Ty (by simp) (by simp)
        hArg₃
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2.1 with
      ⟨rx, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry, hY₂Eval⟩
    rcases smt_eval_seq_of_smt_type_seq M hM X₃ SmtType.Char hArgs.2.2 with
      ⟨sr, hX₃Eval⟩
    have hY₃Eval : __smtx_model_eval M Y₃ = SmtValue.Seq sr := by
      rw [← hEval₃]
      exact hX₃Eval
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_replace_re X₁ X₂ X₃))
        (__smtx_model_eval M (SmtTerm.str_replace_re Y₁ Y₂ Y₃)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_98, __smtx_model_eval.eq_98,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval, hX₃Eval, hY₃Eval]
    simp [__smtx_model_eval_str_replace_re, __smtx_model_eval_eq,
      native_veq,
      native_str_replace_re_congr (native_unpack_string sx) rx ry
        (native_unpack_string sr) hExt]

theorem congTrueSpine_str_replace_re_all_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.str_replace_re_all
      x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_replace_re_all) y₁) y₂)
          y₃)
        hEqBool
    have hLeftNN :
        __smtx_typeof (SmtTerm.str_replace_re_all X₁ X₂ X₃) ≠
          SmtType.None := by
      simpa [X₁, X₂, X₃] using hTypes.2
    have hTerm :
        term_has_non_none_type (SmtTerm.str_replace_re_all X₁ X₂ X₃) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs :=
      str_replace_re_args_of_non_none
        (op := SmtTerm.str_replace_re_all)
        (typeof_str_replace_re_all_eq X₁ X₂ X₃) hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ :=
      smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2.1
    have hY₃Ty : __smtx_typeof Y₃ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₃]
      exact hArgs.2.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    have hEval₃ : __smtx_model_eval M X₃ = __smtx_model_eval M Y₃ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₃ y₃
        (SmtType.Seq SmtType.Char) hArgs.2.2 hY₃Ty (by simp) (by simp)
        hArg₃
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2.1 with
      ⟨rx, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry, hY₂Eval⟩
    rcases smt_eval_seq_of_smt_type_seq M hM X₃ SmtType.Char hArgs.2.2 with
      ⟨sr, hX₃Eval⟩
    have hY₃Eval : __smtx_model_eval M Y₃ = SmtValue.Seq sr := by
      rw [← hEval₃]
      exact hX₃Eval
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_replace_re_all X₁ X₂ X₃))
        (__smtx_model_eval M (SmtTerm.str_replace_re_all Y₁ Y₂ Y₃)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_99, __smtx_model_eval.eq_99,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval, hX₃Eval, hY₃Eval]
    simp [__smtx_model_eval_str_replace_re_all, __smtx_model_eval_eq,
      native_veq,
      native_str_replace_re_all_congr (native_unpack_string sx) rx ry
        (native_unpack_string sr) hExt]

theorem congTrueSpine_str_indexof_re_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.str_indexof_re
      x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) y₁) y₂)
          y₃)
        hEqBool
    have hLeftNN : __smtx_typeof (SmtTerm.str_indexof_re X₁ X₂ X₃) ≠
        SmtType.None := by
      simpa [X₁, X₂, X₃] using hTypes.2
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re X₁ X₂ X₃) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs := str_indexof_re_args_of_non_none hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ :=
      smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2.1
    have hY₃Ty : __smtx_typeof Y₃ = SmtType.Int := by
      rw [← hArgTy₃]
      exact hArgs.2.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    have hEval₃ : __smtx_model_eval M X₃ = __smtx_model_eval M Y₃ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₃ y₃
        SmtType.Int hArgs.2.2 hY₃Ty (by simp) (by simp) hArg₃
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2.1 with
      ⟨rx, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry, hY₂Eval⟩
    rcases smt_eval_int_of_smt_type_int M hM X₃ hArgs.2.2 with
      ⟨i, hX₃Eval⟩
    have hY₃Eval : __smtx_model_eval M Y₃ = SmtValue.Numeral i := by
      rw [← hEval₃]
      exact hX₃Eval
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hExt : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx = native_str_in_re str ry := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_indexof_re X₁ X₂ X₃))
        (__smtx_model_eval M (SmtTerm.str_indexof_re Y₁ Y₂ Y₃)) =
          SmtValue.Boolean true
    rw [__smtx_model_eval.eq_100, __smtx_model_eval.eq_100,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval, hX₃Eval, hY₃Eval]
    simp [__smtx_model_eval_str_indexof_re, __smtx_model_eval_eq,
      native_veq,
      native_str_indexof_re_congr (native_unpack_string sx) rx ry i hExt]

theorem congTrueSpine_str_indexof_re_split_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x₁) x₂)
          x₃) rhs) ->
    CongTrueSpine M
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x₁) x₂)
        x₃) rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x₁) x₂)
          x₃) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M UserOp.str_indexof_re_split
      x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let X₁ : SmtTerm := __eo_to_smt x₁
    let X₂ : SmtTerm := __eo_to_smt x₂
    let X₃ : SmtTerm := __eo_to_smt x₃
    let Y₁ : SmtTerm := __eo_to_smt y₁
    let Y₂ : SmtTerm := __eo_to_smt y₂
    let Y₃ : SmtTerm := __eo_to_smt y₃
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x₁) x₂)
          x₃)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_indexof_re_split) y₁) y₂)
          y₃)
        hEqBool
    have hLeftNN :
        __smtx_typeof (SmtTerm.str_indexof_re_split X₁ X₂ X₃) ≠
          SmtType.None := by
      simpa [X₁, X₂, X₃] using hTypes.2
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re_split X₁ X₂ X₃) := by
      unfold term_has_non_none_type
      exact hLeftNN
    have hArgs := str_indexof_re_split_args_of_non_none hTerm
    have hArgTy₁ : __smtx_typeof X₁ = __smtx_typeof Y₁ :=
      smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁
    have hArgTy₂ : __smtx_typeof X₂ = __smtx_typeof Y₂ :=
      smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂
    have hArgTy₃ : __smtx_typeof X₃ = __smtx_typeof Y₃ :=
      smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃
    have hY₁Ty : __smtx_typeof Y₁ = SmtType.Seq SmtType.Char := by
      rw [← hArgTy₁]
      exact hArgs.1
    have hY₂Ty : __smtx_typeof Y₂ = SmtType.RegLan := by
      rw [← hArgTy₂]
      exact hArgs.2.1
    have hY₃Ty : __smtx_typeof Y₃ = SmtType.RegLan := by
      rw [← hArgTy₃]
      exact hArgs.2.2
    have hEval₁ : __smtx_model_eval M X₁ = __smtx_model_eval M Y₁ :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        (SmtType.Seq SmtType.Char) hArgs.1 hY₁Ty (by simp) (by simp)
        hArg₁
    rcases smt_eval_seq_of_smt_type_seq M hM X₁ SmtType.Char hArgs.1 with
      ⟨sx, hX₁Eval⟩
    have hY₁Eval : __smtx_model_eval M Y₁ = SmtValue.Seq sx := by
      rw [← hEval₁]
      exact hX₁Eval
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₂ hArgs.2.1 with
      ⟨rx₁, hX₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₂ hY₂Ty with
      ⟨ry₁, hY₂Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM X₃ hArgs.2.2 with
      ⟨rx₂, hX₃Eval⟩
    rcases smt_eval_reglan_of_smt_type_reglan M hM Y₃ hY₃Ty with
      ⟨ry₂, hY₃Eval⟩
    have hRel₂ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₂) (__smtx_model_eval M Y₂) :=
      smt_value_rel_of_eq_true_or_same M x₂ y₂ hArg₂
    have hRel₃ :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M X₃) (__smtx_model_eval M Y₃) :=
      smt_value_rel_of_eq_true_or_same M x₃ y₃ hArg₃
    have hExt₂ : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx₁ = native_str_in_re str ry₁ := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₂
      rw [hX₂Eval, hY₂Eval] at hRel₂
      simpa [__smtx_model_eval_eq] using hRel₂
    have hExt₃ : ∀ str,
        native_string_valid str = true ->
          native_str_in_re str rx₂ = native_str_in_re str ry₂ := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel₃
      rw [hX₃Eval, hY₃Eval] at hRel₃
      simpa [__smtx_model_eval_eq] using hRel₃
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.str_indexof_re_split X₁ X₂ X₃))
        (__smtx_model_eval M (SmtTerm.str_indexof_re_split Y₁ Y₂ Y₃)) =
          SmtValue.Boolean true
    rw [smtx_model_eval_str_indexof_re_split_term_eq,
      smtx_model_eval_str_indexof_re_split_term_eq,
      hX₁Eval, hY₁Eval, hX₂Eval, hY₂Eval, hX₃Eval, hY₃Eval]
    simp [__smtx_model_eval_str_indexof_re_split, __smtx_model_eval_eq,
      native_veq,
      native_str_indexof_re_split_congr (native_unpack_string sx)
        rx₁ ry₁ rx₂ ry₂ hExt₂ hExt₃]

private def stringsStoiNonDigitRegex : SmtTerm :=
  SmtTerm.re_inter SmtTerm.re_allchar
    (SmtTerm.re_comp
      (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
        (SmtTerm.String (native_string_lit "9"))))

def stringsStoiNonDigitTerm (a : SmtTerm) : SmtTerm :=
  SmtTerm.str_indexof_re a stringsStoiNonDigitRegex (SmtTerm.Numeral 0)

private noncomputable def stringsStoiNonDigitEval (a : SmtValue) : SmtValue :=
  __smtx_model_eval_str_indexof_re a
    (__smtx_model_eval_re_inter
      (SmtValue.RegLan native_re_allchar)
      (__smtx_model_eval_re_comp
        (__smtx_model_eval_re_range
          (SmtValue.Seq (native_pack_string (native_string_lit "0")))
          (SmtValue.Seq (native_pack_string (native_string_lit "9"))))))
    (SmtValue.Numeral 0)

private theorem strings_stoi_non_digit_arg_non_reg_of_non_none
    (a : SmtTerm) :
    __smtx_typeof (stringsStoiNonDigitTerm a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (stringsStoiNonDigitTerm a) := by
    unfold term_has_non_none_type
    exact hNN
  have hArgs := str_indexof_re_args_of_non_none hTerm
  exact ⟨SmtType.Seq SmtType.Char, hArgs.1, by simp, by simp⟩

theorem congTrueSpine_strings_stoi_non_digit_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_strings_stoi_non_digit x)
        rhs) ->
    CongTrueSpine M
      (Term._at_strings_stoi_non_digit x) rhs ->
    eo_interprets M
      (mkEq (Term._at_strings_stoi_non_digit x)
        rhs) true := by
  exact
    congTrueSpine_non_reg_unop_eq_true M hM
      UserOp._at_strings_stoi_non_digit stringsStoiNonDigitTerm
      stringsStoiNonDigitEval
      (by intro a; rfl)
      strings_stoi_non_digit_arg_non_reg_of_non_none
      (by
        intro a
        rw [stringsStoiNonDigitTerm, stringsStoiNonDigitEval,
          stringsStoiNonDigitRegex, __smtx_model_eval.eq_100,
          __smtx_model_eval.eq_112, __smtx_model_eval.eq_109,
          __smtx_model_eval.eq_110,
          __smtx_model_eval.eq_4, __smtx_model_eval.eq_4,
          __smtx_model_eval.eq_2]
        rfl)
      x rhs

theorem congTypeSpine_strings_stoi_non_digit_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term._at_strings_stoi_non_digit x) ->
    CongTypeSpine
      (Term._at_strings_stoi_non_digit x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term._at_strings_stoi_non_digit x)
        rhs) := by
  exact
    congTypeSpine_typecongr_unop_eq_has_bool_type
      UserOp._at_strings_stoi_non_digit stringsStoiNonDigitTerm
      (by intro a; rfl)
      (by
        intro a b h
        rw [stringsStoiNonDigitTerm, stringsStoiNonDigitTerm,
          typeof_str_indexof_re_eq, typeof_str_indexof_re_eq, h])
      x rhs

theorem congTypeSpine_dt_sel_eq_has_bool_type
    (s : native_String) (d : Datatype) (i j : native_Nat) (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.DtSel s d i j) x) ->
    CongTypeSpine (Term.Apply (Term.DtSel s d i j) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.DtSel s d i j) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_dt_sel_inv s d i j x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) =
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) y)) := by
    change
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j))
            (__eo_to_smt x)) =
        __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j))
            (__eo_to_smt y))
    cases __eo_to_smt (Term.DtSel s d i j) <;>
      simp [__smtx_typeof, hArgTy]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.DtSel s d i j) x)
    (Term.Apply (Term.DtSel s d i j) y)
    hOpTy
    hTrans

theorem congTrueSpine_dt_sel_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i j : native_Nat) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.DtSel s d i j) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.DtSel s d i j) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.DtSel s d i j) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_dt_sel_inv M s d i j x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · let F : SmtTerm := __eo_to_smt (Term.DtSel s d i j)
    let X : SmtTerm := __eo_to_smt x
    let Y : SmtTerm := __eo_to_smt y
    have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.DtSel s d i j) x)
        (Term.Apply (Term.DtSel s d i j) y)
        hEqBool
    have hxOpNN :
        __smtx_typeof (SmtTerm.Apply F X) ≠ SmtType.None := by
      simpa [F, X] using hTypes.2
    rcases dt_sel_arg_non_reg_of_non_none s d i j X hxOpNN with
      ⟨A, hxA, hANN, hAReg⟩
    have hArgTy : __smtx_typeof X = __smtx_typeof Y :=
      smt_type_eq_of_eq_true_or_same M x y hArg
    have hyA : __smtx_typeof Y = A := by
      rw [← hArgTy]
      exact hxA
    have hEvalArg : __smtx_model_eval M X = __smtx_model_eval M Y :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.Apply F X))
        (__smtx_model_eval M (SmtTerm.Apply F Y)) =
          SmtValue.Boolean true
    change
      __smtx_model_eval_eq
        (__smtx_model_eval M
          (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) X))
        (__smtx_model_eval M
          (SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) Y)) =
          SmtValue.Boolean true
    rw [TranslationProofs.eo_to_smt_term_dt_sel]
    cases hRes : TranslationProofs.__eo_reserved_datatype_name s
    · simp [native_ite]
      rw [__smtx_model_eval, __smtx_model_eval, hEvalArg]
      exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
        (RuleProofs.smt_value_rel_refl _)
    · simp [native_ite, __smtx_model_eval]
      rw [hEvalArg]
      exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
        (RuleProofs.smt_value_rel_refl _)

/--
The remaining typing core for congruence: once the generated program has been
reduced to a spine of congruent applications, the equality between the original
spine and the rewritten spine is Boolean.
-/
theorem congTypeSpine_refl_eq_has_bool_type (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_bool_type (mkEq t t) := by
  intro hTrans
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t t rfl hTrans

theorem no_translation_of_eo_to_smt_none {t : Term} :
    __eo_to_smt t = SmtTerm.None ->
    RuleProofs.eo_has_smt_translation t ->
    False := by
  intro hNone hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans
  rw [hNone] at hTrans
  exact hTrans (by simp )

theorem no_bool_eq_left_of_eo_to_smt_none {t rhs : Term} :
    __eo_to_smt t = SmtTerm.None ->
    RuleProofs.eo_has_bool_type (mkEq t rhs) ->
    False := by
  intro hNone hBool
  unfold RuleProofs.eo_has_bool_type at hBool
  change
    __smtx_typeof (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt rhs)) =
      SmtType.Bool at hBool
  rw [hNone] at hBool
  simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
    native_ite, native_Teq] at hBool

theorem no_translation_of_smt_type_none {t : Term} :
    __smtx_typeof (__eo_to_smt t) = SmtType.None ->
    RuleProofs.eo_has_smt_translation t ->
    False := by
  intro hTy hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans
  exact hTrans hTy

theorem no_bool_eq_left_of_smt_type_none {t rhs : Term} :
    __smtx_typeof (__eo_to_smt t) = SmtType.None ->
    RuleProofs.eo_has_bool_type (mkEq t rhs) ->
    False := by
  intro hTy hBool
  unfold RuleProofs.eo_has_bool_type at hBool
  change
    __smtx_typeof (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt rhs)) =
      SmtType.Bool at hBool
  rw [typeof_eq_eq, hTy] at hBool
  simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
    at hBool

private theorem eo_to_smt_set_insert_type_congr_base :
    ∀ xs a b,
      __smtx_typeof a = __smtx_typeof b ->
        __smtx_typeof (__eo_to_smt_set_insert xs a) =
          __smtx_typeof (__eo_to_smt_set_insert xs b) := by
  intro xs a b hTy
  cases xs <;> try rfl
  case Apply f tail =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      case _at__at_TypedList_nil =>
        cases hGuard :
            native_Teq (__smtx_typeof b)
              (SmtType.Set (__eo_to_smt_type tail))
        · simp [__eo_to_smt_set_insert, hTy, hGuard, native_ite]
        · simp [__eo_to_smt_set_insert, hTy, hGuard, native_ite]
    case Apply f' head =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        case _at__at_TypedList_cons =>
        change
          __smtx_typeof
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail a)) =
            __smtx_typeof
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail b))
        rw [typeof_set_union_eq, typeof_set_union_eq,
          eo_to_smt_set_insert_type_congr_base tail a b hTy]
termination_by xs a b _ => xs

private theorem eo_to_smt_set_insert_arg_type_none_of_translation
    (xs x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.None := by
  intro hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans
  cases xs
  all_goals
    try
      exfalso
      apply hTrans
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    all_goals
      try
        exfalso
        apply hTrans
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    case UOp op =>
      cases op
      case _at__at_TypedList_nil =>
        change
          __smtx_typeof
              (SmtTerm.Apply SmtTerm.None (__eo_to_smt tail)) =
            SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply]
      all_goals
        exfalso
        apply hTrans
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    case Apply f' head =>
      cases f'
      all_goals
        try
          exfalso
          apply hTrans
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      case UOp op =>
        cases op
        case _at__at_TypedList_cons =>
          change
            __smtx_typeof
                (SmtTerm.Apply
                  (SmtTerm.Apply SmtTerm.None (__eo_to_smt head))
                  (__eo_to_smt tail)) = SmtType.None
          simp [__smtx_typeof, __smtx_typeof_apply]
        all_goals
          exfalso
          apply hTrans
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none

private theorem set_insert_arg_not_eq_bool_of_translation
    (xs ys x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ->
    RuleProofs.eo_has_bool_type (mkEq xs ys) ->
    False := by
  intro hTrans hBool
  exact
    no_bool_eq_left_of_smt_type_none
      (t := xs)
      (rhs := ys)
      (eo_to_smt_set_insert_arg_type_none_of_translation xs x hTrans)
      hBool

private theorem eo_to_smt_set_insert_type_congr_arg
    (xs x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ->
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)) =
        __smtx_typeof
              (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) y)) := by
  intro hTrans hTy
  change
    __smtx_typeof
        (__eo_to_smt_set_insert xs (__eo_to_smt x)) =
      __smtx_typeof
        (__eo_to_smt_set_insert xs (__eo_to_smt y))
  exact eo_to_smt_set_insert_type_congr_base
    xs (__eo_to_smt x) (__eo_to_smt y) hTy

theorem congTypeSpine_set_insert_eq_has_bool_type
    (xs x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv UserOp.set_insert xs x rhs hSpine with
    ⟨ys, y, hRhs, hList, hArg⟩
  subst hRhs
  cases hList with
  | inl hSame =>
      subst ys
      have hArgTy :
          __smtx_typeof (__eo_to_smt x) =
            __smtx_typeof (__eo_to_smt y) :=
        smt_type_eq_of_eq_bool_or_same x y hArg
      exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) y)
        (eo_to_smt_set_insert_type_congr_arg xs x y hTrans hArgTy)
        hTrans
  | inr hBool =>
      exact False.elim
        (set_insert_arg_not_eq_bool_of_translation xs ys x hTrans hBool)

private theorem eo_to_smt_set_insert_eval_congr_base
    (M : SmtModel) :
    ∀ xs a b,
      __smtx_typeof a = __smtx_typeof b ->
      __smtx_model_eval M a = __smtx_model_eval M b ->
        __smtx_model_eval M (__eo_to_smt_set_insert xs a) =
          __smtx_model_eval M (__eo_to_smt_set_insert xs b) := by
  intro xs a b hTy hEval
  cases xs <;> try rfl
  case Apply f tail =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      case _at__at_TypedList_nil =>
        cases hGuard :
            native_Teq (__smtx_typeof b)
              (SmtType.Set (__eo_to_smt_type tail))
        · simp [__eo_to_smt_set_insert, hTy, hGuard, native_ite]
        · simpa [__eo_to_smt_set_insert, hTy, hGuard, native_ite] using hEval
    case Apply f' head =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        case _at__at_TypedList_cons =>
        change
          __smtx_model_eval M
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail a)) =
            __smtx_model_eval M
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail b))
        rw [smtx_model_eval_set_union_term_eq, smtx_model_eval_set_union_term_eq,
          eo_to_smt_set_insert_eval_congr_base M tail a b hTy hEval]
termination_by xs a b _ _ => xs

private theorem eo_to_smt_set_insert_base_set_type_of_set_type :
    ∀ xs a A,
      __smtx_typeof (__eo_to_smt_set_insert xs a) = SmtType.Set A ->
        ∃ B, __smtx_typeof a = SmtType.Set B := by
  intro xs a A hTy
  cases xs <;> try (simp [__eo_to_smt_set_insert] at hTy)
  case Apply f tail =>
    cases f <;> try (simp [__eo_to_smt_set_insert] at hTy)
    case UOp op =>
      cases op <;> try (simp [__eo_to_smt_set_insert] at hTy)
      case _at__at_TypedList_nil =>
        cases hGuard :
            native_Teq (__smtx_typeof a)
              (SmtType.Set (__eo_to_smt_type tail))
        · simp [hGuard] at hTy
        · simp [hGuard] at hTy
          exact ⟨A, hTy⟩
    case Apply f' head =>
      cases f' <;> try (simp [__eo_to_smt_set_insert] at hTy)
      case UOp op =>
        cases op <;> try (simp [__eo_to_smt_set_insert] at hTy)
        case _at__at_TypedList_cons =>
        have hNN : term_has_non_none_type
            (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
              (__eo_to_smt_set_insert tail a)) := by
          unfold term_has_non_none_type
          rw [hTy]
          simp
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
            (typeof_set_union_eq
              (SmtTerm.set_singleton (__eo_to_smt head))
              (__eo_to_smt_set_insert tail a))
            hNN with
          ⟨B, _hHead, hTail⟩
        exact
          eo_to_smt_set_insert_base_set_type_of_set_type tail a B hTail
termination_by xs a A _ => xs

private theorem eo_to_smt_set_insert_base_set_type_of_non_none :
    ∀ xs a,
      __smtx_typeof (__eo_to_smt_set_insert xs a) ≠ SmtType.None ->
        ∃ B, __smtx_typeof a = SmtType.Set B := by
  intro xs a hNN
  cases xs
  all_goals
    try
      exfalso
      apply hNN
      simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
  case Apply f tail =>
    cases f
    all_goals
      try
        exfalso
        apply hNN
        simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
    case UOp op =>
      cases op
      case _at__at_TypedList_nil =>
        cases hGuard :
            native_Teq (__smtx_typeof a)
              (SmtType.Set (__eo_to_smt_type tail))
        · exfalso
          apply hNN
          simp [__eo_to_smt_set_insert, hGuard, native_ite,
            TranslationProofs.smtx_typeof_none]
        · exact ⟨__eo_to_smt_type tail, by simpa [native_Teq] using hGuard⟩
      all_goals
        exfalso
        apply hNN
        simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
    case Apply f' head =>
      cases f'
      all_goals
        try
          exfalso
          apply hNN
          simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]
      case UOp op =>
        cases op
        case _at__at_TypedList_cons =>
          have hNNUnion : term_has_non_none_type
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail a)) := by
            unfold term_has_non_none_type
            change
              __smtx_typeof
                  (__eo_to_smt_set_insert
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
                      tail) a) ≠ SmtType.None at hNN
            exact hNN
          rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
              (typeof_set_union_eq (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail a))
              hNNUnion with
            ⟨B, _hHead, hTail⟩
          exact eo_to_smt_set_insert_base_set_type_of_set_type tail a B hTail
        all_goals
          exfalso
          apply hNN
          simp [__eo_to_smt_set_insert, TranslationProofs.smtx_typeof_none]

private theorem set_insert_base_arg_non_reg_of_translation
    (xs x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ->
      ∃ A,
        __smtx_typeof (__eo_to_smt x) = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hTrans
  rcases eo_to_smt_set_insert_base_set_type_of_non_none
      xs (__eo_to_smt x) hTrans with
    ⟨B, hBase⟩
  exact ⟨SmtType.Set B, hBase, by simp, by simp⟩

theorem congTrueSpine_set_insert_eq_true
    (M : SmtModel) (hM : model_total_typed M) (xs x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M UserOp.set_insert xs x rhs hSpine with
    ⟨ys, y, hRhs, hList, hArg⟩
  subst hRhs
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x)
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) ys) y)
      hEqBool
  have hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) :=
    hTypes.2
  cases hList with
  | inl hSame =>
      subst ys
      apply RuleProofs.eo_interprets_eq_of_rel M
      · exact hEqBool
      · rcases set_insert_base_arg_non_reg_of_translation xs x hTrans with
          ⟨A, hxA, hANN, hAReg⟩
        have hyA : __smtx_typeof (__eo_to_smt y) = A := by
          rw [← smt_type_eq_of_eq_true_or_same M x y hArg]
          exact hxA
        have hEval :
            __smtx_model_eval M (__eo_to_smt x) =
              __smtx_model_eval M (__eo_to_smt y) :=
          eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type
            M hM x y A hxA hyA hANN hAReg hArg
        have hBaseTy :
            __smtx_typeof (__eo_to_smt x) =
              __smtx_typeof (__eo_to_smt y) := by
          rw [hxA, hyA]
        rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
        change
          __smtx_model_eval_eq
              (__smtx_model_eval M
                (__eo_to_smt_set_insert xs (__eo_to_smt x)))
              (__smtx_model_eval M
                (__eo_to_smt_set_insert xs (__eo_to_smt y))) =
            SmtValue.Boolean true
        rw [eo_to_smt_set_insert_eval_congr_base M
          xs (__eo_to_smt x) (__eo_to_smt y) hBaseTy hEval]
        exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
          (RuleProofs.smt_value_rel_refl _)
  | inr hBool =>
      exact False.elim
        (set_insert_arg_not_eq_bool_of_translation xs ys x hTrans
          (RuleProofs.eo_has_bool_type_of_interprets_true M (mkEq xs ys)
            hBool))

private theorem eo_to_smt_exists_type_congr_body :
    ∀ xs a b,
      __smtx_typeof a = __smtx_typeof b ->
        __smtx_typeof (__eo_to_smt_exists xs a) =
          __smtx_typeof (__eo_to_smt_exists xs b) := by
  intro xs a b hTy
  cases xs <;> try rfl
  case __eo_List_nil =>
    exact hTy
  case Apply f tail =>
    cases f <;> try rfl
    case Apply f' head =>
      cases f' <;> try rfl
      case __eo_List_cons =>
        cases head <;> try rfl
        case Var name T =>
          cases name <;> try rfl
          case String s =>
            change
              __smtx_typeof
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists tail a)) =
                __smtx_typeof
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists tail b))
            rw [smtx_typeof_exists_term_eq, smtx_typeof_exists_term_eq]
            rw [eo_to_smt_exists_type_congr_body tail a b hTy]
termination_by xs a b _ => xs

theorem exists_translation_arg_is_cons
    (xs body : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ->
    ∃ head tail,
      xs = Term.Apply (Term.Apply Term.__eo_List_cons head) tail := by
  intro hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans
  cases xs
  all_goals
    try
      exfalso
      apply hTrans
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    all_goals
      try
        exfalso
        apply hTrans
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    case Apply f' head =>
      cases f'
      all_goals
        try
          exfalso
          apply hTrans
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      case __eo_List_cons =>
        exact ⟨head, tail, rfl⟩

theorem forall_translation_arg_is_cons
    (xs body : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ->
    ∃ head tail,
      xs = Term.Apply (Term.Apply Term.__eo_List_cons head) tail := by
  intro hTrans
  unfold RuleProofs.eo_has_smt_translation at hTrans
  cases xs
  all_goals
    try
      exfalso
      apply hTrans
      change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
      rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
      rfl
  case Apply f tail =>
    cases f
    all_goals
      try
        exfalso
        apply hTrans
        change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
        rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
        rfl
    case Apply f' head =>
      cases f'
      all_goals
        try
          exfalso
          apply hTrans
          change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
          rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
          rfl
      case __eo_List_cons =>
        exact ⟨head, tail, rfl⟩

theorem exists_arg_not_eq_bool_of_translation
    (xs ys body : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ->
    RuleProofs.eo_has_bool_type (mkEq xs ys) ->
    False := by
  intro hTrans hBool
  rcases exists_translation_arg_is_cons xs body hTrans with
    ⟨head, tail, hXs⟩
  subst hXs
  exact
    no_bool_eq_left_of_smt_type_none
      (t := Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
      (rhs := ys)
      (by
        change
          __smtx_typeof
              (SmtTerm.Apply
                (SmtTerm.Apply SmtTerm.None (__eo_to_smt head))
                (__eo_to_smt tail)) = SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply])
      hBool

theorem forall_arg_not_eq_bool_of_translation
    (xs ys body : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ->
    RuleProofs.eo_has_bool_type (mkEq xs ys) ->
    False := by
  intro hTrans hBool
  rcases forall_translation_arg_is_cons xs body hTrans with
    ⟨head, tail, hXs⟩
  subst hXs
  exact
    no_bool_eq_left_of_smt_type_none
      (t := Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
      (rhs := ys)
      (by
        change
          __smtx_typeof
              (SmtTerm.Apply
                (SmtTerm.Apply SmtTerm.None (__eo_to_smt head))
                (__eo_to_smt tail)) = SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply])
      hBool

private theorem eo_to_smt_exists_type_congr_arg
    (xs body body' : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ->
    __smtx_typeof (__eo_to_smt body) =
      __smtx_typeof (__eo_to_smt body') ->
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body')) := by
  intro hTrans hTy
  rcases exists_translation_arg_is_cons xs body hTrans with
    ⟨head, tail, hXs⟩
  subst hXs
  change
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
          (__eo_to_smt body)) =
      __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
          (__eo_to_smt body'))
  exact eo_to_smt_exists_type_congr_body
    (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
    (__eo_to_smt body) (__eo_to_smt body') hTy

private theorem eo_to_smt_forall_type_congr_arg
    (xs body body' : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ->
    __smtx_typeof (__eo_to_smt body) =
      __smtx_typeof (__eo_to_smt body') ->
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body')) := by
  intro hTrans hTy
  rcases forall_translation_arg_is_cons xs body hTrans with
    ⟨head, tail, hXs⟩
  subst hXs
  change
    __smtx_typeof
        (SmtTerm.not
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
            (SmtTerm.not (__eo_to_smt body)))) =
      __smtx_typeof
        (SmtTerm.not
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
            (SmtTerm.not (__eo_to_smt body'))))
  rw [typeof_not_eq, typeof_not_eq]
  rw [eo_to_smt_exists_type_congr_body
    (Term.Apply (Term.Apply Term.__eo_List_cons head) tail)
    (SmtTerm.not (__eo_to_smt body)) (SmtTerm.not (__eo_to_smt body'))
    (by rw [typeof_not_eq, typeof_not_eq, hTy])]

theorem congTypeSpine_exists_eq_has_bool_type
    (xs body rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv UserOp.exists xs body rhs hSpine with
    ⟨ys, body', hRhs, hList, hBody⟩
  subst hRhs
  cases hList with
  | inl _ =>
      subst ys
      have hBodyTy :
          __smtx_typeof (__eo_to_smt body) =
            __smtx_typeof (__eo_to_smt body') :=
        smt_type_eq_of_eq_bool_or_same body body' hBody
      exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body)
        (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body')
        (eo_to_smt_exists_type_congr_arg xs body body' hTrans hBodyTy)
        hTrans
  | inr hBool =>
      exact False.elim
        (exists_arg_not_eq_bool_of_translation xs ys body hTrans hBool)

theorem congTypeSpine_forall_eq_has_bool_type
    (xs body rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv UserOp.forall xs body rhs hSpine with
    ⟨ys, body', hRhs, hList, hBody⟩
  subst hRhs
  cases hList with
  | inl _ =>
      subst ys
      have hBodyTy :
          __smtx_typeof (__eo_to_smt body) =
            __smtx_typeof (__eo_to_smt body') :=
        smt_type_eq_of_eq_bool_or_same body body' hBody
      exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body')
        (eo_to_smt_forall_type_congr_arg xs body body' hTrans hBodyTy)
        hTrans
  | inr hBool =>
      exact False.elim
        (forall_arg_not_eq_bool_of_translation xs ys body hTrans hBool)


end CongSupport
