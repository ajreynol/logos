module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryRegexHelpers
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryRegexHelpers

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

theorem eo_typeof_concat_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    ∃ n m,
      A = Term.Apply (Term.UOp UserOp.BitVec) n ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) m := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | BitVec =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | BitVec =>
                          exact ⟨n, m, rfl, rfl⟩
                      | _ =>
                          simp [__eo_typeof_concat] at h
                  | _ =>
                      simp [__eo_typeof_concat] at h
              | _ =>
                  simp [__eo_typeof_concat] at h
          | _ =>
              simp [__eo_typeof_concat] at h
      | _ =>
          simp [__eo_typeof_concat] at h
  | _ =>
      simp [__eo_typeof_concat] at h

theorem eo_typeof_concat_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_concat_arg_types_of_ne_stuck h with
    ⟨n, m, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_concat_non_none_of_eo_bitvec_types_non_none
    {A B : Term}
    (hA : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) A) ≠
      SmtType.None)
    (hB : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) B) ≠
      SmtType.None) :
    __smtx_typeof_concat
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) A))
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) B)) ≠
      SmtType.None := by
  cases A <;> simp [__eo_to_smt_type] at hA ⊢
  case Numeral n =>
    by_cases hn : native_zleq 0 n = true
    · cases B <;> simp [__eo_to_smt_type] at hB ⊢
      rename_i m
      by_cases hm : native_zleq 0 m = true
      · simp [hn, hm, native_ite, __smtx_typeof_concat]
      · simp [hm, native_ite] at hB
    · simp [hn, native_ite] at hA

theorem smt_concat_non_none_of_eo_typeof_concat_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_concat (__eo_typeof X) (__eo_typeof Y) ≠ Term.Stuck) :
    __smtx_typeof_concat
        (__smtx_typeof (__eo_to_smt X)) (__smtx_typeof (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_concat_arg_types_of_ne_stuck hApp with
    ⟨n, m, hXTy, hYTy⟩
  have hXTyNN :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        SmtType.None := by
    simpa [hXTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
  have hYTyNN :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) m) ≠
        SmtType.None := by
    simpa [hYTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation Y hYTrans
  rw [hXSmt, hYSmt, hXTy, hYTy]
  exact smt_concat_non_none_of_eo_bitvec_types_non_none hXTyNN hYTyNN

theorem eo_typeof_bvand_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    ∃ w,
      A = Term.Apply (Term.UOp UserOp.BitVec) w ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | BitVec =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | BitVec =>
                          have hReq :
                              __eo_requires (__eo_eq n m)
                                  (Term.Boolean true)
                                  (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
                                Term.Stuck := by
                            simpa [__eo_typeof_bvand] using h
                          have hm : m = n :=
                            support_eq_of_eo_eq_true n m
                              (support_eo_requires_cond_eq_of_non_stuck hReq)
                          exact ⟨n, rfl, by rw [hm]⟩
                      | _ =>
                          simp [__eo_typeof_bvand] at h
                  | _ =>
                      simp [__eo_typeof_bvand] at h
              | _ =>
                  simp [__eo_typeof_bvand] at h
          | _ =>
              simp [__eo_typeof_bvand] at h
      | _ =>
          simp [__eo_typeof_bvand] at h
  | _ =>
      simp [__eo_typeof_bvand] at h

theorem eo_typeof_bvand_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_bvand_arg_types_of_ne_stuck h with
    ⟨w, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_bv_binop_non_none_of_eo_bitvec_type_non_none
    {A : Term}
    (hA : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) A) ≠
      SmtType.None) :
    __smtx_typeof_bv_op_2
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) A))
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) A)) ≠
      SmtType.None := by
  cases A <;> simp [__eo_to_smt_type] at hA ⊢
  case Numeral n =>
    by_cases hn : native_zleq 0 n = true
    · simp [hn, native_ite, __smtx_typeof_bv_op_2, native_nateq]
    · simp [hn, native_ite] at hA

theorem smt_bv_binop_ret_non_none_of_eo_bitvec_type_non_none
    {A : Term} {ret : SmtType}
    (hA : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) A) ≠
      SmtType.None)
    (hRet : ret ≠ SmtType.None) :
    __smtx_typeof_bv_op_2_ret
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) A))
        (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) A)) ret ≠
      SmtType.None := by
  cases A <;> simp [__eo_to_smt_type] at hA ⊢
  case Numeral n =>
    by_cases hn : native_zleq 0 n = true
    · simpa [hn, native_ite, __smtx_typeof_bv_op_2_ret, native_nateq]
        using hRet
    · simp [hn, native_ite] at hA

theorem smt_bv_binop_ret_eq_ret_of_non_none
    {A B ret : SmtType}
    (h :
      __smtx_typeof_bv_op_2_ret A B ret ≠ SmtType.None) :
    __smtx_typeof_bv_op_2_ret A B ret = ret := by
  cases A <;> cases B <;>
    simp [__smtx_typeof_bv_op_2_ret] at h ⊢
  case BitVec.BitVec n m =>
    by_cases hnm : native_nateq n m = true
    · simp [hnm, native_ite]
    · simp [hnm, native_ite] at h

theorem eo_typeof_from_bools_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_from_bools A B ≠ Term.Stuck) :
    ∃ n, A = Term.Bool ∧ B = Term.Apply (Term.UOp UserOp.BitVec) n := by
  cases A with
  | Bool =>
      cases B with
      | Apply f n =>
          cases f with
          | UOp opB =>
              cases opB with
              | BitVec =>
                  exact ⟨n, rfl, rfl⟩
              | _ =>
                  simp [__eo_typeof__at_from_bools] at h
          | _ =>
              simp [__eo_typeof__at_from_bools] at h
      | _ =>
          simp [__eo_typeof__at_from_bools] at h
  | _ =>
      simp [__eo_typeof__at_from_bools] at h

theorem eo_typeof_from_bools_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_from_bools A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_from_bools_arg_types_of_ne_stuck h with
    ⟨n, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_from_bools_non_none_of_eo_typeof_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof__at_from_bools (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.concat
          (SmtTerm.ite (__eo_to_smt X)
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
          (__eo_to_smt Y)) ≠
      SmtType.None := by
  rcases eo_typeof_from_bools_arg_types_of_ne_stuck hApp with
    ⟨n, hXTy, hYTy⟩
  have hXSmt : __smtx_typeof (__eo_to_smt X) = SmtType.Bool := by
    have hMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
    rw [hXTy] at hMatch
    exact hMatch
  rcases smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec hYTrans hYTy with
    ⟨w, hYSmt⟩
  have hBitTy :
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt X)
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
        SmtType.BitVec 1 := by
    rw [typeof_ite_eq, hXSmt, smt_typeof_binary_one_one,
      smt_typeof_binary_one_zero]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  rw [typeof_concat_eq, hBitTy, hYSmt]
  simp [__smtx_typeof_concat]

theorem smt_bv_binop_non_none_of_eo_typeof_bvand_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_bvand (__eo_typeof X) (__eo_typeof Y) ≠ Term.Stuck) :
    __smtx_typeof_bv_op_2
        (__smtx_typeof (__eo_to_smt X)) (__smtx_typeof (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_bvand_arg_types_of_ne_stuck hApp with
    ⟨w, hXTy, hYTy⟩
  have hXTyNN :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        SmtType.None := by
    simpa [hXTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
  rw [hXSmt, hYSmt, hXTy, hYTy]
  exact smt_bv_binop_non_none_of_eo_bitvec_type_non_none hXTyNN

theorem smt_bv_binop_ret_non_none_of_eo_bitvec_arg_types
    (X Y : Term) {ret : SmtType}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hArgs :
      ∃ w,
        __eo_typeof X = Term.Apply (Term.UOp UserOp.BitVec) w ∧
          __eo_typeof Y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hRet : ret ≠ SmtType.None) :
    __smtx_typeof_bv_op_2_ret
        (__smtx_typeof (__eo_to_smt X)) (__smtx_typeof (__eo_to_smt Y))
        ret ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases hArgs with ⟨w, hXTy, hYTy⟩
  have hXTyNN :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        SmtType.None := by
    simpa [hXTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
  rw [hXSmt, hYSmt, hXTy, hYTy]
  exact smt_bv_binop_ret_non_none_of_eo_bitvec_type_non_none
    hXTyNN hRet

theorem eo_typeof_bvcomp_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_bvcomp A B ≠ Term.Stuck) :
    ∃ w,
      A = Term.Apply (Term.UOp UserOp.BitVec) w ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | BitVec =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | BitVec =>
                          have hReq :
                              __eo_requires (__eo_eq n m)
                                  (Term.Boolean true)
                                  (Term.Apply (Term.UOp UserOp.BitVec)
                                    (Term.Numeral 1)) ≠
                                Term.Stuck := by
                            simpa [__eo_typeof_bvcomp] using h
                          have hm : m = n :=
                            support_eq_of_eo_eq_true n m
                              (support_eo_requires_cond_eq_of_non_stuck hReq)
                          exact ⟨n, rfl, by rw [hm]⟩
                      | _ =>
                          simp [__eo_typeof_bvcomp] at h
                  | _ =>
                      simp [__eo_typeof_bvcomp] at h
              | _ =>
                  simp [__eo_typeof_bvcomp] at h
          | _ =>
              simp [__eo_typeof_bvcomp] at h
      | _ =>
          simp [__eo_typeof_bvcomp] at h
  | _ =>
      simp [__eo_typeof_bvcomp] at h

theorem eo_typeof_bvult_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_bvult A B ≠ Term.Stuck) :
    ∃ w,
      A = Term.Apply (Term.UOp UserOp.BitVec) w ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | BitVec =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | BitVec =>
                          have hReq :
                              __eo_requires (__eo_eq n m)
                                  (Term.Boolean true) Term.Bool ≠
                                Term.Stuck := by
                            simpa [__eo_typeof_bvult] using h
                          have hm : m = n :=
                            support_eq_of_eo_eq_true n m
                              (support_eo_requires_cond_eq_of_non_stuck hReq)
                          exact ⟨n, rfl, by rw [hm]⟩
                      | _ =>
                          simp [__eo_typeof_bvult] at h
                  | _ =>
                      simp [__eo_typeof_bvult] at h
              | _ =>
                  simp [__eo_typeof_bvult] at h
          | _ =>
              simp [__eo_typeof_bvult] at h
      | _ =>
          simp [__eo_typeof_bvult] at h
  | _ =>
      simp [__eo_typeof_bvult] at h

theorem smt_bv_cmp_to_bv1_non_none_of_eo_typeof_bvcomp_ne_stuck
    (smtCmp : SmtTerm -> SmtTerm -> SmtTerm)
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtCmp X Y) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof X) (__smtx_typeof Y) SmtType.Bool)
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_bvcomp (__eo_typeof X) (__eo_typeof Y) ≠ Term.Stuck) :
    __smtx_typeof
        (SmtTerm.ite (smtCmp (__eo_to_smt X) (__eo_to_smt Y))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) ≠
      SmtType.None := by
  have hCmpNN :
      __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt X)) (__smtx_typeof (__eo_to_smt Y))
          SmtType.Bool ≠
        SmtType.None :=
    smt_bv_binop_ret_non_none_of_eo_bitvec_arg_types
      X Y hXTrans hYTrans (eo_typeof_bvcomp_arg_types_of_ne_stuck hApp)
      (by simp)
  have hCmpTy :
      __smtx_typeof (smtCmp (__eo_to_smt X) (__eo_to_smt Y)) =
        SmtType.Bool := by
    rw [hSmtType]
    exact smt_bv_binop_ret_eq_ret_of_non_none hCmpNN
  rw [typeof_ite_eq, hCmpTy, smt_typeof_binary_one_one,
    smt_typeof_binary_one_zero]
  simp [__smtx_typeof_ite, native_ite, native_Teq]


end SubstitutePreservationSupport
