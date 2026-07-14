import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
import Cpc.Proofs.Rules.Aci_norm

/-! Support for eliminating an all-ones element from an n-ary bit-vector XOR. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvXorOnesSupport

def insertedTail (zs n w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor)
    (bvAllOnesConst n w)) zs

def lhs (xs zs n w : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.bvxor) xs (insertedTail zs n w)

def baseList (xs zs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.bvxor) xs zs

def base (xs zs : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.bvxor) (baseList xs zs)

def rhs (xs zs : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) (base xs zs)

def term (xs zs n w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs xs zs n w))
    (rhs xs zs)

private theorem native_width_roundtrip
    (W : native_Int) :
    native_zleq 0 W = true ->
    native_nat_to_int (native_int_to_nat W) = W := by
  intro hW
  have hWProp : (0 : native_Int) <= W := by
    simpa [SmtEval.native_zleq] using hW
  have hInt : (Int.ofNat (Int.toNat W) : Int) = W :=
    Int.toNat_of_nonneg hWProp
  simpa [SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using hInt

private theorem list_concat_eq_rec_of_lists
    (a z : Term) :
    __eo_is_list (Term.UOp UserOp.bvxor) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) z = Term.Boolean true ->
    __eo_list_concat (Term.UOp UserOp.bvxor) a z =
      __eo_list_concat_rec a z := by
  intro hA hZ
  simp [__eo_list_concat, hA, hZ, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

private theorem list_concat_lists_of_ne_stuck
    (f a b : Term) :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true ∧
      __eo_is_list f b = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) ≠ Term.Stuck := by
    simpa [__eo_list_concat] using h
  have hA := support_eo_requires_cond_eq_of_non_stuck hReq
  have hTail :
      __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) ≠ Term.Stuck := by
    exact eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hReq
  have hB := support_eo_requires_cond_eq_of_non_stuck hTail
  exact ⟨hA, hB⟩

private theorem smtx_typeof_bvxor_term_eq
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvxor x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_typeof_bvnot_term_eq
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnot x) =
      __smtx_typeof_bv_op_1 (__smtx_typeof x) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smtx_eval_bvxor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvxor x y) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvnot_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvnot x) =
      __smtx_model_eval_bvnot (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem context
    (xs zs n w : Term) (k W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    n = Term.Numeral k ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    __eo_typeof (term xs zs n w) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true := by
  intro _hXsTy _hZsTy hN hW hW0 hResultTy
  have hSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
    (__eo_typeof (lhs xs zs n w)) (__eo_typeof (rhs xs zs))
    (by simpa [term] using hResultTy)
  have hLhsNe : lhs xs zs n w ≠ Term.Stuck := by
    intro h
    apply hSides.1
    rw [h]
    rfl
  have hLists := list_concat_lists_of_ne_stuck
    (Term.UOp UserOp.bvxor) xs (insertedTail zs n w) hLhsNe
  have hZsList := eo_is_list_tail_true_of_cons_self
    (Term.UOp UserOp.bvxor) (bvAllOnesConst n w) zs hLists.2
  exact ⟨hLists.1, hZsList⟩

private theorem common_types
    (xs zs n w : Term) (k W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    n = Term.Numeral k ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    __eo_is_list (Term.UOp UserOp.bvxor) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvxor) zs = Term.Boolean true ->
    let width := native_int_to_nat W
    __smtx_typeof (__eo_to_smt (bvAllOnesConst n w)) =
        SmtType.BitVec width ∧
      __smtx_typeof (__eo_to_smt (insertedTail zs n w)) =
        SmtType.BitVec width ∧
      __smtx_typeof
          (__eo_to_smt (__eo_list_concat_rec xs (insertedTail zs n w))) =
        SmtType.BitVec width ∧
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec xs zs)) =
        SmtType.BitVec width ∧
      __smtx_typeof (__eo_to_smt (base xs zs)) =
        SmtType.BitVec width := by
  intro hXsTy hZsTy hN hW hW0 hXsList hZsList
  subst n
  subst w
  let width := native_int_to_nat W
  have hConstTy :
      __smtx_typeof
          (__eo_to_smt
            (bvAllOnesConst (Term.Numeral k) (Term.Numeral W))) =
        SmtType.BitVec width := by
    simpa [width] using smt_typeof_bv_const k W hW0
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvxor)
          (insertedTail zs (Term.Numeral k) (Term.Numeral W)) =
        Term.Boolean true := by
    exact eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.bvxor)
      (bvAllOnesConst (Term.Numeral k) (Term.Numeral W)) zs
      (by decide) hZsList
  have hInsertedTy :
      __smtx_typeof
          (__eo_to_smt
            (insertedTail zs (Term.Numeral k) (Term.Numeral W))) =
        SmtType.BitVec width := by
    change __smtx_typeof
        (SmtTerm.bvxor
          (__eo_to_smt
            (bvAllOnesConst (Term.Numeral k) (Term.Numeral W)))
          (__eo_to_smt zs)) = _
    rw [smtx_typeof_bvxor_term_eq]
    simp [__smtx_typeof_bv_op_2, hConstTy, hZsTy, width,
      native_nateq, native_ite]
  have hLhsRecTy := BvNaryXorSupport.listConcatRecSmtType
    xs (insertedTail zs (Term.Numeral k) (Term.Numeral W)) width
    hXsList hInsertedList (by simpa [width] using hXsTy) hInsertedTy
  have hBaseRecTy := BvNaryXorSupport.listConcatRecSmtType
    xs zs width hXsList hZsList
    (by simpa [width] using hXsTy) (by simpa [width] using hZsTy)
  have hBaseList :
      __eo_is_list (Term.UOp UserOp.bvxor)
          (__eo_list_concat_rec xs zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.bvxor) xs zs hXsList hZsList
  have hBaseTy := BvNaryXorSupport.listSingletonElimSmtType
    (__eo_list_concat_rec xs zs) width hBaseList hBaseRecTy
  have hBaseEq := list_concat_eq_rec_of_lists xs zs hXsList hZsList
  exact ⟨hConstTy, hInsertedTy, hLhsRecTy, hBaseRecTy, by
    simpa [base, baseList, hBaseEq] using hBaseTy⟩

theorem typed_term
    (xs zs n w : Term) (k W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    n = Term.Numeral k ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    __eo_typeof (term xs zs n w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (term xs zs n w) := by
  intro hXsTy hZsTy hN hW hW0 hResultTy
  have hLists := context xs zs n w k W hXsTy hZsTy hN hW hW0 hResultTy
  have hTypes := common_types xs zs n w k W hXsTy hZsTy
    hN hW hW0 hLists.1 hLists.2
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvxor) (insertedTail zs n w) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.bvxor) (bvAllOnesConst n w) zs
      (by decide) hLists.2
  have hLhsEq := list_concat_eq_rec_of_lists xs (insertedTail zs n w)
    hLists.1 hInsertedList
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs xs zs n w)) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [lhs, hLhsEq] using hTypes.2.2.1
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (rhs xs zs)) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof (SmtTerm.bvnot (__eo_to_smt (base xs zs))) = _
    rw [smtx_typeof_bvnot_term_eq]
    simp [__smtx_typeof_bv_op_1, hTypes.2.2.2.2, native_ite]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (lhs xs zs n w) (rhs xs zs)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

theorem facts_term
    (M : SmtModel) (hM : model_total_typed M)
    (xs zs n w : Term) (k W : native_Int) :
    __smtx_typeof (__eo_to_smt xs) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt zs) =
      SmtType.BitVec (native_int_to_nat W) ->
    n = Term.Numeral k ->
    w = Term.Numeral W ->
    native_zleq 0 W = true ->
    eo_interprets M (bvAllOnesValuePrem n w) true ->
    __eo_typeof (term xs zs n w) = Term.Bool ->
    eo_interprets M (term xs zs n w) true := by
  intro hXsTy hZsTy hN hW hW0 hPrem hResultTy
  have hBool := typed_term xs zs n w k W hXsTy hZsTy
    hN hW hW0 hResultTy
  have hLists := context xs zs n w k W hXsTy hZsTy hN hW hW0 hResultTy
  have hTypes := common_types xs zs n w k W hXsTy hZsTy
    hN hW hW0 hLists.1 hLists.2
  let width := native_int_to_nat W
  have hWidthEq : native_nat_to_int width = W := by
    exact native_width_roundtrip W hW0
  have hInsertedList :
      __eo_is_list (Term.UOp UserOp.bvxor) (insertedTail zs n w) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.bvxor) (bvAllOnesConst n w) zs
      (by decide) hLists.2
  have hLhsEq := list_concat_eq_rec_of_lists xs (insertedTail zs n w)
    hLists.1 hInsertedList
  have hBaseEq := list_concat_eq_rec_of_lists xs zs hLists.1 hLists.2
  have hBaseRecList :
      __eo_is_list (Term.UOp UserOp.bvxor)
          (__eo_list_concat_rec xs zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.bvxor) xs zs hLists.1 hLists.2
  have hLhsConcatEval := BvNaryXorSupport.listConcatRecEvalEq
    M hM xs (insertedTail zs n w) width hLists.1 hInsertedList
    (by simpa [width] using hXsTy) (by simpa [width] using hTypes.2.1)
  have hBaseConcatEval := BvNaryXorSupport.listConcatRecEvalEq
    M hM xs zs width hLists.1 hLists.2
    (by simpa [width] using hXsTy) (by simpa [width] using hZsTy)
  have hSingletonEval := BvNaryXorSupport.listSingletonElimEvalEq
    M hM (__eo_list_concat_rec xs zs) width hBaseRecList
    (by simpa [width] using hTypes.2.2.2.1)
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt xs) width
      (by simpa [width] using hXsTy) with
    ⟨px, hXsEval, hXsCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt zs) width
      (by simpa [width] using hZsTy) with
    ⟨pz, hZsEval, hZsCan⟩
  have hMaxEval := eval_bv_all_ones_const_of_prem M n w k W
    hN hW hW0 hPrem
  have hMaxEvalNat :
      __smtx_model_eval M (__eo_to_smt (bvAllOnesConst n w)) =
        SmtValue.Binary (native_nat_to_int width)
          (native_int_pow2 (native_nat_to_int width) - 1) := by
    simpa [hWidthEq] using hMaxEval
  have hInsertedEval :
      __smtx_model_eval M (__eo_to_smt (insertedTail zs n w)) =
        __smtx_model_eval_bvnot
          (SmtValue.Binary (native_nat_to_int width) pz) := by
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt (bvAllOnesConst n w))
          (__eo_to_smt zs)) = _
    rw [smtx_eval_bvxor_term_eq, hMaxEvalNat, hZsEval]
    exact bvxor_all_ones_eval_eq_bvnot width pz hZsCan
  have hBaseConcatEval' :
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec xs zs)) =
        __smtx_model_eval_bvxor
          (SmtValue.Binary (native_nat_to_int width) px)
          (SmtValue.Binary (native_nat_to_int width) pz) := by
    rw [hBaseConcatEval]
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt xs) (__eo_to_smt zs)) = _
    rw [smtx_eval_bvxor_term_eq, hXsEval, hZsEval]
  have hRhsEq :
      rhs xs zs =
        Term.Apply (Term.UOp UserOp.bvnot)
          (__eo_list_singleton_elim (Term.UOp UserOp.bvxor)
            (__eo_list_concat_rec xs zs)) := by
    unfold rhs base baseList
    rw [hBaseEq]
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs xs zs n w)) =
        __smtx_model_eval M (__eo_to_smt (rhs xs zs)) := by
    rw [show __eo_to_smt (lhs xs zs n w) =
        __eo_to_smt (__eo_list_concat_rec xs (insertedTail zs n w)) by
      rw [← hLhsEq]
      rfl]
    rw [hRhsEq]
    rw [hLhsConcatEval]
    change __smtx_model_eval M
        (SmtTerm.bvxor (__eo_to_smt xs)
          (__eo_to_smt (insertedTail zs n w))) = _
    rw [smtx_eval_bvxor_term_eq, hXsEval, hInsertedEval]
    rw [bvxor_bvnot_right_eval_eq_bvnot_bvxor width px pz
      hXsCan hZsCan]
    rw [← hBaseConcatEval']
    rw [← hSingletonEval]
    rw [← smtx_eval_bvnot_term_eq]
    change __smtx_model_eval M
        (SmtTerm.bvnot
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.bvxor)
              (__eo_list_concat_rec xs zs)))) =
      __smtx_model_eval M
        (SmtTerm.bvnot
          (__eo_to_smt
            (__eo_list_singleton_elim (Term.UOp UserOp.bvxor)
              (__eo_list_concat_rec xs zs))))
    rfl
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (lhs xs zs n w)))
      (__smtx_model_eval M (__eo_to_smt (rhs xs zs)))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

end BvXorOnesSupport
