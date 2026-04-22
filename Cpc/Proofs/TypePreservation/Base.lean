import Lean
import Cpc.Proofs.TypePreservation.Model

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

syntax "smtx_model_eval_choice_nth_eq_1" : term
syntax "smtx_model_eval_choice_nth_eq_2" : term

open Lean Elab Term Meta in
private def choiceNthEvalEqThm (idx : Nat) : TermElabM Expr := do
  let eqTy ← inferType (mkConst ``Smtm.__smtx_model_eval.eq_136)
  forallTelescopeReducing eqTy fun _ body => do
    let some (_, _, rhs) := body.eq? | throwError "unexpected __smtx_model_eval.eq_136 shape"
    let .const fnName _ := rhs.getAppFn | throwError "unexpected choice_nth evaluator shape"
    let some eqns ← Lean.Meta.getEqnsFor? fnName | throwError "missing choice_nth evaluator equations"
    let some eqThm := eqns[idx]? | throwError "choice_nth evaluator equation index out of bounds"
    pure (mkConst eqThm)

open Lean Elab Term Meta in
elab_rules : term
  | `(smtx_model_eval_choice_nth_eq_1) => choiceNthEvalEqThm 0
  | `(smtx_model_eval_choice_nth_eq_2) => choiceNthEvalEqThm 1

/-- Shows that evaluating `boolean` terms produces values of the expected type. -/
theorem typeof_value_model_eval_boolean
    (M : SmtModel)
    (b : native_Bool) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Boolean b)) =
      __smtx_typeof (SmtTerm.Boolean b) := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `numeral` terms produces values of the expected type. -/
theorem typeof_value_model_eval_numeral
    (M : SmtModel)
    (n : native_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `rational` terms produces values of the expected type. -/
theorem typeof_value_model_eval_rational
    (M : SmtModel)
    (q : native_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `binary` terms produces values of the expected type. -/
theorem typeof_value_model_eval_binary
    (M : SmtModel)
    (w n : native_Int)
    (ht : term_has_non_none_type (SmtTerm.Binary w n)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Binary w n)) =
      __smtx_typeof (SmtTerm.Binary w n) := by
  unfold term_has_non_none_type at ht
  let g :=
    native_and (native_zleq 0 w)
      (native_zeq n (native_mod_total n (native_int_pow2 w)))
  have hg : g = true := by
    cases h : g with
    | false =>
        exfalso
        apply ht
        unfold __smtx_typeof
        simp [g, native_ite, h]
    | true =>
        rfl
  have hWidth : native_zleq 0 w = true := by
    cases h1 : native_zleq 0 w
    · simp [g, SmtEval.native_and, h1] at hg
    · rfl
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
    cases h2 : native_zeq n (native_mod_total n (native_int_pow2 w))
    · simp [g, SmtEval.native_and, hWidth, h2] at hg
    · rfl
  have hType :
      __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec (native_int_to_nat w) := by
    simp [__smtx_typeof, native_ite, SmtEval.native_and, hWidth, hMod]
  rw [hType]
  simp [__smtx_model_eval, __smtx_bv_literal, __smtx_typeof_value]

/-- Shows that evaluating `var` terms produces values of the expected type. -/
theorem typeof_value_model_eval_var
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.Var s T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Var s T)) =
      __smtx_typeof (SmtTerm.Var s T) := by
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T (by
      unfold term_has_non_none_type at ht
      unfold __smtx_typeof at ht
      exact ht)
  unfold __smtx_model_eval __smtx_typeof
  rw [model_total_typed_lookup hM s T hT]
  exact hGuard.symm

/-- Shows that evaluating `uconst` terms produces values of the expected type. -/
theorem typeof_value_model_eval_uconst
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.UConst s T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.UConst s T)) =
      __smtx_typeof (SmtTerm.UConst s T) := by
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T (by
      unfold term_has_non_none_type at ht
      unfold __smtx_typeof at ht
      exact ht)
  unfold __smtx_model_eval __smtx_typeof
  rw [model_total_typed_lookup hM s T hT]
  exact hGuard.symm

/-- Derives `model_eval_var` from `uninhabited`. -/
theorem model_eval_var_of_uninhabited
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : ¬ type_inhabited T) :
    __smtx_model_eval M (SmtTerm.Var s T) = SmtValue.NotValue := by
  unfold __smtx_model_eval
  simpa using model_total_typed_lookup_uninhabited hM s T hT

/-- Derives `model_eval_uconst` from `uninhabited`. -/
theorem model_eval_uconst_of_uninhabited
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : ¬ type_inhabited T) :
    __smtx_model_eval M (SmtTerm.UConst s T) = SmtValue.NotValue := by
  unfold __smtx_model_eval
  simpa using model_total_typed_lookup_uninhabited hM s T hT

/-- Shows that evaluating `re_allchar` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_allchar
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_allchar) =
      __smtx_typeof SmtTerm.re_allchar := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `re_none` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_none
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_none) =
      __smtx_typeof SmtTerm.re_none := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `re_all` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_all
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_all) =
      __smtx_typeof SmtTerm.re_all := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `seq_empty` terms produces values of the expected type. -/
theorem typeof_value_model_eval_seq_empty
    (M : SmtModel)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.seq_empty T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_empty T)) =
      __smtx_typeof (SmtTerm.seq_empty T) := by
  have hGuard : __smtx_typeof_guard_wf T (SmtType.Seq T) = SmtType.Seq T :=
    smtx_typeof_guard_wf_of_non_none T (SmtType.Seq T) (by
      unfold term_has_non_none_type at ht
      unfold __smtx_typeof at ht
      exact ht)
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, hGuard]

/-- Shows that evaluating `set_empty` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_empty
    (M : SmtModel)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.set_empty T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.set_empty T)) =
      __smtx_typeof (SmtTerm.set_empty T) := by
  have hGuard : __smtx_typeof_guard_wf T (SmtType.Set T) = SmtType.Set T :=
    smtx_typeof_guard_wf_of_non_none T (SmtType.Set T) (by
      unfold term_has_non_none_type at ht
      unfold __smtx_typeof at ht
      exact ht)
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type,
    hGuard]

/-- Shows that evaluating `seq_unit` terms produces values of the expected type. -/
theorem typeof_value_model_eval_seq_unit
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_unit t)) =
      __smtx_typeof (SmtTerm.seq_unit t) := by
  unfold term_has_non_none_type at ht
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, native_ite, native_Teq,
    ht, hpres]

/-- Shows that evaluating `set_singleton` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_singleton
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.set_singleton t)) =
      __smtx_typeof (SmtTerm.set_singleton t) := by
  unfold term_has_non_none_type at ht
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_model_eval_set_singleton, __smtx_typeof_value, __smtx_typeof_map_value,
    __smtx_map_to_set_type, native_ite, native_Teq, ht, hpres]

/-- Derives `exists_body_bool` from `non_none`. -/
theorem exists_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht ⊢

/-- Derives `exists_term_typeof` from `non_none`. -/
theorem exists_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool := by
  simp [__smtx_typeof, native_ite, native_Teq, exists_body_bool_of_non_none ht]

/-- Shows that evaluating `exists` terms produces values of the expected type. -/
theorem typeof_value_model_eval_exists
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.exists s T body)) =
      __smtx_typeof (SmtTerm.exists s T body) := by
  classical
  rw [exists_term_typeof_of_non_none ht]
  unfold __smtx_model_eval
  by_cases h :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · simp [h, __smtx_typeof_value]
  · simp [h, __smtx_typeof_value]

/-- Derives `forall_body_bool` from `non_none`. -/
theorem forall_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht ⊢

/-- Derives `forall_term_typeof` from `non_none`. -/
theorem forall_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof (SmtTerm.forall s T body) = SmtType.Bool := by
  simp [__smtx_typeof, native_ite, native_Teq, forall_body_bool_of_non_none ht]

/-- Shows that evaluating `forall` terms produces values of the expected type. -/
theorem typeof_value_model_eval_forall
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.forall s T body)) =
      __smtx_typeof (SmtTerm.forall s T body) := by
  classical
  rw [forall_term_typeof_of_non_none ht]
  unfold __smtx_model_eval
  by_cases h :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · have hIf :
        (if h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
          SmtValue.Boolean true
        else
          SmtValue.Boolean false) = SmtValue.Boolean true := by
        by_cases h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
        · simpa using h'
        · contradiction
    rw [hIf]
    rfl
  · have hIf :
        (if h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
          SmtValue.Boolean true
        else
          SmtValue.Boolean false) = SmtValue.Boolean false := by
        by_cases h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
        · contradiction
        · simp [h']
    rw [hIf]
    rfl

/-- Provides a witness for `choice_term_has`. -/
theorem choice_term_has_witness
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    ∃ v : SmtValue, __smtx_typeof_value v = T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, __smtx_typeof_choice_nth, native_ite, native_Teq, h] at ht ⊢
  · exact smtx_typeof_guard_wf_inhabited_of_non_none T T ht

/-- Derives `choice_term_typeof` from `non_none`. -/
theorem choice_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    __smtx_typeof (SmtTerm.choice_nth s T body 0) = T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, __smtx_typeof_choice_nth, native_ite, native_Teq, h] at ht ⊢
  · exact smtx_typeof_guard_wf_of_non_none T T ht

/-- Shows that evaluating `choice` terms produces values of the expected type. -/
theorem typeof_value_model_eval_choice
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.choice_nth s T body 0)) =
      __smtx_typeof (SmtTerm.choice_nth s T body 0) := by
  classical
  have hTy : ∃ v : SmtValue, __smtx_typeof_value v = T :=
    choice_term_has_witness ht
  rw [choice_term_typeof_of_non_none ht]
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · rw [__smtx_model_eval.eq_136, smtx_model_eval_choice_nth_eq_1]
    simp [hSat]
    exact (Classical.choose_spec hSat).1
  · rw [__smtx_model_eval.eq_136, smtx_model_eval_choice_nth_eq_1]
    simp [hSat, hTy]
    exact Classical.choose_spec hTy

/-- Shows that evaluating `choice_nth` terms preserves the computed choice type for any index. -/
theorem typeof_value_model_eval_choice_nth
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (n : native_Nat)
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body n)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.choice_nth s T body n)) =
      __smtx_typeof (SmtTerm.choice_nth s T body n) := by
  classical
  induction n generalizing M s T body with
  | zero =>
      simpa using typeof_value_model_eval_choice M s T body ht
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof (SmtTerm.choice_nth s T (SmtTerm.exists s' U body') (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_136, __smtx_typeof.eq_136]
            simp [__smtx_typeof_choice_nth]
          have ht' : term_has_non_none_type (SmtTerm.choice_nth s' U body' n) := by
            unfold term_has_non_none_type
            rw [← hTyEq]
            exact ht
          rw [__smtx_model_eval.eq_136, smtx_model_eval_choice_nth_eq_2]
          rw [hTyEq]
          simpa [__smtx_model_eval.eq_136,
            smtx_model_eval_choice_nth_eq_1, smtx_model_eval_choice_nth_eq_2] using
            ih (__smtx_model_push M s T
              (if hSat :
                  ∃ v : SmtValue,
                    __smtx_typeof_value v = T ∧
                      __smtx_model_eval (__smtx_model_push M s T v)
                        (SmtTerm.exists s' U body') = SmtValue.Boolean true then
                Classical.choose hSat
              else
                if hTy : ∃ v : SmtValue, __smtx_typeof_value v = T then
                  Classical.choose hTy
                else
                  SmtValue.NotValue)) s' U body' ht'
      | _ =>
          exfalso
          apply ht
          rw [__smtx_typeof.eq_136]
          simp [__smtx_typeof_choice_nth]

/-- Extracts inhabitation of the computed `choice_nth` type from a non-`None` typing judgment. -/
theorem choice_term_inhabited_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {n : native_Nat}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body n)) :
    type_inhabited (__smtx_typeof (SmtTerm.choice_nth s T body n)) := by
  refine ⟨__smtx_model_eval default_typed_model (SmtTerm.choice_nth s T body n), ?_⟩
  simpa using typeof_value_model_eval_choice_nth default_typed_model s T body n ht


end Smtm
