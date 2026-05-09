import Lean
import CpcMini.Proofs.TypePreservation.Model

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

syntax "smtx_model_eval_choice_nth_eq_1" : term
syntax "smtx_model_eval_choice_nth_eq_2" : term

open Lean Elab Term Meta in
private def choiceNthEvalEqThm (idx : Nat) : TermElabM Expr := do
  let eqTy ← inferType (mkConst ``Smtm.__smtx_model_eval.eq_14)
  forallTelescopeReducing eqTy fun _ body => do
    let some (_, _, rhs) := body.eq? | throwError "unexpected __smtx_model_eval.eq_14 shape"
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
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

/-- Shows that evaluating `numeral` terms produces values of the expected type. -/
theorem typeof_value_model_eval_numeral
    (M : SmtModel)
    (n : native_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := by
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

/-- Shows that evaluating `rational` terms produces values of the expected type. -/
theorem typeof_value_model_eval_rational
    (M : SmtModel)
    (q : native_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := by
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

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
    by_cases h : g = true
    · exact h
    · exfalso
      apply ht
      simp [__smtx_typeof, g, native_ite, h]
  have hWidth : native_zleq 0 w = true := by
    cases h1 : native_zleq 0 w
    · simp [g, SmtEval.native_and, h1] at hg
    · rfl
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
    cases h2 : native_zeq n (native_mod_total n (native_int_pow2 w))
    · simp [g, SmtEval.native_and, hWidth, h2] at hg
    · rfl
  simp [__smtx_model_eval, __smtx_typeof_value, __smtx_typeof, native_ite, SmtEval.native_and, hWidth, hMod]

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
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  simpa [__smtx_model_eval, __smtx_typeof] using
    (Eq.trans (model_total_typed_lookup hM s T hT) hGuard.symm)

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
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  simpa [__smtx_model_eval, __smtx_typeof] using
    (Eq.trans (model_total_typed_lookup hM s T hT) hGuard.symm)

/-- Derives `model_eval_var` from `uninhabited`. -/
theorem model_eval_var_of_uninhabited
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : ¬ type_inhabited T) :
    __smtx_model_eval M (SmtTerm.Var s T) = SmtValue.NotValue := by
  simpa [__smtx_model_eval] using model_total_typed_lookup_uninhabited hM s T hT

/-- Derives `model_eval_uconst` from `uninhabited`. -/
theorem model_eval_uconst_of_uninhabited
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : ¬ type_inhabited T) :
    __smtx_model_eval M (SmtTerm.UConst s T) = SmtValue.NotValue := by
  simpa [__smtx_model_eval] using model_total_typed_lookup_uninhabited hM s T hT

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
  by_cases h :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v ∧
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · simp [__smtx_model_eval, __smtx_typeof_value, h]
  · simp [__smtx_model_eval, __smtx_typeof_value, h]

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
  by_cases h :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_value_canonical v ->
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · have hIf :
        (if h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_value_canonical v ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
          SmtValue.Boolean true
        else
          SmtValue.Boolean false) = SmtValue.Boolean true := by
        by_cases h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_value_canonical v ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
        · simpa using h'
        · contradiction
    rw [show __smtx_model_eval M (SmtTerm.forall s T body) =
        (if h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_value_canonical v ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
          SmtValue.Boolean true
        else
          SmtValue.Boolean false) by simp [__smtx_model_eval]]
    rw [hIf]
    rfl
  · have hIf :
        (if h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_value_canonical v ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
          SmtValue.Boolean true
        else
          SmtValue.Boolean false) = SmtValue.Boolean false := by
        by_cases h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_value_canonical v ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
        · contradiction
        · simp [h']
    rw [show __smtx_model_eval M (SmtTerm.forall s T body) =
        (if h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_value_canonical v ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
          SmtValue.Boolean true
        else
          SmtValue.Boolean false) by simp [__smtx_model_eval]]
    rw [hIf]
    rfl

/-- Provides a witness for `choice_nth` at depth `0`. -/
theorem choice_nth_zero_has_witness
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body native_nat_zero)) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, __smtx_typeof_choice_nth, native_ite, native_Teq, h] at ht ⊢
  · exact canonical_type_inhabited_of_type_inhabited
      (smtx_typeof_guard_wf_inhabited_of_non_none T T ht)

/-- Derives the type of `choice_nth` at depth `0`. -/
theorem choice_nth_zero_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body native_nat_zero)) :
    __smtx_typeof (SmtTerm.choice_nth s T body native_nat_zero) = T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, __smtx_typeof_choice_nth, native_ite, native_Teq, h] at ht ⊢
  · exact smtx_typeof_guard_wf_of_non_none T T ht

/-- Shows that evaluating `choice_nth` terms produces values of the expected type. -/
theorem typeof_value_model_eval_choice_nth
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (n : native_Nat)
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body n)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.choice_nth s T body n)) =
      __smtx_typeof (SmtTerm.choice_nth s T body n) := by
  induction n generalizing M s T body with
  | zero =>
      classical
      rw [choice_nth_zero_typeof_of_non_none ht]
      by_cases hSat :
          ∃ v : SmtValue,
            __smtx_typeof_value v = T ∧
              __smtx_value_canonical v ∧
              __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
      · rw [__smtx_model_eval.eq_14, smtx_model_eval_choice_nth_eq_1]
        simp [hSat]
        exact (Classical.choose_spec hSat).1
      · rw [__smtx_model_eval.eq_14, smtx_model_eval_choice_nth_eq_1]
        have hWitnessCanon := choice_nth_zero_has_witness ht
        simp [hSat, hWitnessCanon]
        exact (Classical.choose_spec hWitnessCanon).1
  | succ n ih =>
      classical
      cases body with
      | «exists» s' U F =>
          have hRec : term_has_non_none_type (SmtTerm.choice_nth s' U F n) := by
            simpa [term_has_non_none_type, __smtx_typeof, __smtx_typeof_choice_nth] using ht
          let v : SmtValue :=
            if hSat :
                ∃ v : SmtValue,
                  __smtx_typeof_value v = T ∧
                    __smtx_value_canonical v ∧
                    __smtx_model_eval (__smtx_model_push M s T v) (SmtTerm.exists s' U F) = SmtValue.Boolean true then
              Classical.choose hSat
            else if hTy : ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v then
              Classical.choose hTy
            else
              SmtValue.NotValue
          have ih' := ih (__smtx_model_push M s T v) s' U F hRec
          rw [__smtx_model_eval.eq_14, smtx_model_eval_choice_nth_eq_2]
          simpa [__smtx_model_eval.eq_14, smtx_model_eval_choice_nth_eq_2,
            __smtx_typeof, __smtx_typeof_choice_nth, v] using ih'
      | _ =>
          exfalso
          simp [term_has_non_none_type, __smtx_typeof, __smtx_typeof_choice_nth] at ht

end Smtm
