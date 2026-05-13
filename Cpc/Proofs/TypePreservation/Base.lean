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
  let eqTy ← inferType (mkConst ``Smtm.__smtx_model_eval.eq_137)
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
    have hAnd :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) = true := by
      simp [SmtEval.native_and, hWidth, hMod]
    unfold __smtx_typeof
    simp [hAnd, native_ite]
  rw [hType]
  unfold __smtx_model_eval __smtx_typeof_value
  simp [native_ite, SmtEval.native_and, hWidth, hMod]

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

/-- If a variable has sequence type `Seq A`, then `A` is non-`None`. -/
theorem var_type_eq_seq_component_non_none
    {s : native_String}
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.Var s T) = SmtType.Seq A) :
    A ≠ SmtType.None := by
  rw [__smtx_typeof.eq_142] at h
  exact smtx_typeof_guard_wf_self_eq_seq_component_non_none h

/-- If a variable has set type `Set A`, then `A` is non-`None`. -/
theorem var_type_eq_set_component_non_none
    {s : native_String}
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.Var s T) = SmtType.Set A) :
    A ≠ SmtType.None := by
  rw [__smtx_typeof.eq_142] at h
  exact smtx_typeof_guard_wf_self_eq_set_component_non_none h

/-- If a variable has map type `Map A B`, then both components are non-`None`. -/
theorem var_type_eq_map_components_non_none
    {s : native_String}
    {T A B : SmtType}
    (h : __smtx_typeof (SmtTerm.Var s T) = SmtType.Map A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  rw [__smtx_typeof.eq_142] at h
  exact smtx_typeof_guard_wf_self_eq_map_components_non_none h

/-- If a variable has function type `FunType A B`, then both components are non-`None`. -/
theorem var_type_eq_fun_components_non_none
    {s : native_String}
    {T A B : SmtType}
    (h : __smtx_typeof (SmtTerm.Var s T) = SmtType.FunType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  rw [__smtx_typeof.eq_142] at h
  exact smtx_typeof_guard_wf_self_eq_fun_components_non_none h

/-- If a uconst has sequence type `Seq A`, then `A` is non-`None`. -/
theorem uconst_type_eq_seq_component_non_none
    {s : native_String}
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.Seq A) :
    A ≠ SmtType.None := by
  rw [__smtx_typeof.eq_143] at h
  exact smtx_typeof_guard_wf_self_eq_seq_component_non_none h

/-- If a uconst has set type `Set A`, then `A` is non-`None`. -/
theorem uconst_type_eq_set_component_non_none
    {s : native_String}
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.Set A) :
    A ≠ SmtType.None := by
  rw [__smtx_typeof.eq_143] at h
  exact smtx_typeof_guard_wf_self_eq_set_component_non_none h

/-- If a uconst has map type `Map A B`, then both components are non-`None`. -/
theorem uconst_type_eq_map_components_non_none
    {s : native_String}
    {T A B : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.Map A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  rw [__smtx_typeof.eq_143] at h
  exact smtx_typeof_guard_wf_self_eq_map_components_non_none h

/-- If a uconst has function type `FunType A B`, then both components are non-`None`. -/
theorem uconst_type_eq_fun_components_non_none
    {s : native_String}
    {T A B : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.FunType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  rw [__smtx_typeof.eq_143] at h
  exact smtx_typeof_guard_wf_self_eq_fun_components_non_none h

/-- If `seq_empty` has type `Seq A`, then `A` is non-`None`. -/
theorem seq_empty_type_eq_component_non_none
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq A) :
    A ≠ SmtType.None := by
  have hNN : term_has_non_none_type (SmtTerm.seq_empty T) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuardNN : __smtx_typeof_guard_wf T (SmtType.Seq T) ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    rw [__smtx_typeof.eq_78] at hNN
    exact hNN
  have hGuardEq : __smtx_typeof_guard_wf T (SmtType.Seq T) = SmtType.Seq A := by
    rw [__smtx_typeof.eq_78] at h
    exact h
  have hGuard : __smtx_typeof_guard_wf T (SmtType.Seq T) = SmtType.Seq T :=
    smtx_typeof_guard_wf_of_non_none T (SmtType.Seq T) hGuardNN
  have hEq : T = A := by
    have hSeq : SmtType.Seq T = SmtType.Seq A := hGuard.symm.trans hGuardEq
    injection hSeq with hEq
  cases hEq
  exact type_wf_non_none (smtx_typeof_guard_wf_wf_of_non_none T (SmtType.Seq T) hGuardNN)

/-- If `set_empty` has type `Set A`, then `A` is non-`None`. -/
theorem set_empty_type_eq_component_non_none
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.set_empty T) = SmtType.Set A) :
    A ≠ SmtType.None := by
  have hNN : term_has_non_none_type (SmtTerm.set_empty T) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuardNN : __smtx_typeof_guard_wf T (SmtType.Set T) ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    rw [__smtx_typeof.eq_121] at hNN
    exact hNN
  have hGuardEq : __smtx_typeof_guard_wf T (SmtType.Set T) = SmtType.Set A := by
    rw [__smtx_typeof.eq_121] at h
    exact h
  have hGuard : __smtx_typeof_guard_wf T (SmtType.Set T) = SmtType.Set T :=
    smtx_typeof_guard_wf_of_non_none T (SmtType.Set T) hGuardNN
  have hEq : T = A := by
    have hSet : SmtType.Set T = SmtType.Set A := hGuard.symm.trans hGuardEq
    injection hSet with hEq
  cases hEq
  exact type_wf_non_none (smtx_typeof_guard_wf_wf_of_non_none T (SmtType.Set T) hGuardNN)

/-- If `seq_unit t` has type `Seq A`, then `t` has type `A` and `A` is non-`None`. -/
theorem seq_unit_type_eq_arg_of_eq
    {t : SmtTerm}
    {A : SmtType}
    (h : __smtx_typeof (SmtTerm.seq_unit t) = SmtType.Seq A) :
    __smtx_typeof t = A ∧ A ≠ SmtType.None := by
  rw [__smtx_typeof.eq_119] at h
  have hGuardNN :
      __smtx_typeof_guard_wf (__smtx_typeof t)
          (SmtType.Seq (__smtx_typeof t)) ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuard :
      __smtx_typeof_guard_wf (__smtx_typeof t)
          (SmtType.Seq (__smtx_typeof t)) =
        SmtType.Seq (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (__smtx_typeof t)
      (SmtType.Seq (__smtx_typeof t)) hGuardNN
  have hSeq : SmtType.Seq (__smtx_typeof t) = SmtType.Seq A :=
    hGuard.symm.trans h
  injection hSeq with hEq
  subst hEq
  exact ⟨rfl,
    type_wf_non_none
      (smtx_typeof_guard_wf_wf_of_non_none (__smtx_typeof t)
        (SmtType.Seq (__smtx_typeof t)) hGuardNN)⟩

/-- If `set_singleton t` has type `Set A`, then `t` has type `A` and `A` is non-`None`. -/
theorem set_singleton_type_eq_arg_of_eq
    {t : SmtTerm}
    {A : SmtType}
    (h : __smtx_typeof (SmtTerm.set_singleton t) = SmtType.Set A) :
    __smtx_typeof t = A ∧ A ≠ SmtType.None := by
  rw [__smtx_typeof.eq_122] at h
  have hGuardNN :
      __smtx_typeof_guard_wf (__smtx_typeof t)
          (SmtType.Set (__smtx_typeof t)) ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuard :
      __smtx_typeof_guard_wf (__smtx_typeof t)
          (SmtType.Set (__smtx_typeof t)) =
        SmtType.Set (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (__smtx_typeof t)
      (SmtType.Set (__smtx_typeof t)) hGuardNN
  have hSet : SmtType.Set (__smtx_typeof t) = SmtType.Set A :=
    hGuard.symm.trans h
  injection hSet with hEq
  subst hEq
  exact ⟨rfl,
    type_wf_non_none
      (smtx_typeof_guard_wf_wf_of_non_none (__smtx_typeof t)
        (SmtType.Set (__smtx_typeof t)) hGuardNN)⟩

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
    (ht : term_has_non_none_type (SmtTerm.seq_unit t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_unit t)) =
      __smtx_typeof (SmtTerm.seq_unit t) := by
  have hGuard :
      __smtx_typeof_guard_wf (__smtx_typeof t)
          (SmtType.Seq (__smtx_typeof t)) =
        SmtType.Seq (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (__smtx_typeof t)
      (SmtType.Seq (__smtx_typeof t)) (by
        unfold term_has_non_none_type at ht
        rw [__smtx_typeof.eq_119] at ht
        exact ht)
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, hpres, hGuard,
    native_Teq, native_ite]

/-- Shows that evaluating `set_singleton` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_singleton
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.set_singleton t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.set_singleton t)) =
      __smtx_typeof (SmtTerm.set_singleton t) := by
  have hGuard :
      __smtx_typeof_guard_wf (__smtx_typeof t)
          (SmtType.Set (__smtx_typeof t)) =
        SmtType.Set (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (__smtx_typeof t)
      (SmtType.Set (__smtx_typeof t)) (by
        unfold term_has_non_none_type at ht
        rw [__smtx_typeof.eq_122] at ht
        exact ht)
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_model_eval_set_singleton, __smtx_typeof_value, __smtx_typeof_map_value,
    __smtx_map_to_set_type, hpres, hGuard, native_Teq, native_ite]

/-- Derives `exists_body_bool` from `non_none`. -/
theorem exists_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [hEqFalse, native_ite]
  simpa [native_Teq] using hEq

/-- Derives `exists_term_typeof` from `non_none`. -/
theorem exists_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool := by
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    simpa [native_Teq] using exists_body_bool_of_non_none ht
  unfold __smtx_typeof
  simp [hEq, native_ite]

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
          __smtx_value_canonical_bool v = true ∧
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
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [hEqFalse, native_ite]
  simpa [native_Teq] using hEq

/-- Derives `forall_term_typeof` from `non_none`. -/
theorem forall_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof (SmtTerm.forall s T body) = SmtType.Bool := by
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    simpa [native_Teq] using forall_body_bool_of_non_none ht
  unfold __smtx_typeof
  simp [hEq, native_ite]

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
          __smtx_value_canonical_bool v = true ->
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · simp [dif_pos h, __smtx_typeof_value]
  · simp [dif_neg h, __smtx_typeof_value]

/-- Provides a witness for `choice_term_has`. -/
theorem choice_term_has_witness
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [__smtx_typeof_choice_nth, hEqFalse, native_ite]
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold __smtx_typeof at ht
    simpa [__smtx_typeof_choice_nth, hEq, native_ite] using ht
  exact canonical_type_inhabited_of_type_inhabited
    (smtx_typeof_guard_wf_inhabited_of_non_none T T hGuardNN)

/-- Derives the zero-index `choice_nth` type as the self-guarded choice type from `non_none`. -/
theorem choice_term_guard_type_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    __smtx_typeof (SmtTerm.choice_nth s T body 0) = __smtx_typeof_guard_wf T T := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [__smtx_typeof_choice_nth, hEqFalse, native_ite]
  unfold __smtx_typeof
  simp [__smtx_typeof_choice_nth, hEq, native_ite]

/-- Derives `choice_term_typeof` from `non_none`. -/
theorem choice_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    __smtx_typeof (SmtTerm.choice_nth s T body 0) = T := by
  have hGuard : __smtx_typeof (SmtTerm.choice_nth s T body 0) = __smtx_typeof_guard_wf T T :=
    choice_term_guard_type_of_non_none ht
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    unfold term_has_non_none_type at ht
    apply ht
    rw [hGuard, hNone]
  exact hGuard.trans (smtx_typeof_guard_wf_of_non_none T T hGuardNN)

/-- If a `choice_nth` term has sequence type `Seq A`, then `A` is non-`None`. -/
theorem choice_term_seq_component_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {n : native_Nat}
    {A : SmtType}
    (h : __smtx_typeof (SmtTerm.choice_nth s T body n) = SmtType.Seq A) :
    A ≠ SmtType.None := by
  induction n generalizing s T body with
  | zero =>
      have hNN : term_has_non_none_type (SmtTerm.choice_nth s T body 0) := by
        unfold term_has_non_none_type
        intro hNone
        rw [hNone] at h
        simp at h
      have hGuard : __smtx_typeof_guard_wf T T = SmtType.Seq A := by
        calc
          __smtx_typeof_guard_wf T T = __smtx_typeof (SmtTerm.choice_nth s T body 0) := by
            symm
            exact choice_term_guard_type_of_non_none hNN
          _ = SmtType.Seq A := h
      exact smtx_typeof_guard_wf_self_eq_seq_component_non_none hGuard
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof (SmtTerm.choice_nth s T (SmtTerm.exists s' U body') (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_137, __smtx_typeof.eq_137]
            simp [__smtx_typeof_choice_nth]
          exact ih (s := s') (T := U) (body := body') (by simpa [hTyEq] using h)
      | _ =>
          exfalso
          rw [__smtx_typeof.eq_137] at h
          simp [__smtx_typeof_choice_nth] at h

/-- If a `choice_nth` term has set type `Set A`, then `A` is non-`None`. -/
theorem choice_term_set_component_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {n : native_Nat}
    {A : SmtType}
    (h : __smtx_typeof (SmtTerm.choice_nth s T body n) = SmtType.Set A) :
    A ≠ SmtType.None := by
  induction n generalizing s T body with
  | zero =>
      have hNN : term_has_non_none_type (SmtTerm.choice_nth s T body 0) := by
        unfold term_has_non_none_type
        intro hNone
        rw [hNone] at h
        simp at h
      have hGuard : __smtx_typeof_guard_wf T T = SmtType.Set A := by
        calc
          __smtx_typeof_guard_wf T T = __smtx_typeof (SmtTerm.choice_nth s T body 0) := by
            symm
            exact choice_term_guard_type_of_non_none hNN
          _ = SmtType.Set A := h
      exact smtx_typeof_guard_wf_self_eq_set_component_non_none hGuard
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof (SmtTerm.choice_nth s T (SmtTerm.exists s' U body') (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_137, __smtx_typeof.eq_137]
            simp [__smtx_typeof_choice_nth]
          exact ih (s := s') (T := U) (body := body') (by simpa [hTyEq] using h)
      | _ =>
          exfalso
          rw [__smtx_typeof.eq_137] at h
          simp [__smtx_typeof_choice_nth] at h

/-- If a `choice_nth` term has map type `Map A B`, then both components are non-`None`. -/
theorem choice_term_map_components_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {n : native_Nat}
    {A B : SmtType}
    (h : __smtx_typeof (SmtTerm.choice_nth s T body n) = SmtType.Map A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  induction n generalizing s T body with
  | zero =>
      have hNN : term_has_non_none_type (SmtTerm.choice_nth s T body 0) := by
        unfold term_has_non_none_type
        intro hNone
        rw [hNone] at h
        simp at h
      have hGuard : __smtx_typeof_guard_wf T T = SmtType.Map A B := by
        calc
          __smtx_typeof_guard_wf T T = __smtx_typeof (SmtTerm.choice_nth s T body 0) := by
            symm
            exact choice_term_guard_type_of_non_none hNN
          _ = SmtType.Map A B := h
      exact smtx_typeof_guard_wf_self_eq_map_components_non_none hGuard
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof (SmtTerm.choice_nth s T (SmtTerm.exists s' U body') (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_137, __smtx_typeof.eq_137]
            simp [__smtx_typeof_choice_nth]
          exact ih (s := s') (T := U) (body := body') (by simpa [hTyEq] using h)
      | _ =>
          exfalso
          rw [__smtx_typeof.eq_137] at h
          simp [__smtx_typeof_choice_nth] at h

/-- If a `choice_nth` term has function type `FunType A B`, then both components are non-`None`. -/
theorem choice_term_fun_components_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {n : native_Nat}
    {A B : SmtType}
    (h : __smtx_typeof (SmtTerm.choice_nth s T body n) = SmtType.FunType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  induction n generalizing s T body with
  | zero =>
      have hNN : term_has_non_none_type (SmtTerm.choice_nth s T body 0) := by
        unfold term_has_non_none_type
        intro hNone
        rw [hNone] at h
        simp at h
      have hGuard : __smtx_typeof_guard_wf T T = SmtType.FunType A B := by
        calc
          __smtx_typeof_guard_wf T T = __smtx_typeof (SmtTerm.choice_nth s T body 0) := by
            symm
            exact choice_term_guard_type_of_non_none hNN
          _ = SmtType.FunType A B := h
      exact smtx_typeof_guard_wf_self_eq_fun_components_non_none hGuard
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof (SmtTerm.choice_nth s T (SmtTerm.exists s' U body') (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_137, __smtx_typeof.eq_137]
            simp [__smtx_typeof_choice_nth]
          exact ih (s := s') (T := U) (body := body') (by simpa [hTyEq] using h)
      | _ =>
          exfalso
          rw [__smtx_typeof.eq_137] at h
          simp [__smtx_typeof_choice_nth] at h

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
  have hTy : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
      __smtx_value_canonical_bool v = true := by
    rcases choice_term_has_witness ht with ⟨v, hvTy, hvCanon⟩
    exact ⟨v, hvTy, by simpa [__smtx_value_canonical] using hvCanon⟩
  have hTyIf : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
      __smtx_value_canonical_bool v := by
    rcases hTy with ⟨v, hvTy, hvCanon⟩
    exact ⟨v, hvTy, by simpa [hvCanon]⟩
  rw [choice_term_typeof_of_non_none ht]
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · rw [__smtx_model_eval.eq_137, smtx_model_eval_choice_nth_eq_1]
    simp [hSat]
    exact (Classical.choose_spec hSat).1
  · rw [__smtx_model_eval.eq_137, smtx_model_eval_choice_nth_eq_1]
    simp [hSat, hTyIf]
    exact (Classical.choose_spec hTy).1

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
            rw [__smtx_typeof.eq_137, __smtx_typeof.eq_137]
            simp [__smtx_typeof_choice_nth]
          have ht' : term_has_non_none_type (SmtTerm.choice_nth s' U body' n) := by
            unfold term_has_non_none_type
            rw [← hTyEq]
            exact ht
          rw [__smtx_model_eval.eq_137, smtx_model_eval_choice_nth_eq_2]
          rw [hTyEq]
          simpa [__smtx_model_eval.eq_137,
            smtx_model_eval_choice_nth_eq_1, smtx_model_eval_choice_nth_eq_2] using
            ih (__smtx_model_push M s T
              (if hSat :
                  ∃ v : SmtValue,
                    __smtx_typeof_value v = T ∧
                      __smtx_value_canonical_bool v = true ∧
                      __smtx_model_eval (__smtx_model_push M s T v)
                        (SmtTerm.exists s' U body') = SmtValue.Boolean true then
                Classical.choose hSat
              else
                if hTy : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
                    __smtx_value_canonical_bool v then
                  Classical.choose hTy
                else
                  SmtValue.NotValue)) s' U body' ht'
      | _ =>
          exfalso
          apply ht
          rw [__smtx_typeof.eq_137]
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
