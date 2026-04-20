import Cpc.Proofs.TypePreservation.Model

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

/-- Shows that evaluating `boolean` terms produces values of the expected type. -/
theorem typeof_value_model_eval_boolean
    (M : SmtModel)
    (b : native_Bool) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Boolean b)) =
      __smtx_typeof (SmtTerm.Boolean b) := rfl

/-- Shows that evaluating `numeral` terms produces values of the expected type. -/
theorem typeof_value_model_eval_numeral
    (M : SmtModel)
    (n : native_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := rfl

/-- Shows that evaluating `rational` terms produces values of the expected type. -/
theorem typeof_value_model_eval_rational
    (M : SmtModel)
    (q : native_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := rfl

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
      change native_ite g (SmtType.BitVec (native_int_to_nat w)) SmtType.None = SmtType.None
      simp [native_ite, h]
  have hWidth : native_zleq 0 w = true := by
    cases h1 : native_zleq 0 w
    · simp [g, SmtEval.native_and, h1] at hg
    · rfl
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
    cases h2 : native_zeq n (native_mod_total n (native_int_pow2 w))
    · simp [g, SmtEval.native_and, hWidth, h2] at hg
    · rfl
  change native_ite (native_zleq 0 w) (SmtType.BitVec (native_int_to_nat w)) SmtType.None =
    __smtx_typeof (SmtTerm.Binary w n)
  rw [show native_ite (native_zleq 0 w) (SmtType.BitVec (native_int_to_nat w)) SmtType.None = SmtType.BitVec (native_int_to_nat w) by
    simp [native_ite, hWidth]]
  rw [show __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec (native_int_to_nat w) by
    simp [__smtx_typeof, native_ite, SmtEval.native_and, hWidth, hMod]]

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
      simpa [__smtx_typeof] using ht)
  change __smtx_typeof_value (__smtx_model_lookup M s T) =
    __smtx_typeof_guard_wf T T
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
      simpa [__smtx_typeof] using ht)
  change __smtx_typeof_value (__smtx_model_lookup M s T) =
    __smtx_typeof_guard_wf T T
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
  change __smtx_model_lookup M s T = SmtValue.NotValue
  exact model_total_typed_lookup_uninhabited hM s T hT

/-- Derives `model_eval_uconst` from `uninhabited`. -/
theorem model_eval_uconst_of_uninhabited
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : ¬ type_inhabited T) :
    __smtx_model_eval M (SmtTerm.UConst s T) = SmtValue.NotValue := by
  change __smtx_model_lookup M s T = SmtValue.NotValue
  exact model_total_typed_lookup_uninhabited hM s T hT

/-- Shows that evaluating `re_allchar` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_allchar
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_allchar) =
      __smtx_typeof SmtTerm.re_allchar := rfl

/-- Shows that evaluating `re_none` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_none
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_none) =
      __smtx_typeof SmtTerm.re_none := rfl

/-- Shows that evaluating `re_all` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_all
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_all) =
      __smtx_typeof SmtTerm.re_all := rfl

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
      simpa [__smtx_typeof] using ht)
  change __smtx_typeof_seq_value (SmtSeq.empty T) =
    __smtx_typeof_guard_wf T (SmtType.Seq T)
  simp [__smtx_typeof_seq_value, hGuard]

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
      simpa [__smtx_typeof] using ht)
  rw [show __smtx_model_eval M (SmtTerm.set_empty T) =
      SmtValue.Set (SmtMap.default T (SmtValue.Boolean false)) by rfl]
  rw [show __smtx_typeof (SmtTerm.set_empty T) =
      __smtx_typeof_guard_wf T (SmtType.Set T) by rfl]
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
  rw [show __smtx_typeof (SmtTerm.seq_unit t) = SmtType.Seq (__smtx_typeof t) by
    simp [__smtx_typeof, native_ite, native_Teq, ht]]
  rw [show __smtx_model_eval M (SmtTerm.seq_unit t) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M t)
          (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M t)))) by
    rfl]
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, native_ite, native_Teq, hpres]

/-- Shows that evaluating `set_singleton` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_singleton
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.set_singleton t)) =
      __smtx_typeof (SmtTerm.set_singleton t) := by
  unfold term_has_non_none_type at ht
  rw [show __smtx_typeof (SmtTerm.set_singleton t) =
      SmtType.Set (__smtx_typeof t) by
    simp [__smtx_typeof, native_ite, native_Teq, ht]]
  rw [show __smtx_model_eval M (SmtTerm.set_singleton t) =
      __smtx_model_eval_set_singleton (__smtx_model_eval M t) by rfl]
  simp [__smtx_model_eval_set_singleton, __smtx_typeof_value, __smtx_typeof_map_value,
    __smtx_map_to_set_type, native_ite, native_Teq, hpres]

/-- Derives `exists_body_bool` from `non_none`. -/
theorem exists_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht
  rfl

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
  change
    __smtx_typeof_value
      (if h :
          ∃ v : SmtValue,
            __smtx_typeof_value v = T ∧
              __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
        SmtValue.Boolean true
      else
        SmtValue.Boolean false) = SmtType.Bool
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
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht
  rfl

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
  change
    __smtx_typeof_value
      (if h :
          ∀ v : SmtValue,
            __smtx_typeof_value v = T ->
              __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
        SmtValue.Boolean true
      else
        SmtValue.Boolean false) = SmtType.Bool
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
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    ∃ v : SmtValue, __smtx_typeof_value v = T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [SmtTerm.choice, __smtx_typeof_choice_nth, native_ite, native_Teq, h] at ht
  · exact smtx_typeof_guard_wf_inhabited_of_non_none T T ht

/-- Derives `choice_term_typeof` from `non_none`. -/
theorem choice_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    __smtx_typeof (SmtTerm.choice s T body) = T := by
  have hTy := choice_term_has_witness ht
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [SmtTerm.choice, __smtx_typeof_choice_nth, native_ite, native_Teq, h] at ht ⊢
  · exact smtx_typeof_guard_wf_of_non_none T T ht

/-- Shows that evaluating `choice` terms produces values of the expected type. -/
theorem typeof_value_model_eval_choice
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.choice s T body)) =
      __smtx_typeof (SmtTerm.choice s T body) := by
  classical
  have hTy : ∃ v : SmtValue, __smtx_typeof_value v = T :=
    choice_term_has_witness ht
  rw [choice_term_typeof_of_non_none ht]
  change
    __smtx_typeof_value
      (if hSat :
          ∃ v : SmtValue,
            __smtx_typeof_value v = T ∧
              __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
        Classical.choose hSat
      else
        if hTy' : ∃ v : SmtValue, __smtx_typeof_value v = T then
          Classical.choose hTy'
        else
          SmtValue.NotValue) = T
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · simpa [hSat] using (Classical.choose_spec hSat).1
  · simpa [hSat, hTy] using Classical.choose_spec hTy


end Smtm
