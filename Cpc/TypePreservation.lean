import Cpc.SmtModel

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

def model_total_typed (M : SmtModel) : Prop :=
  ∀ s T, __smtx_typeof_value (__smtx_model_lookup M s T) = T

def model_typed_at (M : SmtModel) (s : smt_lit_String) (T : SmtType) : Prop :=
  __smtx_typeof_value (__smtx_model_lookup M s T) = T

inductive supported_preservation_term : SmtTerm -> Prop
  | boolean (b : smt_lit_Bool) : supported_preservation_term (SmtTerm.Boolean b)
  | numeral (n : smt_lit_Int) : supported_preservation_term (SmtTerm.Numeral n)
  | rational (q : smt_lit_Rat) : supported_preservation_term (SmtTerm.Rational q)
  | var (s : smt_lit_String) (T : SmtType) : supported_preservation_term (SmtTerm.Var s T)
  | uconst (s : smt_lit_String) (T : SmtType) : supported_preservation_term (SmtTerm.UConst s T)

theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_lookup M s T) = T :=
  hM s T

theorem model_typed_at_push
    {M : SmtModel}
    {s : smt_lit_String}
    {T : SmtType}
    {v : SmtValue}
    (hv : __smtx_typeof_value v = T) :
    model_typed_at (__smtx_model_push M s T v) s T := by
  unfold model_typed_at __smtx_model_lookup __smtx_model_push
  simp [__smtx_model_key, hv]

theorem model_total_typed_push
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType)
    (v : SmtValue)
    (hv : __smtx_typeof_value v = T) :
    model_total_typed (__smtx_model_push M s T v) := by
  intro s' T'
  unfold __smtx_model_lookup __smtx_model_push
  by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
  · cases h
    simp [hv]
  · simp [h]
    exact hM s' T'

theorem typeof_value_model_eval_boolean
    (M : SmtModel)
    (b : smt_lit_Bool) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Boolean b)) =
      __smtx_typeof (SmtTerm.Boolean b) := rfl

theorem typeof_value_model_eval_numeral
    (M : SmtModel)
    (n : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := rfl

theorem typeof_value_model_eval_rational
    (M : SmtModel)
    (q : smt_lit_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := rfl

theorem typeof_value_model_eval_var
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Var s T)) =
      __smtx_typeof (SmtTerm.Var s T) := by
  change __smtx_typeof_value (__smtx_model_lookup M s T) = T
  exact hM s T

theorem typeof_value_model_eval_uconst
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.UConst s T)) =
      __smtx_typeof (SmtTerm.UConst s T) := by
  change __smtx_typeof_value (__smtx_model_lookup M s T) = T
  exact hM s T

theorem supported_type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (_ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  cases hs with
  | boolean b =>
      exact typeof_value_model_eval_boolean M b
  | numeral n =>
      exact typeof_value_model_eval_numeral M n
  | rational q =>
      exact typeof_value_model_eval_rational M q
  | var s T =>
      exact typeof_value_model_eval_var M hM s T
  | uconst s T =>
      exact typeof_value_model_eval_uconst M hM s T

theorem typeof_value_model_eval_re_allchar
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_allchar) =
      __smtx_typeof SmtTerm.re_allchar := rfl

theorem typeof_value_model_eval_re_none
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_none) =
      __smtx_typeof SmtTerm.re_none := rfl

theorem typeof_value_model_eval_re_all
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_all) =
      __smtx_typeof SmtTerm.re_all := rfl

theorem typeof_value_model_eval_seq_empty
    (M : SmtModel)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_empty T)) =
      __smtx_typeof (SmtTerm.seq_empty T) := rfl

theorem typeof_value_model_eval_set_empty
    (M : SmtModel)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.set_empty T)) =
      __smtx_typeof (SmtTerm.set_empty T) := rfl

theorem typeof_value_model_eval_seq_unit
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.seq_unit t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.seq_unit t) := by
  unfold term_has_non_none_type at ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.seq_unit t) = SmtType.Seq (__smtx_typeof t) by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, ht]]
  rw [show __smtx_model_eval M (SmtTerm.Apply SmtTerm.seq_unit t) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M t)
          (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M t)))) by
    rfl]
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, smt_lit_ite, smt_lit_Teq, hpres]

theorem typeof_value_model_eval_set_singleton
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.set_singleton t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.set_singleton t) := by
  unfold term_has_non_none_type at ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.set_singleton t) =
      SmtType.Map (__smtx_typeof t) SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, ht]]
  rw [show __smtx_model_eval M (SmtTerm.Apply SmtTerm.set_singleton t) =
      SmtValue.Map
        (SmtMap.cons (__smtx_model_eval M t) (SmtValue.Boolean true)
          (SmtMap.default (__smtx_typeof_value (__smtx_model_eval M t)) (SmtValue.Boolean false))) by
    rfl]
  simp [__smtx_typeof_value, __smtx_typeof_map_value, smt_lit_ite, smt_lit_Teq, hpres]

theorem exists_body_bool_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.exists s T) body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  rfl

theorem exists_term_typeof_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.exists s T) body)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.exists s T) body) = SmtType.Bool := by
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, exists_body_bool_of_non_none ht]

theorem typeof_value_model_eval_exists
    (M : SmtModel)
    (s : smt_lit_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.exists s T) body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.exists s T) body)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.exists s T) body) := by
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

theorem forall_body_bool_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.forall s T) body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  rfl

theorem forall_term_typeof_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.forall s T) body)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.forall s T) body) = SmtType.Bool := by
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, forall_body_bool_of_non_none ht]

theorem typeof_value_model_eval_forall
    (M : SmtModel)
    (s : smt_lit_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.forall s T) body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.forall s T) body)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.forall s T) body) := by
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

theorem choice_term_has_witness
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.choice s T) body)) :
    ∃ v : SmtValue, __smtx_typeof_value v = T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  exact ht.1

theorem choice_term_typeof_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.choice s T) body)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.choice s T) body) = T := by
  have hTy := choice_term_has_witness ht
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h, hTy] at ht ⊢

theorem typeof_value_model_eval_choice
    (M : SmtModel)
    (s : smt_lit_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.choice s T) body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.choice s T) body)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.choice s T) body) := by
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

def fake_bool_value : SmtValue :=
  SmtValue.Apply
    (SmtValue.Map (SmtMap.default SmtType.Int (SmtValue.Boolean false)))
    (SmtValue.Numeral 0)

theorem fake_bool_value_typeof :
    __smtx_typeof_value fake_bool_value = SmtType.Bool := by
  native_decide

def fake_int_value : SmtValue :=
  SmtValue.Apply
    (SmtValue.Map (SmtMap.default SmtType.Int (SmtValue.Numeral 0)))
    (SmtValue.Numeral 0)

theorem fake_int_value_typeof :
    __smtx_typeof_value fake_int_value = SmtType.Int := by
  native_decide

def fake_real_value : SmtValue :=
  SmtValue.Apply
    (SmtValue.Map (SmtMap.default SmtType.Int (SmtValue.Rational 0)))
    (SmtValue.Numeral 0)

theorem fake_real_value_typeof :
    __smtx_typeof_value fake_real_value = SmtType.Real := by
  native_decide

def local_typed_bool_model : SmtModel :=
  __smtx_model_push SmtModel.empty "b" SmtType.Bool fake_bool_value

theorem local_typed_bool_model_typed :
    model_typed_at local_typed_bool_model "b" SmtType.Bool := by
  simpa [local_typed_bool_model] using
    (model_typed_at_push (M := SmtModel.empty) (s := "b") (T := SmtType.Bool)
      (v := fake_bool_value) fake_bool_value_typeof)

def preservation_counterexample_not_var : SmtTerm :=
  SmtTerm.Apply SmtTerm.not (SmtTerm.Var "b" SmtType.Bool)

theorem preservation_counterexample_not_var_typeof :
    __smtx_typeof preservation_counterexample_not_var = SmtType.Bool := by
  rfl

theorem preservation_counterexample_not_var_eval_value :
    __smtx_model_eval local_typed_bool_model preservation_counterexample_not_var =
      SmtValue.NotValue := by
  change __smtx_model_eval_not (__smtx_model_lookup local_typed_bool_model "b" SmtType.Bool) =
    SmtValue.NotValue
  have hLookup :
      __smtx_model_lookup local_typed_bool_model "b" SmtType.Bool = fake_bool_value := by
    unfold local_typed_bool_model __smtx_model_lookup __smtx_model_push
    simp [__smtx_model_key]
  rw [hLookup]
  rfl

theorem preservation_counterexample_not_var_eval :
    __smtx_typeof_value (__smtx_model_eval local_typed_bool_model preservation_counterexample_not_var) =
      SmtType.None := by
  rw [preservation_counterexample_not_var_eval_value]
  rfl

def local_typed_int_model : SmtModel :=
  __smtx_model_push SmtModel.empty "i" SmtType.Int fake_int_value

theorem local_typed_int_model_typed :
    model_typed_at local_typed_int_model "i" SmtType.Int := by
  simpa [local_typed_int_model] using
    (model_typed_at_push (M := SmtModel.empty) (s := "i") (T := SmtType.Int)
      (v := fake_int_value) fake_int_value_typeof)

def preservation_counterexample_plus_var : SmtTerm :=
  SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus (SmtTerm.Var "i" SmtType.Int)) (SmtTerm.Numeral 1)

theorem preservation_counterexample_plus_var_typeof :
    __smtx_typeof preservation_counterexample_plus_var = SmtType.Int := by
  rfl

theorem preservation_counterexample_plus_var_eval_value :
    __smtx_model_eval local_typed_int_model preservation_counterexample_plus_var =
      SmtValue.NotValue := by
  change
    __smtx_model_eval_plus (__smtx_model_lookup local_typed_int_model "i" SmtType.Int)
      (SmtValue.Numeral 1) = SmtValue.NotValue
  have hLookup :
      __smtx_model_lookup local_typed_int_model "i" SmtType.Int = fake_int_value := by
    unfold local_typed_int_model __smtx_model_lookup __smtx_model_push
    simp [__smtx_model_key]
  rw [hLookup]
  rfl

theorem preservation_counterexample_plus_var_eval :
    __smtx_typeof_value (__smtx_model_eval local_typed_int_model preservation_counterexample_plus_var) =
      SmtType.None := by
  rw [preservation_counterexample_plus_var_eval_value]
  rfl

def local_typed_real_model : SmtModel :=
  __smtx_model_push SmtModel.empty "r" SmtType.Real fake_real_value

theorem local_typed_real_model_typed :
    model_typed_at local_typed_real_model "r" SmtType.Real := by
  simpa [local_typed_real_model] using
    (model_typed_at_push (M := SmtModel.empty) (s := "r") (T := SmtType.Real)
      (v := fake_real_value) fake_real_value_typeof)

def preservation_counterexample_to_int_var : SmtTerm :=
  SmtTerm.Apply SmtTerm.to_int (SmtTerm.Var "r" SmtType.Real)

theorem preservation_counterexample_to_int_var_typeof :
    __smtx_typeof preservation_counterexample_to_int_var = SmtType.Int := by
  rfl

theorem preservation_counterexample_to_int_var_eval_value :
    __smtx_model_eval local_typed_real_model preservation_counterexample_to_int_var =
      SmtValue.NotValue := by
  change __smtx_model_eval_to_int (__smtx_model_lookup local_typed_real_model "r" SmtType.Real) =
    SmtValue.NotValue
  have hLookup :
      __smtx_model_lookup local_typed_real_model "r" SmtType.Real = fake_real_value := by
    unfold local_typed_real_model __smtx_model_lookup __smtx_model_push
    simp [__smtx_model_key]
  rw [hLookup]
  rfl

theorem preservation_counterexample_to_int_var_eval :
    __smtx_typeof_value (__smtx_model_eval local_typed_real_model preservation_counterexample_to_int_var) =
      SmtType.None := by
  rw [preservation_counterexample_to_int_var_eval_value]
  rfl

def preservation_counterexample_exists : SmtTerm :=
  SmtTerm.Apply (SmtTerm.exists "x" SmtType.Bool) (SmtTerm.Numeral 0)

theorem preservation_counterexample_exists_typeof :
    __smtx_typeof preservation_counterexample_exists = SmtType.None := by
  rfl

theorem preservation_counterexample_exists_excluded :
    ¬ term_has_non_none_type preservation_counterexample_exists := by
  simp [term_has_non_none_type, preservation_counterexample_exists_typeof]

theorem preservation_counterexample_exists_eval :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_exists) =
      SmtType.Bool := by
  classical
  have hnot :
      ¬ ∃ v : SmtValue,
        __smtx_typeof_value v = SmtType.Bool ∧
          __smtx_model_eval (__smtx_model_push SmtModel.empty "x" SmtType.Bool v)
            (SmtTerm.Numeral 0) = SmtValue.Boolean true := by
    intro h
    rcases h with ⟨v, _, hv⟩
    change SmtValue.Numeral 0 = SmtValue.Boolean true at hv
    cases hv
  change
    __smtx_typeof_value
      (if h :
          ∃ v : SmtValue,
            __smtx_typeof_value v = SmtType.Bool ∧
              __smtx_model_eval (__smtx_model_push SmtModel.empty "x" SmtType.Bool v)
                (SmtTerm.Numeral 0) = SmtValue.Boolean true then
        SmtValue.Boolean true
      else
        SmtValue.Boolean false) = SmtType.Bool
  simp [hnot, __smtx_typeof_value]

def returns_type_ref (s : smt_lit_String) : SmtType -> Prop
  | SmtType.Map _ U => returns_type_ref s U
  | SmtType.TypeRef s' => s' = s
  | _ => False

theorem returns_type_ref_of_apply_value
    {s : smt_lit_String}
    {T U : SmtType}
    (h : returns_type_ref s (__smtx_typeof_apply_value T U)) :
    returns_type_ref s T := by
  cases T with
  | Map T1 U1 =>
      cases hNone : smt_lit_Teq T1 SmtType.None <;>
      cases hEq : smt_lit_Teq T1 U <;>
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, smt_lit_ite,
        returns_type_ref, hNone, hEq] at h ⊢
      exact h
  | _ =>
      exfalso
      simp [__smtx_typeof_apply_value, returns_type_ref] at h

theorem typeof_dt_cons_value_rec_zero_not_returns_type_ref
    (s : smt_lit_String)
    (T : SmtType)
    (hT : ¬ returns_type_ref s T) :
    ∀ c d, ¬ returns_type_ref s (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) smt_lit_nat_zero)
  | SmtDatatypeCons.unit, d => by
      simpa [__smtx_typeof_dt_cons_value_rec] using hT
  | SmtDatatypeCons.cons U c, d => by
      simpa [__smtx_typeof_dt_cons_value_rec, returns_type_ref] using
        typeof_dt_cons_value_rec_zero_not_returns_type_ref s T hT c d

theorem typeof_dt_cons_value_rec_not_returns_type_ref
    (s : smt_lit_String)
    (T : SmtType)
    (hT : ¬ returns_type_ref s T) :
    ∀ d n, ¬ returns_type_ref s (__smtx_typeof_dt_cons_value_rec T d n)
  | SmtDatatype.null, n => by
      cases n <;> simp [__smtx_typeof_dt_cons_value_rec, returns_type_ref]
  | SmtDatatype.sum c d, smt_lit_nat_zero =>
      typeof_dt_cons_value_rec_zero_not_returns_type_ref s T hT c d
  | SmtDatatype.sum c d, smt_lit_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_not_returns_type_ref s T hT d n

mutual

theorem typeof_value_not_returns_type_ref
    (s : smt_lit_String) :
    ∀ v : SmtValue, ¬ returns_type_ref s (__smtx_typeof_value v)
  | SmtValue.NotValue => by
      simp [__smtx_typeof_value, returns_type_ref]
  | SmtValue.Boolean _ => by
      simp [__smtx_typeof_value, returns_type_ref]
  | SmtValue.Numeral _ => by
      simp [__smtx_typeof_value, returns_type_ref]
  | SmtValue.Rational _ => by
      simp [__smtx_typeof_value, returns_type_ref]
  | SmtValue.Binary w _ => by
      cases hWidth : smt_lit_zleq 0 w <;>
      simp [__smtx_typeof_value, smt_lit_ite, returns_type_ref, hWidth]
  | SmtValue.Map m =>
      typeof_map_value_not_returns_type_ref s m
  | SmtValue.Seq ss =>
      typeof_seq_value_not_returns_type_ref s ss
  | SmtValue.Char _ => by
      simp [__smtx_typeof_value, returns_type_ref]
  | SmtValue.RegLan _ => by
      simp [__smtx_typeof_value, returns_type_ref]
  | SmtValue.DtCons s' d i => by
      simpa [returns_type_ref] using
        typeof_dt_cons_value_rec_not_returns_type_ref s (SmtType.Datatype s' d)
          (by simp [returns_type_ref]) (__smtx_dt_substitute s' d d) i
  | SmtValue.Apply f v => by
      intro h
      exact typeof_value_not_returns_type_ref s f (returns_type_ref_of_apply_value h)

theorem typeof_map_value_not_returns_type_ref
    (s : smt_lit_String) :
    ∀ m : SmtMap, ¬ returns_type_ref s (__smtx_typeof_map_value m)
  | SmtMap.cons i e m => by
      cases hEq : smt_lit_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
          (__smtx_typeof_map_value m) <;>
        simp [__smtx_typeof_map_value, smt_lit_ite, hEq, returns_type_ref,
          typeof_map_value_not_returns_type_ref s m]
  | SmtMap.default T e => by
      simpa [__smtx_typeof_map_value, returns_type_ref] using
        typeof_value_not_returns_type_ref s e

theorem typeof_seq_value_not_returns_type_ref
    (s : smt_lit_String) :
    ∀ ss : SmtSeq, ¬ returns_type_ref s (__smtx_typeof_seq_value ss)
  | SmtSeq.cons v vs => by
      cases hEq : smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v))
          (__smtx_typeof_seq_value vs) <;>
        simp [__smtx_typeof_seq_value, smt_lit_ite, hEq, returns_type_ref,
          typeof_seq_value_not_returns_type_ref s vs]
  | SmtSeq.empty T => by
      simp [__smtx_typeof_seq_value, returns_type_ref]

end

theorem no_value_of_type_ref
    (s : smt_lit_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef s := by
  intro h
  rcases h with ⟨v, hv⟩
  apply typeof_value_not_returns_type_ref s v
  simp [hv, returns_type_ref]

theorem no_total_typed_model :
    ¬ ∃ M : SmtModel, model_total_typed M := by
  intro h
  rcases h with ⟨M, hM⟩
  have hTy :
      __smtx_typeof_value (__smtx_model_lookup M "x" (SmtType.TypeRef "A")) =
        SmtType.TypeRef "A" :=
    hM "x" (SmtType.TypeRef "A")
  exact no_value_of_type_ref "A" ⟨__smtx_model_lookup M "x" (SmtType.TypeRef "A"), hTy⟩

def preservation_counterexample_choice_type_ref : SmtTerm :=
  SmtTerm.Apply (SmtTerm.choice "x" (SmtType.TypeRef "A")) (SmtTerm.Boolean true)

theorem preservation_counterexample_choice_type_ref_typeof :
    __smtx_typeof preservation_counterexample_choice_type_ref = SmtType.None := by
  simp [preservation_counterexample_choice_type_ref, __smtx_typeof, smt_lit_ite, smt_lit_Teq,
    no_value_of_type_ref]

theorem preservation_counterexample_choice_type_ref_excluded :
    ¬ term_has_non_none_type preservation_counterexample_choice_type_ref := by
  simp [term_has_non_none_type, preservation_counterexample_choice_type_ref_typeof]

theorem preservation_counterexample_choice_type_ref_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_choice_type_ref =
      SmtValue.NotValue := by
  classical
  have hNo :
      ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef "A" :=
    no_value_of_type_ref "A"
  have hNoSat :
      ¬ ∃ v : SmtValue,
          __smtx_typeof_value v = SmtType.TypeRef "A" ∧
            __smtx_model_eval
                (__smtx_model_push SmtModel.empty "x" (SmtType.TypeRef "A") v)
                (SmtTerm.Boolean true) =
              SmtValue.Boolean true := by
    intro h
    rcases h with ⟨v, hv, _⟩
    exact hNo ⟨v, hv⟩
  change
    (if hSat :
          ∃ v : SmtValue,
            __smtx_typeof_value v = SmtType.TypeRef "A" ∧
              __smtx_model_eval
                  (__smtx_model_push SmtModel.empty "x" (SmtType.TypeRef "A") v)
                  (SmtTerm.Boolean true) =
                SmtValue.Boolean true then
        Classical.choose hSat
      else
        if hTy : ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef "A" then
          Classical.choose hTy
        else
          SmtValue.NotValue) = SmtValue.NotValue
  simp [hNoSat, hNo]

theorem preservation_counterexample_choice_type_ref_eval :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_choice_type_ref) =
      SmtType.None := by
  rw [preservation_counterexample_choice_type_ref_eval_value]
  rfl

def unary_dt : SmtDatatype :=
  SmtDatatype.sum (SmtDatatypeCons.cons SmtType.Int SmtDatatypeCons.unit) SmtDatatype.null

def preservation_counterexample_dt_cons : SmtTerm :=
  SmtTerm.DtCons "D" unary_dt 0

theorem preservation_counterexample_dt_cons_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons =
      SmtValue.DtCons "D" unary_dt 0 := by
  rfl

theorem preservation_counterexample_dt_cons_typeof :
    __smtx_typeof preservation_counterexample_dt_cons =
      SmtType.Map SmtType.Int (SmtType.Datatype "D" unary_dt) := by
  have h :
      __smtx_typeof preservation_counterexample_dt_cons =
        __smtx_typeof_dt_cons_rec (SmtType.Datatype "D" unary_dt)
          (__smtx_dt_substitute "D" unary_dt unary_dt) 0 := by
    rfl
  rw [h]
  native_decide

theorem typeof_value_model_eval_dt_cons :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons) =
      __smtx_typeof preservation_counterexample_dt_cons := by
  rw [preservation_counterexample_dt_cons_eval_value]
  rw [preservation_counterexample_dt_cons_typeof]
  native_decide

def preservation_counterexample_dt_sel : SmtTerm :=
  SmtTerm.DtSel "D" unary_dt 0 0

theorem preservation_counterexample_dt_sel_typeof :
    __smtx_typeof preservation_counterexample_dt_sel = SmtType.None := by
  rfl

theorem preservation_counterexample_dt_sel_excluded :
    ¬ term_has_non_none_type preservation_counterexample_dt_sel := by
  simp [term_has_non_none_type, preservation_counterexample_dt_sel_typeof]

def preservation_counterexample_dt_tester : SmtTerm :=
  SmtTerm.DtTester "D" unary_dt 0

theorem preservation_counterexample_dt_tester_typeof :
    __smtx_typeof preservation_counterexample_dt_tester = SmtType.None := by
  rfl

theorem preservation_counterexample_dt_tester_excluded :
    ¬ term_has_non_none_type preservation_counterexample_dt_tester := by
  simp [term_has_non_none_type, preservation_counterexample_dt_tester_typeof]

def preservation_counterexample_dt_cons_app : SmtTerm :=
  SmtTerm.Apply preservation_counterexample_dt_cons (SmtTerm.Numeral 7)

theorem preservation_counterexample_dt_cons_app_typeof :
    __smtx_typeof preservation_counterexample_dt_cons_app =
      SmtType.Datatype "D" unary_dt := by
  have h :
      __smtx_typeof preservation_counterexample_dt_cons_app =
        __smtx_typeof_apply (__smtx_typeof preservation_counterexample_dt_cons) SmtType.Int := by
    rfl
  rw [h]
  rw [preservation_counterexample_dt_cons_typeof]
  native_decide

theorem preservation_counterexample_dt_cons_app_non_none :
    term_has_non_none_type preservation_counterexample_dt_cons_app := by
  simp [term_has_non_none_type, preservation_counterexample_dt_cons_app_typeof]

theorem preservation_counterexample_dt_cons_app_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app =
      SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7) := by
  change __smtx_model_eval_apply (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons)
    (SmtValue.Numeral 7) = SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7)
  rw [preservation_counterexample_dt_cons_eval_value]
  rfl

theorem typeof_value_model_eval_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      __smtx_typeof preservation_counterexample_dt_cons_app := by
  rw [preservation_counterexample_dt_cons_app_eval_value]
  rw [preservation_counterexample_dt_cons_app_typeof]
  native_decide

def preservation_counterexample_seq_unit_dt_cons_app : SmtTerm :=
  SmtTerm.Apply SmtTerm.seq_unit preservation_counterexample_dt_cons_app

theorem preservation_counterexample_seq_unit_dt_cons_app_typeof :
    __smtx_typeof preservation_counterexample_seq_unit_dt_cons_app =
      SmtType.Seq (SmtType.Datatype "D" unary_dt) := by
  have h :
      __smtx_typeof preservation_counterexample_seq_unit_dt_cons_app =
        smt_lit_ite
          (smt_lit_Teq (__smtx_typeof preservation_counterexample_dt_cons_app) SmtType.None)
          SmtType.None (SmtType.Seq (__smtx_typeof preservation_counterexample_dt_cons_app)) := by
    rfl
  rw [h]
  rw [preservation_counterexample_dt_cons_app_typeof]
  native_decide

theorem preservation_counterexample_seq_unit_dt_cons_app_non_none :
    term_has_non_none_type preservation_counterexample_seq_unit_dt_cons_app := by
  simp [term_has_non_none_type, preservation_counterexample_seq_unit_dt_cons_app_typeof]

theorem preservation_counterexample_seq_unit_dt_cons_app_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app =
      SmtValue.Seq
        (SmtSeq.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtSeq.empty (SmtType.Datatype "D" unary_dt))) := by
  change
    SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app)
          (SmtSeq.empty
            (__smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app)))) =
      SmtValue.Seq
        (SmtSeq.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtSeq.empty (SmtType.Datatype "D" unary_dt)))
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem typeof_value_model_eval_seq_unit_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app) =
      __smtx_typeof preservation_counterexample_seq_unit_dt_cons_app := by
  rw [preservation_counterexample_seq_unit_dt_cons_app_eval_value]
  rw [preservation_counterexample_seq_unit_dt_cons_app_typeof]
  native_decide

def preservation_counterexample_set_singleton_dt_cons_app : SmtTerm :=
  SmtTerm.Apply SmtTerm.set_singleton preservation_counterexample_dt_cons_app

theorem preservation_counterexample_set_singleton_dt_cons_app_typeof :
    __smtx_typeof preservation_counterexample_set_singleton_dt_cons_app =
      SmtType.Map (SmtType.Datatype "D" unary_dt) SmtType.Bool := by
  have h :
      __smtx_typeof preservation_counterexample_set_singleton_dt_cons_app =
        smt_lit_ite
          (smt_lit_Teq (__smtx_typeof preservation_counterexample_dt_cons_app) SmtType.None)
          SmtType.None
          (SmtType.Map (__smtx_typeof preservation_counterexample_dt_cons_app) SmtType.Bool) := by
    rfl
  rw [h]
  rw [preservation_counterexample_dt_cons_app_typeof]
  native_decide

theorem preservation_counterexample_set_singleton_dt_cons_app_non_none :
    term_has_non_none_type preservation_counterexample_set_singleton_dt_cons_app := by
  simp [term_has_non_none_type, preservation_counterexample_set_singleton_dt_cons_app_typeof]

theorem preservation_counterexample_set_singleton_dt_cons_app_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app =
      SmtValue.Map
        (SmtMap.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtValue.Boolean true)
          (SmtMap.default (SmtType.Datatype "D" unary_dt) (SmtValue.Boolean false))) := by
  change
    __smtx_model_eval_set_singleton
      (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      SmtValue.Map
        (SmtMap.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtValue.Boolean true)
          (SmtMap.default (SmtType.Datatype "D" unary_dt) (SmtValue.Boolean false)))
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem typeof_value_model_eval_set_singleton_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app) =
      __smtx_typeof preservation_counterexample_set_singleton_dt_cons_app := by
  rw [preservation_counterexample_set_singleton_dt_cons_app_eval_value]
  rw [preservation_counterexample_set_singleton_dt_cons_app_typeof]
  native_decide

end Smtm
