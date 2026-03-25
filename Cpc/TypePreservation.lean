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

theorem typeof_map_value_shape :
    ∀ m : SmtMap,
      (∃ T U, __smtx_typeof_map_value m = SmtType.Map T U) ∨
        __smtx_typeof_map_value m = SmtType.None
  | SmtMap.default T e => Or.inl ⟨T, __smtx_typeof_value e, rfl⟩
  | SmtMap.cons i e m => by
      by_cases hEq :
          smt_lit_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · simpa [__smtx_typeof_map_value, smt_lit_ite, hEq] using typeof_map_value_shape m
      · exact Or.inr (by simp [__smtx_typeof_map_value, smt_lit_ite, hEq])

theorem typeof_seq_value_shape :
    ∀ ss : SmtSeq,
      (∃ T, __smtx_typeof_seq_value ss = SmtType.Seq T) ∨
        __smtx_typeof_seq_value ss = SmtType.None
  | SmtSeq.empty T => Or.inl ⟨T, rfl⟩
  | SmtSeq.cons v vs => by
      by_cases hEq : smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · simpa [__smtx_typeof_seq_value, smt_lit_ite, hEq] using typeof_seq_value_shape vs
      · exact Or.inr (by simp [__smtx_typeof_seq_value, smt_lit_ite, hEq])

def dt_cons_chain_result : SmtType -> Prop
  | SmtType.None => True
  | SmtType.Datatype _ _ => True
  | SmtType.DtConsType _ U => dt_cons_chain_result U
  | _ => False

theorem typeof_dt_cons_value_rec_chain_result
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    ∀ d n,
      dt_cons_chain_result (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d n)
  | SmtDatatype.null, n => by
      simp [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, smt_lit_nat_zero => by
      simp [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, smt_lit_nat_zero => by
      simpa [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_chain_result s d0 (SmtDatatype.sum c d) smt_lit_nat_zero
  | SmtDatatype.sum c d, smt_lit_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_chain_result s d0 d n

theorem typeof_value_dt_cons_type_chain_result :
    ∀ v : SmtValue, ∀ T U : SmtType,
      __smtx_typeof_value v = SmtType.DtConsType T U -> dt_cons_chain_result U
  | SmtValue.NotValue, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Boolean _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Numeral _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Rational _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Binary w _, T, U, h => by
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | SmtValue.Map m, T, U, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Seq ss, T, U, h => by
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Char _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.RegLan _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.DtCons s d i, T, U, h => by
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simpa [dt_cons_chain_result] using hShape
  | SmtValue.Apply f v, T, U, h => by
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType A B =>
        cases hNone : smt_lit_Teq A SmtType.None <;>
        cases hEq : smt_lit_Teq A (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        have hShape := typeof_value_dt_cons_type_chain_result f A B hf
        simpa [h, dt_cons_chain_result] using hShape

theorem no_value_of_dt_cons_type_bool
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T SmtType.Bool := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Bool hv
  simp [dt_cons_chain_result] at hShape

theorem no_value_of_dt_cons_type_int
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T SmtType.Int := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Int hv
  simp [dt_cons_chain_result] at hShape

theorem no_value_of_dt_cons_type_real
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T SmtType.Real := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Real hv
  simp [dt_cons_chain_result] at hShape

theorem no_value_of_dt_cons_type_type_ref
    (T : SmtType)
    (s : smt_lit_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T (SmtType.TypeRef s) := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T (SmtType.TypeRef s) hv
  simp [dt_cons_chain_result] at hShape

theorem typeof_value_ne_type_ref
    (s : smt_lit_String) :
    ∀ v : SmtValue, __smtx_typeof_value v ≠ SmtType.TypeRef s
  | SmtValue.NotValue => by
      simp [__smtx_typeof_value]
  | SmtValue.Boolean _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Numeral _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Rational _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Binary w _ => by
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth]
  | SmtValue.Map m => by
      intro h
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Seq ss => by
      intro h
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Char _ => by
      simp [__smtx_typeof_value]
  | SmtValue.RegLan _ => by
      simp [__smtx_typeof_value]
  | SmtValue.DtCons s' d i => by
      intro h
      have hShape := typeof_dt_cons_value_rec_chain_result s' d (__smtx_dt_substitute s' d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | SmtValue.Apply f v => by
      intro h
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_type_ref T s ⟨f, by simpa [h] using hf⟩

theorem no_value_of_type_ref
    (s : smt_lit_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef s := by
  intro h
  rcases h with ⟨v, hv⟩
  exact typeof_value_ne_type_ref s v hv

theorem bool_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Bool) :
    ∃ b : smt_lit_Bool, v = SmtValue.Boolean b := by
  cases v with
  | Boolean b =>
      exact ⟨b, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_bool T ⟨f, by simpa [h] using hf⟩

theorem int_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Int) :
    ∃ n : smt_lit_Int, v = SmtValue.Numeral n := by
  cases v with
  | Numeral n =>
      exact ⟨n, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_int T ⟨f, by simpa [h] using hf⟩

theorem real_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Real) :
    ∃ q : smt_lit_Rat, v = SmtValue.Rational q := by
  cases v with
  | Rational q =>
      exact ⟨q, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_real T ⟨f, by simpa [h] using hf⟩

theorem no_value_of_dt_cons_type_of_non_chain
    (T U : SmtType)
    (hU : ¬ dt_cons_chain_result U) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T U := by
  intro h
  rcases h with ⟨v, hv⟩
  exact hU (typeof_value_dt_cons_type_chain_result v T U hv)

theorem no_value_of_dt_cons_type_seq
    (T U : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T (SmtType.Seq U) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.Seq U) (by
    simp [dt_cons_chain_result])

theorem no_value_of_dt_cons_type_reglan
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T SmtType.RegLan := by
  exact no_value_of_dt_cons_type_of_non_chain T SmtType.RegLan (by
    simp [dt_cons_chain_result])

theorem seq_value_canonical
    {v : SmtValue}
    {T : SmtType}
    (h : __smtx_typeof_value v = SmtType.Seq T) :
    ∃ ss : SmtSeq, v = SmtValue.Seq ss := by
  cases v with
  | Seq ss =>
      exact ⟨ss, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType A B =>
        cases hNone : smt_lit_Teq A SmtType.None <;>
        cases hEq : smt_lit_Teq A (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_seq A T ⟨f, by simpa [h] using hf⟩

theorem reglan_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.RegLan) :
    ∃ r : smt_lit_RegLan, v = SmtValue.RegLan r := by
  cases v with
  | RegLan r =>
      exact ⟨r, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType A B =>
        cases hNone : smt_lit_Teq A SmtType.None <;>
        cases hEq : smt_lit_Teq A (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_reglan A ⟨f, by simpa [h] using hf⟩

theorem bool_binop_args_bool_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) SmtType.Bool)
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.Bool ∧ __smtx_typeof t2 = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  simpa [h1, h2] using
    (show SmtType.Bool = SmtType.Bool ∧ SmtType.Bool = SmtType.Bool from ⟨rfl, rfl⟩)

theorem arith_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2, h1, h2] at ht
  · simpa [h1, h2] using
      (show (SmtType.Int = SmtType.Int ∧ SmtType.Int = SmtType.Int) ∨
          (SmtType.Int = SmtType.Real ∧ SmtType.Int = SmtType.Real) from
        Or.inl ⟨rfl, rfl⟩)
  · simpa [h1, h2] using
      (show (SmtType.Real = SmtType.Int ∧ SmtType.Real = SmtType.Int) ∨
          (SmtType.Real = SmtType.Real ∧ SmtType.Real = SmtType.Real) from
        Or.inr ⟨rfl, rfl⟩)

theorem arith_binop_ret_bool_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2_ret, h1, h2] at ht
  · simpa [h1, h2] using
      (show (SmtType.Int = SmtType.Int ∧ SmtType.Int = SmtType.Int) ∨
          (SmtType.Int = SmtType.Real ∧ SmtType.Int = SmtType.Real) from
        Or.inl ⟨rfl, rfl⟩)
  · simpa [h1, h2] using
      (show (SmtType.Real = SmtType.Int ∧ SmtType.Real = SmtType.Int) ∨
          (SmtType.Real = SmtType.Real ∧ SmtType.Real = SmtType.Real) from
        Or.inr ⟨rfl, rfl⟩)

theorem to_real_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_real t)) :
    __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  · simpa [h] using (show SmtType.Int = SmtType.Int ∨ SmtType.Int = SmtType.Real from Or.inl rfl)
  · simpa [h] using (show SmtType.Real = SmtType.Int ∨ SmtType.Real = SmtType.Real from Or.inr rfl)

theorem real_arg_of_non_none
    {op t : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) SmtType.Real)
          (if op = SmtTerm.to_int then SmtType.Int else SmtType.Bool) SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht
  simpa [h] using (show SmtType.Real = SmtType.Real from rfl)

theorem int_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.abs t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  simpa [h] using (show SmtType.Int = SmtType.Int from rfl)

theorem typeof_value_model_eval_eq_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_eq v1 v2) = SmtType.Bool := by
  cases v1 <;> cases v2
  case Seq.Seq ss1 ss2 =>
    cases ss1 <;> cases ss2 <;> simp [__smtx_model_eval_eq, __smtx_typeof_value]
  case Apply.Apply f1 a1 f2 a2 =>
    simp [__smtx_model_eval_eq, __smtx_typeof_value]
  all_goals
    simp [__smtx_model_eval_eq, __smtx_typeof_value]

theorem typeof_value_model_eval_xor_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_xor v1 v2) = SmtType.Bool := by
  unfold __smtx_model_eval_xor
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v1 v2) with ⟨b, hb⟩
  rw [hb]
  rfl

theorem typeof_value_model_eval_distinct_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_distinct v1 v2) = SmtType.Bool := by
  unfold __smtx_model_eval_distinct
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v1 v2) with ⟨b, hb⟩
  rw [hb]
  rfl

theorem eq_term_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2) = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, h1, h2] at ht ⊢
  all_goals
    first | exact ht

theorem typeof_value_model_eval_not
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.not t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.not t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.not t) := by
  have hArg : __smtx_typeof t = SmtType.Bool := by
    unfold term_has_non_none_type at ht
    cases h : __smtx_typeof t <;>
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
    simpa [h] using (show SmtType.Bool = SmtType.Bool from rfl)
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.not t) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_not (__smtx_model_eval M t)) = SmtType.Bool
  rcases bool_value_canonical (by simpa [hArg] using hpres) with ⟨b, hb⟩
  rw [hb]
  rfl

theorem typeof_value_model_eval_or
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_or (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_and
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_and (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_imp
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_imp (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_eq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2) := by
  rw [eq_term_typeof_of_non_none ht]
  simpa using typeof_value_model_eval_eq_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_xor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.xor) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  simpa using typeof_value_model_eval_xor_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_distinct
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2) := by
  rw [eq_term_typeof_of_non_none ht]
  simpa using typeof_value_model_eval_distinct_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_plus
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.plus) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_plus (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_plus (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_neg
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval__ (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval__ (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_mult
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_mult (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_mult (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_lt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_lt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_lt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_leq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_leq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_leq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_gt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_gt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_gt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_geq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_geq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_geq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_to_real
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_real t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.to_real t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) := by
  rcases to_real_arg_of_non_none ht with hArg | hArg
  · rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) = SmtType.Real by
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
    change __smtx_typeof_value (__smtx_model_eval_to_real (__smtx_model_eval M t)) = SmtType.Real
    rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
    rw [hn]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) = SmtType.Real by
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
    change __smtx_typeof_value (__smtx_model_eval_to_real (__smtx_model_eval M t)) = SmtType.Real
    rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
    rw [hq]
    rfl

theorem typeof_value_model_eval_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.to_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_int t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_to_int (__smtx_model_eval M t)) = SmtType.Int
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  rfl

theorem typeof_value_model_eval_is_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.is_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.is_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.is_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.is_int t) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_is_int (__smtx_model_eval M t)) = SmtType.Bool
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  simpa [__smtx_model_eval_is_int, __smtx_model_eval_to_int, __smtx_model_eval_to_real] using
    typeof_value_model_eval_eq_value
      (SmtValue.Rational (smt_lit_to_real (smt_lit_to_int q))) (SmtValue.Rational q)

theorem typeof_value_model_eval_abs
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.abs t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.abs t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.abs t) := by
  have hArg : __smtx_typeof t = SmtType.Int := int_arg_of_non_none ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.abs t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_abs (__smtx_model_eval M t)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  cases hlt : smt_lit_zlt n 0 <;>
    simp [__smtx_model_eval_abs, __smtx_model_eval_lt, __smtx_model_eval_ite,
      __smtx_model_eval__, __smtx_typeof_value, hlt]

theorem int_ret_arg_of_non_none
    {op t : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) SmtType.Int) R SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht
  simpa [h] using (show SmtType.Int = SmtType.Int from rfl)

theorem str_substr_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr t1) t2) t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Int ∧
        __smtx_typeof t3 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof, __smtx_typeof_str_substr, h1, h2, h3] at ht
      exact ⟨T, rfl, rfl, rfl⟩
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof, __smtx_typeof_str_substr, h1, h2, h3] at ht

theorem str_indexof_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Seq T ∧
        __smtx_typeof t3 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          cases h3 : __smtx_typeof t3 with
          | Int =>
              have hEq : T = U := by
                simpa [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2,
                  h3] using ht
              subst hEq
              exact ⟨T, rfl, rfl, rfl⟩
          | _ =>
              simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2,
                h3] at ht
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2,
              h3] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht

theorem str_at_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at t1) t2)) :
    ∃ T : SmtType, __smtx_typeof t1 = SmtType.Seq T ∧ __smtx_typeof t2 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof, __smtx_typeof_str_at, h1, h2] at ht
      exact ⟨T, rfl, rfl⟩
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof, __smtx_typeof_str_at, h1, h2] at ht

theorem reglan_arg_of_non_none
    {op t : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht
  simpa [h] using (show SmtType.RegLan = SmtType.RegLan from rfl)

theorem reglan_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) SmtType.RegLan)
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.RegLan ∧ __smtx_typeof t2 = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  simpa [h1, h2] using
    (show SmtType.RegLan = SmtType.RegLan ∧ SmtType.RegLan = SmtType.RegLan from
      ⟨rfl, rfl⟩)

theorem seq_char_arg_of_non_none
    {op t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) ret
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.Seq SmtType.Char := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | Seq A =>
      have hSeq : A = SmtType.Char ∧ ¬ ret = SmtType.None := by
        simpa [hTy, smt_lit_ite, smt_lit_Teq, h] using ht
      have hA : A = SmtType.Char := hSeq.1
      subst hA
      rfl
  | _ =>
      simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht

theorem seq_char_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char)) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.Seq SmtType.Char := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | Seq B =>
          have hSeqs : A = SmtType.Char ∧ B = SmtType.Char ∧ ¬ ret = SmtType.None := by
            simpa [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] using ht
          have hAB : A = SmtType.Char ∧ B = SmtType.Char := ⟨hSeqs.1, hSeqs.2.1⟩
          rcases hAB with ⟨hA, hB⟩
          subst hA
          subst hB
          exact ⟨rfl, rfl⟩
      | _ =>
          simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht

theorem seq_char_reglan_args_of_non_none
    {op t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) SmtType.RegLan) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧ __smtx_typeof t2 = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | RegLan =>
          have hSeq : A = SmtType.Char ∧ ¬ ret = SmtType.None := by
            simpa [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] using ht
          have hA : A = SmtType.Char := hSeq.1
          subst hA
          exact ⟨rfl, rfl⟩
      | _ =>
          simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht

theorem typeof_value_model_eval_str_len
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_len t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_len t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_len t) := by
  unfold term_has_non_none_type at ht
  cases hArg : __smtx_typeof t <;>
    simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, smt_lit_ite, smt_lit_Teq, hArg] at ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_len t) = SmtType.Int by
    simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_len (__smtx_model_eval M t)) = SmtType.Int
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

theorem typeof_value_model_eval_str_indexof
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3) := by
  rcases str_indexof_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3) =
        SmtType.Int by
    simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2, h3]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_indexof (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Int
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rcases int_value_canonical (by simpa [h3] using hpres3) with ⟨n, hn⟩
  rw [hss1, hss2, hn]
  rfl

theorem typeof_value_model_eval_str_to_code
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_code t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_to_code t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_code t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_code) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_code t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_to_code (__smtx_model_eval M t)) =
    SmtType.Int
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

theorem typeof_value_model_eval_str_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_int t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_int t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_to_int (__smtx_model_eval M t)) =
    SmtType.Int
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

theorem typeof_value_model_eval_str_to_re
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_re t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_to_re t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_re t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_re) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_re t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_to_re (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

theorem typeof_value_model_eval_re_mult
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_mult t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.re_mult t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.re_mult t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_mult) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.re_mult t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_re_mult (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

theorem typeof_value_model_eval_re_plus
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_plus t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.re_plus t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.re_plus t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_plus) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.re_plus t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_re_plus (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

theorem typeof_value_model_eval_re_opt
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_opt t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.re_opt t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.re_opt t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_opt) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.re_opt t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_re_opt (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

theorem typeof_value_model_eval_re_comp
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_comp t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.re_comp t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.re_comp t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_comp) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.re_comp t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_re_comp (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

theorem typeof_value_model_eval_re_range
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.re_range) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_range (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  rfl

theorem typeof_value_model_eval_re_concat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_concat) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_concat (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

theorem typeof_value_model_eval_re_inter
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_inter) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_inter (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

theorem typeof_value_model_eval_re_union
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_union) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_union (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

theorem typeof_value_model_eval_re_diff
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_diff) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_diff (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

theorem typeof_value_model_eval_str_in_re
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2) := by
  have hArgs := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_in_re (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss, hss⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r, hr⟩
  rw [hss, hr]
  rfl

theorem typeof_value_model_eval_str_lt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_lt) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_lt (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  rfl

theorem typeof_value_model_eval_str_leq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_leq) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_leq (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_leq
  rcases bool_value_canonical
      (typeof_value_model_eval_eq_value (SmtValue.Seq ss1) (SmtValue.Seq ss2)) with
    ⟨bEq, hbEq⟩
  rw [hbEq]
  rfl

theorem typeof_value_model_eval_str_prefixof
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_prefixof) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_prefixof (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_prefixof
  simpa using
    typeof_value_model_eval_eq_value
      (SmtValue.Seq ss1)
      (__smtx_model_eval_str_substr (SmtValue.Seq ss2) (SmtValue.Numeral 0)
        (__smtx_model_eval_str_len (SmtValue.Seq ss1)))

theorem typeof_value_model_eval_str_suffixof
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_suffixof) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_suffixof (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_suffixof
  simpa using
    typeof_value_model_eval_eq_value
      (SmtValue.Seq ss1)
      (__smtx_model_eval_str_substr (SmtValue.Seq ss2)
        (__smtx_model_eval__ (__smtx_model_eval_str_len (SmtValue.Seq ss2))
          (__smtx_model_eval_str_len (SmtValue.Seq ss1)))
        (__smtx_model_eval_str_len (SmtValue.Seq ss1)))

theorem typeof_value_model_eval_str_is_digit
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_is_digit t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_is_digit t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_is_digit t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_is_digit) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_is_digit t) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_is_digit (__smtx_model_eval M t)) =
    SmtType.Bool
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  simp [__smtx_model_eval_str_is_digit, __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
    __smtx_model_eval_and, __smtx_typeof_value]

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

theorem no_total_typed_model :
    ¬ ∃ M : SmtModel, model_total_typed M := by
  intro h
  rcases h with ⟨M, hM⟩
  have hTy :
      __smtx_typeof_value
          (__smtx_model_lookup M "x" (SmtType.TypeRef "A")) =
        SmtType.TypeRef "A" :=
    hM "x" (SmtType.TypeRef "A")
  exact
    no_value_of_type_ref "A"
      ⟨__smtx_model_lookup M "x" (SmtType.TypeRef "A"), hTy⟩

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
      SmtType.DtConsType SmtType.Int (SmtType.Datatype "D" unary_dt) := by
  have h :
      __smtx_typeof preservation_counterexample_dt_cons =
        __smtx_typeof_dt_cons_rec (SmtType.Datatype "D" unary_dt)
          (__smtx_dt_substitute "D" unary_dt unary_dt) 0 := by
    rfl
  rw [h]
  native_decide

theorem preservation_counterexample_dt_cons_non_none :
    term_has_non_none_type preservation_counterexample_dt_cons := by
  simp [term_has_non_none_type, preservation_counterexample_dt_cons_typeof]

theorem preservation_counterexample_dt_cons_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons) =
      SmtType.DtConsType SmtType.Int (SmtType.Datatype "D" unary_dt) := by
  rw [preservation_counterexample_dt_cons_eval_value]
  native_decide

theorem typeof_value_model_eval_dt_cons :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons) =
      __smtx_typeof preservation_counterexample_dt_cons := by
  rw [preservation_counterexample_dt_cons_eval_typeof, preservation_counterexample_dt_cons_typeof]

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

theorem preservation_counterexample_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      SmtType.Datatype "D" unary_dt := by
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem typeof_value_model_eval_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      __smtx_typeof preservation_counterexample_dt_cons_app := by
  rw [preservation_counterexample_dt_cons_app_eval_typeof, preservation_counterexample_dt_cons_app_typeof]

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

theorem preservation_counterexample_seq_unit_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app) =
      SmtType.Seq (SmtType.Datatype "D" unary_dt) := by
  rw [preservation_counterexample_seq_unit_dt_cons_app_eval_value]
  native_decide

theorem typeof_value_model_eval_seq_unit_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app) =
      __smtx_typeof preservation_counterexample_seq_unit_dt_cons_app := by
  rw [preservation_counterexample_seq_unit_dt_cons_app_eval_typeof,
    preservation_counterexample_seq_unit_dt_cons_app_typeof]

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

theorem preservation_counterexample_set_singleton_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app) =
      SmtType.Map (SmtType.Datatype "D" unary_dt) SmtType.Bool := by
  rw [preservation_counterexample_set_singleton_dt_cons_app_eval_value]
  native_decide

theorem typeof_value_model_eval_set_singleton_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app) =
      __smtx_typeof preservation_counterexample_set_singleton_dt_cons_app := by
  rw [preservation_counterexample_set_singleton_dt_cons_app_eval_typeof,
    preservation_counterexample_set_singleton_dt_cons_app_typeof]

def preservation_counterexample_str_concat : SmtTerm :=
  SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat (SmtTerm.String "a")) (SmtTerm.String "b")

theorem preservation_counterexample_str_concat_typeof :
    __smtx_typeof preservation_counterexample_str_concat = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_seq_op_2 (SmtType.Seq SmtType.Char) (SmtType.Seq SmtType.Char) =
    SmtType.Seq SmtType.Char
  rfl

theorem preservation_counterexample_str_concat_non_none :
    term_has_non_none_type preservation_counterexample_str_concat := by
  simp [term_has_non_none_type, preservation_counterexample_str_concat_typeof]

theorem preservation_counterexample_str_concat_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_str_concat =
      SmtValue.Seq
        (smt_lit_pack_seq (__smtx_typeof_seq_value (smt_lit_pack_string "a"))
          (smt_lit_seq_concat (smt_lit_unpack_seq (smt_lit_pack_string "a"))
            (smt_lit_unpack_seq (smt_lit_pack_string "b")))) := by
  rfl

theorem preservation_counterexample_str_concat_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_concat) =
      SmtType.None := by
  rw [preservation_counterexample_str_concat_eval_value]
  native_decide

theorem preservation_counterexample_str_concat_mismatch :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_concat) ≠
      __smtx_typeof preservation_counterexample_str_concat := by
  rw [preservation_counterexample_str_concat_eval_typeof,
    preservation_counterexample_str_concat_typeof]
  decide

def preservation_counterexample_str_substr : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply
      (SmtTerm.Apply SmtTerm.str_substr (SmtTerm.String "ab"))
      (SmtTerm.Numeral 0))
    (SmtTerm.Numeral 1)

theorem preservation_counterexample_str_substr_typeof :
    __smtx_typeof preservation_counterexample_str_substr = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_str_substr (SmtType.Seq SmtType.Char) SmtType.Int SmtType.Int =
    SmtType.Seq SmtType.Char
  rfl

theorem preservation_counterexample_str_substr_non_none :
    term_has_non_none_type preservation_counterexample_str_substr := by
  simp [term_has_non_none_type, preservation_counterexample_str_substr_typeof]

theorem preservation_counterexample_str_substr_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_str_substr =
      SmtValue.Seq
        (smt_lit_pack_seq (__smtx_typeof_seq_value (smt_lit_pack_string "ab"))
          (smt_lit_seq_extract (smt_lit_unpack_seq (smt_lit_pack_string "ab")) 0 1)) := by
  rfl

theorem preservation_counterexample_str_substr_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_substr) =
      SmtType.None := by
  rw [preservation_counterexample_str_substr_eval_value]
  native_decide

theorem preservation_counterexample_str_substr_mismatch :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_substr) ≠
      __smtx_typeof preservation_counterexample_str_substr := by
  rw [preservation_counterexample_str_substr_eval_typeof,
    preservation_counterexample_str_substr_typeof]
  decide

def preservation_counterexample_str_rev : SmtTerm :=
  SmtTerm.Apply SmtTerm.str_rev (SmtTerm.String "ab")

theorem preservation_counterexample_str_rev_typeof :
    __smtx_typeof preservation_counterexample_str_rev = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_seq_op_1 (SmtType.Seq SmtType.Char) = SmtType.Seq SmtType.Char
  rfl

theorem preservation_counterexample_str_rev_non_none :
    term_has_non_none_type preservation_counterexample_str_rev := by
  simp [term_has_non_none_type, preservation_counterexample_str_rev_typeof]

theorem preservation_counterexample_str_rev_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_str_rev =
      SmtValue.Seq
        (smt_lit_pack_seq (__smtx_typeof_seq_value (smt_lit_pack_string "ab"))
          (smt_lit_seq_rev (smt_lit_unpack_seq (smt_lit_pack_string "ab")))) := by
  rfl

theorem preservation_counterexample_str_rev_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_rev) =
      SmtType.None := by
  rw [preservation_counterexample_str_rev_eval_value]
  native_decide

theorem preservation_counterexample_str_rev_mismatch :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_rev) ≠
      __smtx_typeof preservation_counterexample_str_rev := by
  rw [preservation_counterexample_str_rev_eval_typeof,
    preservation_counterexample_str_rev_typeof]
  decide

end Smtm
