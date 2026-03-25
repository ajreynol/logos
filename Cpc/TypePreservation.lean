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

theorem typeof_dt_cons_value_rec_datatype_shape
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    ∀ d n,
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d n = SmtType.None ∨
        __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d n = SmtType.Datatype s d0 ∨
        ∃ T U, __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d n = SmtType.Map T U
  | SmtDatatype.null, n => Or.inl (by simp [__smtx_typeof_dt_cons_value_rec])
  | SmtDatatype.sum SmtDatatypeCons.unit d, smt_lit_nat_zero =>
      Or.inr (Or.inl (by simp [__smtx_typeof_dt_cons_value_rec]))
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, smt_lit_nat_zero =>
      Or.inr <| Or.inr ⟨U,
        __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) (SmtDatatype.sum c d) smt_lit_nat_zero,
        by simp [__smtx_typeof_dt_cons_value_rec]⟩
  | SmtDatatype.sum c d, smt_lit_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_datatype_shape s d0 d n

theorem typeof_value_ne_dt_cons_type
    (T U : SmtType) :
    ∀ v : SmtValue, __smtx_typeof_value v ≠ SmtType.DtConsType T U
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
  | SmtValue.DtCons s d i => by
      intro h
      cases typeof_dt_cons_value_rec_datatype_shape s d (__smtx_dt_substitute s d d) i with
      | inl hNone =>
          simp [__smtx_typeof_value, hNone] at h
      | inr hRest =>
          cases hRest with
          | inl hDt =>
              simp [__smtx_typeof_value, hDt] at h
          | inr hMap =>
              rcases hMap with ⟨A, B, hMap⟩
              simp [__smtx_typeof_value, hMap] at h
  | SmtValue.Apply f v => by
      intro h
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T' U' =>
        exact typeof_value_ne_dt_cons_type T' U' f hf

theorem no_value_of_dt_cons_type
    (T U : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T U := by
  intro h
  rcases h with ⟨v, hv⟩
  exact typeof_value_ne_dt_cons_type T U v hv

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
      cases typeof_dt_cons_value_rec_datatype_shape s' d (__smtx_dt_substitute s' d d) i with
      | inl hNone =>
          simp [__smtx_typeof_value, hNone] at h
      | inr hRest =>
          cases hRest with
          | inl hDt =>
              simp [__smtx_typeof_value, hDt] at h
          | inr hMap =>
              rcases hMap with ⟨A, B, hMap⟩
              simp [__smtx_typeof_value, hMap] at h
  | SmtValue.Apply f v => by
      intro h
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        exact typeof_value_ne_dt_cons_type T U f hf

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
      cases typeof_dt_cons_value_rec_datatype_shape s d (__smtx_dt_substitute s d d) i with
      | inl hNone =>
          simp [__smtx_typeof_value, hNone] at h
      | inr hRest =>
          cases hRest with
          | inl hDt =>
              simp [__smtx_typeof_value, hDt] at h
          | inr hMap =>
              rcases hMap with ⟨A, B, hMap⟩
              simp [__smtx_typeof_value, hMap] at h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        exact typeof_value_ne_dt_cons_type T U f hf

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
      cases typeof_dt_cons_value_rec_datatype_shape s d (__smtx_dt_substitute s d d) i with
      | inl hNone =>
          simp [__smtx_typeof_value, hNone] at h
      | inr hRest =>
          cases hRest with
          | inl hDt =>
              simp [__smtx_typeof_value, hDt] at h
          | inr hMap =>
              rcases hMap with ⟨A, B, hMap⟩
              simp [__smtx_typeof_value, hMap] at h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        exact typeof_value_ne_dt_cons_type T U f hf

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
      cases typeof_dt_cons_value_rec_datatype_shape s d (__smtx_dt_substitute s d d) i with
      | inl hNone =>
          simp [__smtx_typeof_value, hNone] at h
      | inr hRest =>
          cases hRest with
          | inl hDt =>
              simp [__smtx_typeof_value, hDt] at h
          | inr hMap =>
              rcases hMap with ⟨A, B, hMap⟩
              simp [__smtx_typeof_value, hMap] at h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        exact typeof_value_ne_dt_cons_type T U f hf

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
          (__smtx_model_lookup M "x" (SmtType.DtConsType SmtType.Int SmtType.Int)) =
        SmtType.DtConsType SmtType.Int SmtType.Int :=
    hM "x" (SmtType.DtConsType SmtType.Int SmtType.Int)
  exact
    no_value_of_dt_cons_type SmtType.Int SmtType.Int
      ⟨__smtx_model_lookup M "x" (SmtType.DtConsType SmtType.Int SmtType.Int), hTy⟩

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
      SmtType.Map SmtType.Int (SmtType.Datatype "D" unary_dt) := by
  rw [preservation_counterexample_dt_cons_eval_value]
  native_decide

theorem preservation_counterexample_dt_cons_mismatch :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons) ≠
      __smtx_typeof preservation_counterexample_dt_cons := by
  rw [preservation_counterexample_dt_cons_eval_typeof]
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

theorem preservation_counterexample_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      SmtType.None := by
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem preservation_counterexample_dt_cons_app_mismatch :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) ≠
      __smtx_typeof preservation_counterexample_dt_cons_app := by
  rw [preservation_counterexample_dt_cons_app_eval_typeof]
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
          (SmtSeq.empty SmtType.None)) := by
  change
    SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app)
          (SmtSeq.empty
            (__smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app)))) =
      SmtValue.Seq
        (SmtSeq.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtSeq.empty SmtType.None))
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem preservation_counterexample_seq_unit_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app) =
      SmtType.Seq SmtType.None := by
  rw [preservation_counterexample_seq_unit_dt_cons_app_eval_value]
  native_decide

theorem preservation_counterexample_seq_unit_dt_cons_app_mismatch :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app) ≠
      __smtx_typeof preservation_counterexample_seq_unit_dt_cons_app := by
  rw [preservation_counterexample_seq_unit_dt_cons_app_eval_typeof]
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
          (SmtMap.default SmtType.None (SmtValue.Boolean false))) := by
  change
    __smtx_model_eval_set_singleton
      (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      SmtValue.Map
        (SmtMap.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtValue.Boolean true)
          (SmtMap.default SmtType.None (SmtValue.Boolean false)))
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem preservation_counterexample_set_singleton_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app) =
      SmtType.Map SmtType.None SmtType.Bool := by
  rw [preservation_counterexample_set_singleton_dt_cons_app_eval_value]
  native_decide

theorem preservation_counterexample_set_singleton_dt_cons_app_mismatch :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app) ≠
      __smtx_typeof preservation_counterexample_set_singleton_dt_cons_app := by
  rw [preservation_counterexample_set_singleton_dt_cons_app_eval_typeof]
  rw [preservation_counterexample_set_singleton_dt_cons_app_typeof]
  native_decide

end Smtm
