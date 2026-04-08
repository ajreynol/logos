import CpcMini.Proofs.TypePreservation.Base

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

/-- Lemma about `typeof_map_value_shape`. -/
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

/-- Lemma about `typeof_seq_value_shape`. -/
theorem typeof_seq_value_shape :
    ∀ ss : SmtSeq,
      (∃ T, __smtx_typeof_seq_value ss = SmtType.Seq T) ∨
        __smtx_typeof_seq_value ss = SmtType.None
  | SmtSeq.empty T => Or.inl ⟨T, rfl⟩
  | SmtSeq.cons v vs => by
      by_cases hEq : smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · simpa [__smtx_typeof_seq_value, smt_lit_ite, hEq] using typeof_seq_value_shape vs
      · exact Or.inr (by simp [__smtx_typeof_seq_value, smt_lit_ite, hEq])

/-- Definition used in the proof development for `dt_cons_chain_result`. -/
def dt_cons_chain_result : SmtType -> Prop
  | SmtType.None => True
  | SmtType.Datatype _ _ => True
  | SmtType.FunType _ U => dt_cons_chain_result U
  | _ => False

/-- Lemma about `typeof_dt_cons_value_rec_chain_result`. -/
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

/-- Lemma about `typeof_value_dt_cons_type_chain_result`. -/
theorem typeof_value_dt_cons_type_chain_result :
    ∀ v : SmtValue, ∀ T U : SmtType,
      __smtx_typeof_value v = SmtType.FunType T U -> dt_cons_chain_result U
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
  | SmtValue.Set m, T, U, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
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
      case FunType A B =>
        cases hNone : smt_lit_Teq A SmtType.None <;>
        cases hEq : smt_lit_Teq A (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        have hShape := typeof_value_dt_cons_type_chain_result f A B hf
        simpa [h, dt_cons_chain_result] using hShape

/-- Derives `no_value` from `dt_cons_type_bool`. -/
theorem no_value_of_dt_cons_type_bool
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T SmtType.Bool := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Bool hv
  simp [dt_cons_chain_result] at hShape

/-- Derives `no_value` from `dt_cons_type_of_non_chain`. -/
theorem no_value_of_dt_cons_type_of_non_chain
    (T U : SmtType)
    (hU : ¬ dt_cons_chain_result U) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T U := by
  intro h
  rcases h with ⟨v, hv⟩
  exact hU (typeof_value_dt_cons_type_chain_result v T U hv)

/-- Derives `no_value` from `dt_cons_type_seq`. -/
theorem no_value_of_dt_cons_type_seq
    (T U : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T (SmtType.Seq U) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.Seq U) (by
    simp [dt_cons_chain_result])

/-- Derives `no_value` from `dt_cons_type_map`. -/
theorem no_value_of_dt_cons_type_map
    (T A B : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T (SmtType.Map A B) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.Map A B) (by
    simp [dt_cons_chain_result])

/-- Derives `no_value` from `dt_cons_type_type_ref`. -/
theorem no_value_of_dt_cons_type_type_ref
    (T : SmtType)
    (s : smt_lit_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T (SmtType.TypeRef s) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.TypeRef s) (by
    simp [dt_cons_chain_result])

/-- Derives `no_value` from `type_ref`. -/
theorem no_value_of_type_ref
    (s : smt_lit_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef s := by
  intro h
  rcases h with ⟨v, hv⟩
  cases v with
  | NotValue =>
      simp [__smtx_typeof_value] at hv
  | Boolean _ =>
      simp [__smtx_typeof_value] at hv
  | Numeral _ =>
      simp [__smtx_typeof_value] at hv
  | Rational _ =>
      simp [__smtx_typeof_value] at hv
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at hv
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at hv
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hv
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at hv
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hv
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at hv
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hv
  | Char _ =>
      simp [__smtx_typeof_value] at hv
  | RegLan _ =>
      simp [__smtx_typeof_value] at hv
  | DtCons s' d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s' d (__smtx_dt_substitute s' d d) i
      rw [__smtx_typeof_value] at hv
      rw [hv] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at hv
      case FunType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at hv
        exact no_value_of_dt_cons_type_type_ref T s ⟨f, by simpa [hv] using hf⟩

/-- Canonical-form lemma for `bool_value`. -/
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
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Seq ss =>
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
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_bool T ⟨f, by simpa [h] using hf⟩

/-- Canonical-form lemma for `map_value`. -/
theorem map_value_canonical
    {v : SmtValue}
    {A B : SmtType}
    (h : __smtx_typeof_value v = SmtType.Map A B) :
    ∃ m : SmtMap, v = SmtValue.Map m := by
  cases v with
  | Map m =>
      exact ⟨m, rfl⟩
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
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          cases B' <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
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
      case FunType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_map T A B ⟨f, by simpa [h] using hf⟩

/-- Canonical-form lemma for `seq_value`. -/
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
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
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
      case FunType A B =>
        cases hNone : smt_lit_Teq A SmtType.None <;>
        cases hEq : smt_lit_Teq A (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_seq A T ⟨f, by simpa [h] using hf⟩

/-- Predicate asserting that every value in a list has the given SMT type. -/
def list_typed (T : SmtType) : List SmtValue -> Prop
  | [] => True
  | v :: vs => __smtx_typeof_value v = T ∧ list_typed T vs

/-- Derives `typeof_seq_value_pack_seq` from `typed`. -/
theorem typeof_seq_value_pack_seq_of_typed
    {T : SmtType} :
    ∀ {xs : List SmtValue},
      list_typed T xs ->
        __smtx_typeof_seq_value (smt_lit_pack_seq T xs) = SmtType.Seq T
  | [], hxs => by
      rfl
  | v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      have ih := typeof_seq_value_pack_seq_of_typed hxs
      simp [smt_lit_pack_seq, __smtx_typeof_seq_value, hv, ih, smt_lit_ite, smt_lit_Teq]

/-- Lemma about `char_value_list_typed`. -/
theorem char_value_list_typed :
    ∀ cs : List Char, list_typed SmtType.Char (cs.map SmtValue.Char)
  | [] => by
      simp [list_typed]
  | _ :: cs => by
      simp [list_typed, char_value_list_typed cs, __smtx_typeof_value]

/-- Derives `char_values` from `string_typed`. -/
theorem char_values_of_string_typed
    (s : smt_lit_String) :
    list_typed SmtType.Char (__smtx_ssm_char_values_of_string s) := by
  simpa [__smtx_ssm_char_values_of_string] using char_value_list_typed s.toList

/-- Lemma about `typeof_pack_string`. -/
theorem typeof_pack_string
    (s : smt_lit_String) :
    __smtx_typeof_seq_value (smt_lit_pack_string s) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_seq_value
      (smt_lit_pack_seq SmtType.Char (__smtx_ssm_char_values_of_string s)) =
    SmtType.Seq SmtType.Char
  exact typeof_seq_value_pack_seq_of_typed (char_values_of_string_typed s)

/-- Shows that evaluating `string` terms produces values of the expected type. -/
theorem typeof_value_model_eval_string
    (M : SmtModel)
    (s : smt_lit_String) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.String s)) =
      __smtx_typeof (SmtTerm.String s) := by
  change __smtx_typeof_seq_value (smt_lit_pack_string s) = SmtType.Seq SmtType.Char
  exact typeof_pack_string s

/-- Lemma about `map_lookup_typed`. -/
theorem map_lookup_typed :
    ∀ {m : SmtMap} {A B : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_typeof_value i = A ->
        __smtx_typeof_value (__smtx_msm_lookup m i) = B
  | SmtMap.default T e, A, B, i, hMap, hi => by
      cases hMap
      simp [__smtx_msm_lookup]
  | SmtMap.cons j e m, A, B, i, hMap, hi => by
      by_cases hEq :
          smt_lit_Teq (SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · have hm : __smtx_typeof_map_value m = SmtType.Map A B := by
          simpa [__smtx_typeof_map_value, smt_lit_ite, hEq] using hMap
        have hEq' :
            SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
              __smtx_typeof_map_value m := by
          simpa [smt_lit_Teq] using hEq
        have hHead : SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
            SmtType.Map A B := hEq'.trans hm
        have hj : __smtx_typeof_value j = A := by
          cases hHead
          rfl
        have he : __smtx_typeof_value e = B := by
          cases hHead
          rfl
        have hRec : __smtx_typeof_value (__smtx_msm_lookup m i) = B :=
          map_lookup_typed hm hi
        by_cases hVeq : smt_lit_veq j i
        · simpa [__smtx_msm_lookup, smt_lit_ite, hVeq] using he
        · simpa [__smtx_msm_lookup, smt_lit_ite, hVeq] using hRec
      · simp [__smtx_typeof_map_value, smt_lit_ite, hEq] at hMap

/-- Shows that evaluating `eq_value` terms produces values of the expected type. -/
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

end Smtm
