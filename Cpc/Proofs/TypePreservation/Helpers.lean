import Cpc.Proofs.TypePreservation.Base

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
          native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · simpa [__smtx_typeof_map_value, native_ite, hEq] using typeof_map_value_shape m
      · exact Or.inr (by simp [__smtx_typeof_map_value, native_ite, hEq])

/-- Lemma about `typeof_seq_value_shape`. -/
theorem typeof_seq_value_shape :
    ∀ ss : SmtSeq,
      (∃ T, __smtx_typeof_seq_value ss = SmtType.Seq T) ∨
        __smtx_typeof_seq_value ss = SmtType.None
  | SmtSeq.empty T => Or.inl ⟨T, rfl⟩
  | SmtSeq.cons v vs => by
      by_cases hEq : native_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · simpa [__smtx_typeof_seq_value, native_ite, hEq] using typeof_seq_value_shape vs
      · exact Or.inr (by simp [__smtx_typeof_seq_value, native_ite, hEq])

/-- Definition used in the proof development for `dt_cons_chain_result`. -/
def dt_cons_chain_result : SmtType -> Prop
  | SmtType.None => True
  | SmtType.Datatype _ _ => True
  | SmtType.FunType _ U => dt_cons_chain_result U
  | _ => False

/-- Lemma about `typeof_dt_cons_value_rec_chain_result`. -/
theorem typeof_dt_cons_value_rec_chain_result
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d n,
      dt_cons_chain_result (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d n)
  | SmtDatatype.null, n => by
      simp [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero => by
      simp [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero => by
      simpa [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_chain_result s d0 (SmtDatatype.sum c d) native_nat_zero
  | SmtDatatype.sum c d, native_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_chain_result s d0 d n

/-- Lemma about `dt_cons_chain_result_of_dt_cons_value_type`. -/
theorem dt_cons_chain_result_of_dt_cons_value_type
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {T : SmtType}
    (h : __smtx_typeof_value (SmtValue.DtCons s d i) = T) :
    dt_cons_chain_result T := by
  have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
  by_cases hWf : __smtx_type_wf (SmtType.Datatype s d)
  · simp [__smtx_typeof_value, hWf] at h
    cases h
    simpa using hShape
  · simp [__smtx_typeof_value, hWf] at h
    cases h
    simpa [dt_cons_chain_result] using True.intro

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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | SmtValue.Apply f v, T, U, h => by
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType A B =>
        cases hNone : native_Teq A SmtType.None <;>
        cases hEq : native_Teq A (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
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

/-- Derives `no_value` from `dt_cons_type_int`. -/
theorem no_value_of_dt_cons_type_int
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T SmtType.Int := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Int hv
  simp [dt_cons_chain_result] at hShape

/-- Derives `no_value` from `dt_cons_type_real`. -/
theorem no_value_of_dt_cons_type_real
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T SmtType.Real := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Real hv
  simp [dt_cons_chain_result] at hShape

/-- Derives `no_value` from `dt_cons_type_type_ref`. -/
theorem no_value_of_dt_cons_type_type_ref
    (T : SmtType)
    (s : native_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T (SmtType.TypeRef s) := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T (SmtType.TypeRef s) hv
  simp [dt_cons_chain_result] at hShape

/-- Lemma about `typeof_value_ne_type_ref`. -/
theorem typeof_value_ne_type_ref
    (s : native_String) :
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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth]
  | SmtValue.Map m => by
      intro h
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Set m => by
      intro h
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | SmtValue.Apply f v => by
      intro h
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType T U =>
        cases hNone : native_Teq T SmtType.None <;>
        cases hEq : native_Teq T (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_type_ref T s ⟨f, by simpa [h] using hf⟩

/-- Derives `no_value` from `type_ref`. -/
theorem no_value_of_type_ref
    (s : native_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef s := by
  intro h
  rcases h with ⟨v, hv⟩
  exact typeof_value_ne_type_ref s v hv

/-- Canonical-form lemma for `bool_value`. -/
theorem bool_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Bool) :
    ∃ b : native_Bool, v = SmtValue.Boolean b := by
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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Set m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType T U =>
        cases hNone : native_Teq T SmtType.None <;>
        cases hEq : native_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_bool T ⟨f, by simpa [h] using hf⟩

/-- Canonical-form lemma for `int_value`. -/
theorem int_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Int) :
    ∃ n : native_Int, v = SmtValue.Numeral n := by
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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Set m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType T U =>
        cases hNone : native_Teq T SmtType.None <;>
        cases hEq : native_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_int T ⟨f, by simpa [h] using hf⟩

/-- Canonical-form lemma for `real_value`. -/
theorem real_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Real) :
    ∃ q : native_Rat, v = SmtValue.Rational q := by
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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Set m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType T U =>
        cases hNone : native_Teq T SmtType.None <;>
        cases hEq : native_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_real T ⟨f, by simpa [h] using hf⟩

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

/-- Derives `no_value` from `dt_cons_type_reglan`. -/
theorem no_value_of_dt_cons_type_reglan
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T SmtType.RegLan := by
  exact no_value_of_dt_cons_type_of_non_chain T SmtType.RegLan (by
    simp [dt_cons_chain_result])

/-- Derives `no_value` from `dt_cons_type_map`. -/
theorem no_value_of_dt_cons_type_map
    (T A B : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T (SmtType.Map A B) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.Map A B) (by
    simp [dt_cons_chain_result])

/-- Derives `no_value` from `dt_cons_type_set`. -/
theorem no_value_of_dt_cons_type_set
    (T A : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T (SmtType.Set A) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.Set A) (by
    simp [dt_cons_chain_result])

/-- Derives `no_value` from `dt_cons_type_bitvec`. -/
theorem no_value_of_dt_cons_type_bitvec
    (T : SmtType)
    (w : native_Nat) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.FunType T (SmtType.BitVec w) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.BitVec w) (by
    simp [dt_cons_chain_result])

/-- Canonical-form lemma for `bitvec_value`. -/
theorem bitvec_value_canonical
    {v : SmtValue}
    {w : native_Nat}
    (h : __smtx_typeof_value v = SmtType.BitVec w) :
    ∃ n : native_Int, v = SmtValue.Binary (native_nat_to_int w) n := by
  cases v with
  | Binary w' n =>
      cases hWidth : native_zleq 0 w' <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
      have hw' : w' = native_nat_to_int w := by
        have hNonneg : 0 <= w' := by
          simpa [native_zleq, SmtEval.native_zleq] using hWidth
        have hNat : native_int_to_nat w' = w := by
          cases h
          rfl
        have hInt : (Int.ofNat (Int.toNat w') : Int) = w' :=
          Int.toNat_of_nonneg hNonneg
        simp [native_int_to_nat, SmtEval.native_int_to_nat] at hNat
        simp [hNat] at hInt
        exact hInt.symm
      subst hw'
      exact ⟨n, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
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
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType T U =>
        cases hNone : native_Teq T SmtType.None <;>
        cases hEq : native_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_bitvec T w ⟨f, by simpa [h] using hf⟩

/-- Lemma about `bitvec_width_nonneg`. -/
theorem bitvec_width_nonneg
    {w n : native_Int} {u : native_Nat}
    (h : __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec u) :
    native_zleq 0 w = true := by
  cases hWidth : native_zleq 0 w <;>
    simp [__smtx_typeof_value, native_ite, hWidth] at h
  simp

/-- Derives `typeof_value_binary` from `nonneg`. -/
theorem typeof_value_binary_of_nonneg
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec (native_int_to_nat w) := by
  simp [__smtx_typeof_value, native_ite, hWidth]

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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType T U =>
        cases hNone : native_Teq T SmtType.None <;>
        cases hEq : native_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_map T A B ⟨f, by simpa [h] using hf⟩

/-- Canonical-form lemma for `set_value`. -/
theorem set_value_canonical
    {v : SmtValue}
    {A : SmtType}
    (h : __smtx_typeof_value v = SmtType.Set A) :
    ∃ m : SmtMap, v = SmtValue.Set m := by
  cases v with
  | Set m =>
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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType T U =>
        cases hNone : native_Teq T SmtType.None <;>
        cases hEq : native_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_set T A ⟨f, by simpa [h] using hf⟩

/-- Lemma about `set_map_value_typed`. -/
theorem set_map_value_typed
    {m : SmtMap}
    {A : SmtType}
    (h : __smtx_typeof_value (SmtValue.Set m) = SmtType.Set A) :
    __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool := by
  cases typeof_map_value_shape m with
  | inl hMap =>
      rcases hMap with ⟨A', B', hMap⟩
      cases B' <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      case Bool =>
        cases h
        simp [hMap]
  | inr hNone =>
      simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h

/-- Derives `map_codomain_inhabited` from `map_value`. -/
theorem map_codomain_inhabited_of_map_value :
    ∀ {m : SmtMap} {A B : SmtType},
      __smtx_typeof_map_value m = SmtType.Map A B -> type_inhabited B
  | SmtMap.default T e, A, B, h => by
      cases h
      exact ⟨e, rfl⟩
  | SmtMap.cons i e m, A, B, h => by
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · simp [__smtx_typeof_map_value, native_ite, hEq] at h
        exact map_codomain_inhabited_of_map_value h
      · simp [__smtx_typeof_map_value, native_ite, hEq] at h

/-- Lemma about `map_codomain_inhabited`. -/
theorem map_codomain_inhabited
    {A B : SmtType}
    (h : type_inhabited (SmtType.Map A B)) :
    type_inhabited B := by
  rcases h with ⟨v, hv⟩
  rcases map_value_canonical (A := A) (B := B) hv with ⟨m, hm⟩
  cases hm
  simpa [__smtx_typeof_value] using
    map_codomain_inhabited_of_map_value (A := A) (B := B) hv

/-- Lemma about `not_type_inhabited_map`. -/
theorem not_type_inhabited_map
    {A B : SmtType}
    (hB : ¬ type_inhabited B) :
    ¬ type_inhabited (SmtType.Map A B) := by
  intro hMap
  exact hB (map_codomain_inhabited hMap)

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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType A B =>
        cases hNone : native_Teq A SmtType.None <;>
        cases hEq : native_Teq A (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_seq A T ⟨f, by simpa [h] using hf⟩

/-- Predicate asserting that every value in a list has the given SMT type. -/
def list_typed (T : SmtType) : List SmtValue -> Prop
  | [] => True
  | v :: vs => __smtx_typeof_value v = T ∧ list_typed T vs

/-- Lemma about `list_typed_append`. -/
theorem list_typed_append
    {T : SmtType} :
    ∀ {xs ys : List SmtValue},
      list_typed T xs ->
        list_typed T ys ->
        list_typed T (xs ++ ys)
  | [], ys, hxs, hys => by
      simpa [list_typed] using hys
  | v :: xs, ys, hxs, hys => by
      rcases hxs with ⟨hv, hxs⟩
      exact ⟨hv, list_typed_append hxs hys⟩

/-- Lemma about `list_typed_take`. -/
theorem list_typed_take
    {T : SmtType} :
    ∀ n {xs : List SmtValue},
      list_typed T xs ->
        list_typed T (xs.take n)
  | 0, xs, hxs => by
      simp [list_typed]
  | Nat.succ n, [], hxs => by
      simp [list_typed]
  | Nat.succ n, v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      exact ⟨hv, list_typed_take n hxs⟩

/-- Lemma about `list_typed_drop`. -/
theorem list_typed_drop
    {T : SmtType} :
    ∀ n {xs : List SmtValue},
      list_typed T xs ->
        list_typed T (xs.drop n)
  | 0, xs, hxs => by
      simpa using hxs
  | Nat.succ n, [], hxs => by
      simp [list_typed]
  | Nat.succ n, v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      simpa using list_typed_drop n hxs

/-- Lemma about `list_typed_reverse`. -/
theorem list_typed_reverse
    {T : SmtType} :
    ∀ {xs : List SmtValue},
      list_typed T xs ->
        list_typed T xs.reverse
  | [], hxs => by
      simp [list_typed]
  | v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      simpa [List.reverse_cons, list_typed, hv] using
        list_typed_append (list_typed_reverse hxs) (by simp [list_typed, hv])

/-- Lemma about `list_typed_extract`. -/
theorem list_typed_extract
    {T : SmtType}
    {xs : List SmtValue}
    (hxs : list_typed T xs)
    (i n : native_Int) :
    list_typed T (native_seq_extract xs i n) := by
  unfold native_seq_extract
  dsimp
  by_cases h :
      (decide (i < 0) || decide (n <= 0) || decide (i >= (↑xs.length : Int))) = true
  · rw [if_pos h]
    simp [list_typed]
  · rw [if_neg h]
    exact
      list_typed_take (Int.toNat (min n (Int.ofNat xs.length - i)))
        (list_typed_drop (Int.toNat i) hxs)

/-- Lemma about `list_typed_replace`. -/
theorem list_typed_replace
    {T : SmtType}
    {xs pat repl : List SmtValue}
    (hxs : list_typed T xs)
    (hrepl : list_typed T repl) :
    list_typed T (native_seq_replace xs pat repl) := by
  unfold native_seq_replace
  cases pat with
  | nil =>
      simpa [native_seq_concat] using list_typed_append hrepl hxs
  | cons p ps =>
      by_cases hIdx : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [hIdx]
        exact hxs
      · simp [hIdx]
        simpa [List.append_assoc] using
          (list_typed_append
            (list_typed_append
              (list_typed_take (Int.toNat (native_seq_indexof xs (p :: ps) 0)) hxs)
              hrepl)
            (list_typed_drop (Int.toNat (native_seq_indexof xs (p :: ps) 0) + (p :: ps).length)
              hxs))

/-- Auxiliary lemma for `list_typed_replace_all`. -/
theorem list_typed_replace_all_aux
    {T : SmtType} :
    ∀ fuel (pat repl : List SmtValue) {xs : List SmtValue},
      list_typed T repl ->
        list_typed T xs ->
        list_typed T (native_seq_replace_all_aux fuel pat repl xs)
  | 0, pat, repl, xs, hrepl, hxs => by
      simp [native_seq_replace_all_aux]
      exact hxs
  | Nat.succ fuel, [], repl, xs, hrepl, hxs => by
      simp [native_seq_replace_all_aux]
      exact hxs
  | Nat.succ fuel, p :: ps, repl, xs, hrepl, hxs => by
      by_cases hIdx : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace_all_aux, hIdx]
        exact hxs
      · simp [native_seq_replace_all_aux, hIdx]
        simpa [List.append_assoc] using
          (list_typed_append
            (list_typed_append
              (list_typed_take (Int.toNat (native_seq_indexof xs (p :: ps) 0)) hxs)
              hrepl)
            (list_typed_replace_all_aux fuel (p :: ps) repl hrepl
              (list_typed_drop
                (Int.toNat (native_seq_indexof xs (p :: ps) 0) + (p :: ps).length) hxs)))

/-- Lemma about `list_typed_replace_all`. -/
theorem list_typed_replace_all
    {T : SmtType}
    {xs pat repl : List SmtValue}
    (hxs : list_typed T xs)
    (hrepl : list_typed T repl) :
    list_typed T (native_seq_replace_all xs pat repl) := by
  unfold native_seq_replace_all
  exact list_typed_replace_all_aux (xs.length + 1) pat repl hrepl hxs

/-- Lemma about `list_typed_update`. -/
theorem list_typed_update
    {T : SmtType}
    {xs ys : List SmtValue}
    (hxs : list_typed T xs)
    (hys : list_typed T ys)
    (i : native_Int) :
    list_typed T (native_seq_update xs i ys) := by
  unfold native_seq_update
  dsimp
  by_cases h : (decide (i < 0) || decide ((↑xs.length : Int) <= i)) = true
  · rw [if_pos h]
    exact hxs
  · rw [if_neg h]
    simpa [List.append_assoc] using
      (list_typed_append
        (list_typed_append (list_typed_take (Int.toNat i) hxs) hys)
        (list_typed_drop (Int.toNat i + 1) hxs))

/-- Derives `elem_typeof_seq_value` from `typeof_seq_value`. -/
theorem elem_typeof_seq_value_of_typeof_seq_value :
    ∀ {ss : SmtSeq} {T : SmtType},
      __smtx_typeof_seq_value ss = SmtType.Seq T ->
        __smtx_elem_typeof_seq_value ss = T
  | SmtSeq.empty U, T, h => by
      simpa [__smtx_typeof_seq_value, __smtx_elem_typeof_seq_value] using h
  | SmtSeq.cons v vs, T, h => by
      by_cases hEq : native_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · have hvs : __smtx_typeof_seq_value vs = SmtType.Seq T := by
          simpa [__smtx_typeof_seq_value, native_ite, hEq] using h
        simpa [__smtx_elem_typeof_seq_value] using
          (elem_typeof_seq_value_of_typeof_seq_value hvs)
      · simp [__smtx_typeof_seq_value, native_ite, hEq] at h

/-- Derives `typed_unpack_seq` from `typeof_seq_value`. -/
theorem typed_unpack_seq_of_typeof_seq_value :
    ∀ {ss : SmtSeq} {T : SmtType},
      __smtx_typeof_seq_value ss = SmtType.Seq T ->
        list_typed T (native_unpack_seq ss)
  | SmtSeq.empty U, T, h => by
      simp [native_unpack_seq, list_typed]
  | SmtSeq.cons v vs, T, h => by
      by_cases hEq : native_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · have hEq' : SmtType.Seq (__smtx_typeof_value v) = __smtx_typeof_seq_value vs := by
          simpa [native_Teq] using hEq
        have hvs : __smtx_typeof_seq_value vs = SmtType.Seq T := by
          simpa [__smtx_typeof_seq_value, native_ite, hEq] using h
        rw [hvs] at hEq'
        have hv : __smtx_typeof_value v = T := by
          cases hEq'
          rfl
        exact ⟨hv, typed_unpack_seq_of_typeof_seq_value hvs⟩
      · simp [__smtx_typeof_seq_value, native_ite, hEq] at h

/-- Derives `typeof_seq_value_pack_seq` from `typed`. -/
theorem typeof_seq_value_pack_seq_of_typed
    {T : SmtType} :
    ∀ {xs : List SmtValue},
      list_typed T xs ->
        __smtx_typeof_seq_value (native_pack_seq T xs) = SmtType.Seq T
  | [], hxs => by
      rfl
  | v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      have ih := typeof_seq_value_pack_seq_of_typed hxs
      simp [native_pack_seq, __smtx_typeof_seq_value, hv, ih, native_ite, native_Teq]

/-- Lemma about `char_value_list_typed`. -/
theorem char_value_list_typed :
    ∀ cs : List Char, list_typed SmtType.Char (cs.map SmtValue.Char)
  | [] => by
      simp [list_typed]
  | _ :: cs => by
      simp [list_typed, char_value_list_typed cs, __smtx_typeof_value]

/-- Derives `char_values` from `string_typed`. -/
theorem char_values_of_string_typed
    (s : native_String) :
    list_typed SmtType.Char (__smtx_ssm_char_values_of_string s) := by
  simpa [__smtx_ssm_char_values_of_string] using char_value_list_typed s.toList

/-- Lemma about `typeof_pack_string`. -/
theorem typeof_pack_string
    (s : native_String) :
    __smtx_typeof_seq_value (native_pack_string s) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_seq_value
      (native_pack_seq SmtType.Char (__smtx_ssm_char_values_of_string s)) =
    SmtType.Seq SmtType.Char
  exact typeof_seq_value_pack_seq_of_typed (char_values_of_string_typed s)

/-- Shows that evaluating `string` terms produces values of the expected type. -/
theorem typeof_value_model_eval_string
    (M : SmtModel)
    (s : native_String) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.String s)) =
      __smtx_typeof (SmtTerm.String s) := by
  change __smtx_typeof_seq_value (native_pack_string s) = SmtType.Seq SmtType.Char
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
          native_Teq (SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · have hm : __smtx_typeof_map_value m = SmtType.Map A B := by
          simpa [__smtx_typeof_map_value, native_ite, hEq] using hMap
        have hEq' :
            SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
              __smtx_typeof_map_value m := by
          simpa [native_Teq] using hEq
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
        by_cases hVeq : native_veq j i
        · simpa [__smtx_msm_lookup, native_ite, hVeq] using he
        · simpa [__smtx_msm_lookup, native_ite, hVeq] using hRec
      · simp [__smtx_typeof_map_value, native_ite, hEq] at hMap

/-- Lemma about `map_store_typed`. -/
theorem map_store_typed
    {m : SmtMap}
    {A B : SmtType}
    {i e : SmtValue}
    (hMap : __smtx_typeof_map_value m = SmtType.Map A B)
    (hi : __smtx_typeof_value i = A)
    (he : __smtx_typeof_value e = B) :
    __smtx_typeof_value (SmtValue.Map (SmtMap.cons i e m)) = SmtType.Map A B := by
  simp [__smtx_typeof_value, __smtx_typeof_map_value, hMap, hi, he, native_ite, native_Teq]

/-- Canonical-form lemma for `reglan_value`. -/
theorem reglan_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.RegLan) :
    ∃ r : native_RegLan, v = SmtValue.RegLan r := by
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
      cases hWidth : native_zleq 0 w <;>
        simp [__smtx_typeof_value, native_ite, hWidth] at h
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
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case FunType A B =>
        cases hNone : native_Teq A SmtType.None <;>
        cases hEq : native_Teq A (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_reglan A ⟨f, by simpa [h] using hf⟩

/-- Derives `bool_binop_args_bool` from `non_none`. -/
theorem bool_binop_args_bool_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.Bool ∧ __smtx_typeof t2 = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, native_ite, native_Teq, h1, h2] at ht
  simp

/-- Derives `arith_binop_args` from `non_none`. -/
theorem arith_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2, h1, h2] at ht
  · simp
  · simp

/-- Derives `arith_binop_ret_bool_args` from `non_none`. -/
theorem arith_binop_ret_bool_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool)
    (ht : term_has_non_none_type (op t1 t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2_ret, h1, h2] at ht
  · simp
  · simp

/-- Derives `arith_binop_ret_args` from `non_none`. -/
theorem arith_binop_ret_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) R)
    (ht : term_has_non_none_type (op t1 t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2_ret, h1, h2] at ht
  · simp
  · simp

/-- Derives `to_real_arg` from `non_none`. -/
theorem to_real_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.to_real t)) :
    __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht
  · simp
  · simp

/-- Derives `real_arg` from `non_none`. -/
theorem real_arg_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {Tout : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Real)
          Tout SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, native_ite, native_Teq, h] at ht
  simp

/-- Derives `int_arg` from `non_none`. -/
theorem int_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.abs t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht
  simp

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

/-- Shows that evaluating `xor_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_xor_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_xor v1 v2) = SmtType.Bool := by
  unfold __smtx_model_eval_xor
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v1 v2) with ⟨b, hb⟩
  rw [hb]
  rfl

/-- Shows that evaluating `distinct_value` terms produces values of the expected type. -/
theorem typeof_value_model_eval_distinct_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_distinct v1 v2) = SmtType.Bool := by
  unfold __smtx_model_eval_distinct
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v1 v2) with ⟨b, hb⟩
  rw [hb]
  rfl

end Smtm
