import CpcMini.Proofs.TypePreservation.Base

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

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
  | SmtType.DtcAppType _ U => dt_cons_chain_result U
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

/-- Removes the datatype well-formedness guard from a non-`None` `dt_cons` value typing equality. -/
theorem typeof_value_dt_cons_inner_eq_of_eq_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {U : SmtType}
    (h :
      __smtx_typeof_value (SmtValue.DtCons s d i) = U)
    (hU : U ≠ SmtType.None) :
    __smtx_typeof_dt_cons_value_rec
        (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i = U := by
  simpa [__smtx_typeof_value] using h

/-- Raw datatype constructor values always have constructor-chain result types. -/
theorem dt_cons_chain_result_of_dt_cons_value_type
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {T : SmtType}
    (h : __smtx_typeof_value (SmtValue.DtCons s d i) = T) :
    dt_cons_chain_result T := by
  by_cases hT : T = SmtType.None
  · simp [dt_cons_chain_result, hT]
  · have hShape :=
      typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
    have hInner :
        __smtx_typeof_dt_cons_value_rec
            (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i = T :=
      typeof_value_dt_cons_inner_eq_of_eq_non_none h hT
    rw [hInner] at hShape
    exact hShape

/-- Lemma about datatype-constructor application chains. -/
theorem typeof_value_dt_cons_head_type_chain_result :
    ∀ v : SmtValue, ∀ T U : SmtType,
      (∃ s d i, __vsm_apply_head v = SmtValue.DtCons s d i) ->
      __smtx_typeof_value v = SmtType.DtcAppType T U -> dt_cons_chain_result U
  | SmtValue.NotValue, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary _ _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue _ _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan _, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.DtCons s d i, T, U, hHead, h => by
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      have hInner :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i =
            SmtType.DtcAppType T U :=
        typeof_value_dt_cons_inner_eq_of_eq_non_none h (by simp)
      rw [hInner] at hShape
      simpa [dt_cons_chain_result] using hShape
  | SmtValue.Apply f v, T, U, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons s d i := by
        simpa [__vsm_apply_head] using hHead
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtcAppType A B =>
        cases hNone : native_Teq A SmtType.None <;>
        cases hEq : native_Teq A (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq] at h
        have hShape :=
          typeof_value_dt_cons_head_type_chain_result f A B ⟨s, d, i, hHeadF⟩ hf
        simpa [h, dt_cons_chain_result] using hShape

/-- Values whose application head is a datatype constructor always have constructor-chain result types. -/
theorem typeof_value_dt_cons_head_chain_result :
    ∀ v : SmtValue, ∀ T : SmtType,
      (∃ s d i, __vsm_apply_head v = SmtValue.DtCons s d i) ->
      __smtx_typeof_value v = T -> dt_cons_chain_result T
  | SmtValue.NotValue, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary _ _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue _ _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan _, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.DtCons s d i, T, hHead, h => by
      simpa using dt_cons_chain_result_of_dt_cons_value_type h
  | SmtValue.Apply f v, T, hHead, h => by
      rcases hHead with ⟨s, d, i, hHead⟩
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons s d i := by
        simpa [__vsm_apply_head] using hHead
      change __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value v) = T at h
      cases hf : __smtx_typeof_value f
      case None =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Bool =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Int =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Real =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case RegLan =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case BitVec n =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Map A B =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Set A =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Seq A =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Char =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case Datatype s' d' =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case TypeRef s' =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case USort u =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case FunType A B =>
        simp [__smtx_typeof_apply_value, hf] at h
        cases h
        simp [dt_cons_chain_result]
      case DtcAppType A B =>
        cases hNone : native_Teq A SmtType.None
        case false =>
          cases hEq : native_Teq A (__smtx_typeof_value v)
          case false =>
            have hNoneTy : SmtType.None = T := by
              simpa [hf, __smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hNone, hEq] using h
            cases hNoneTy
            simp [dt_cons_chain_result]
          case true =>
            have hBTy : B = T := by
              simpa [hf, __smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hNone, hEq] using h
            have hShape :=
              typeof_value_dt_cons_head_type_chain_result f A B ⟨s, d, i, hHeadF⟩ hf
            cases hBTy
            simpa [dt_cons_chain_result] using hShape
        case true =>
          have hNoneTy : SmtType.None = T := by
            simpa [hf, __smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hNone] using h
          cases hNoneTy
          simp [dt_cons_chain_result]

/-- Raw applications with neither `Fun` nor datatype-constructor heads have type `none`. -/
theorem typeof_value_apply_of_head_ne_fun_ne_dt_cons :
    ∀ v i : SmtValue,
      (∀ m, __vsm_apply_head v ≠ SmtValue.Fun m) ->
      (∀ s d n, __vsm_apply_head v ≠ SmtValue.DtCons s d n) ->
      __smtx_typeof_value (SmtValue.Apply v i) = SmtType.None
  | SmtValue.NotValue, i, hFun, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Boolean _, i, hFun, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Numeral _, i, hFun, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Rational _, i, hFun, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.Binary w n, i, hFun, hDt => by
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, native_ite,
            SmtEval.native_and, hWidth, hMod]
  | SmtValue.Map m, i, hFun, hDt => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          change __smtx_typeof_apply_value (__smtx_typeof_map_value m) (__smtx_typeof_value i) = SmtType.None
          rw [hMap]
          simp [__smtx_typeof_apply_value]
      | inr hNone =>
          change __smtx_typeof_apply_value (__smtx_typeof_map_value m) (__smtx_typeof_value i) = SmtType.None
          rw [hNone]
          simp [__smtx_typeof_apply_value]
  | SmtValue.Fun m, i, hFun, hDt => by
      exact False.elim (hFun m rfl)
  | SmtValue.Set m, i, hFun, hDt => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          change __smtx_typeof_apply_value (__smtx_map_to_set_type (__smtx_typeof_map_value m)) (__smtx_typeof_value i) = SmtType.None
          rw [hMap]
          cases U <;> simp [__smtx_map_to_set_type, __smtx_typeof_apply_value]
      | inr hNone =>
          change __smtx_typeof_apply_value (__smtx_map_to_set_type (__smtx_typeof_map_value m)) (__smtx_typeof_value i) = SmtType.None
          rw [hNone]
          simp [__smtx_map_to_set_type, __smtx_typeof_apply_value]
  | SmtValue.Seq ss, i, hFun, hDt => by
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          change __smtx_typeof_apply_value (__smtx_typeof_seq_value ss) (__smtx_typeof_value i) = SmtType.None
          rw [hSeq]
          simp [__smtx_typeof_apply_value]
      | inr hNone =>
          change __smtx_typeof_apply_value (__smtx_typeof_seq_value ss) (__smtx_typeof_value i) = SmtType.None
          rw [hNone]
          simp [__smtx_typeof_apply_value]
  | SmtValue.Char _, i, hFun, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.UValue _ _, i, hFun, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.RegLan _, i, hFun, hDt => by
      simp [__smtx_typeof_value, __smtx_typeof_apply_value]
  | SmtValue.DtCons s d n, i, hFun, hDt => by
      exact False.elim (hDt s d n rfl)
  | SmtValue.Apply f a, i, hFun, hDt => by
      have hFunF : ∀ m, __vsm_apply_head f ≠ SmtValue.Fun m := by
        intro m hm
        exact hFun m (by simpa [__vsm_apply_head] using hm)
      have hDtF : ∀ s d n, __vsm_apply_head f ≠ SmtValue.DtCons s d n := by
        intro s d n hm
        exact hDt s d n (by simpa [__vsm_apply_head] using hm)
      have hNone :
          __smtx_typeof_value (SmtValue.Apply f a) = SmtType.None :=
        typeof_value_apply_of_head_ne_fun_ne_dt_cons f a hFunF hDtF
      change __smtx_typeof_apply_value (__smtx_typeof_value (SmtValue.Apply f a)) (__smtx_typeof_value i) = SmtType.None
      rw [hNone]
      simp [__smtx_typeof_apply_value]

/-- A raw application with a non-chain result type must have a `Fun` head. -/
theorem apply_value_non_chain_result_implies_fun_head
    {v i : SmtValue}
    {U : SmtType}
    (hU : ¬ dt_cons_chain_result U)
    (h : __smtx_typeof_value (SmtValue.Apply v i) = U) :
    ∃ m, __vsm_apply_head v = SmtValue.Fun m := by
  have hUNone : U ≠ SmtType.None := by
    intro hEq
    exact hU (by simp [dt_cons_chain_result, hEq])
  by_cases hFun : ∃ m, __vsm_apply_head v = SmtValue.Fun m
  · exact hFun
  · by_cases hDt : ∃ s d n, __vsm_apply_head v = SmtValue.DtCons s d n
    · rcases hDt with ⟨s, d, n, hHead⟩
      have hChain :
          dt_cons_chain_result U :=
        typeof_value_dt_cons_head_chain_result
          (SmtValue.Apply v i) U
          ⟨s, d, n, by simpa [__vsm_apply_head] using hHead⟩ h
      exact False.elim (hU hChain)
    · have hNone :
          __smtx_typeof_value (SmtValue.Apply v i) = SmtType.None :=
        typeof_value_apply_of_head_ne_fun_ne_dt_cons v i
          (by
            intro m hm
            exact hFun ⟨m, hm⟩)
          (by
            intro s d n hm
            exact hDt ⟨s, d, n, hm⟩)
      exact False.elim (hUNone (by simpa [hNone] using h.symm))

/-- Raw applications whose head is a `Fun` chain always have type `none`. -/
theorem typeof_value_apply_of_head_fun :
    ∀ v i : SmtValue,
      (∃ m, __vsm_apply_head v = SmtValue.Fun m) ->
      __smtx_typeof_value (SmtValue.Apply v i) = SmtType.None
  | SmtValue.NotValue, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Boolean _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Numeral _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Rational _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Binary _ _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Map _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Fun m, i, hHead => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap, __smtx_typeof_apply_value]
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone, __smtx_typeof_apply_value]
  | SmtValue.Set _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Seq _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Char _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.UValue _ _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.RegLan _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.DtCons _ _ _, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      simp [__vsm_apply_head] at hm
  | SmtValue.Apply f a, i, hHead => by
      rcases hHead with ⟨m, hm⟩
      have hInner : __smtx_typeof_value (SmtValue.Apply f a) = SmtType.None :=
        typeof_value_apply_of_head_fun f a ⟨m, by simpa [__vsm_apply_head] using hm⟩
      change __smtx_typeof_apply_value (__smtx_typeof_value (SmtValue.Apply f a)) (__smtx_typeof_value i) = SmtType.None
      rw [hInner]
      simp [__smtx_typeof_apply_value]

/--
Proof bridge for the canonical-form lemmas. With the current unguarded value-level
`Apply` typing this is not derivable from `SmtModel`; it remains the open proof
obligation separating the proof skeleton from the reverted model semantics.
-/
theorem apply_value_non_chain_result_impossible
    {f x : SmtValue}
    {U : SmtType}
    (hU : ¬ dt_cons_chain_result U)
    (h : __smtx_typeof_value (SmtValue.Apply f x) = U) :
    False := by
  have hUNone : U ≠ SmtType.None := by
    intro hEq
    exact hU (by simp [dt_cons_chain_result, hEq])
  rcases apply_value_non_chain_result_implies_fun_head hU h with ⟨m, hHead⟩
  have hNone : __smtx_typeof_value (SmtValue.Apply f x) = SmtType.None :=
    typeof_value_apply_of_head_fun f x ⟨m, hHead⟩
  exact hUNone (by simpa [hNone] using h.symm)

/-- Derives `no_value` from `type_ref`. -/
theorem no_value_of_type_ref
    (s : native_String) :
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
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at hv
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at hv
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hv
  | Fun m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at hv
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at hv
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
  | UValue _ _ =>
      simp [__smtx_typeof_value] at hv
  | RegLan _ =>
      simp [__smtx_typeof_value] at hv
  | DtCons s' d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s' d (__smtx_dt_substitute s' d d) i
      have hInner :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s' d) (__smtx_dt_substitute s' d d) i =
            SmtType.TypeRef s :=
        typeof_value_dt_cons_inner_eq_of_eq_non_none hv (by simp)
      rw [hInner] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exact apply_value_non_chain_result_impossible
        (U := SmtType.TypeRef s) (by simp [dt_cons_chain_result]) hv

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
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
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
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      have hInner :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i =
            SmtType.Bool :=
        typeof_value_dt_cons_inner_eq_of_eq_non_none h (by simp)
      rw [hInner] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Bool) (by simp [dt_cons_chain_result]) h

/-- Canonical-form lemma for `fun_value`. -/
theorem fun_value_canonical
    {v : SmtValue}
    {A B : SmtType}
    (h : __smtx_typeof_value v = SmtType.FunType A B) :
    ∃ m : SmtMap, v = SmtValue.Fun m := by
  cases v with
  | Fun m =>
      exact ⟨m, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          cases B' <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
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
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      have hInner :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i =
            SmtType.FunType A B :=
        typeof_value_dt_cons_inner_eq_of_eq_non_none h (by simp)
      rw [hInner] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.FunType A B) (by simp [dt_cons_chain_result]) h

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
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Fun m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A', B', hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
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
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      have hInner :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i =
            SmtType.Map A B :=
        typeof_value_dt_cons_inner_eq_of_eq_non_none h (by simp)
      rw [hInner] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Map A B) (by simp [dt_cons_chain_result]) h

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
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      have hInner :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i =
            SmtType.Seq T :=
        typeof_value_dt_cons_inner_eq_of_eq_non_none h (by simp)
      rw [hInner] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Seq T) (by simp [dt_cons_chain_result]) h

/-- Predicate asserting that every value in a list has the given SMT type. -/
def list_typed (T : SmtType) : List SmtValue -> Prop
  | [] => True
  | v :: vs => __smtx_typeof_value v = T ∧ list_typed T vs

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
  simpa [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value] using typeof_pack_string s

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
