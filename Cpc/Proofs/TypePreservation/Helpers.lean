import Cpc.Proofs.TypePreservation.Base

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
  | SmtValue.Binary w n => by
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod]
  | SmtValue.Map m => by
      intro h
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Fun m => by
      intro h
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
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
  | SmtValue.UValue _ _ => by
      simp [__smtx_typeof_value]
  | SmtValue.RegLan _ => by
      simp [__smtx_typeof_value]
  | SmtValue.DtCons s' d i => by
      intro h
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | SmtValue.Apply f v => by
      intro h
      exact apply_value_non_chain_result_impossible
        (U := SmtType.TypeRef s) (by simp [dt_cons_chain_result]) h

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
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
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
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Bool) (by simp [dt_cons_chain_result]) h

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
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
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
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Int) (by simp [dt_cons_chain_result]) h

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
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
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
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Real) (by simp [dt_cons_chain_result]) h

/-- Canonical-form lemma for `bitvec_value`. -/
theorem bitvec_value_canonical
    {v : SmtValue}
    {w : native_Nat}
    (h : __smtx_typeof_value v = SmtType.BitVec w) :
    ∃ n : native_Int, v = SmtValue.Binary (native_nat_to_int w) n := by
  cases v with
  | Binary w' n =>
      cases hWidth : native_zleq 0 w' <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w')) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.BitVec w) (by simp [dt_cons_chain_result]) h

/-- Lemma about `bitvec_width_nonneg`. -/
theorem bitvec_width_nonneg
    {w n : native_Int} {u : native_Nat}
    (h : __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec u) :
    native_zleq 0 w = true := by
  cases hWidth : native_zleq 0 w <;>
    cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  simp

/-- A well-typed bitvector value has a canonical payload for its width. -/
theorem bitvec_payload_canonical
    {w n : native_Int} {u : native_Nat}
    (h : __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec u) :
    native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
  cases hWidth : native_zleq 0 w <;>
    cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  simp

/-- A canonical bitvector payload is in range for its width. -/
theorem bitvec_payload_range_of_canonical
    {w n : native_Int}
    (hWidth : native_zleq 0 w = true)
    (hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    0 <= n ∧ n < native_int_pow2 w := by
  have hw : 0 <= w := by
    simpa [SmtEval.native_zleq] using hWidth
  have hPowPos : 0 < native_int_pow2 w := by
    have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
    simp [SmtEval.native_int_pow2, SmtEval.native_zexp_total, hnot]
    exact Int.pow_pos (by decide)
  have hEq : n = native_mod_total n (native_int_pow2 w) := by
    simpa [SmtEval.native_zeq] using hMod
  constructor
  · rw [hEq]
    exact Int.emod_nonneg n (Int.ne_of_gt hPowPos)
  · rw [hEq]
    exact Int.emod_lt_of_pos n hPowPos

/-- Powers of two are monotone for nonnegative integer exponents. -/
theorem native_int_pow2_le_of_le_nonneg
    {a b : native_Int}
    (ha : 0 <= a)
    (hab : a <= b) :
    native_int_pow2 a <= native_int_pow2 b := by
  have hb : 0 <= b := Int.le_trans ha hab
  have hnotA : ¬ a < 0 := Int.not_lt_of_ge ha
  have hnotB : ¬ b < 0 := Int.not_lt_of_ge hb
  have hnat : Int.toNat a <= Int.toNat b :=
    Int.toNat_le_toNat hab
  have hpowNat : 2 ^ Int.toNat a <= 2 ^ Int.toNat b :=
    Nat.pow_le_pow_of_le (by decide) hnat
  have hpowInt :
      ((2 ^ Int.toNat a : Nat) : Int) <= ((2 ^ Int.toNat b : Nat) : Int) :=
    Int.ofNat_le.mpr hpowNat
  simpa [SmtEval.native_int_pow2, SmtEval.native_zexp_total, hnotA, hnotB] using hpowInt

/-- A payload canonical for width `w` remains canonical after zero-extension by `i`. -/
theorem bitvec_payload_canonical_zero_extend
    {i w n : native_Int}
    (hi0 : native_zleq 0 i = true)
    (hw0 : native_zleq 0 w = true)
    (hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    native_zeq n (native_mod_total n (native_int_pow2 (native_zplus i w))) = true := by
  have hi : 0 <= i := by
    simpa [SmtEval.native_zleq] using hi0
  have hw : 0 <= w := by
    simpa [SmtEval.native_zleq] using hw0
  have hRange := bitvec_payload_range_of_canonical hw0 hMod
  have hleWidth : w <= native_zplus i w := by
    simpa [SmtEval.native_zplus] using (Int.le_add_of_nonneg_left (a := w) hi)
  have hpowLe : native_int_pow2 w <= native_int_pow2 (native_zplus i w) :=
    native_int_pow2_le_of_le_nonneg hw hleWidth
  have hltNew : n < native_int_pow2 (native_zplus i w) :=
    Int.lt_of_lt_of_le hRange.2 hpowLe
  have hEqNew : native_mod_total n (native_int_pow2 (native_zplus i w)) = n := by
    simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hRange.1 hltNew
  simp [SmtEval.native_zeq, hEqNew]

/-- Reducing a payload modulo a width makes it canonical for that width. -/
theorem native_mod_total_canonical
    (w n : native_Int) :
    native_zeq (native_mod_total n (native_int_pow2 w))
      (native_mod_total (native_mod_total n (native_int_pow2 w)) (native_int_pow2 w)) = true := by
  simp [SmtEval.native_zeq, SmtEval.native_mod_total]

/-- Derives `typeof_value_binary` from `nonneg`. -/
theorem typeof_value_binary_of_nonneg
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true)
    (hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec (native_int_to_nat w) := by
  simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod]

/-- A bitvector value whose payload has just been reduced modulo its width is well-typed. -/
theorem typeof_value_binary_mod_of_nonneg
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __smtx_typeof_value (SmtValue.Binary w (native_mod_total n (native_int_pow2 w))) =
      SmtType.BitVec (native_int_to_nat w) := by
  have hMod :
      native_zeq (native_mod_total n (native_int_pow2 w))
        (native_mod_total (native_mod_total n (native_int_pow2 w)) (native_int_pow2 w)) = true := by
    exact native_mod_total_canonical w n
  exact typeof_value_binary_of_nonneg w (native_mod_total n (native_int_pow2 w)) hWidth hMod

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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Map A B) (by simp [dt_cons_chain_result]) h

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
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Set A) (by simp [dt_cons_chain_result]) h

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
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.Seq T) (by simp [dt_cons_chain_result]) h

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
  rw [__smtx_model_eval.eq_4, __smtx_typeof.eq_4]
  simpa [__smtx_typeof_value] using typeof_pack_string s

/-- Lemma about `map_lookup_typed`. -/
theorem map_lookup_typed :
    ∀ {m : SmtMap} {A B : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_typeof_value i = A ->
        __smtx_typeof_value (__smtx_msm_lookup A m i) = B
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
        have hRec : __smtx_typeof_value (__smtx_msm_lookup A m i) = B :=
          map_lookup_typed hm hi
        by_cases hVeq : __smtx_value_eq A j i
        · simpa [__smtx_msm_lookup, native_ite, hVeq] using he
        · simpa [__smtx_msm_lookup, native_ite, hVeq] using hRec
      · simp [__smtx_typeof_map_value, native_ite, hEq] at hMap

/-- Lemma about `map_select_typed`. -/
theorem map_select_typed
    {m : SmtMap} {A B : SmtType} {i : SmtValue}
    (hMap : __smtx_typeof_map_value m = SmtType.Map A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_map_select (SmtValue.Map m) i) = B := by
  have hIndex :
      __smtx_index_typeof_map (__smtx_typeof_map_value m) = A := by
    simp [hMap, __smtx_index_typeof_map]
  simpa [__smtx_map_select, hIndex] using
    map_lookup_typed (m := m) (A := A) (B := B) (i := i) hMap hi

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
  | DtCons s d i =>
      simpa [dt_cons_chain_result] using dt_cons_chain_result_of_dt_cons_value_type h
  | Apply f x =>
      exfalso
      exact apply_value_non_chain_result_impossible
        (U := SmtType.RegLan) (by simp [dt_cons_chain_result]) h

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

/-- Derives `arith_unop_arg` from `non_none`. -/
theorem arith_unop_arg_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_arith_overload_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, __smtx_typeof_arith_overload_op_1, h] at ht
  · simp
  · simp

/-- Derives `to_real_arg` from `non_none`. -/
theorem to_real_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.to_real t)) :
    __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  rw [__smtx_typeof.eq_18] at ht
  cases h : __smtx_typeof t <;>
    simp [native_ite, native_Teq, h] at ht
  · exact Or.inl rfl
  · exact Or.inr rfl

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
  rw [__smtx_typeof.eq_21] at ht
  cases h : __smtx_typeof t <;>
    simp [native_ite, native_Teq, h] at ht
  rfl

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

end Smtm
