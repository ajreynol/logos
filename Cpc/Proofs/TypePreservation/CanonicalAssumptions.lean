import Cpc.SmtModel

open SmtEval
open Smtm

namespace Smtm

/--
Datatype-default canonicity for the generated model.

The theorem keeps the historical `_assumption` name used by the downstream
proof skeleton, but `native_inhabited_type` now uniformly carries exactly this
canonical default witness.
-/
theorem cpc_datatype_type_default_typed_canonical_assumption
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  classical
  simpa [native_inhabited_type, __smtx_value_canonical, native_and] using _hInh

private def smt_map_keys : SmtMap -> List SmtValue
  | SmtMap.cons i _ m => i :: smt_map_keys m
  | SmtMap.default _ _ => []

private theorem native_veq_eq_false_of_ne {a b : SmtValue} (h : a ≠ b) :
    native_veq a b = false := by
  simp [native_veq, h]

private theorem native_veq_false_symm {a b : SmtValue}
    (h : native_veq a b = false) :
    native_veq b a = false := by
  simp [native_veq] at h ⊢
  intro hEq
  exact h hEq.symm

private theorem native_veq_true_iff_eq {a b : SmtValue} :
    native_veq a b = true ↔ a = b := by
  simp [native_veq]

private theorem type_default_typed_canonical_of_native_inhabited
    {T : SmtType}
    (h : native_inhabited_type T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical_bool (__smtx_type_default T) = true := by
  simpa [native_inhabited_type, native_and] using h

private theorem value_dt_substitute_canonical_bool
    (s : native_String)
    (d : SmtDatatype) :
    ∀ v : SmtValue,
      __smtx_value_canonical_bool v = true ->
        __smtx_value_canonical_bool (__smtx_value_dt_substitute s d v) = true
  | SmtValue.NotValue, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Boolean b, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Numeral n, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Rational q, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Binary w n, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Map m, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Fun fid A B, h => by
    simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Set m, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Seq ss, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Char c, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.UValue i e, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.RegLan r, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.DtCons s' d' i, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Apply f a, h => by
      have hParts :
          __smtx_value_canonical_bool f = true ∧
            __smtx_value_canonical_bool a = true := by
        simpa [__smtx_value_canonical_bool, native_and] using h
      have hf : __smtx_value_canonical_bool f = true := by
        exact hParts.1
      have ha : __smtx_value_canonical_bool a = true := by
        exact hParts.2
      have hf' := value_dt_substitute_canonical_bool s d f hf
      have ha' := value_dt_substitute_canonical_bool s d a ha
      simp [__smtx_value_dt_substitute, __smtx_value_canonical_bool,
        native_and, hf', ha']

private theorem value_dt_substitute_eq_notValue
    (s : native_String)
    (d : SmtDatatype) :
    ∀ v : SmtValue,
      __smtx_value_dt_substitute s d v = SmtValue.NotValue ↔
        v = SmtValue.NotValue
  | SmtValue.NotValue => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Boolean b => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Numeral n => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Rational q => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Binary w n => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Map m => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Fun fid A B => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Set m => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Seq ss => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Char c => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.UValue i e => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.RegLan r => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.DtCons s' d' i => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Apply f a => by
      simp [__smtx_value_dt_substitute]

private theorem value_dt_substitute_ne_notValue
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    __smtx_value_dt_substitute s d v ≠ SmtValue.NotValue := by
  intro hSub
  exact h ((value_dt_substitute_eq_notValue s d v).1 hSub)

private theorem native_veq_value_dt_substitute_notValue_false
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    native_veq (__smtx_value_dt_substitute s d v) SmtValue.NotValue = false := by
  exact native_veq_eq_false_of_ne (value_dt_substitute_ne_notValue s d h)

private theorem value_dt_substitute_type_default_eq_of_not_datatype
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType)
    (hDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d') :
    __smtx_value_dt_substitute s d (__smtx_type_default T) =
      __smtx_type_default T := by
  cases T <;> simp [__smtx_type_default, __smtx_value_dt_substitute]
  case Datatype s' d' =>
    exact False.elim (hDatatype s' d' rfl)

private theorem dt_cons_wf_rec_tail_of_true
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_ite] at h ⊢
  all_goals first | exact h | exact h.2 | exact h.2.2

private theorem dt_wf_cons_of_wf
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  by_cases hc : __smtx_dt_cons_wf_rec c refs = true
  · exact hc
  · have hFalse : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = false := by
      cases d <;> simp [__smtx_dt_wf_rec, native_ite, hc]
    rw [hFalse] at h
    simp at h

private theorem dt_wf_tail_of_nonempty_tail_wf
    {c cTail : SmtDatatypeCons}
    {dTail : SmtDatatype}
    {refs : RefList}
    (h :
      __smtx_dt_wf_rec
        (SmtDatatype.sum c (SmtDatatype.sum cTail dTail)) refs = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true := by
  have hc : __smtx_dt_cons_wf_rec c refs = true :=
    dt_wf_cons_of_wf h
  simpa [__smtx_dt_wf_rec, native_ite, hc] using h

private theorem dt_cons_wf_field_default_substitute_canonical
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_value_canonical_bool
      (__smtx_value_dt_substitute s d (__smtx_type_default T)) = true := by
  cases T <;>
    simp [__smtx_dt_cons_wf_rec, __smtx_type_default,
      __smtx_value_dt_substitute, native_ite] at hWf ⊢
  case TypeRef r =>
      simp [__smtx_value_canonical_bool]
  all_goals
    have hDef :=
      type_default_typed_canonical_of_native_inhabited hWf.1
    exact value_dt_substitute_canonical_bool s d
      (__smtx_type_default _) hDef.2

private theorem datatype_cons_default_canonical_of_wf
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        __smtx_value_canonical_bool v = true ->
          __smtx_value_canonical_bool
            (__smtx_datatype_cons_default s d v c) = true
  | SmtDatatypeCons.unit, v, _hWf, hv => by
      simpa [__smtx_datatype_cons_default] using hv
  | SmtDatatypeCons.cons T c, v, hWf, hv => by
      let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
      by_cases hDefault : native_veq v0 SmtValue.NotValue = true
      · simp [__smtx_datatype_cons_default, v0, native_ite, hDefault,
          __smtx_value_canonical_bool]
      · have hDefaultFalse : native_veq v0 SmtValue.NotValue = false := by
          cases h : native_veq v0 SmtValue.NotValue <;>
            simp [h] at hDefault ⊢
        have hTail : __smtx_dt_cons_wf_rec c refs = true :=
          dt_cons_wf_rec_tail_of_true hWf
        have hSubCan :
            __smtx_value_canonical_bool v0 = true := by
          simpa [v0] using
            dt_cons_wf_field_default_substitute_canonical
              s d (T := T) (c := c) hWf
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v v0) = true := by
          simp [__smtx_value_canonical_bool, native_and, hv, hSubCan]
        have hRec :=
          datatype_cons_default_canonical_of_wf s d refs c
            (SmtValue.Apply v v0) hTail hApplyCan
        simpa [__smtx_datatype_cons_default, v0, native_ite, hDefaultFalse]
          using hRec

private theorem datatype_cons_default_head_of_ne_notValue
    (s : native_String)
    (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_datatype_cons_default s d v c ≠ SmtValue.NotValue ->
        __vsm_apply_head (__smtx_datatype_cons_default s d v c) =
          __vsm_apply_head v
  | SmtDatatypeCons.unit, v, _hNe => by
      simp [__smtx_datatype_cons_default]
  | SmtDatatypeCons.cons T c, v, hNe => by
      by_cases hDefault :
          native_veq
              (__smtx_value_dt_substitute s d (__smtx_type_default T))
              SmtValue.NotValue = true
      · have hEq :
            __smtx_datatype_cons_default s d v
                (SmtDatatypeCons.cons T c) = SmtValue.NotValue := by
          simp [__smtx_datatype_cons_default, native_ite, hDefault]
        exact False.elim (hNe hEq)
      · have hDefaultFalse :
            native_veq
                (__smtx_value_dt_substitute s d (__smtx_type_default T))
                SmtValue.NotValue = false := by
          cases h :
              native_veq
                (__smtx_value_dt_substitute s d (__smtx_type_default T))
                SmtValue.NotValue <;>
            simp [h] at hDefault ⊢
        have hTailNe :
            __smtx_datatype_cons_default s d
                (SmtValue.Apply v
                  (__smtx_value_dt_substitute s d (__smtx_type_default T))) c ≠
              SmtValue.NotValue := by
          intro hTail
          apply hNe
          simpa [__smtx_datatype_cons_default, native_ite, hDefaultFalse]
            using hTail
        have hHead :=
          datatype_cons_default_head_of_ne_notValue s d c
            (SmtValue.Apply v
              (__smtx_value_dt_substitute s d (__smtx_type_default T))) hTailNe
        simpa [__smtx_datatype_cons_default, native_ite, hDefaultFalse,
          __vsm_apply_head] using hHead

private theorem type_default_ne_notValue_of_native_inhabited
    {T : SmtType}
    (hInh : native_inhabited_type T = true)
    (hT : T ≠ SmtType.None) :
    __smtx_type_default T ≠ SmtValue.NotValue := by
  intro hEq
  have hTy := (type_default_typed_canonical_of_native_inhabited hInh).1
  rw [hEq] at hTy
  simp [__smtx_typeof_value] at hTy
  exact hT hTy.symm

private theorem dt_cons_wf_finite_field_default_substitute_ne_notValue
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
      SmtValue.NotValue := by
  cases T <;>
    simp [__smtx_dt_cons_wf_rec, __smtx_is_finite_datatype_cons,
      __smtx_is_finite_type, __smtx_type_default,
      __smtx_value_dt_substitute, native_and, native_ite] at hWf hFin ⊢
  all_goals
    have hDefaultNe :
        __smtx_type_default _ ≠ SmtValue.NotValue :=
      type_default_ne_notValue_of_native_inhabited hWf.1 (by simp)
    exact value_dt_substitute_ne_notValue s d hDefaultNe

private theorem dt_cons_finite_tail_of_true
    {T : SmtType}
    {c : SmtDatatypeCons}
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    __smtx_is_finite_datatype_cons c = true := by
  cases T <;>
    simp [__smtx_is_finite_datatype_cons, __smtx_is_finite_type,
      native_and] at hFin ⊢
  all_goals first | exact hFin | exact hFin.2

private theorem dt_cons_finite_head_of_true
    {T : SmtType}
    {c : SmtDatatypeCons}
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    __smtx_is_finite_type T = true := by
  cases T <;>
    simp [__smtx_is_finite_datatype_cons, __smtx_is_finite_type,
      native_and] at hFin ⊢
  all_goals first | exact hFin | exact hFin.1

private theorem dt_cons_wf_head_type_wf_rec_of_finite
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    __smtx_type_wf_rec T refs = true := by
  cases T <;>
    simp [__smtx_dt_cons_wf_rec, __smtx_is_finite_datatype_cons,
      __smtx_is_finite_type, native_and, native_ite] at hWf hFin ⊢
  all_goals first | exact hWf.2.1 | exact hWf.1

private theorem finite_dt_cons_of_finite_sum
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    (hFin : __smtx_is_finite_datatype (SmtDatatype.sum c d) = true) :
    __smtx_is_finite_datatype_cons c = true := by
  have hParts :
      __smtx_is_finite_datatype_cons c = true ∧
        __smtx_is_finite_datatype d = true := by
    simpa [__smtx_is_finite_datatype, native_and] using hFin
  exact hParts.1

private theorem finite_dt_tail_of_finite_sum
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    (hFin : __smtx_is_finite_datatype (SmtDatatype.sum c d) = true) :
    __smtx_is_finite_datatype d = true := by
  have hParts :
      __smtx_is_finite_datatype_cons c = true ∧
        __smtx_is_finite_datatype d = true := by
    simpa [__smtx_is_finite_datatype, native_and] using hFin
  exact hParts.2

private theorem datatype_cons_default_ne_notValue_of_wf_finite
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        __smtx_is_finite_datatype_cons c = true ->
          v ≠ SmtValue.NotValue ->
            __smtx_datatype_cons_default s d v c ≠ SmtValue.NotValue
  | SmtDatatypeCons.unit, v, _hWf, _hFin, hvNe => by
      simpa [__smtx_datatype_cons_default] using hvNe
  | SmtDatatypeCons.cons T c, v, hWf, hFin, _hvNe => by
      let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
      have hV0Ne : v0 ≠ SmtValue.NotValue := by
        simpa [v0] using
          dt_cons_wf_finite_field_default_substitute_ne_notValue
            s d (T := T) (c := c) hWf hFin
      have hV0False : native_veq v0 SmtValue.NotValue = false :=
        native_veq_eq_false_of_ne hV0Ne
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailFin : __smtx_is_finite_datatype_cons c = true := by
        exact dt_cons_finite_tail_of_true hFin
      have hApplyNe : SmtValue.Apply v v0 ≠ SmtValue.NotValue := by
        intro hEq
        cases hEq
      have hRec :=
        datatype_cons_default_ne_notValue_of_wf_finite
          s d refs c (SmtValue.Apply v v0) hTailWf hTailFin hApplyNe
      simpa [__smtx_datatype_cons_default, v0, native_ite, hV0False]
        using hRec

private theorem datatype_default_sum_first_of_cons_default_ne_notValue
    (s : native_String)
    (d0 : SmtDatatype)
    (c : SmtDatatypeCons)
    (d : SmtDatatype)
    (n : native_Nat)
    (hNe :
      __smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c ≠
        SmtValue.NotValue) :
    __smtx_datatype_default s d0 (SmtDatatype.sum c d) n =
      __smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c := by
  have hFalse :
      native_veq
          (__smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c)
          SmtValue.NotValue = false :=
    native_veq_eq_false_of_ne hNe
  simp [__smtx_datatype_default, native_ite, native_not, hFalse]

private def dtc_substitute_field_type
    (s : native_String)
    (d : SmtDatatype) : SmtType -> SmtType
  | SmtType.Datatype s' d' =>
      SmtType.Datatype s'
        (native_ite (native_streq s s') d' (__smtx_dt_substitute s d d'))
  | T =>
      native_ite (native_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T

private def dtc_type_chain
    (s : native_String)
    (d : SmtDatatype) : SmtDatatypeCons -> SmtType -> SmtType
  | SmtDatatypeCons.unit, R => R
  | SmtDatatypeCons.cons T c, R =>
      SmtType.DtcAppType (dtc_substitute_field_type s d T)
        (dtc_type_chain s d c R)

private def dt_append : SmtDatatype -> SmtDatatype -> SmtDatatype
  | SmtDatatype.null, d => d
  | SmtDatatype.sum c rest, d => SmtDatatype.sum c (dt_append rest d)

private def dt_constructor_offset : SmtDatatype -> Nat
  | SmtDatatype.null => 0
  | SmtDatatype.sum _ rest => Nat.succ (dt_constructor_offset rest)

private theorem dt_append_singleton_tail
    : ∀ (pre : SmtDatatype) (c : SmtDatatypeCons) (tail : SmtDatatype),
    dt_append (dt_append pre (SmtDatatype.sum c SmtDatatype.null)) tail =
      dt_append pre (SmtDatatype.sum c tail)
  | SmtDatatype.null, c, tail => by
      rfl
  | SmtDatatype.sum cHead rest, c, tail => by
      simp [dt_append, dt_append_singleton_tail rest c tail]

private def dtc_all_fields_non_datatype : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons (SmtType.Datatype _ _) _ => False
  | SmtDatatypeCons.cons _ c => dtc_all_fields_non_datatype c

private def dt_first_constructor_all_fields_non_datatype : SmtDatatype -> Prop
  | SmtDatatype.null => True
  | SmtDatatype.sum c _ => dtc_all_fields_non_datatype c

private theorem typeof_dt_cons_value_rec_substitute_zero_eq_chain
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (dTail : SmtDatatype),
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
          (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) dTail) 0 =
        dtc_type_chain s d0 c (SmtType.Datatype s d0)
  | SmtDatatypeCons.unit, dTail => by
      simp [__smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
        dtc_type_chain]
  | SmtDatatypeCons.cons T c, dTail => by
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
          dtc_type_chain, dtc_substitute_field_type, native_ite, native_Teq,
          native_streq, typeof_dt_cons_value_rec_substitute_zero_eq_chain s d0 c dTail]

private theorem typeof_dt_cons_second_eq_dtc_type_chain
    (s : native_String)
    (c cTail : SmtDatatypeCons)
    (dTail : SmtDatatype) :
    let d := SmtDatatype.sum c (SmtDatatype.sum cTail dTail)
    __smtx_typeof_value (SmtValue.DtCons s d 1) =
      dtc_type_chain s d cTail (SmtType.Datatype s d) := by
  intro d
  simpa [d, __smtx_typeof_value, __smtx_dt_substitute,
    __smtx_typeof_dt_cons_value_rec] using
    typeof_dt_cons_value_rec_substitute_zero_eq_chain
      s d cTail (__smtx_dt_substitute s d dTail)

private theorem typeof_dt_cons_value_rec_append_offset_eq_dtc_type_chain
    (s : native_String)
    (dRoot : SmtDatatype) :
    ∀ (pre : SmtDatatype) (c : SmtDatatypeCons) (dTail : SmtDatatype),
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dRoot)
          (__smtx_dt_substitute s dRoot
            (dt_append pre (SmtDatatype.sum c dTail)))
          (dt_constructor_offset pre) =
        dtc_type_chain s dRoot c (SmtType.Datatype s dRoot)
  | SmtDatatype.null, c, dTail => by
      simpa [dt_append, dt_constructor_offset] using
        typeof_dt_cons_value_rec_substitute_zero_eq_chain
          s dRoot c (__smtx_dt_substitute s dRoot dTail)
  | SmtDatatype.sum cHead rest, c, dTail => by
      simpa [dt_append, dt_constructor_offset, __smtx_dt_substitute,
        __smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_append_offset_eq_dtc_type_chain
          s dRoot rest c dTail

private theorem typeof_dt_cons_append_offset_eq_dtc_type_chain
    (s : native_String)
    (dRoot pre : SmtDatatype)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (hRoot : dRoot = dt_append pre (SmtDatatype.sum c dTail)) :
    __smtx_typeof_value
        (SmtValue.DtCons s dRoot (dt_constructor_offset pre)) =
      dtc_type_chain s dRoot c (SmtType.Datatype s dRoot) := by
  subst dRoot
  simpa [__smtx_typeof_value] using
    typeof_dt_cons_value_rec_append_offset_eq_dtc_type_chain
      s (dt_append pre (SmtDatatype.sum c dTail)) pre c dTail

private theorem typeof_dt_cons_first_eq_dtc_type_chain
    (s : native_String)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype) :
    let d := SmtDatatype.sum c dTail
    __smtx_typeof_value (SmtValue.DtCons s d 0) =
      dtc_type_chain s d c (SmtType.Datatype s d) := by
  intro d
  simpa [d, __smtx_typeof_value, __smtx_dt_substitute,
    __smtx_typeof_dt_cons_value_rec] using
    typeof_dt_cons_value_rec_substitute_zero_eq_chain
      s d c (__smtx_dt_substitute s d dTail)

private theorem dtc_substitute_field_type_eq_of_non_datatype_finite
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    (hNotDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d')
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    dtc_substitute_field_type s d T = T := by
  cases T <;>
    simp [dtc_substitute_field_type, __smtx_is_finite_datatype_cons,
      __smtx_is_finite_type, native_and, native_ite, native_Teq] at hFin hNotDatatype ⊢

private theorem type_ne_none_of_finite_datatype_cons_head
    {T : SmtType}
    {c : SmtDatatypeCons}
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    T ≠ SmtType.None := by
  intro hEq
  have hBad := hFin
  rw [hEq] at hBad
  simp [__smtx_is_finite_datatype_cons, __smtx_is_finite_type,
    native_and] at hBad

private theorem dtc_substitute_field_type_ne_none_of_finite
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    dtc_substitute_field_type s d T ≠ SmtType.None := by
  cases T <;>
    simp [dtc_substitute_field_type, __smtx_is_finite_datatype_cons,
      __smtx_is_finite_type, native_and, native_ite, native_Teq] at hFin ⊢

private theorem value_dt_substitute_datatype_cons_default_eq_of_all_non_datatype
    (s : native_String)
    (d : SmtDatatype)
    (sField : native_String)
    (dField : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      dtc_all_fields_non_datatype c ->
        __smtx_value_dt_substitute s d
            (__smtx_datatype_cons_default sField dField v c) =
          __smtx_datatype_cons_default sField (__smtx_dt_substitute s d dField)
            (__smtx_value_dt_substitute s d v) c
  | SmtDatatypeCons.unit, v, _hAll => by
      simp [__smtx_datatype_cons_default]
  | SmtDatatypeCons.cons T c, v, hAll => by
      have hNotDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d' := by
        intro s' d' hEq
        rw [hEq] at hAll
        simp [dtc_all_fields_non_datatype] at hAll
      have hAllTail : dtc_all_fields_non_datatype c := by
        cases T <;> simp [dtc_all_fields_non_datatype] at hAll
        all_goals first | exact hAll | exact False.elim hAll
      have hOld :
          __smtx_value_dt_substitute sField dField (__smtx_type_default T) =
            __smtx_type_default T :=
        value_dt_substitute_type_default_eq_of_not_datatype
          sField dField T hNotDatatype
      have hNew :
          __smtx_value_dt_substitute sField (__smtx_dt_substitute s d dField)
              (__smtx_type_default T) =
            __smtx_type_default T :=
        value_dt_substitute_type_default_eq_of_not_datatype
          sField (__smtx_dt_substitute s d dField) T hNotDatatype
      have hSub :
          __smtx_value_dt_substitute s d (__smtx_type_default T) =
            __smtx_type_default T :=
        value_dt_substitute_type_default_eq_of_not_datatype
          s d T hNotDatatype
      cases hDefault : native_veq (__smtx_type_default T) SmtValue.NotValue
      · have hRec :=
          value_dt_substitute_datatype_cons_default_eq_of_all_non_datatype
            s d sField dField c
            (SmtValue.Apply v (__smtx_type_default T)) hAllTail
        simpa [__smtx_datatype_cons_default, hOld, hNew, hSub, hDefault,
          native_ite, __smtx_value_dt_substitute] using hRec
      · simp [__smtx_datatype_cons_default, hOld, hNew, hDefault, native_ite,
          __smtx_value_dt_substitute]

private theorem dtc_substitute_eq_self_of_all_non_datatype_finite
    (s : native_String)
    (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons),
      dtc_all_fields_non_datatype c ->
        __smtx_is_finite_datatype_cons c = true ->
          __smtx_dtc_substitute s d c = c
  | SmtDatatypeCons.unit, _hAll, _hFin => by
      simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, hAll, hFin => by
      have hAllTail : dtc_all_fields_non_datatype c := by
        cases T <;> simp [dtc_all_fields_non_datatype] at hAll
        all_goals first | exact hAll | exact False.elim hAll
      have hFinTail : __smtx_is_finite_datatype_cons c = true :=
        dt_cons_finite_tail_of_true hFin
      have hTail :=
        dtc_substitute_eq_self_of_all_non_datatype_finite
          s d c hAllTail hFinTail
      cases T <;>
        simp [dtc_all_fields_non_datatype, __smtx_dtc_substitute,
          __smtx_is_finite_datatype_cons, __smtx_is_finite_type,
          native_and, native_ite, native_Teq, hTail] at hAll hFin ⊢

private theorem datatype_field_name_ne_of_wf_rec_contains
    {s sField : native_String}
    {dField : SmtDatatype}
    {refs : RefList}
    (hRoot : native_reflist_contains refs s = true)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true) :
    native_streq s sField = false := by
  cases hEq : native_streq s sField <;> simp [native_streq] at hEq ⊢
  subst sField
  simp [__smtx_type_wf_rec, hRoot, native_ite] at hRec

mutual

private theorem dtc_substitute_eq_self_of_wf_rec_finite_contains
    (s : native_String)
    (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (refs : RefList),
      native_reflist_contains refs s = true ->
        __smtx_dt_cons_wf_rec c refs = true ->
          __smtx_is_finite_datatype_cons c = true ->
            __smtx_dtc_substitute s d c = c
  | SmtDatatypeCons.unit, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, refs, hRoot, hWf, hFin => by
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailFin : __smtx_is_finite_datatype_cons c = true :=
        dt_cons_finite_tail_of_true hFin
      have hTailSub :
          __smtx_dtc_substitute s d c = c :=
        dtc_substitute_eq_self_of_wf_rec_finite_contains
          s d c refs hRoot hTailWf hTailFin
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_is_finite_datatype_cons,
          __smtx_is_finite_type, native_and, native_ite, native_Teq,
          hTailSub] at hWf hFin ⊢
      case Datatype sField dField =>
        have hParts :
            native_inhabited_type (SmtType.Datatype sField dField) = true ∧
              __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true ∧
                __smtx_dt_cons_wf_rec c refs = true := by
          simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
        have hNameNe : native_streq s sField = false :=
          datatype_field_name_ne_of_wf_rec_contains hRoot hParts.2.1
        have hRefsRoot :
            native_reflist_contains (native_reflist_insert refs sField) s = true := by
          simp [native_reflist_contains, native_reflist_insert] at hRoot ⊢
          exact Or.inr hRoot
        have hDtWf :
            __smtx_dt_wf_rec dField
                (native_reflist_insert refs sField) = true := by
          have hDtParts :
              ¬ sField ∈ refs ∧
                __smtx_dt_wf_rec dField
                  (native_reflist_insert refs sField) = true := by
            simpa [__smtx_type_wf_rec, native_reflist_contains,
              native_reflist_insert, native_ite] using hParts.2.1
          exact hDtParts.2
        have hDtFin : __smtx_is_finite_datatype dField = true := by
          simpa [__smtx_is_finite_type] using hFin.1
        have hDtSub :
            __smtx_dt_substitute s d dField = dField :=
          dt_substitute_eq_self_of_wf_rec_finite_contains
            s d dField (native_reflist_insert refs sField)
            hRefsRoot hDtWf hDtFin
        simp [hNameNe, hDtSub]

private theorem dt_substitute_eq_self_of_wf_rec_finite_contains
    (s : native_String)
    (d : SmtDatatype) :
    ∀ (d0 : SmtDatatype) (refs : RefList),
      native_reflist_contains refs s = true ->
        __smtx_dt_wf_rec d0 refs = true ->
          __smtx_is_finite_datatype d0 = true ->
            __smtx_dt_substitute s d d0 = d0
  | SmtDatatype.null, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_dt_substitute]
  | SmtDatatype.sum c dTail, refs, hRoot, hWf, hFin => by
      have hConsWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      have hConsFin : __smtx_is_finite_datatype_cons c = true :=
        finite_dt_cons_of_finite_sum hFin
      have hConsSub :
          __smtx_dtc_substitute s d c = c :=
        dtc_substitute_eq_self_of_wf_rec_finite_contains
          s d c refs hRoot hConsWf hConsFin
      cases dTail with
      | null =>
          simp [__smtx_dt_substitute, hConsSub]
      | sum cTail dTailTail =>
          have hTailWf :
              __smtx_dt_wf_rec
                  (SmtDatatype.sum cTail dTailTail) refs = true :=
            dt_wf_tail_of_nonempty_tail_wf hWf
          have hTailFin :
              __smtx_is_finite_datatype
                  (SmtDatatype.sum cTail dTailTail) = true :=
            finite_dt_tail_of_finite_sum hFin
          have hTailSub :
              __smtx_dt_substitute s d
                  (SmtDatatype.sum cTail dTailTail) =
                SmtDatatype.sum cTail dTailTail :=
            dt_substitute_eq_self_of_wf_rec_finite_contains
              s d (SmtDatatype.sum cTail dTailTail) refs
              hRoot hTailWf hTailFin
          change
            SmtDatatype.sum (__smtx_dtc_substitute s d c)
                (__smtx_dt_substitute s d
                  (SmtDatatype.sum cTail dTailTail)) =
              SmtDatatype.sum c (SmtDatatype.sum cTail dTailTail)
          rw [hConsSub, hTailSub]

end

mutual

private theorem dtc_substitute_eq_self_of_wf_rec_not_contains
    (s : native_String)
    (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (refs : RefList),
      native_reflist_contains refs s = false ->
        __smtx_dt_cons_wf_rec c refs = true ->
          __smtx_dtc_substitute s d c = c
  | SmtDatatypeCons.unit, _refs, _hNot, _hWf => by
      simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, refs, hNot, hWf => by
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailSub :
          __smtx_dtc_substitute s d c = c :=
        dtc_substitute_eq_self_of_wf_rec_not_contains
          s d c refs hNot hTailWf
      cases T <;>
        simp [__smtx_dtc_substitute, native_Teq, native_ite, hTailSub]
          at hWf ⊢
      case TypeRef r =>
        have hParts :
            native_reflist_contains refs r = true ∧
              __smtx_dt_cons_wf_rec c refs = true := by
          simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
        have hNe : r ≠ s := by
          intro hEq
          subst r
          rw [hNot] at hParts
          simp at hParts
        simp [hNe]
      case Datatype sField dField =>
        have hParts :
            native_inhabited_type (SmtType.Datatype sField dField) = true ∧
              __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true ∧
                __smtx_dt_cons_wf_rec c refs = true := by
          simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
        by_cases hEq : s = sField
        · subst sField
          simp [native_streq]
        · have hDtWf :
              __smtx_dt_wf_rec dField
                  (native_reflist_insert refs sField) = true := by
            have hDtParts :
                ¬ sField ∈ refs ∧
                  __smtx_dt_wf_rec dField
                    (native_reflist_insert refs sField) = true := by
              simpa [__smtx_type_wf_rec, native_reflist_contains,
                native_reflist_insert, native_ite] using hParts.2.1
            exact hDtParts.2
          have hNotInserted :
              native_reflist_contains
                  (native_reflist_insert refs sField) s = false := by
            simp [native_reflist_contains, native_reflist_insert] at hNot ⊢
            exact ⟨hEq, hNot⟩
          have hDtSub :
              __smtx_dt_substitute s d dField = dField :=
            dt_substitute_eq_self_of_wf_rec_not_contains
              s d dField (native_reflist_insert refs sField)
              hNotInserted hDtWf
          simp [native_streq, hEq, hDtSub]

private theorem dt_substitute_eq_self_of_wf_rec_not_contains
    (s : native_String)
    (d : SmtDatatype) :
    ∀ (d0 : SmtDatatype) (refs : RefList),
      native_reflist_contains refs s = false ->
        __smtx_dt_wf_rec d0 refs = true ->
          __smtx_dt_substitute s d d0 = d0
  | SmtDatatype.null, _refs, _hNot, _hWf => by
      simp [__smtx_dt_substitute]
  | SmtDatatype.sum c dTail, refs, hNot, hWf => by
      have hConsWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      have hConsSub :
          __smtx_dtc_substitute s d c = c :=
        dtc_substitute_eq_self_of_wf_rec_not_contains
          s d c refs hNot hConsWf
      cases dTail with
      | null =>
          simp [__smtx_dt_substitute, hConsSub]
      | sum cTail dTailTail =>
          have hTailWf :
              __smtx_dt_wf_rec
                  (SmtDatatype.sum cTail dTailTail) refs = true :=
            dt_wf_tail_of_nonempty_tail_wf hWf
          have hTailSub :
              __smtx_dt_substitute s d
                  (SmtDatatype.sum cTail dTailTail) =
                SmtDatatype.sum cTail dTailTail :=
            dt_substitute_eq_self_of_wf_rec_not_contains
              s d (SmtDatatype.sum cTail dTailTail) refs hNot hTailWf
          change
            SmtDatatype.sum (__smtx_dtc_substitute s d c)
                (__smtx_dt_substitute s d
                  (SmtDatatype.sum cTail dTailTail)) =
              SmtDatatype.sum c (SmtDatatype.sum cTail dTailTail)
          rw [hConsSub, hTailSub]

end

mutual

private theorem type_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
    (s : native_String)
    (d : SmtDatatype) :
    ∀ (T : SmtType) (refs : RefList),
      native_reflist_contains refs s = true ->
        __smtx_type_wf_rec T refs = true ->
          __smtx_is_finite_type T = true ->
            __smtx_value_dt_substitute s d (__smtx_type_default T) =
              __smtx_type_default T
  | SmtType.Datatype sField dField, refs, hRoot, hWf, hFin => by
      have hRefsRoot :
          native_reflist_contains (native_reflist_insert refs sField) s = true := by
        simp [native_reflist_contains, native_reflist_insert] at hRoot ⊢
        exact Or.inr hRoot
      have hRefsField :
          native_reflist_contains (native_reflist_insert refs sField) sField = true := by
        simp [native_reflist_contains, native_reflist_insert]
      have hDtWf :
          __smtx_dt_wf_rec dField (native_reflist_insert refs sField) = true := by
        have hDtParts :
            ¬ sField ∈ refs ∧
              __smtx_dt_wf_rec dField
                (native_reflist_insert refs sField) = true := by
          simpa [__smtx_type_wf_rec, native_reflist_contains,
            native_reflist_insert, native_ite] using hWf
        exact hDtParts.2
      have hDtFin : __smtx_is_finite_datatype dField = true := by
        simpa [__smtx_is_finite_type] using hFin
      have hDtSub :
          __smtx_dt_substitute s d dField = dField :=
        dt_substitute_eq_self_of_wf_rec_finite_contains
          s d dField (native_reflist_insert refs sField)
          hRefsRoot hDtWf hDtFin
      have hRecDefault :
          __smtx_value_dt_substitute s d
              (__smtx_datatype_default sField dField dField native_nat_zero) =
            __smtx_datatype_default sField dField dField native_nat_zero :=
        datatype_default_rec_value_dt_substitute_eq_self_of_wf_rec_finite_contains
          s d sField dField (native_reflist_insert refs sField)
          dField native_nat_zero hRefsRoot hRefsField hDtSub hDtWf hDtFin
      simpa [__smtx_type_default] using hRecDefault
  | SmtType.None, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.Bool, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.Int, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.Real, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.RegLan, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.BitVec _w, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.Map _T _U, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.Set _T, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.Seq _T, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.Char, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.TypeRef _r, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.USort _u, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.FunType _T _U, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
  | SmtType.DtcAppType _T _U, _refs, _hRoot, _hWf, _hFin => by
      simp [__smtx_type_default, __smtx_value_dt_substitute]
termination_by T _ _ _ _ => sizeOf T
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

private theorem datatype_default_rec_value_dt_substitute_eq_self_of_wf_rec_finite_contains
    (s : native_String)
    (d : SmtDatatype)
    (sField : native_String)
    (dField : SmtDatatype)
    (refs : RefList) :
    ∀ (dCur : SmtDatatype) (n : native_Nat),
      native_reflist_contains refs s = true ->
        native_reflist_contains refs sField = true ->
          __smtx_dt_substitute s d dField = dField ->
            __smtx_dt_wf_rec dCur refs = true ->
              __smtx_is_finite_datatype dCur = true ->
                __smtx_value_dt_substitute s d
                    (__smtx_datatype_default sField dField dCur n) =
                  __smtx_datatype_default sField dField dCur n
  | SmtDatatype.null, _n, _hRoot, _hFieldRoot, _hDtSub, _hWf, _hFin => by
      simp [__smtx_datatype_default, __smtx_value_dt_substitute]
  | SmtDatatype.sum c SmtDatatype.null, n, hRoot, hFieldRoot, hDtSub, hWf, hFin => by
      let v0 := __smtx_datatype_cons_default sField dField
        (SmtValue.DtCons sField dField n) c
      have hHeadStable :
          __smtx_value_dt_substitute s d (SmtValue.DtCons sField dField n) =
            SmtValue.DtCons sField dField n := by
        simp [__smtx_value_dt_substitute, hDtSub]
      have hConsWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      have hConsFin : __smtx_is_finite_datatype_cons c = true :=
        finite_dt_cons_of_finite_sum hFin
      have hConsStable :
          __smtx_value_dt_substitute s d v0 = v0 :=
        datatype_cons_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
          s d sField dField refs c (SmtValue.DtCons sField dField n)
          hRoot hFieldRoot hDtSub hConsWf hConsFin hHeadStable
      cases hChoose : native_not (native_veq v0 SmtValue.NotValue) <;>
        simp [__smtx_datatype_default, native_ite, v0, hChoose, hConsStable,
          __smtx_value_dt_substitute]
  | SmtDatatype.sum c (SmtDatatype.sum cTail dTailTail), n, hRoot, hFieldRoot, hDtSub, hWf, hFin => by
      let v0 := __smtx_datatype_cons_default sField dField
        (SmtValue.DtCons sField dField n) c
      have hHeadStable :
          __smtx_value_dt_substitute s d (SmtValue.DtCons sField dField n) =
            SmtValue.DtCons sField dField n := by
        simp [__smtx_value_dt_substitute, hDtSub]
      have hConsWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      have hConsFin : __smtx_is_finite_datatype_cons c = true :=
        finite_dt_cons_of_finite_sum hFin
      have hConsStable :
          __smtx_value_dt_substitute s d v0 = v0 :=
        datatype_cons_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
          s d sField dField refs c (SmtValue.DtCons sField dField n)
          hRoot hFieldRoot hDtSub hConsWf hConsFin hHeadStable
      have hTailWf :
          __smtx_dt_wf_rec
              (SmtDatatype.sum cTail dTailTail) refs = true :=
        dt_wf_tail_of_nonempty_tail_wf hWf
      have hTailFin :
          __smtx_is_finite_datatype
              (SmtDatatype.sum cTail dTailTail) = true :=
        finite_dt_tail_of_finite_sum hFin
      have hTailStable :
          __smtx_value_dt_substitute s d
              (__smtx_datatype_default sField dField
                (SmtDatatype.sum cTail dTailTail) (native_nat_succ n)) =
            __smtx_datatype_default sField dField
              (SmtDatatype.sum cTail dTailTail) (native_nat_succ n) :=
        datatype_default_rec_value_dt_substitute_eq_self_of_wf_rec_finite_contains
          s d sField dField refs (SmtDatatype.sum cTail dTailTail)
          (native_nat_succ n) hRoot hFieldRoot hDtSub hTailWf hTailFin
      cases hChoose : native_not (native_veq v0 SmtValue.NotValue)
      · simpa [__smtx_datatype_default, native_ite, v0, hChoose]
          using hTailStable
      · simp [__smtx_datatype_default, native_ite, v0, hChoose,
          hConsStable]
termination_by dCur _ _ _ _ _ _ =>
  sizeOf dCur
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

private theorem datatype_cons_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
    (s : native_String)
    (d : SmtDatatype)
    (sField : native_String)
    (dField : SmtDatatype)
    (refs : RefList) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      native_reflist_contains refs s = true ->
        native_reflist_contains refs sField = true ->
          __smtx_dt_substitute s d dField = dField ->
            __smtx_dt_cons_wf_rec c refs = true ->
              __smtx_is_finite_datatype_cons c = true ->
                __smtx_value_dt_substitute s d v = v ->
                  __smtx_value_dt_substitute s d
                      (__smtx_datatype_cons_default sField dField v c) =
                    __smtx_datatype_cons_default sField dField v c
  | SmtDatatypeCons.unit, v, _hRoot, _hFieldRoot, _hDtSub, _hWf, _hFin, hv => by
      simpa [__smtx_datatype_cons_default] using hv
  | SmtDatatypeCons.cons T c, v, hRoot, hFieldRoot, hDtSub, hWf, hFin, hv => by
      let arg := __smtx_value_dt_substitute sField dField (__smtx_type_default T)
      have hTypeFin : __smtx_is_finite_type T = true :=
        dt_cons_finite_head_of_true hFin
      have hTypeWf : __smtx_type_wf_rec T refs = true :=
        dt_cons_wf_head_type_wf_rec_of_finite hWf hFin
      have hArgSelfField :
          __smtx_value_dt_substitute sField dField (__smtx_type_default T) =
            __smtx_type_default T :=
        type_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
          sField dField T refs hFieldRoot hTypeWf hTypeFin
      have hArgSelfRoot :
          __smtx_value_dt_substitute s d (__smtx_type_default T) =
            __smtx_type_default T :=
        type_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
          s d T refs hRoot hTypeWf hTypeFin
      have hArgStable :
          __smtx_value_dt_substitute s d arg = arg := by
        simp [arg, hArgSelfField, hArgSelfRoot]
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailFin : __smtx_is_finite_datatype_cons c = true :=
        dt_cons_finite_tail_of_true hFin
      by_cases hArgNot :
          native_veq arg SmtValue.NotValue = true
      · simp [__smtx_datatype_cons_default, native_ite, arg, hArgNot,
          __smtx_value_dt_substitute]
      · have hArgNotFalse : native_veq arg SmtValue.NotValue = false := by
          cases h : native_veq arg SmtValue.NotValue <;>
            simp [h] at hArgNot ⊢
        have hApplyStable :
            __smtx_value_dt_substitute s d (SmtValue.Apply v arg) =
              SmtValue.Apply v arg := by
          simp [__smtx_value_dt_substitute, hv, hArgStable]
        have hRec :
            __smtx_value_dt_substitute s d
                (__smtx_datatype_cons_default sField dField
                  (SmtValue.Apply v arg) c) =
              __smtx_datatype_cons_default sField dField
                (SmtValue.Apply v arg) c :=
          datatype_cons_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
            s d sField dField refs c (SmtValue.Apply v arg)
            hRoot hFieldRoot hDtSub hTailWf hTailFin hApplyStable
        simpa [__smtx_datatype_cons_default, arg, hArgNotFalse] using hRec
termination_by c _ _ _ _ _ _ _ =>
  sizeOf c
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

end

private theorem datatype_type_default_substitute_typeof_of_wf_rec_finite_contains
    (s : native_String)
    (d : SmtDatatype)
    (sField : native_String)
    (dField : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true)
    (hInh : native_inhabited_type (SmtType.Datatype sField dField) = true)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true)
    (hFinite : __smtx_is_finite_type (SmtType.Datatype sField dField) = true) :
    __smtx_typeof_value
        (__smtx_value_dt_substitute s d
          (__smtx_type_default (SmtType.Datatype sField dField))) =
      dtc_substitute_field_type s d (SmtType.Datatype sField dField) := by
  have hNameNe : native_streq s sField = false :=
    datatype_field_name_ne_of_wf_rec_contains hRoot hRec
  have hRefsRoot :
      native_reflist_contains (native_reflist_insert refs sField) s = true := by
    simp [native_reflist_contains, native_reflist_insert] at hRoot ⊢
    exact Or.inr hRoot
  have hDtWf :
      __smtx_dt_wf_rec dField (native_reflist_insert refs sField) = true := by
    have hDtParts :
        ¬ sField ∈ refs ∧
          __smtx_dt_wf_rec dField
            (native_reflist_insert refs sField) = true := by
      simpa [__smtx_type_wf_rec, native_reflist_contains,
        native_reflist_insert, native_ite] using hRec
    exact hDtParts.2
  have hDtFin : __smtx_is_finite_datatype dField = true := by
    simpa [__smtx_is_finite_type] using hFinite
  have hDtSub :
      __smtx_dt_substitute s d dField = dField :=
    dt_substitute_eq_self_of_wf_rec_finite_contains
      s d dField (native_reflist_insert refs sField)
      hRefsRoot hDtWf hDtFin
  have hDefTy :=
    (type_default_typed_canonical_of_native_inhabited hInh).1
  have hDefaultStable :
      __smtx_value_dt_substitute s d
          (__smtx_type_default (SmtType.Datatype sField dField)) =
        __smtx_type_default (SmtType.Datatype sField dField) :=
    type_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
      s d (SmtType.Datatype sField dField) refs hRoot hRec hFinite
  rw [hDefaultStable]
  simpa [dtc_substitute_field_type, hNameNe, hDtSub] using hDefTy

private theorem dtc_substitute_field_type_eq_self_of_wf_rec_finite_contains
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true)
    (hRec : __smtx_type_wf_rec T refs = true)
    (hFinite : __smtx_is_finite_type T = true) :
    dtc_substitute_field_type s d T = T := by
  cases T <;>
    simp [dtc_substitute_field_type, __smtx_is_finite_type, native_ite,
      native_Teq] at hRec hFinite ⊢
  case Datatype sField dField =>
    have hNameNe : native_streq s sField = false :=
      datatype_field_name_ne_of_wf_rec_contains hRoot hRec
    have hRefsRoot :
        native_reflist_contains (native_reflist_insert refs sField) s = true := by
      simp [native_reflist_contains, native_reflist_insert] at hRoot ⊢
      exact Or.inr hRoot
    have hDtWf :
        __smtx_dt_wf_rec dField
            (native_reflist_insert refs sField) = true := by
      have hDtParts :
          ¬ sField ∈ refs ∧
            __smtx_dt_wf_rec dField
              (native_reflist_insert refs sField) = true := by
        simpa [__smtx_type_wf_rec, native_reflist_contains,
          native_reflist_insert, native_ite] using hRec
      exact hDtParts.2
    have hDtFin : __smtx_is_finite_datatype dField = true := by
      simpa [__smtx_is_finite_type] using hFinite
    have hDtSub :
        __smtx_dt_substitute s d dField = dField :=
      dt_substitute_eq_self_of_wf_rec_finite_contains
        s d dField (native_reflist_insert refs sField)
        hRefsRoot hDtWf hDtFin
    simp [hNameNe, hDtSub]

private theorem dtc_non_datatype_field_default_substitute_typeof
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hNotDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d')
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    __smtx_typeof_value
        (__smtx_value_dt_substitute s d (__smtx_type_default T)) =
      dtc_substitute_field_type s d T := by
  have hFieldEq := dtc_substitute_field_type_eq_of_non_datatype_finite
    s d hNotDatatype hFin
  have hTInh : native_inhabited_type T = true := by
    cases T <;>
      simp [__smtx_dt_cons_wf_rec, __smtx_is_finite_datatype_cons,
        __smtx_is_finite_type, native_and, native_ite] at hWf hFin ⊢
    all_goals first | exact hWf.1 | exact hWf.2.1
  have hEq := value_dt_substitute_type_default_eq_of_not_datatype s d T hNotDatatype
  have hDef := (type_default_typed_canonical_of_native_inhabited hTInh).1
  simpa [hFieldEq, hEq] using hDef

private theorem datatype_cons_default_typeof_all_non_datatype_fields
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue) (R : SmtType),
      dtc_all_fields_non_datatype c ->
        __smtx_dt_cons_wf_rec c refs = true ->
          __smtx_is_finite_datatype_cons c = true ->
            __smtx_typeof_value v = dtc_type_chain s d c R ->
              __smtx_typeof_value (__smtx_datatype_cons_default s d v c) = R
  | SmtDatatypeCons.unit, v, R, _hAll, _hWf, _hFin, hvTy => by
      simpa [__smtx_datatype_cons_default, dtc_type_chain] using hvTy
  | SmtDatatypeCons.cons T c, v, R, hAll, hWf, hFin, hvTy => by
      have hNotDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d' := by
        intro s' d' hEq
        rw [hEq] at hAll
        simp [dtc_all_fields_non_datatype] at hAll
      have hAllTail : dtc_all_fields_non_datatype c := by
        cases T <;> simp [dtc_all_fields_non_datatype] at hAll
        all_goals first | exact hAll | exact False.elim hAll
      let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
      have hV0Ne : v0 ≠ SmtValue.NotValue := by
        simpa [v0] using
          dt_cons_wf_finite_field_default_substitute_ne_notValue
            s d (T := T) (c := c) hWf hFin
      have hV0False : native_veq v0 SmtValue.NotValue = false :=
        native_veq_eq_false_of_ne hV0Ne
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailFin : __smtx_is_finite_datatype_cons c = true :=
        dt_cons_finite_tail_of_true hFin
      have hFieldTy :
          __smtx_typeof_value v0 = dtc_substitute_field_type s d T := by
        simpa [v0] using
          dtc_non_datatype_field_default_substitute_typeof
            s d hNotDatatype hWf hFin
      have hFieldEq :
          dtc_substitute_field_type s d T = T :=
        dtc_substitute_field_type_eq_of_non_datatype_finite
          s d hNotDatatype hFin
      have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None := by
        rw [hFieldEq]
        exact type_ne_none_of_finite_datatype_cons_head hFin
      have hApplyTy :
          __smtx_typeof_value (SmtValue.Apply v v0) = dtc_type_chain s d c R := by
        have hvTy' :
            __smtx_typeof_value v =
              SmtType.DtcAppType (dtc_substitute_field_type s d T)
                (dtc_type_chain s d c R) := by
          simpa [dtc_type_chain] using hvTy
        change
          __smtx_typeof_apply_value (__smtx_typeof_value v)
              (__smtx_typeof_value v0) =
            dtc_type_chain s d c R
        rw [hvTy', hFieldTy]
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_Teq,
          native_ite, hFieldNeNone]
      have hRec :=
        datatype_cons_default_typeof_all_non_datatype_fields s d refs c
          (SmtValue.Apply v v0) R hAllTail hTailWf hTailFin hApplyTy
      simpa [__smtx_datatype_cons_default, v0, hV0False, native_ite] using hRec

private theorem datatype_type_default_substitute_typeof_all_non_datatype_fields
    (s : native_String)
    (d : SmtDatatype)
    (sField : native_String)
    (dField : SmtDatatype)
    (refs : RefList)
    (hAll : dt_first_constructor_all_fields_non_datatype dField)
    (hRoot : native_reflist_contains refs s = true)
    (_hInh : native_inhabited_type (SmtType.Datatype sField dField) = true)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true)
    (hFinite : __smtx_is_finite_type (SmtType.Datatype sField dField) = true) :
    __smtx_typeof_value
        (__smtx_value_dt_substitute s d
          (__smtx_type_default (SmtType.Datatype sField dField))) =
      dtc_substitute_field_type s d (SmtType.Datatype sField dField) := by
  cases dField with
  | null =>
      simp [__smtx_type_wf_rec, __smtx_dt_wf_rec, native_ite] at hRec
  | sum c dTail =>
      let refsField := native_reflist_insert refs sField
      let dField0 := SmtDatatype.sum c dTail
      let dSub := __smtx_dt_substitute s d dField0
      have hNameNe : native_streq s sField = false :=
        datatype_field_name_ne_of_wf_rec_contains hRoot hRec
      have hDtWf : __smtx_dt_wf_rec dField0 refsField = true := by
        have hParts :
            ¬ sField ∈ refs ∧
              __smtx_dt_wf_rec dField0 refsField = true := by
          simpa [dField0, refsField, __smtx_type_wf_rec,
            native_reflist_contains, native_reflist_insert, native_ite] using hRec
        exact hParts.2
      have hFinDt : __smtx_is_finite_datatype dField0 = true := by
        simpa [dField0, __smtx_is_finite_type] using hFinite
      have hAllCons : dtc_all_fields_non_datatype c := by
        simpa [dField0, dt_first_constructor_all_fields_non_datatype] using hAll
      have hConsWf : __smtx_dt_cons_wf_rec c refsField = true :=
        dt_wf_cons_of_wf hDtWf
      have hConsFin : __smtx_is_finite_datatype_cons c = true :=
        finite_dt_cons_of_finite_sum hFinDt
      have hCSub :
          __smtx_dtc_substitute s d c = c :=
        dtc_substitute_eq_self_of_all_non_datatype_finite
          s d c hAllCons hConsFin
      have hDSubEq :
          dSub = SmtDatatype.sum c (__smtx_dt_substitute s d dTail) := by
        simp [dSub, dField0, __smtx_dt_substitute, hCSub]
      have hConsNe :
          __smtx_datatype_cons_default sField dField0
              (SmtValue.DtCons sField dField0 0) c ≠
            SmtValue.NotValue :=
        datatype_cons_default_ne_notValue_of_wf_finite
          sField dField0 refsField c (SmtValue.DtCons sField dField0 0)
          hConsWf hConsFin (by intro hEq; cases hEq)
      have hDefaultEq :
          __smtx_type_default (SmtType.Datatype sField dField0) =
            __smtx_datatype_cons_default sField dField0
              (SmtValue.DtCons sField dField0 0) c := by
        simpa [dField0, __smtx_type_default] using
          datatype_default_sum_first_of_cons_default_ne_notValue
            sField dField0 c dTail 0 hConsNe
      have hConsSub :
          __smtx_value_dt_substitute s d
              (__smtx_datatype_cons_default sField dField0
                (SmtValue.DtCons sField dField0 0) c) =
            __smtx_datatype_cons_default sField dSub
              (SmtValue.DtCons sField dSub 0) c := by
        simpa [dSub, dField0, __smtx_value_dt_substitute] using
          value_dt_substitute_datatype_cons_default_eq_of_all_non_datatype
            s d sField dField0 c (SmtValue.DtCons sField dField0 0)
            hAllCons
      have hHeadTy :
          __smtx_typeof_value (SmtValue.DtCons sField dSub 0) =
            dtc_type_chain sField dSub c (SmtType.Datatype sField dSub) := by
        simpa [hDSubEq] using
          typeof_dt_cons_first_eq_dtc_type_chain
            sField c (__smtx_dt_substitute s d dTail)
      have hConsTy :
          __smtx_typeof_value
              (__smtx_datatype_cons_default sField dSub
                (SmtValue.DtCons sField dSub 0) c) =
            SmtType.Datatype sField dSub :=
        datatype_cons_default_typeof_all_non_datatype_fields
          sField dSub refsField c (SmtValue.DtCons sField dSub 0)
          (SmtType.Datatype sField dSub) hAllCons hConsWf hConsFin hHeadTy
      calc
        __smtx_typeof_value
            (__smtx_value_dt_substitute s d
              (__smtx_type_default (SmtType.Datatype sField dField0))) =
            __smtx_typeof_value
              (__smtx_value_dt_substitute s d
                (__smtx_datatype_cons_default sField dField0
                  (SmtValue.DtCons sField dField0 0) c)) := by
              rw [hDefaultEq]
        _ =
            __smtx_typeof_value
              (__smtx_datatype_cons_default sField dSub
                (SmtValue.DtCons sField dSub 0) c) := by
              rw [hConsSub]
        _ = SmtType.Datatype sField dSub := hConsTy
        _ =
            dtc_substitute_field_type s d (SmtType.Datatype sField dField0) := by
              simp [dtc_substitute_field_type, dSub, dField0, native_ite,
                hNameNe]

private theorem one_mod_pow2_succ (w : Nat) :
    (1 : Int) % (native_int_pow2 (native_nat_to_int (Nat.succ w))) = 1 := by
  have hnot : ¬ ((w : Int) + 1 < 0) := by omega
  have hpow :
      native_int_pow2 (native_nat_to_int (Nat.succ w)) =
        (2 : Int) ^ (Nat.succ w) := by
    simp [native_int_pow2, native_zexp_total, native_nat_to_int, hnot]
  rw [hpow]
  exact Int.emod_eq_of_lt (by decide) (by
    have hNat : (1 : Nat) < 2 ^ Nat.succ w :=
      Nat.one_lt_pow (by simp) (by decide)
    exact_mod_cast hNat)

private theorem one_mod_pow2_succ_zeq (w : Nat) :
    native_zeq (1 : Int)
      (native_mod_total 1 (native_int_pow2 (native_nat_to_int (Nat.succ w)))) = true := by
  simp [native_zeq, native_mod_total, one_mod_pow2_succ]

private theorem bitvec_succ_one_typeof (w : Nat) :
    __smtx_typeof_value
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1) =
        SmtType.BitVec (Nat.succ w) := by
  have hmod :
      native_zeq (1 : Int)
        (native_mod_total 1 (native_int_pow2 ((w : Int) + 1))) = true := by
    simpa [native_nat_to_int] using one_mod_pow2_succ_zeq w
  have hnonneg : native_zleq 0 ((w : Int) + 1) = true := by
    have hle : (0 : Int) <= (w : Int) + 1 :=
      Int.add_nonneg (Int.natCast_nonneg w) (by decide)
    simpa [native_zleq] using hle
  simp [__smtx_typeof_value, native_and, native_ite, native_int_to_nat,
    native_nat_to_int, Nat.succ_eq_add_one]
  exact ⟨hnonneg, hmod⟩

private theorem bitvec_succ_one_canonical (w : Nat) :
    __smtx_value_canonical_bool
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1) = true := by
  have hmod :
      native_zeq (1 : Int)
        (native_mod_total 1 (native_int_pow2 ((w : Int) + 1))) = true := by
    simpa [native_nat_to_int] using one_mod_pow2_succ_zeq w
  simp [__smtx_value_canonical_bool, native_ite, native_nat_to_int,
    Nat.succ_eq_add_one]
  exact Or.inr hmod

private theorem bitvec_succ_one_ne_default (w : Nat) :
    native_veq
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1)
      (__smtx_type_default (SmtType.BitVec (Nat.succ w))) = false := by
  simp [__smtx_type_default, native_nat_to_int, native_veq]

private def fresh_numeral_index : List SmtValue -> Nat
  | [] => 0
  | SmtValue.Numeral n :: xs => Nat.max (Int.toNat n + 1) (fresh_numeral_index xs)
  | _ :: xs => fresh_numeral_index xs

private theorem fresh_numeral_index_gt_of_mem :
    ∀ {xs : List SmtValue} {n : native_Int},
      SmtValue.Numeral n ∈ xs ->
        Int.toNat n < fresh_numeral_index xs := by
  intro xs
  induction xs with
  | nil =>
      intro n h
      cases h
  | cons v xs ih =>
      intro n h
      cases v <;> simp [fresh_numeral_index] at h ⊢
      case Numeral m =>
        rcases h with hEq | hTail
        · subst n
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
        · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
      all_goals
        exact ih h

private theorem fresh_numeral_not_mem (xs : List SmtValue) :
    SmtValue.Numeral (Int.ofNat (fresh_numeral_index xs)) ∉ xs := by
  intro h
  have hlt := fresh_numeral_index_gt_of_mem
    (xs := xs) (n := Int.ofNat (fresh_numeral_index xs)) h
  simp at hlt

private theorem fresh_numeral_veq_false_of_mem (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j (SmtValue.Numeral (Int.ofNat (fresh_numeral_index xs))) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_numeral_not_mem xs hj)

private def fresh_rational_index : List SmtValue -> Nat
  | [] => 0
  | SmtValue.Rational q :: xs => Nat.max (Int.toNat (Rat.floor q) + 1) (fresh_rational_index xs)
  | _ :: xs => fresh_rational_index xs

private theorem fresh_rational_index_gt_of_mem :
    ∀ {xs : List SmtValue} {q : native_Rat},
      SmtValue.Rational q ∈ xs ->
        Int.toNat (Rat.floor q) < fresh_rational_index xs := by
  intro xs
  induction xs with
  | nil =>
      intro q h
      cases h
  | cons v xs ih =>
      intro q h
      cases v <;> simp [fresh_rational_index] at h ⊢
      case Rational r =>
        rcases h with hEq | hTail
        · subst q
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
        · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
      all_goals
        exact ih h

private theorem fresh_rational_not_mem (xs : List SmtValue) :
    SmtValue.Rational (Int.ofNat (fresh_rational_index xs)) ∉ xs := by
  intro h
  have hlt := fresh_rational_index_gt_of_mem
    (xs := xs) (q := (Int.ofNat (fresh_rational_index xs) : native_Rat)) h
  simp at hlt

private theorem fresh_rational_veq_false_of_mem (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j
        (SmtValue.Rational (Int.ofNat (fresh_rational_index xs))) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_rational_not_mem xs hj)

private def fresh_usort_index (sort : native_Nat) : List SmtValue -> Nat
  | [] => 0
  | SmtValue.UValue i n :: xs =>
      if i = sort then Nat.max (n + 1) (fresh_usort_index sort xs)
      else fresh_usort_index sort xs
  | _ :: xs => fresh_usort_index sort xs

private theorem fresh_usort_index_gt_of_mem (sort : native_Nat) :
    ∀ {xs : List SmtValue} {n : native_Nat},
      SmtValue.UValue sort n ∈ xs ->
        n < fresh_usort_index sort xs := by
  intro xs
  induction xs with
  | nil =>
      intro n h
      cases h
  | cons v xs ih =>
      intro n h
      cases v
      case UValue i m =>
        by_cases hi : i = sort
        · subst i
          simp [fresh_usort_index] at h ⊢
          rcases h with hEq | hTail
          · subst n
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
          · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
        · have hNe : sort ≠ i := fun hEq => hi hEq.symm
          simp [fresh_usort_index, hi, hNe] at h ⊢
          exact ih h
      all_goals
        simp [fresh_usort_index] at h ⊢
        exact ih h

private theorem fresh_usort_not_mem (sort : native_Nat) (xs : List SmtValue) :
    SmtValue.UValue sort (fresh_usort_index sort xs) ∉ xs := by
  intro h
  have hlt := fresh_usort_index_gt_of_mem sort
    (xs := xs) (n := fresh_usort_index sort xs) h
  exact Nat.lt_irrefl _ hlt

private theorem fresh_usort_veq_false_of_mem (sort : native_Nat) (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j (SmtValue.UValue sort (fresh_usort_index sort xs)) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_usort_not_mem sort xs hj)

private noncomputable def smt_value_size_bound : List SmtValue -> Nat
  | [] => 0
  | v :: vs => Nat.max (sizeOf v + 1) (smt_value_size_bound vs)

private theorem smt_value_size_lt_bound_of_mem :
    ∀ {xs : List SmtValue} {v : SmtValue},
      v ∈ xs -> sizeOf v < smt_value_size_bound xs := by
  intro xs
  induction xs with
  | nil =>
      intro v h
      cases h
  | cons x xs ih =>
      intro v h
      simp [smt_value_size_bound] at h ⊢
      rcases h with hEq | hTail
      · subst v
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)

private theorem native_veq_false_of_mem_and_size_bound
    {xs : List SmtValue}
    {j i : SmtValue}
    (hj : j ∈ xs)
    (hi : smt_value_size_bound xs ≤ sizeOf i) :
    native_veq j i = false := by
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst i
    have hLt := smt_value_size_lt_bound_of_mem (xs := xs) hj
    exact Nat.not_lt_of_ge hi hLt)

private theorem int_large_witness (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Int ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.Numeral (Int.ofNat minSize), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical_bool]
  · rw [show sizeOf (SmtValue.Numeral (Int.ofNat minSize)) =
        1 + sizeOf (Int.ofNat minSize) by rfl]
    rw [show sizeOf (Int.ofNat minSize) = 1 + minSize by rfl]
    omega

private theorem real_large_witness (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Real ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.Rational (Int.ofNat minSize : native_Rat), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical_bool]
  · rw [show sizeOf (SmtValue.Rational (Int.ofNat minSize : native_Rat)) =
        1 + sizeOf (Int.ofNat minSize : native_Rat) by rfl]
    rw [show sizeOf (Int.ofNat minSize : native_Rat) =
        1 + sizeOf (Int.ofNat minSize) + sizeOf (1 : Nat) +
          sizeOf (by decide : (1 : Nat) ≠ 0) by rfl]
    rw [show sizeOf (Int.ofNat minSize) = 1 + minSize by rfl]
    omega

private theorem usort_large_witness (u : native_Nat) (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.USort u ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.UValue u minSize, ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical_bool]
  · rw [show sizeOf (SmtValue.UValue u minSize) =
        1 + sizeOf u + sizeOf minSize by rfl]
    simp [sizeOf]

private def smt_type_simple_finite_nonunit_context : SmtType -> Prop
  | SmtType.Bool => True
  | SmtType.Char => True
  | SmtType.BitVec (Nat.succ _) => True
  | _ => False

private theorem simple_finite_nonunit_witness :
    ∀ (T : SmtType),
      smt_type_simple_finite_nonunit_context T ->
        ∃ e : SmtValue,
          __smtx_typeof_value e = T ∧
            __smtx_value_canonical_bool e = true ∧
              native_veq e (__smtx_type_default T) = false
  | SmtType.Bool, _hCtx => by
      refine ⟨SmtValue.Boolean true, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_veq]
  | SmtType.Char, _hCtx => by
      refine ⟨SmtValue.Char (Char.ofNat 1), ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_nat_to_char, native_veq]
  | SmtType.BitVec (Nat.succ w), _hCtx => by
      refine
        ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1, ?_, ?_, ?_⟩
      · exact bitvec_succ_one_typeof w
      · exact bitvec_succ_one_canonical w
      · exact bitvec_succ_one_ne_default w
  | SmtType.BitVec 0, hCtx => by cases hCtx
  | SmtType.None, hCtx => by cases hCtx
  | SmtType.Int, hCtx => by cases hCtx
  | SmtType.Real, hCtx => by cases hCtx
  | SmtType.RegLan, hCtx => by cases hCtx
  | SmtType.Map _T _U, hCtx => by cases hCtx
  | SmtType.Set _T, hCtx => by cases hCtx
  | SmtType.Seq _T, hCtx => by cases hCtx
  | SmtType.Datatype _s _d, hCtx => by cases hCtx
  | SmtType.TypeRef _s, hCtx => by cases hCtx
  | SmtType.USort _u, hCtx => by cases hCtx
  | SmtType.FunType _T _U, hCtx => by cases hCtx
  | SmtType.DtcAppType _T _U, hCtx => by cases hCtx

private theorem smt_type_simple_finite_nonunit_context_nonunit :
    ∀ {T : SmtType},
      smt_type_simple_finite_nonunit_context T ->
        __smtx_is_unit_type T = false
  | SmtType.Bool, _ => by simp [__smtx_is_unit_type]
  | SmtType.Char, _ => by simp [__smtx_is_unit_type]
  | SmtType.BitVec (Nat.succ _w), _ => by
      simp [__smtx_is_unit_type, native_nateq]

private def smt_type_simple_large_context : SmtType -> Prop
  | SmtType.Int => True
  | SmtType.Real => True
  | SmtType.USort _ => True
  | SmtType.Set T => smt_type_simple_large_context T
  | SmtType.Seq T => smt_type_simple_large_context T
  | SmtType.Map K V =>
      smt_type_simple_large_context V ∨
        (smt_type_simple_large_context K ∧
          smt_type_simple_finite_nonunit_context V)
  | _ => False

mutual

private theorem smt_type_simple_large_context_infinite :
    ∀ {T : SmtType},
      smt_type_simple_large_context T ->
        __smtx_is_finite_type T = false
  | SmtType.Int, _ => by
      simp [__smtx_is_finite_type]
  | SmtType.Real, _ => by
      simp [__smtx_is_finite_type]
  | SmtType.USort _u, _ => by
      simp [__smtx_is_finite_type]
  | SmtType.Set T, hCtx => by
      simpa [__smtx_is_finite_type] using
        smt_type_simple_large_context_infinite (T := T) hCtx
  | SmtType.Seq T, hCtx => by
      simpa [__smtx_is_finite_type] using
        smt_type_simple_large_context_infinite (T := T) hCtx
  | SmtType.Map K V, hCtx => by
      rcases hCtx with hValueLarge | hKeyLarge
      · have hVInf : __smtx_is_finite_type V = false :=
          smt_type_simple_large_context_infinite (T := V) hValueLarge
        have hVNonUnit : __smtx_is_unit_type V = false :=
          smt_type_simple_large_context_nonunit (T := V) hValueLarge
        cases hKFin : __smtx_is_finite_type K <;>
          simp [__smtx_is_finite_type, hVNonUnit, hKFin, hVInf,
            native_or, native_and]
      · rcases hKeyLarge with ⟨hKeyLarge, hValueNonUnit⟩
        have hKInf : __smtx_is_finite_type K = false :=
          smt_type_simple_large_context_infinite (T := K) hKeyLarge
        have hVNonUnit : __smtx_is_unit_type V = false :=
          smt_type_simple_finite_nonunit_context_nonunit hValueNonUnit
        cases hVFin : __smtx_is_finite_type V <;>
          simp [__smtx_is_finite_type, hVNonUnit, hKInf, hVFin,
            native_or, native_and]
termination_by T _ => sizeOf T
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

private theorem smt_type_simple_large_context_nonunit :
    ∀ {T : SmtType},
      smt_type_simple_large_context T ->
        __smtx_is_unit_type T = false
  | SmtType.Int, _ => by
      simp [__smtx_is_unit_type]
  | SmtType.Real, _ => by
      simp [__smtx_is_unit_type]
  | SmtType.USort _u, _ => by
      simp [__smtx_is_unit_type]
  | SmtType.Set _T, _hCtx => by
      simp [__smtx_is_unit_type]
  | SmtType.Seq _T, _hCtx => by
      simp [__smtx_is_unit_type]
  | SmtType.Map K V, hCtx => by
      rcases hCtx with hValueLarge | hKeyLarge
      · have hVNonUnit : __smtx_is_unit_type V = false :=
          smt_type_simple_large_context_nonunit (T := V) hValueLarge
        simpa [__smtx_is_unit_type] using hVNonUnit
      · rcases hKeyLarge with ⟨_hKeyLarge, hValueNonUnit⟩
        have hVNonUnit : __smtx_is_unit_type V = false :=
          smt_type_simple_finite_nonunit_context_nonunit hValueNonUnit
        simpa [__smtx_is_unit_type] using hVNonUnit
termination_by T _ => sizeOf T
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

end

private theorem simple_type_large_witness :
    ∀ (T : SmtType) (refs : RefList),
      smt_type_simple_large_context T ->
        __smtx_type_wf_rec T refs = true ->
          ∀ minSize : Nat,
            ∃ i : SmtValue,
              __smtx_typeof_value i = T ∧
                __smtx_value_canonical_bool i = true ∧
                  minSize ≤ sizeOf i
  | SmtType.Int, _refs, _hCtx, _hWf, minSize => int_large_witness minSize
  | SmtType.Real, _refs, _hCtx, _hWf, minSize => real_large_witness minSize
  | SmtType.USort u, _refs, _hCtx, _hWf, minSize => usort_large_witness u minSize
  | SmtType.Set T, _refs, hCtx, hWf, minSize => by
      have hParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      rcases simple_type_large_witness T native_reflist_nil hCtx hParts.2 minSize with
        ⟨x, hxTy, hxCan, hxSize⟩
      let e :=
        SmtValue.Set
          (SmtMap.cons x (SmtValue.Boolean true)
            (SmtMap.default T (SmtValue.Boolean false)))
      have hTInf : __smtx_is_finite_type T = false :=
        smt_type_simple_large_context_infinite hCtx
      refine ⟨e, ?_, ?_, ?_⟩
      · simp [e, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hxTy, native_ite, native_Teq]
      · simp [e, __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hxCan, hTInf, native_and, native_ite,
          native_not, native_veq]
      · rw [show
          sizeOf e =
            1 + sizeOf
              (SmtMap.cons x (SmtValue.Boolean true)
                (SmtMap.default T (SmtValue.Boolean false))) by rfl]
        rw [show
          sizeOf
              (SmtMap.cons x (SmtValue.Boolean true)
                (SmtMap.default T (SmtValue.Boolean false))) =
            1 + sizeOf x + sizeOf (SmtValue.Boolean true) +
              sizeOf (SmtMap.default T (SmtValue.Boolean false)) by rfl]
        omega
  | SmtType.Seq T, _refs, hCtx, hWf, minSize => by
      have hParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      rcases simple_type_large_witness T native_reflist_nil hCtx hParts.2 minSize with
        ⟨x, hxTy, hxCan, hxSize⟩
      let e := SmtValue.Seq (SmtSeq.cons x (SmtSeq.empty T))
      refine ⟨e, ?_, ?_, ?_⟩
      · simp [e, __smtx_typeof_value, __smtx_typeof_seq_value,
          hxTy, native_ite, native_Teq]
      · simp [e, __smtx_value_canonical_bool, __smtx_seq_canonical,
          hxCan, native_and]
      · rw [show
          sizeOf e =
            1 + sizeOf (SmtSeq.cons x (SmtSeq.empty T)) by rfl]
        rw [show
          sizeOf (SmtSeq.cons x (SmtSeq.empty T)) =
            1 + sizeOf x + sizeOf (SmtSeq.empty T) by rfl]
        omega
  | SmtType.Map K V, _refs, hCtx, hWf, minSize => by
      have hParts :
          native_inhabited_type K = true ∧
            __smtx_type_wf_rec K native_reflist_nil = true ∧
              native_inhabited_type V = true ∧
                __smtx_type_wf_rec V native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      have hKDefault :=
        type_default_typed_canonical_of_native_inhabited hParts.1
      have hVDefault :=
        type_default_typed_canonical_of_native_inhabited hParts.2.2.1
      let defV := __smtx_type_default V
      rcases hCtx with hValueLarge | hKeyLarge
      · rcases simple_type_large_witness V native_reflist_nil hValueLarge
            hParts.2.2.2 (Nat.max minSize (sizeOf defV + 1)) with
          ⟨val, hValTy, hValCan, hValSize⟩
        have hValNeDef : val ≠ defV := by
          intro hEq
          subst val
          have hLt : sizeOf defV < Nat.max minSize (sizeOf defV + 1) :=
            Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
          exact Nat.not_lt_of_ge hValSize hLt
        refine
          ⟨SmtValue.Map
            (SmtMap.cons (__smtx_type_default K) val
              (SmtMap.default K defV)), ?_, ?_, ?_⟩
        · simp [__smtx_typeof_value, __smtx_typeof_map_value, defV,
            hKDefault.1, hValTy, hVDefault.1, native_ite, native_Teq]
        · by_cases hKFin : __smtx_is_finite_type K = true
          · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
              __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
              __smtx_msm_get_default, defV, hKDefault.2, hValCan,
              hVDefault.1, hVDefault.2, hKFin, hValNeDef, native_and,
              native_ite, native_not, native_veq]
          · have hKInf : __smtx_is_finite_type K = false := by
              cases h : __smtx_is_finite_type K <;> simp [h] at hKFin ⊢
            simp [__smtx_value_canonical_bool, __smtx_map_canonical,
              __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
              __smtx_msm_get_default, defV, hKDefault.2, hValCan,
              hVDefault.2, hKInf, hValNeDef, native_and, native_ite,
              native_not, native_veq]
        · rw [show
            sizeOf
                (SmtValue.Map
                  (SmtMap.cons (__smtx_type_default K) val
                    (SmtMap.default K defV))) =
              1 + sizeOf
                (SmtMap.cons (__smtx_type_default K) val
                  (SmtMap.default K defV)) by rfl]
          rw [show
            sizeOf
                (SmtMap.cons (__smtx_type_default K) val
                  (SmtMap.default K defV)) =
              1 + sizeOf (__smtx_type_default K) + sizeOf val +
                sizeOf (SmtMap.default K defV) by rfl]
          have hMin : minSize ≤ Nat.max minSize (sizeOf defV + 1) :=
            Nat.le_max_left _ _
          omega
      · rcases hKeyLarge with ⟨hKeyLarge, hValueFiniteNonUnit⟩
        rcases simple_type_large_witness K native_reflist_nil hKeyLarge
            hParts.2.1 minSize with
          ⟨key, hKeyTy, hKeyCan, hKeySize⟩
        rcases simple_finite_nonunit_witness V hValueFiniteNonUnit with
          ⟨val, hValTy, hValCan, hValNeDefault⟩
        have hKInf : __smtx_is_finite_type K = false :=
          smt_type_simple_large_context_infinite hKeyLarge
        have hValNeDef : val ≠ defV := by
          intro hEq
          subst val
          simp [defV, native_veq] at hValNeDefault
        refine
          ⟨SmtValue.Map
            (SmtMap.cons key val (SmtMap.default K defV)), ?_, ?_, ?_⟩
        · simp [__smtx_typeof_value, __smtx_typeof_map_value, defV,
            hKeyTy, hValTy, hVDefault.1, native_ite, native_Teq]
        · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
            __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
            __smtx_msm_get_default, defV, hKeyCan, hValCan, hVDefault.2,
            hKInf, hValNeDef, native_and, native_ite, native_not,
            native_veq]
        · rw [show
            sizeOf
                (SmtValue.Map
                  (SmtMap.cons key val (SmtMap.default K defV))) =
              1 + sizeOf (SmtMap.cons key val (SmtMap.default K defV)) by rfl]
          rw [show
            sizeOf (SmtMap.cons key val (SmtMap.default K defV)) =
              1 + sizeOf key + sizeOf val +
                sizeOf (SmtMap.default K defV) by rfl]
          omega
  | SmtType.None, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Bool, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.RegLan, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.BitVec _w, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Char, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Datatype _s _d, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.TypeRef _s, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.FunType _T _U, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.DtcAppType _T _U, _refs, hCtx, _hWf, _minSize => by cases hCtx
termination_by T _ _ _ _ => sizeOf T
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

private def smt_type_simple_map_value_context : SmtType -> Prop
  | SmtType.Map K V =>
      smt_type_simple_large_context V ∨
        (smt_type_simple_large_context K ∧
          smt_type_simple_finite_nonunit_context V)
  | _ => False

private theorem simple_map_value_large_witness :
    ∀ (T : SmtType) (refs : RefList),
      smt_type_simple_map_value_context T ->
        __smtx_type_wf_rec T refs = true ->
          ∀ minSize : Nat,
            ∃ i : SmtValue,
              __smtx_typeof_value i = T ∧
                __smtx_value_canonical_bool i = true ∧
                  minSize ≤ sizeOf i
  | SmtType.Map K V, _refs, hCtx, hWf, minSize => by
      exact simple_type_large_witness (SmtType.Map K V) _ hCtx hWf minSize
  | SmtType.None, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Bool, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Int, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Real, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.RegLan, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.BitVec _w, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Set _T, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Seq _T, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Char, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.Datatype _s _d, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.TypeRef _s, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.USort _u, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.FunType _T _U, _refs, hCtx, _hWf, _minSize => by cases hCtx
  | SmtType.DtcAppType _T _U, _refs, hCtx, _hWf, _minSize => by cases hCtx

private theorem sizeOf_lt_apply_left (f a : SmtValue) :
    sizeOf f < sizeOf (SmtValue.Apply f a) := by
  rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
  omega

private theorem sizeOf_lt_apply_right (f a : SmtValue) :
    sizeOf a < sizeOf (SmtValue.Apply f a) := by
  rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
  omega

private theorem datatype_fresh_of_size_bound
    {s : native_String}
    {d : SmtDatatype}
    {avoid : List SmtValue}
    (hLarge :
      ∃ i : SmtValue,
        __smtx_typeof_value i = SmtType.Datatype s d ∧
          __smtx_value_canonical_bool i = true ∧
            smt_value_size_bound avoid ≤ sizeOf i) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  rcases hLarge with ⟨i, hiTy, hiCan, hiSize⟩
  refine ⟨i, hiTy, hiCan, ?_⟩
  intro j hj
  exact native_veq_false_of_mem_and_size_bound hj hiSize

private theorem finite_datatype_sum_false_cases
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    (hFin : __smtx_is_finite_datatype (SmtDatatype.sum c d) = false) :
    __smtx_is_finite_datatype_cons c = false ∨
      __smtx_is_finite_datatype d = false := by
  cases hc : __smtx_is_finite_datatype_cons c <;>
    cases hd : __smtx_is_finite_datatype d <;>
      simp [__smtx_is_finite_datatype, native_and, hc, hd] at hFin ⊢

private theorem finite_datatype_cons_false_cases
    {T : SmtType}
    {c : SmtDatatypeCons}
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = false) :
    __smtx_is_finite_type T = false ∨
      __smtx_is_finite_datatype_cons c = false := by
  cases hT : __smtx_is_finite_type T <;>
    cases hc : __smtx_is_finite_datatype_cons c <;>
      simp [__smtx_is_finite_datatype_cons, native_and, hT, hc] at hFin ⊢

private theorem dtc_substitute_field_type_ne_none_of_finite_type
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    (hFin : __smtx_is_finite_type T = true) :
    dtc_substitute_field_type s d T ≠ SmtType.None := by
  cases T <;> simp [dtc_substitute_field_type, __smtx_is_finite_type,
    native_ite, native_Teq] at hFin ⊢

private theorem dt_cons_wf_finite_head_default_substitute_ne_notValue
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hFin : __smtx_is_finite_type T = true) :
    __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
      SmtValue.NotValue := by
  cases T <;>
    simp [__smtx_dt_cons_wf_rec, __smtx_is_finite_type,
      __smtx_type_default, __smtx_value_dt_substitute, native_ite] at hWf hFin ⊢
  all_goals
    have hDefaultNe :
        __smtx_type_default _ ≠ SmtValue.NotValue :=
      type_default_ne_notValue_of_native_inhabited hWf.1 (by simp)
    exact value_dt_substitute_ne_notValue s d hDefaultNe

private theorem dtc_head_default_substitute_typeof_of_wf_finite_head
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hRoot : native_reflist_contains refs s = true)
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hFin : __smtx_is_finite_type T = true) :
    __smtx_typeof_value
        (__smtx_value_dt_substitute s d (__smtx_type_default T)) =
      dtc_substitute_field_type s d T := by
  cases T <;>
    simp [__smtx_dt_cons_wf_rec, __smtx_is_finite_type,
      __smtx_type_default, __smtx_value_dt_substitute,
      dtc_substitute_field_type, native_ite, native_Teq, native_and] at hWf hFin ⊢
  case Datatype sField dField =>
      have hParts :
          native_inhabited_type (SmtType.Datatype sField dField) = true ∧
            __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true ∧
              __smtx_dt_cons_wf_rec c refs = true := by
        simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
      exact datatype_type_default_substitute_typeof_of_wf_rec_finite_contains
        s d sField dField refs hRoot hParts.1 hParts.2.1 hFin
  all_goals
    first
    | rfl
    | exact (type_default_typed_canonical_of_native_inhabited hWf.1).1

private theorem dtc_field_default_substitute_typeof_direct
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hRoot : native_reflist_contains refs s = true)
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    __smtx_typeof_value
        (__smtx_value_dt_substitute s d (__smtx_type_default T)) =
      dtc_substitute_field_type s d T := by
  cases T with
  | Datatype sField dField =>
      have hParts :
          native_inhabited_type (SmtType.Datatype sField dField) = true ∧
            __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true ∧
              __smtx_dt_cons_wf_rec c refs = true := by
        simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
      have hFieldFin :
          __smtx_is_finite_type (SmtType.Datatype sField dField) = true := by
        have hFinParts :
            __smtx_is_finite_type (SmtType.Datatype sField dField) = true ∧
              __smtx_is_finite_datatype_cons c = true := by
          simpa [__smtx_is_finite_datatype_cons, native_and] using hFin
        exact hFinParts.1
      exact datatype_type_default_substitute_typeof_of_wf_rec_finite_contains
        s d sField dField refs hRoot hParts.1 hParts.2.1 hFieldFin
  | _ =>
      exact dtc_non_datatype_field_default_substitute_typeof
        s d (by intro s' d' hEq; cases hEq) hWf hFin

private theorem datatype_cons_default_typeof_of_wf_finite_direct
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue) (R : SmtType),
      __smtx_dt_cons_wf_rec c refs = true ->
        __smtx_is_finite_datatype_cons c = true ->
          __smtx_typeof_value v = dtc_type_chain s d c R ->
            __smtx_typeof_value (__smtx_datatype_cons_default s d v c) = R
  | SmtDatatypeCons.unit, v, R, _hWf, _hFin, hvTy => by
      simpa [__smtx_datatype_cons_default, dtc_type_chain] using hvTy
  | SmtDatatypeCons.cons T c, v, R, hWf, hFin, hvTy => by
      let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
      have hV0Ne : v0 ≠ SmtValue.NotValue := by
        simpa [v0] using
          dt_cons_wf_finite_field_default_substitute_ne_notValue
            s d (T := T) (c := c) hWf hFin
      have hV0False : native_veq v0 SmtValue.NotValue = false :=
        native_veq_eq_false_of_ne hV0Ne
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailFin : __smtx_is_finite_datatype_cons c = true :=
        dt_cons_finite_tail_of_true hFin
      have hFieldTy :
          __smtx_typeof_value v0 = dtc_substitute_field_type s d T := by
        simpa [v0] using
          dtc_field_default_substitute_typeof_direct
            s d (T := T) (c := c) hRoot hWf hFin
      have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None := by
        exact dtc_substitute_field_type_ne_none_of_finite s d hFin
      have hApplyTy :
          __smtx_typeof_value (SmtValue.Apply v v0) = dtc_type_chain s d c R := by
        have hvTy' :
            __smtx_typeof_value v =
              SmtType.DtcAppType (dtc_substitute_field_type s d T)
                (dtc_type_chain s d c R) := by
          simpa [dtc_type_chain] using hvTy
        change
          __smtx_typeof_apply_value (__smtx_typeof_value v)
              (__smtx_typeof_value v0) =
            dtc_type_chain s d c R
        rw [hvTy', hFieldTy]
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_Teq,
          native_ite, hFieldNeNone]
      have hRec :=
        datatype_cons_default_typeof_of_wf_finite_direct s d refs hRoot c
          (SmtValue.Apply v v0) R hTailWf hTailFin hApplyTy
      simpa [__smtx_datatype_cons_default, v0, hV0False, native_ite] using hRec

private theorem datatype_cons_default_typeof_self_ref_head
    (s : native_String)
    (cTail : SmtDatatypeCons)
    (dRest : SmtDatatype)
    (refs : RefList)
    (seed : SmtValue)
    (hRoot : native_reflist_contains refs s = true)
    (hTailWf : __smtx_dt_cons_wf_rec cTail refs = true)
    (hTailFin : __smtx_is_finite_datatype_cons cTail = true)
    (hSeedTy :
      __smtx_typeof_value seed =
        SmtType.Datatype s
          (SmtDatatype.sum (SmtDatatypeCons.cons (SmtType.TypeRef s) cTail)
            dRest)) :
    let d :=
      SmtDatatype.sum (SmtDatatypeCons.cons (SmtType.TypeRef s) cTail) dRest
    __smtx_typeof_value
        (__smtx_datatype_cons_default s d
          (SmtValue.Apply (SmtValue.DtCons s d 0) seed) cTail) =
      SmtType.Datatype s d := by
  intro d
  have hHeadTy :
      __smtx_typeof_value (SmtValue.DtCons s d 0) =
        SmtType.DtcAppType (SmtType.Datatype s d)
          (dtc_type_chain s d cTail (SmtType.Datatype s d)) := by
    simpa [d, dtc_type_chain, dtc_substitute_field_type, native_ite,
      native_Teq] using
      typeof_dt_cons_first_eq_dtc_type_chain s
        (SmtDatatypeCons.cons (SmtType.TypeRef s) cTail) dRest
  have hSeedTy' : __smtx_typeof_value seed = SmtType.Datatype s d := by
    simpa [d] using hSeedTy
  have hApplyTy :
      __smtx_typeof_value (SmtValue.Apply (SmtValue.DtCons s d 0) seed) =
        dtc_type_chain s d cTail (SmtType.Datatype s d) := by
    change
      __smtx_typeof_apply_value
          (__smtx_typeof_value (SmtValue.DtCons s d 0))
          (__smtx_typeof_value seed) =
        dtc_type_chain s d cTail (SmtType.Datatype s d)
    rw [hHeadTy, hSeedTy']
    simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_Teq,
      native_ite]
  exact datatype_cons_default_typeof_of_wf_finite_direct
    s d refs hRoot cTail (SmtValue.Apply (SmtValue.DtCons s d 0) seed)
    (SmtType.Datatype s d) hTailWf hTailFin hApplyTy

private theorem datatype_cons_default_canonical_self_ref_head
    (s : native_String)
    (cTail : SmtDatatypeCons)
    (dRest : SmtDatatype)
    (refs : RefList)
    (seed : SmtValue)
    (hTailWf : __smtx_dt_cons_wf_rec cTail refs = true)
    (hSeedCan : __smtx_value_canonical_bool seed = true) :
    let d :=
      SmtDatatype.sum (SmtDatatypeCons.cons (SmtType.TypeRef s) cTail) dRest
    __smtx_value_canonical_bool
        (__smtx_datatype_cons_default s d
          (SmtValue.Apply (SmtValue.DtCons s d 0) seed) cTail) = true := by
  intro d
  have hApplyCan :
      __smtx_value_canonical_bool
          (SmtValue.Apply (SmtValue.DtCons s d 0) seed) = true := by
    simp [__smtx_value_canonical_bool, native_and, hSeedCan]
  exact datatype_cons_default_canonical_of_wf
    s d refs cTail (SmtValue.Apply (SmtValue.DtCons s d 0) seed)
    hTailWf hApplyCan

private theorem sizeOf_lt_datatype_cons_default_of_wf_finite
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList) :
    ∀ (c : SmtDatatypeCons) (seed v : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        __smtx_is_finite_datatype_cons c = true ->
          sizeOf seed < sizeOf v ->
            sizeOf seed < sizeOf (__smtx_datatype_cons_default s d v c)
  | SmtDatatypeCons.unit, seed, v, _hWf, _hFin, hLt => by
      simpa [__smtx_datatype_cons_default] using hLt
  | SmtDatatypeCons.cons T c, seed, v, hWf, hFin, hLt => by
      let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
      have hV0Ne : v0 ≠ SmtValue.NotValue := by
        simpa [v0] using
          dt_cons_wf_finite_field_default_substitute_ne_notValue
            s d (T := T) (c := c) hWf hFin
      have hV0False : native_veq v0 SmtValue.NotValue = false :=
        native_veq_eq_false_of_ne hV0Ne
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailFin : __smtx_is_finite_datatype_cons c = true :=
        dt_cons_finite_tail_of_true hFin
      have hApplyLt : sizeOf seed < sizeOf (SmtValue.Apply v v0) :=
        Nat.lt_trans hLt (sizeOf_lt_apply_left v v0)
      have hRec :=
        sizeOf_lt_datatype_cons_default_of_wf_finite
          s d refs c seed (SmtValue.Apply v v0) hTailWf hTailFin hApplyLt
      simpa [__smtx_datatype_cons_default, v0, hV0False, native_ite] using hRec

private theorem sizeOf_lt_datatype_cons_default_self_ref_head
    (s : native_String)
    (cTail : SmtDatatypeCons)
    (dRest : SmtDatatype)
    (refs : RefList)
    (seed : SmtValue)
    (hTailWf : __smtx_dt_cons_wf_rec cTail refs = true)
    (hTailFin : __smtx_is_finite_datatype_cons cTail = true) :
    let d :=
      SmtDatatype.sum (SmtDatatypeCons.cons (SmtType.TypeRef s) cTail) dRest
    sizeOf seed <
      sizeOf
        (__smtx_datatype_cons_default s d
          (SmtValue.Apply (SmtValue.DtCons s d 0) seed) cTail) := by
  intro d
  exact sizeOf_lt_datatype_cons_default_of_wf_finite
    s d refs cTail seed (SmtValue.Apply (SmtValue.DtCons s d 0) seed)
    hTailWf hTailFin (sizeOf_lt_apply_right (SmtValue.DtCons s d 0) seed)

private theorem datatype_cons_default_with_head_arg_witness
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true)
    {T : SmtType}
    {cTail : SmtDatatypeCons}
    {v arg : SmtValue}
    (hTailWf : __smtx_dt_cons_wf_rec cTail refs = true)
    (hTailFin : __smtx_is_finite_datatype_cons cTail = true)
    (hvTy :
      __smtx_typeof_value v =
        SmtType.DtcAppType (dtc_substitute_field_type s d T)
          (dtc_type_chain s d cTail (SmtType.Datatype s d)))
    (hvCan : __smtx_value_canonical_bool v = true)
    (hArgTy : __smtx_typeof_value arg = dtc_substitute_field_type s d T)
    (hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None)
    (hArgCan : __smtx_value_canonical_bool arg = true) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool e = true ∧
          sizeOf arg < sizeOf e := by
  let e := __smtx_datatype_cons_default s d (SmtValue.Apply v arg) cTail
  have hApplyTy :
      __smtx_typeof_value (SmtValue.Apply v arg) =
        dtc_type_chain s d cTail (SmtType.Datatype s d) := by
    change
      __smtx_typeof_apply_value
          (__smtx_typeof_value v) (__smtx_typeof_value arg) =
        dtc_type_chain s d cTail (SmtType.Datatype s d)
    rw [hvTy, hArgTy]
    simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_Teq,
      native_ite, hFieldNeNone]
  have hApplyCan :
      __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
    simp [__smtx_value_canonical_bool, native_and, hvCan, hArgCan]
  refine ⟨e, ?_, ?_, ?_⟩
  · simpa [e] using
      datatype_cons_default_typeof_of_wf_finite_direct
        s d refs hRoot cTail (SmtValue.Apply v arg)
        (SmtType.Datatype s d) hTailWf hTailFin hApplyTy
  · simpa [e] using
      datatype_cons_default_canonical_of_wf
        s d refs cTail (SmtValue.Apply v arg) hTailWf hApplyCan
  · have hGrow :
        sizeOf arg <
          sizeOf
            (__smtx_datatype_cons_default s d (SmtValue.Apply v arg) cTail) :=
      sizeOf_lt_datatype_cons_default_of_wf_finite
        s d refs cTail arg (SmtValue.Apply v arg) hTailWf hTailFin
        (sizeOf_lt_apply_right v arg)
    simpa [e] using hGrow

private theorem datatype_cons_default_ne_of_ne
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList) :
    ∀ (c : SmtDatatypeCons) (v w : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        __smtx_is_finite_datatype_cons c = true ->
          v ≠ w ->
            __smtx_datatype_cons_default s d v c ≠
              __smtx_datatype_cons_default s d w c
  | SmtDatatypeCons.unit, v, w, _hWf, _hFin, hNe => by
      simpa [__smtx_datatype_cons_default] using hNe
  | SmtDatatypeCons.cons T c, v, w, hWf, hFin, hNe => by
      let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
      have hV0Ne : v0 ≠ SmtValue.NotValue := by
        simpa [v0] using
          dt_cons_wf_finite_field_default_substitute_ne_notValue
            s d (T := T) (c := c) hWf hFin
      have hV0False : native_veq v0 SmtValue.NotValue = false :=
        native_veq_eq_false_of_ne hV0Ne
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailFin : __smtx_is_finite_datatype_cons c = true :=
        dt_cons_finite_tail_of_true hFin
      have hApplyNe : SmtValue.Apply v v0 ≠ SmtValue.Apply w v0 := by
        intro hEq
        exact hNe (SmtValue.Apply.inj hEq).1
      have hRec :=
        datatype_cons_default_ne_of_ne s d refs c
          (SmtValue.Apply v v0) (SmtValue.Apply w v0)
          hTailWf hTailFin hApplyNe
      simpa [__smtx_datatype_cons_default, v0, native_ite, hV0False]
        using hRec

private def dtc_self_ref_finite_context
    (root : native_String) : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => False
  | SmtDatatypeCons.cons T c =>
      (∃ r, T = SmtType.TypeRef r ∧ r = root ∧
        __smtx_is_finite_datatype_cons c = true) ∨
      (__smtx_is_finite_type T = true ∧ dtc_self_ref_finite_context root c)

private theorem datatype_cons_self_ref_context_witness
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true) :
    ∀ (c : SmtDatatypeCons) (v seed : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        dtc_self_ref_finite_context s c ->
          __smtx_typeof_value v = dtc_type_chain s d c (SmtType.Datatype s d) ->
            __smtx_value_canonical_bool v = true ->
              __smtx_typeof_value seed = SmtType.Datatype s d ->
                __smtx_value_canonical_bool seed = true ->
                  ∃ e : SmtValue,
                    __smtx_typeof_value e = SmtType.Datatype s d ∧
                      __smtx_value_canonical_bool e = true ∧
                        sizeOf seed < sizeOf e
  | SmtDatatypeCons.unit, _v, _seed, _hWf, hCtx, _hvTy, _hvCan,
      _hSeedTy, _hSeedCan => by
      cases hCtx
  | SmtDatatypeCons.cons T c, v, seed, hWf, hCtx, hvTy, hvCan,
      hSeedTy, hSeedCan => by
      rcases hCtx with hSelf | hPrefix
      · rcases hSelf with ⟨r, hT, hr, hTailFin⟩
        subst T
        subst r
        have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
          dt_cons_wf_rec_tail_of_true hWf
        let e := __smtx_datatype_cons_default s d (SmtValue.Apply v seed) c
        refine ⟨e, ?_, ?_, ?_⟩
        · have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (SmtType.Datatype s d)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain, dtc_substitute_field_type, native_ite,
              native_Teq] using hvTy
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply v seed) =
                dtc_type_chain s d c (SmtType.Datatype s d) := by
            change
              __smtx_typeof_apply_value
                  (__smtx_typeof_value v) (__smtx_typeof_value seed) =
                dtc_type_chain s d c (SmtType.Datatype s d)
            rw [hvTy', hSeedTy]
            simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
              native_Teq, native_ite]
          simpa [e] using
            datatype_cons_default_typeof_of_wf_finite_direct
              s d refs hRoot c (SmtValue.Apply v seed)
              (SmtType.Datatype s d) hTailWf hTailFin hApplyTy
        · have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply v seed) = true := by
            simp [__smtx_value_canonical_bool, native_and, hvCan, hSeedCan]
          simpa [e] using
            datatype_cons_default_canonical_of_wf
              s d refs c (SmtValue.Apply v seed) hTailWf hApplyCan
        · have hGrow :
              sizeOf seed <
                sizeOf
                  (__smtx_datatype_cons_default s d
                    (SmtValue.Apply v seed) c) :=
            sizeOf_lt_datatype_cons_default_of_wf_finite
              s d refs c seed (SmtValue.Apply v seed) hTailWf hTailFin
              (sizeOf_lt_apply_right v seed)
          simpa [e] using hGrow
      · rcases hPrefix with ⟨hHeadFin, hTailCtx⟩
        let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
        have hV0Ne : v0 ≠ SmtValue.NotValue := by
          simpa [v0] using
            dt_cons_wf_finite_head_default_substitute_ne_notValue
              s d (T := T) (c := c) hWf hHeadFin
        have hV0Ty :
            __smtx_typeof_value v0 = dtc_substitute_field_type s d T := by
          simpa [v0] using
            dtc_head_default_substitute_typeof_of_wf_finite_head
              s d (T := T) (c := c) hRoot hWf hHeadFin
        have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None :=
          dtc_substitute_field_type_ne_none_of_finite_type s d hHeadFin
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v v0) =
              dtc_type_chain s d c (SmtType.Datatype s d) := by
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          change
            __smtx_typeof_apply_value
                (__smtx_typeof_value v) (__smtx_typeof_value v0) =
              dtc_type_chain s d c (SmtType.Datatype s d)
          rw [hvTy', hV0Ty]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            native_Teq, native_ite, hFieldNeNone]
        have hV0Can :
            __smtx_value_canonical_bool v0 = true := by
          simpa [v0] using
            dt_cons_wf_field_default_substitute_canonical
              s d (T := T) (c := c) hWf
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v v0) = true := by
          simp [__smtx_value_canonical_bool, native_and, hvCan, hV0Can]
        have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
          dt_cons_wf_rec_tail_of_true hWf
        exact datatype_cons_self_ref_context_witness s d refs hRoot c
          (SmtValue.Apply v v0) seed hTailWf hTailCtx hApplyTy hApplyCan
          hSeedTy hSeedCan

private def dtc_primitive_infinite_finite_context : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => False
  | SmtDatatypeCons.cons T c =>
      (T = SmtType.Int ∧ __smtx_is_finite_datatype_cons c = true) ∨
      (T = SmtType.Real ∧ __smtx_is_finite_datatype_cons c = true) ∨
      (∃ u, T = SmtType.USort u ∧
        __smtx_is_finite_datatype_cons c = true) ∨
      (__smtx_is_finite_type T = true ∧
        dtc_primitive_infinite_finite_context c)

private theorem datatype_cons_primitive_context_witness
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true)
    (minSize : Nat) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        dtc_primitive_infinite_finite_context c ->
          __smtx_typeof_value v = dtc_type_chain s d c (SmtType.Datatype s d) ->
            __smtx_value_canonical_bool v = true ->
              ∃ e : SmtValue,
                __smtx_typeof_value e = SmtType.Datatype s d ∧
                  __smtx_value_canonical_bool e = true ∧
                    minSize ≤ sizeOf e
  | SmtDatatypeCons.unit, _v, _hWf, hCtx, _hvTy, _hvCan => by
      cases hCtx
  | SmtDatatypeCons.cons T c, v, hWf, hCtx, hvTy, hvCan => by
      rcases hCtx with hInt | hReal | hUSort | hPrefix
      · rcases hInt with ⟨hT, hTailFin⟩
        subst T
        have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
          dt_cons_wf_rec_tail_of_true hWf
        rcases int_large_witness minSize with
          ⟨arg, hArgTy, hArgCan, hArgSize⟩
        have hvTy' :
            __smtx_typeof_value v =
              SmtType.DtcAppType (dtc_substitute_field_type s d SmtType.Int)
                (dtc_type_chain s d c (SmtType.Datatype s d)) := by
          simpa [dtc_type_chain] using hvTy
        have hArgTy' :
            __smtx_typeof_value arg = dtc_substitute_field_type s d SmtType.Int := by
          simpa [dtc_substitute_field_type, native_ite, native_Teq] using hArgTy
        rcases datatype_cons_default_with_head_arg_witness
            s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
            (by simp [dtc_substitute_field_type, native_ite, native_Teq])
            hArgCan with
          ⟨e, heTy, heCan, hGrow⟩
        exact ⟨e, heTy, heCan, by omega⟩
      · rcases hReal with ⟨hT, hTailFin⟩
        subst T
        have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
          dt_cons_wf_rec_tail_of_true hWf
        rcases real_large_witness minSize with
          ⟨arg, hArgTy, hArgCan, hArgSize⟩
        have hvTy' :
            __smtx_typeof_value v =
              SmtType.DtcAppType (dtc_substitute_field_type s d SmtType.Real)
                (dtc_type_chain s d c (SmtType.Datatype s d)) := by
          simpa [dtc_type_chain] using hvTy
        have hArgTy' :
            __smtx_typeof_value arg = dtc_substitute_field_type s d SmtType.Real := by
          simpa [dtc_substitute_field_type, native_ite, native_Teq] using hArgTy
        rcases datatype_cons_default_with_head_arg_witness
            s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
            (by simp [dtc_substitute_field_type, native_ite, native_Teq])
            hArgCan with
          ⟨e, heTy, heCan, hGrow⟩
        exact ⟨e, heTy, heCan, by omega⟩
      · rcases hUSort with ⟨u, hT, hTailFin⟩
        subst T
        have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
          dt_cons_wf_rec_tail_of_true hWf
        rcases usort_large_witness u minSize with
          ⟨arg, hArgTy, hArgCan, hArgSize⟩
        have hvTy' :
            __smtx_typeof_value v =
              SmtType.DtcAppType
                (dtc_substitute_field_type s d (SmtType.USort u))
                (dtc_type_chain s d c (SmtType.Datatype s d)) := by
          simpa [dtc_type_chain] using hvTy
        have hArgTy' :
            __smtx_typeof_value arg =
              dtc_substitute_field_type s d (SmtType.USort u) := by
          simpa [dtc_substitute_field_type, native_ite, native_Teq] using hArgTy
        rcases datatype_cons_default_with_head_arg_witness
            s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
            (by simp [dtc_substitute_field_type, native_ite, native_Teq])
            hArgCan with
          ⟨e, heTy, heCan, hGrow⟩
        exact ⟨e, heTy, heCan, by omega⟩
      · rcases hPrefix with ⟨hHeadFin, hTailCtx⟩
        let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
        have hV0Ty :
            __smtx_typeof_value v0 = dtc_substitute_field_type s d T := by
          simpa [v0] using
            dtc_head_default_substitute_typeof_of_wf_finite_head
              s d (T := T) (c := c) hRoot hWf hHeadFin
        have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None :=
          dtc_substitute_field_type_ne_none_of_finite_type s d hHeadFin
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v v0) =
              dtc_type_chain s d c (SmtType.Datatype s d) := by
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          change
            __smtx_typeof_apply_value
                (__smtx_typeof_value v) (__smtx_typeof_value v0) =
              dtc_type_chain s d c (SmtType.Datatype s d)
          rw [hvTy', hV0Ty]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            native_Teq, native_ite, hFieldNeNone]
        have hV0Can :
            __smtx_value_canonical_bool v0 = true := by
          simpa [v0] using
            dt_cons_wf_field_default_substitute_canonical
              s d (T := T) (c := c) hWf
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v v0) = true := by
          simp [__smtx_value_canonical_bool, native_and, hvCan, hV0Can]
        have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
          dt_cons_wf_rec_tail_of_true hWf
        exact datatype_cons_primitive_context_witness s d refs hRoot minSize c
          (SmtValue.Apply v v0) hTailWf hTailCtx hApplyTy hApplyCan

private def dtc_deferred_infinite_context
    (root : native_String) : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => False
  | SmtDatatypeCons.cons T c =>
      (∃ r, T = SmtType.TypeRef r ∧ r = root ∧
        dtc_deferred_infinite_context root c) ∨
      (T = SmtType.Int ∧
        (__smtx_is_finite_datatype_cons c = true ∨
          dtc_deferred_infinite_context root c)) ∨
      (T = SmtType.Real ∧
        (__smtx_is_finite_datatype_cons c = true ∨
          dtc_deferred_infinite_context root c)) ∨
      (∃ u, T = SmtType.USort u ∧
        (__smtx_is_finite_datatype_cons c = true ∨
          dtc_deferred_infinite_context root c)) ∨
      (smt_type_simple_large_context T ∧
        (__smtx_is_finite_datatype_cons c = true ∨
          dtc_deferred_infinite_context root c)) ∨
      (smt_type_simple_map_value_context T ∧
        (__smtx_is_finite_datatype_cons c = true ∨
          dtc_deferred_infinite_context root c)) ∨
      (__smtx_is_finite_type T = true ∧
        dtc_deferred_infinite_context root c)

private theorem datatype_cons_deferred_context_witness
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true)
    (minSize : Nat)
    (hDefaultTy :
      __smtx_typeof_value
          (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d)
    (hDefaultCan :
      __smtx_value_canonical_bool
          (__smtx_type_default (SmtType.Datatype s d)) = true) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        dtc_deferred_infinite_context s c ->
          __smtx_typeof_value v = dtc_type_chain s d c (SmtType.Datatype s d) ->
            __smtx_value_canonical_bool v = true ->
              ∃ e : SmtValue,
                __smtx_typeof_value e = SmtType.Datatype s d ∧
                  __smtx_value_canonical_bool e = true ∧
                    minSize ≤ sizeOf e
  | SmtDatatypeCons.unit, _v, _hWf, hCtx, _hvTy, _hvCan => by
      cases hCtx
  | SmtDatatypeCons.cons T c, v, hWf, hCtx, hvTy, hvCan => by
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      rcases hCtx with hSelf | hInt | hReal | hUSort | hSimple | hMap | hPrefix
      · rcases hSelf with ⟨r, hT, hr, hTailCtx⟩
        subst T
        subst r
        let arg := __smtx_type_default (SmtType.Datatype s d)
        have hvTy' :
            __smtx_typeof_value v =
              SmtType.DtcAppType (SmtType.Datatype s d)
                (dtc_type_chain s d c (SmtType.Datatype s d)) := by
          simpa [dtc_type_chain, dtc_substitute_field_type, native_ite,
            native_Teq] using hvTy
        have hArgTy :
            __smtx_typeof_value arg = SmtType.Datatype s d := by
          simpa [arg] using hDefaultTy
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v arg) =
              dtc_type_chain s d c (SmtType.Datatype s d) := by
          change
            __smtx_typeof_apply_value
                (__smtx_typeof_value v) (__smtx_typeof_value arg) =
              dtc_type_chain s d c (SmtType.Datatype s d)
          rw [hvTy', hArgTy]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            native_Teq, native_ite]
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
          simp [__smtx_value_canonical_bool, native_and, hvCan,
            hDefaultCan, arg]
        exact datatype_cons_deferred_context_witness
          s d refs hRoot minSize hDefaultTy hDefaultCan c
          (SmtValue.Apply v arg) hTailWf hTailCtx hApplyTy hApplyCan
      · rcases hInt with ⟨hT, hTail⟩
        subst T
        rcases hTail with hTailFin | hTailCtx
        · rcases int_large_witness minSize with
            ⟨arg, hArgTy, hArgCan, hArgSize⟩
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d SmtType.Int)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy' :
              __smtx_typeof_value arg =
                dtc_substitute_field_type s d SmtType.Int := by
            simpa [dtc_substitute_field_type, native_ite, native_Teq] using hArgTy
          rcases datatype_cons_default_with_head_arg_witness
              s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
              (by simp [dtc_substitute_field_type, native_ite, native_Teq])
              hArgCan with
            ⟨e, heTy, heCan, hGrow⟩
          exact ⟨e, heTy, heCan, by omega⟩
        · let arg := __smtx_type_default SmtType.Int
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d SmtType.Int)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy :
              __smtx_typeof_value arg =
                dtc_substitute_field_type s d SmtType.Int := by
            simp [arg, __smtx_type_default, __smtx_typeof_value,
              dtc_substitute_field_type, native_ite, native_Teq]
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply v arg) =
                dtc_type_chain s d c (SmtType.Datatype s d) := by
            change
              __smtx_typeof_apply_value
                  (__smtx_typeof_value v) (__smtx_typeof_value arg) =
                dtc_type_chain s d c (SmtType.Datatype s d)
            rw [hvTy', hArgTy]
            simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
              native_Teq, native_ite, dtc_substitute_field_type]
          have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
            simp [arg, __smtx_type_default, __smtx_value_canonical_bool,
              native_and, hvCan]
          exact datatype_cons_deferred_context_witness
            s d refs hRoot minSize hDefaultTy hDefaultCan c
            (SmtValue.Apply v arg) hTailWf hTailCtx hApplyTy hApplyCan
      · rcases hReal with ⟨hT, hTail⟩
        subst T
        rcases hTail with hTailFin | hTailCtx
        · rcases real_large_witness minSize with
            ⟨arg, hArgTy, hArgCan, hArgSize⟩
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d SmtType.Real)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy' :
              __smtx_typeof_value arg =
                dtc_substitute_field_type s d SmtType.Real := by
            simpa [dtc_substitute_field_type, native_ite, native_Teq] using hArgTy
          rcases datatype_cons_default_with_head_arg_witness
              s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
              (by simp [dtc_substitute_field_type, native_ite, native_Teq])
              hArgCan with
            ⟨e, heTy, heCan, hGrow⟩
          exact ⟨e, heTy, heCan, by omega⟩
        · let arg := __smtx_type_default SmtType.Real
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d SmtType.Real)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy :
              __smtx_typeof_value arg =
                dtc_substitute_field_type s d SmtType.Real := by
            simp [arg, __smtx_type_default, __smtx_typeof_value,
              dtc_substitute_field_type, native_ite, native_Teq]
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply v arg) =
                dtc_type_chain s d c (SmtType.Datatype s d) := by
            change
              __smtx_typeof_apply_value
                  (__smtx_typeof_value v) (__smtx_typeof_value arg) =
                dtc_type_chain s d c (SmtType.Datatype s d)
            rw [hvTy', hArgTy]
            simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
              native_Teq, native_ite, dtc_substitute_field_type]
          have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
            simp [arg, __smtx_type_default, __smtx_value_canonical_bool,
              native_and, hvCan]
          exact datatype_cons_deferred_context_witness
            s d refs hRoot minSize hDefaultTy hDefaultCan c
            (SmtValue.Apply v arg) hTailWf hTailCtx hApplyTy hApplyCan
      · rcases hUSort with ⟨u, hT, hTail⟩
        subst T
        rcases hTail with hTailFin | hTailCtx
        · rcases usort_large_witness u minSize with
            ⟨arg, hArgTy, hArgCan, hArgSize⟩
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType
                  (dtc_substitute_field_type s d (SmtType.USort u))
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy' :
              __smtx_typeof_value arg =
                dtc_substitute_field_type s d (SmtType.USort u) := by
            simpa [dtc_substitute_field_type, native_ite, native_Teq] using hArgTy
          rcases datatype_cons_default_with_head_arg_witness
              s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
              (by simp [dtc_substitute_field_type, native_ite, native_Teq])
              hArgCan with
            ⟨e, heTy, heCan, hGrow⟩
          exact ⟨e, heTy, heCan, by omega⟩
        · let arg := __smtx_type_default (SmtType.USort u)
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType
                  (dtc_substitute_field_type s d (SmtType.USort u))
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy :
              __smtx_typeof_value arg =
                dtc_substitute_field_type s d (SmtType.USort u) := by
            simp [arg, __smtx_type_default, __smtx_typeof_value,
              dtc_substitute_field_type, native_ite, native_Teq]
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply v arg) =
                dtc_type_chain s d c (SmtType.Datatype s d) := by
            change
              __smtx_typeof_apply_value
                  (__smtx_typeof_value v) (__smtx_typeof_value arg) =
                dtc_type_chain s d c (SmtType.Datatype s d)
            rw [hvTy', hArgTy]
            simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
              native_Teq, native_ite, dtc_substitute_field_type]
          have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
            simp [arg, __smtx_type_default, __smtx_value_canonical_bool,
              native_and, hvCan]
          exact datatype_cons_deferred_context_witness
            s d refs hRoot minSize hDefaultTy hDefaultCan c
            (SmtValue.Apply v arg) hTailWf hTailCtx hApplyTy hApplyCan
      · rcases hSimple with ⟨hTypeCtx, hTail⟩
        rcases hTail with hTailFin | hTailCtx
        · have hTypeWf : __smtx_type_wf_rec T refs = true := by
            cases T <;> simp [smt_type_simple_large_context,
              __smtx_dt_cons_wf_rec, native_ite] at hTypeCtx hWf ⊢
            all_goals
              exact hWf.2.1
          rcases simple_type_large_witness T refs hTypeCtx hTypeWf minSize with
            ⟨arg, hArgTy, hArgCan, hArgSize⟩
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy' :
              __smtx_typeof_value arg = dtc_substitute_field_type s d T := by
            cases T <;> simp [smt_type_simple_large_context,
              dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx hArgTy ⊢
            all_goals
              exact hArgTy
          have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None := by
            cases T <;> simp [smt_type_simple_large_context,
              dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx ⊢
          rcases datatype_cons_default_with_head_arg_witness
              s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
              hFieldNeNone hArgCan with
            ⟨e, heTy, heCan, hGrow⟩
          exact ⟨e, heTy, heCan, by omega⟩
        · let arg := __smtx_type_default T
          have hTypeInh : native_inhabited_type T = true := by
            cases T <;> simp [smt_type_simple_large_context,
              __smtx_dt_cons_wf_rec, native_ite] at hTypeCtx hWf ⊢
            all_goals
              exact hWf.1
          have hDef :=
            type_default_typed_canonical_of_native_inhabited hTypeInh
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy :
              __smtx_typeof_value arg = dtc_substitute_field_type s d T := by
            cases T <;> simp [smt_type_simple_large_context, arg,
              dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx hDef ⊢
            all_goals
              exact hDef.1
          have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None := by
            cases T <;> simp [smt_type_simple_large_context,
              dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx ⊢
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply v arg) =
                dtc_type_chain s d c (SmtType.Datatype s d) := by
            change
              __smtx_typeof_apply_value
                  (__smtx_typeof_value v) (__smtx_typeof_value arg) =
                dtc_type_chain s d c (SmtType.Datatype s d)
            rw [hvTy', hArgTy]
            simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
              native_Teq, native_ite, hFieldNeNone]
          have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
            simp [__smtx_value_canonical_bool, native_and, hvCan,
              hDef.2, arg]
          exact datatype_cons_deferred_context_witness
            s d refs hRoot minSize hDefaultTy hDefaultCan c
            (SmtValue.Apply v arg) hTailWf hTailCtx hApplyTy hApplyCan
      · rcases hMap with ⟨hTypeCtx, hTail⟩
        rcases hTail with hTailFin | hTailCtx
        · have hTypeWf : __smtx_type_wf_rec T refs = true := by
            cases T <;> simp [smt_type_simple_map_value_context,
              __smtx_dt_cons_wf_rec, native_ite] at hTypeCtx hWf ⊢
            all_goals
              exact hWf.2.1
          rcases simple_map_value_large_witness T refs hTypeCtx hTypeWf minSize with
            ⟨arg, hArgTy, hArgCan, hArgSize⟩
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy' :
              __smtx_typeof_value arg = dtc_substitute_field_type s d T := by
            cases T <;> simp [smt_type_simple_map_value_context,
              dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx hArgTy ⊢
            all_goals
              exact hArgTy
          have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None := by
            cases T <;> simp [smt_type_simple_map_value_context,
              dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx ⊢
          rcases datatype_cons_default_with_head_arg_witness
              s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
              hFieldNeNone hArgCan with
            ⟨e, heTy, heCan, hGrow⟩
          exact ⟨e, heTy, heCan, by omega⟩
        · let arg := __smtx_type_default T
          have hTypeInh : native_inhabited_type T = true := by
            cases T <;> simp [smt_type_simple_map_value_context,
              __smtx_dt_cons_wf_rec, native_ite] at hTypeCtx hWf ⊢
            all_goals
              exact hWf.1
          have hDef :=
            type_default_typed_canonical_of_native_inhabited hTypeInh
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          have hArgTy :
              __smtx_typeof_value arg = dtc_substitute_field_type s d T := by
            cases T <;> simp [smt_type_simple_map_value_context, arg,
              dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx hDef ⊢
            all_goals
              exact hDef.1
          have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None := by
            cases T <;> simp [smt_type_simple_map_value_context,
              dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx ⊢
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply v arg) =
                dtc_type_chain s d c (SmtType.Datatype s d) := by
            change
              __smtx_typeof_apply_value
                  (__smtx_typeof_value v) (__smtx_typeof_value arg) =
                dtc_type_chain s d c (SmtType.Datatype s d)
            rw [hvTy', hArgTy]
            simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
              native_Teq, native_ite, hFieldNeNone]
          have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
            simp [__smtx_value_canonical_bool, native_and, hvCan, hDef.2, arg]
          exact datatype_cons_deferred_context_witness
            s d refs hRoot minSize hDefaultTy hDefaultCan c
            (SmtValue.Apply v arg) hTailWf hTailCtx hApplyTy hApplyCan
      · rcases hPrefix with ⟨hHeadFin, hTailCtx⟩
        let arg := __smtx_value_dt_substitute s d (__smtx_type_default T)
        have hArgTy :
            __smtx_typeof_value arg = dtc_substitute_field_type s d T := by
          simpa [arg] using
            dtc_head_default_substitute_typeof_of_wf_finite_head
              s d (T := T) (c := c) hRoot hWf hHeadFin
        have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None :=
          dtc_substitute_field_type_ne_none_of_finite_type s d hHeadFin
        have hArgCan :
            __smtx_value_canonical_bool arg = true := by
          simpa [arg] using
            dt_cons_wf_field_default_substitute_canonical
              s d (T := T) (c := c) hWf
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v arg) =
              dtc_type_chain s d c (SmtType.Datatype s d) := by
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          change
            __smtx_typeof_apply_value
                (__smtx_typeof_value v) (__smtx_typeof_value arg) =
              dtc_type_chain s d c (SmtType.Datatype s d)
          rw [hvTy', hArgTy]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            native_Teq, native_ite, hFieldNeNone]
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
          simp [__smtx_value_canonical_bool, native_and, hvCan, hArgCan]
        exact datatype_cons_deferred_context_witness
          s d refs hRoot minSize hDefaultTy hDefaultCan c
          (SmtValue.Apply v arg) hTailWf hTailCtx hApplyTy hApplyCan
termination_by c _ _ _ _ => sizeOf c
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

private def dtc_simple_type_source_context : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => False
  | SmtDatatypeCons.cons T c =>
      (smt_type_simple_large_context T ∧
        __smtx_is_finite_datatype_cons c = true) ∨
      (__smtx_is_finite_type T = true ∧
        dtc_simple_type_source_context c)

private theorem datatype_cons_simple_type_source_witness
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true)
    (minSize : Nat) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        dtc_simple_type_source_context c ->
          __smtx_typeof_value v = dtc_type_chain s d c (SmtType.Datatype s d) ->
            __smtx_value_canonical_bool v = true ->
              ∃ e : SmtValue,
                __smtx_typeof_value e = SmtType.Datatype s d ∧
                  __smtx_value_canonical_bool e = true ∧
                    minSize ≤ sizeOf e
  | SmtDatatypeCons.unit, _v, _hWf, hCtx, _hvTy, _hvCan => by
      cases hCtx
  | SmtDatatypeCons.cons T c, v, hWf, hCtx, hvTy, hvCan => by
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      rcases hCtx with hSource | hPrefix
      · rcases hSource with ⟨hTypeCtx, hTailFin⟩
        have hTypeWf : __smtx_type_wf_rec T refs = true := by
          cases T <;> simp [smt_type_simple_large_context,
            __smtx_dt_cons_wf_rec, native_ite] at hTypeCtx hWf ⊢
          all_goals
            exact hWf.2.1
        rcases simple_type_large_witness T refs hTypeCtx hTypeWf minSize with
          ⟨arg, hArgTy, hArgCan, hArgSize⟩
        have hvTy' :
            __smtx_typeof_value v =
              SmtType.DtcAppType (dtc_substitute_field_type s d T)
                (dtc_type_chain s d c (SmtType.Datatype s d)) := by
          simpa [dtc_type_chain] using hvTy
        have hArgTy' :
            __smtx_typeof_value arg = dtc_substitute_field_type s d T := by
          cases T <;> simp [smt_type_simple_large_context,
            dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx hArgTy ⊢
          all_goals
            exact hArgTy
        have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None := by
          cases T <;> simp [smt_type_simple_large_context,
            dtc_substitute_field_type, native_ite, native_Teq] at hTypeCtx ⊢
        rcases datatype_cons_default_with_head_arg_witness
            s d refs hRoot hTailWf hTailFin hvTy' hvCan hArgTy'
            hFieldNeNone hArgCan with
          ⟨e, heTy, heCan, hGrow⟩
        exact ⟨e, heTy, heCan, by omega⟩
      · rcases hPrefix with ⟨hHeadFin, hTailCtx⟩
        let arg := __smtx_value_dt_substitute s d (__smtx_type_default T)
        have hArgTy :
            __smtx_typeof_value arg = dtc_substitute_field_type s d T := by
          simpa [arg] using
            dtc_head_default_substitute_typeof_of_wf_finite_head
              s d (T := T) (c := c) hRoot hWf hHeadFin
        have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None :=
          dtc_substitute_field_type_ne_none_of_finite_type s d hHeadFin
        have hArgCan :
            __smtx_value_canonical_bool arg = true := by
          simpa [arg] using
            dt_cons_wf_field_default_substitute_canonical
              s d (T := T) (c := c) hWf
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v arg) =
              dtc_type_chain s d c (SmtType.Datatype s d) := by
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          change
            __smtx_typeof_apply_value
                (__smtx_typeof_value v) (__smtx_typeof_value arg) =
              dtc_type_chain s d c (SmtType.Datatype s d)
          rw [hvTy', hArgTy]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            native_Teq, native_ite, hFieldNeNone]
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
          simp [__smtx_value_canonical_bool, native_and, hvCan, hArgCan]
        exact datatype_cons_simple_type_source_witness
          s d refs hRoot minSize c (SmtValue.Apply v arg)
          hTailWf hTailCtx hApplyTy hApplyCan
termination_by c _ _ _ _ => sizeOf c
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

private theorem infinite_datatype_suffix_large_witness_residual
    (s : native_String)
    (dRoot : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true)
    (minSize : Nat)
    (hDefaultTy :
      __smtx_typeof_value
          (__smtx_type_default (SmtType.Datatype s dRoot)) =
        SmtType.Datatype s dRoot)
    (hDefaultCan :
      __smtx_value_canonical_bool
          (__smtx_type_default (SmtType.Datatype s dRoot)) = true) :
    ∀ (pre dCur : SmtDatatype),
      dRoot = dt_append pre dCur ->
        __smtx_dt_wf_rec dCur refs = true ->
          __smtx_is_finite_datatype dCur = false ->
            ∃ i : SmtValue,
              __smtx_typeof_value i = SmtType.Datatype s dRoot ∧
                __smtx_value_canonical_bool i = true ∧
                  minSize ≤ sizeOf i
  | _pre, SmtDatatype.null, _hEq, _hWf, hInf => by
      simp [__smtx_is_finite_datatype] at hInf
  | pre, SmtDatatype.sum c SmtDatatype.null, hEq, hWf, hInf => by
      have hConsWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      have hHeadTy :
          __smtx_typeof_value
              (SmtValue.DtCons s dRoot (dt_constructor_offset pre)) =
            dtc_type_chain s dRoot c (SmtType.Datatype s dRoot) :=
        typeof_dt_cons_append_offset_eq_dtc_type_chain
          s dRoot pre c SmtDatatype.null hEq
      by_cases hCtx : dtc_self_ref_finite_context s c
      · induction minSize with
        | zero =>
            exact
              ⟨__smtx_type_default (SmtType.Datatype s dRoot),
                hDefaultTy, hDefaultCan, Nat.zero_le _⟩
        | succ n ih =>
            rcases ih with ⟨seed, hSeedTy, hSeedCan, hSeedSize⟩
            rcases datatype_cons_self_ref_context_witness
                s dRoot refs hRoot c
                (SmtValue.DtCons s dRoot (dt_constructor_offset pre))
                seed hConsWf hCtx hHeadTy
                (by simp [__smtx_value_canonical_bool])
                hSeedTy hSeedCan with
              ⟨e, heTy, heCan, hGrow⟩
            exact ⟨e, heTy, heCan, by omega⟩
      · by_cases hPrimCtx : dtc_primitive_infinite_finite_context c
        · rcases datatype_cons_primitive_context_witness
              s dRoot refs hRoot minSize c
              (SmtValue.DtCons s dRoot (dt_constructor_offset pre))
              hConsWf hPrimCtx hHeadTy
              (by simp [__smtx_value_canonical_bool]) with
            ⟨e, heTy, heCan, heSize⟩
          exact ⟨e, heTy, heCan, heSize⟩
        · have hInfCases :
              __smtx_is_finite_datatype_cons c = false ∨
                __smtx_is_finite_datatype SmtDatatype.null = false :=
            finite_datatype_sum_false_cases hInf
          have _hConsInf :
              __smtx_is_finite_datatype_cons c = false := by
            rcases hInfCases with hConsInf | hTailInf
            · exact hConsInf
            · simp [__smtx_is_finite_datatype] at hTailInf
          by_cases hDeferred : dtc_deferred_infinite_context s c
          · exact datatype_cons_deferred_context_witness
              s dRoot refs hRoot minSize hDefaultTy hDefaultCan c
              (SmtValue.DtCons s dRoot (dt_constructor_offset pre))
              hConsWf hDeferred hHeadTy
              (by simp [__smtx_value_canonical_bool])
          · by_cases hSimple : dtc_simple_type_source_context c
            · exact datatype_cons_simple_type_source_witness
                s dRoot refs hRoot minSize c
                (SmtValue.DtCons s dRoot (dt_constructor_offset pre))
                hConsWf hSimple hHeadTy
                (by simp [__smtx_value_canonical_bool])
            · sorry
  | pre, SmtDatatype.sum c (SmtDatatype.sum cTail dTailTail), hEq, hWf, hInf => by
      have hConsWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      have hHeadTy :
          __smtx_typeof_value
              (SmtValue.DtCons s dRoot (dt_constructor_offset pre)) =
            dtc_type_chain s dRoot c (SmtType.Datatype s dRoot) :=
        typeof_dt_cons_append_offset_eq_dtc_type_chain
          s dRoot pre c (SmtDatatype.sum cTail dTailTail) hEq
      by_cases hCtx : dtc_self_ref_finite_context s c
      · induction minSize with
        | zero =>
            exact
              ⟨__smtx_type_default (SmtType.Datatype s dRoot),
                hDefaultTy, hDefaultCan, Nat.zero_le _⟩
        | succ n ih =>
            rcases ih with ⟨seed, hSeedTy, hSeedCan, hSeedSize⟩
            rcases datatype_cons_self_ref_context_witness
                s dRoot refs hRoot c
                (SmtValue.DtCons s dRoot (dt_constructor_offset pre))
                seed hConsWf hCtx hHeadTy
                (by simp [__smtx_value_canonical_bool])
                hSeedTy hSeedCan with
              ⟨e, heTy, heCan, hGrow⟩
            exact ⟨e, heTy, heCan, by omega⟩
      · by_cases hPrimCtx : dtc_primitive_infinite_finite_context c
        · rcases datatype_cons_primitive_context_witness
              s dRoot refs hRoot minSize c
              (SmtValue.DtCons s dRoot (dt_constructor_offset pre))
              hConsWf hPrimCtx hHeadTy
              (by simp [__smtx_value_canonical_bool]) with
            ⟨e, heTy, heCan, heSize⟩
          exact ⟨e, heTy, heCan, heSize⟩
        · have hInfCases :
              __smtx_is_finite_datatype_cons c = false ∨
                __smtx_is_finite_datatype
                  (SmtDatatype.sum cTail dTailTail) = false :=
            finite_datatype_sum_false_cases hInf
          by_cases hTailInf :
              __smtx_is_finite_datatype
                (SmtDatatype.sum cTail dTailTail) = false
          · have hTailWf :
                __smtx_dt_wf_rec
                    (SmtDatatype.sum cTail dTailTail) refs = true :=
              dt_wf_tail_of_nonempty_tail_wf hWf
            let pre' := dt_append pre (SmtDatatype.sum c SmtDatatype.null)
            have hEq' :
                dRoot =
                  dt_append pre' (SmtDatatype.sum cTail dTailTail) := by
              exact hEq.trans
                (dt_append_singleton_tail pre c
                  (SmtDatatype.sum cTail dTailTail)).symm
            have hDecr :
                sizeOf (SmtDatatype.sum cTail dTailTail) <
                  sizeOf
                    (SmtDatatype.sum c
                      (SmtDatatype.sum cTail dTailTail)) := by
              rw [show
                sizeOf (SmtDatatype.sum cTail dTailTail) =
                  1 + sizeOf cTail + sizeOf dTailTail by rfl]
              rw [show
                sizeOf
                    (SmtDatatype.sum c
                      (SmtDatatype.sum cTail dTailTail)) =
                  1 + sizeOf c +
                    (1 + sizeOf cTail + sizeOf dTailTail) by rfl]
              omega
            exact
              infinite_datatype_suffix_large_witness_residual
                s dRoot refs hRoot minSize hDefaultTy hDefaultCan
                pre' (SmtDatatype.sum cTail dTailTail) hEq'
                hTailWf hTailInf
          · have hTailFin :
                __smtx_is_finite_datatype
                  (SmtDatatype.sum cTail dTailTail) = true := by
              cases h :
                  __smtx_is_finite_datatype
                    (SmtDatatype.sum cTail dTailTail) <;>
                simp [h] at hTailInf ⊢
            have _hConsInf :
                __smtx_is_finite_datatype_cons c = false := by
              rcases hInfCases with hConsInf | hTailInf'
              · exact hConsInf
              · rw [hTailFin] at hTailInf'
                simp at hTailInf'
            by_cases hDeferred : dtc_deferred_infinite_context s c
            · exact datatype_cons_deferred_context_witness
                s dRoot refs hRoot minSize hDefaultTy hDefaultCan c
                (SmtValue.DtCons s dRoot (dt_constructor_offset pre))
                hConsWf hDeferred hHeadTy
                (by simp [__smtx_value_canonical_bool])
            · by_cases hSimple : dtc_simple_type_source_context c
              · exact datatype_cons_simple_type_source_witness
                  s dRoot refs hRoot minSize c
                  (SmtValue.DtCons s dRoot (dt_constructor_offset pre))
                  hConsWf hSimple hHeadTy
                  (by simp [__smtx_value_canonical_bool])
              · sorry
termination_by pre dCur _ _ _ => sizeOf dCur
decreasing_by
  simp_wf
  first
  | exact hDecr
  | simpa using hDecr
  | omega

private theorem infinite_datatype_large_witness_residual
    (s : native_String)
    (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (hRec :
      __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true)
    (hInfinite : __smtx_is_finite_type (SmtType.Datatype s d) = false)
    (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  cases d with
  | null =>
      simp [__smtx_is_finite_type, __smtx_is_finite_datatype] at hInfinite
  | sum c dTail =>
      let refs := native_reflist_insert native_reflist_nil s
      have hRoot : native_reflist_contains refs s = true := by
        simp [refs, native_reflist_contains, native_reflist_insert]
      have hDtWf :
          __smtx_dt_wf_rec (SmtDatatype.sum c dTail) refs = true := by
        have hParts :
            ¬ s ∈ native_reflist_nil ∧
              __smtx_dt_wf_rec (SmtDatatype.sum c dTail) refs = true := by
          simpa [refs, __smtx_type_wf_rec, native_reflist_contains,
            native_reflist_insert, native_ite] using hRec
        exact hParts.2
      have hDtInfinite :
          __smtx_is_finite_datatype (SmtDatatype.sum c dTail) = false := by
        simpa [__smtx_is_finite_type] using hInfinite
      have hDefault :
          __smtx_typeof_value
                (__smtx_type_default
                  (SmtType.Datatype s (SmtDatatype.sum c dTail))) =
              SmtType.Datatype s (SmtDatatype.sum c dTail) ∧
            __smtx_value_canonical_bool
                (__smtx_type_default
                  (SmtType.Datatype s (SmtDatatype.sum c dTail))) = true :=
        type_default_typed_canonical_of_native_inhabited hInh
      exact
        infinite_datatype_suffix_large_witness_residual
          s (SmtDatatype.sum c dTail) refs hRoot minSize
          hDefault.1 hDefault.2 SmtDatatype.null
          (SmtDatatype.sum c dTail) rfl hDtWf hDtInfinite

private def smt_seq_heads : List SmtValue -> List SmtValue
  | SmtValue.Seq (SmtSeq.cons v _) :: xs => v :: smt_seq_heads xs
  | _ :: xs => smt_seq_heads xs
  | [] => []

private theorem smt_seq_head_mem_of_mem (x : SmtValue) (s : SmtSeq) :
    ∀ {xs : List SmtValue},
      SmtValue.Seq (SmtSeq.cons x s) ∈ xs ->
        x ∈ smt_seq_heads xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_seq_heads] at h ⊢
      case Seq s' =>
        cases s' <;> simp [smt_seq_heads] at h ⊢
        case empty T' =>
          exact ih h
        case cons y ys =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨hHead, _hTailEq⟩
            subst x
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

private def smt_set_head_keys : List SmtValue -> List SmtValue
  | SmtValue.Set (SmtMap.cons k _ _) :: xs => k :: smt_set_head_keys xs
  | _ :: xs => smt_set_head_keys xs
  | [] => []

private theorem smt_set_head_key_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Set (SmtMap.cons k e m) ∈ xs ->
        k ∈ smt_set_head_keys xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_set_head_keys] at h ⊢
      case Set m' =>
        cases m' <;> simp [smt_set_head_keys] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨hKey, _hRest⟩
            subst k
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

private def smt_map_head_values : List SmtValue -> List SmtValue
  | SmtValue.Map (SmtMap.cons _ e _) :: xs => e :: smt_map_head_values xs
  | _ :: xs => smt_map_head_values xs
  | [] => []

private theorem smt_map_head_value_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Map (SmtMap.cons k e m) ∈ xs ->
        e ∈ smt_map_head_values xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_map_head_values] at h ⊢
      case Map m' =>
        cases m' <;> simp [smt_map_head_values] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨_hKey, hValue, _hRest⟩
            subst e
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

private def smt_map_head_keys : List SmtValue -> List SmtValue
  | SmtValue.Map (SmtMap.cons k _ _) :: xs => k :: smt_map_head_keys xs
  | _ :: xs => smt_map_head_keys xs
  | [] => []

private theorem smt_map_head_key_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Map (SmtMap.cons k e m) ∈ xs ->
        k ∈ smt_map_head_keys xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_map_head_keys] at h ⊢
      case Map m' =>
        cases m' <;> simp [smt_map_head_keys] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨hKey, _hRest⟩
            subst k
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

mutual

private theorem finite_nonunit_type_nondefault_value :
    ∀ (T : SmtType) (refs : RefList),
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T refs = true ->
          __smtx_is_finite_type T = true ->
            __smtx_is_unit_type T = false ->
              ∃ e : SmtValue,
                __smtx_typeof_value e = T ∧
                  __smtx_value_canonical_bool e = true ∧
                    native_veq e (__smtx_type_default T) = false
  | SmtType.None, _refs, _hInh, hRec, _hFinite, _hNonUnit => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, _refs, _hInh, _hRec, _hFinite, _hNonUnit => by
      refine ⟨SmtValue.Boolean true, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_veq]
  | SmtType.Int, _refs, _hInh, _hRec, hFinite, _hNonUnit => by
      simp [__smtx_is_finite_type] at hFinite
  | SmtType.Real, _refs, _hInh, _hRec, hFinite, _hNonUnit => by
      simp [__smtx_is_finite_type] at hFinite
  | SmtType.RegLan, _refs, _hInh, hRec, _hFinite, _hNonUnit => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, _refs, _hInh, _hRec, _hFinite, hNonUnit => by
      cases w with
      | zero =>
          simp [__smtx_is_unit_type, native_nateq] at hNonUnit
      | succ w =>
          refine
            ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1,
              ?_, ?_, ?_⟩
          · exact bitvec_succ_one_typeof w
          · exact bitvec_succ_one_canonical w
          · exact bitvec_succ_one_ne_default w
  | SmtType.Map T U, _refs, _hInh, hRec, hFinite, hNonUnit => by
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hRec
      have hUNonUnit : __smtx_is_unit_type U = false := by
        simpa [__smtx_is_unit_type] using hNonUnit
      have hTFinite : __smtx_is_finite_type T = true := by
        cases hTF : __smtx_is_finite_type T <;>
          cases hUF : __smtx_is_finite_type U <;>
            simp [__smtx_is_finite_type, hUNonUnit, hTF, hUF,
              native_or, native_and] at hFinite ⊢
      have hUFinite : __smtx_is_finite_type U = true := by
        cases hTF : __smtx_is_finite_type T <;>
          cases hUF : __smtx_is_finite_type U <;>
            simp [__smtx_is_finite_type, hUNonUnit, hTF, hUF,
              native_or, native_and] at hFinite ⊢
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      have hUDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.2.2.1
      rcases finite_nonunit_type_nondefault_value
          U native_reflist_nil hRecParts.2.2.1 hRecParts.2.2.2
          hUFinite hUNonUnit with
        ⟨e, heTy, heCan, heNeDefault⟩
      have heNeDefaultProp : e ≠ __smtx_type_default U := by
        intro hEq
        subst e
        simp [native_veq] at heNeDefault
      refine
        ⟨SmtValue.Map
          (SmtMap.cons (__smtx_type_default T) e
            (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          hTDefault.1, heTy, hUDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hTDefault.2, heCan, hUDefault.1,
          hUDefault.2, hTFinite, heNeDefaultProp, native_and, native_ite,
          native_not, native_veq]
      · simp [__smtx_type_default, native_veq]
  | SmtType.Set T, _refs, _hInh, hRec, hFinite, _hNonUnit => by
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hRec
      have hTFinite : __smtx_is_finite_type T = true := by
        simpa [__smtx_is_finite_type] using hFinite
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      refine
        ⟨SmtValue.Set
          (SmtMap.cons (__smtx_type_default T) (SmtValue.Boolean true)
            (SmtMap.default T (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hTDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hTDefault.2, hTFinite, native_and,
          native_ite, native_not, native_veq, __smtx_typeof_value,
          __smtx_type_default]
      · simp [__smtx_type_default, native_veq]
  | SmtType.Seq T, _refs, _hInh, hRec, hFinite, _hNonUnit => by
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hRec
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      refine
        ⟨SmtValue.Seq (SmtSeq.cons (__smtx_type_default T) (SmtSeq.empty T)),
          ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_seq_value,
          hTDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_seq_canonical,
          hTDefault.2, native_and]
      · simp [__smtx_type_default, native_veq]
  | SmtType.Char, _refs, _hInh, _hRec, _hFinite, _hNonUnit => by
      refine ⟨SmtValue.Char (Char.ofNat 1), ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_nat_to_char, native_veq]
  | SmtType.Datatype s d, refs, hInh, hRec, hFinite, hNonUnit => by
      exact finite_nonunit_datatype_nondefault_value
        s d refs hInh hRec hFinite hNonUnit
  | SmtType.TypeRef _s, _refs, _hInh, hRec, _hFinite, _hNonUnit => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.USort _u, _refs, _hInh, _hRec, hFinite, _hNonUnit => by
      simp [__smtx_is_finite_type] at hFinite
  | SmtType.FunType _T _U, _refs, _hInh, hRec, _hFinite, _hNonUnit => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.DtcAppType _T _U, _refs, _hInh, hRec, _hFinite, _hNonUnit => by
      simp [__smtx_type_wf_rec] at hRec
termination_by T refs _ _ _ _ => sizeOf T
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

private theorem finite_nonunit_datatype_nondefault_value :
    ∀ (s : native_String) (d : SmtDatatype) (refs : RefList),
      native_inhabited_type (SmtType.Datatype s d) = true ->
        __smtx_type_wf_rec (SmtType.Datatype s d) refs = true ->
          __smtx_is_finite_type (SmtType.Datatype s d) = true ->
            __smtx_is_unit_type (SmtType.Datatype s d) = false ->
              ∃ e : SmtValue,
                __smtx_typeof_value e = SmtType.Datatype s d ∧
                  __smtx_value_canonical_bool e = true ∧
                    native_veq e
                      (__smtx_type_default (SmtType.Datatype s d)) = false
  | s, SmtDatatype.null, refs, _hInh, hRec, _hFinite, _hNonUnit => by
      simp [__smtx_type_wf_rec, __smtx_dt_wf_rec, native_reflist_contains,
        native_ite] at hRec
  | s, SmtDatatype.sum c SmtDatatype.null, refs, _hInh, hRec, hFinite,
      hNonUnit => by
      let d := SmtDatatype.sum c SmtDatatype.null
      let refsD := native_reflist_insert refs s
      have hDtWf : __smtx_dt_wf_rec d refsD = true := by
        have hParts :
            ¬ s ∈ refs ∧ __smtx_dt_wf_rec d refsD = true := by
          simpa [d, refsD, __smtx_type_wf_rec, native_reflist_contains,
            native_reflist_insert, native_ite] using hRec
        exact hParts.2
      have hRoot : native_reflist_contains refsD s = true := by
        simp [refsD, native_reflist_contains, native_reflist_insert]
      have hConsWf : __smtx_dt_cons_wf_rec c refsD = true :=
        dt_wf_cons_of_wf hDtWf
      have hConsFin : __smtx_is_finite_datatype_cons c = true := by
        have hDtFin : __smtx_is_finite_datatype d = true := by
          simpa [d, __smtx_is_finite_type] using hFinite
        exact finite_dt_cons_of_finite_sum hDtFin
      have hConsNonUnit : __smtx_is_unit_datatype_cons c = false := by
        simpa [d, __smtx_is_unit_type, __smtx_is_unit_datatype] using hNonUnit
      have hHeadTy :
          __smtx_typeof_value (SmtValue.DtCons s d 0) =
            dtc_type_chain s d c (SmtType.Datatype s d) := by
        simpa [d] using typeof_dt_cons_first_eq_dtc_type_chain
          s c SmtDatatype.null
      rcases finite_nonunit_datatype_cons_nondefault_value
          s d refsD hRoot c (SmtValue.DtCons s d 0)
          hConsWf hConsFin hConsNonUnit hHeadTy
          (by simp [__smtx_value_canonical_bool]) with
        ⟨e, heTy, heCan, heNeDefaultCons⟩
      have hConsNe :
          __smtx_datatype_cons_default s d (SmtValue.DtCons s d 0) c ≠
            SmtValue.NotValue :=
        datatype_cons_default_ne_notValue_of_wf_finite
          s d refsD c (SmtValue.DtCons s d 0) hConsWf hConsFin
          (by intro hEq; cases hEq)
      have hDefaultEq :
          __smtx_type_default (SmtType.Datatype s d) =
            __smtx_datatype_cons_default s d (SmtValue.DtCons s d 0) c := by
        simpa [d, __smtx_type_default] using
          datatype_default_sum_first_of_cons_default_ne_notValue
            s d c SmtDatatype.null 0 hConsNe
      refine ⟨e, heTy, heCan, ?_⟩
      have heNeDefault :
          native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false := by
        rw [hDefaultEq]
        exact heNeDefaultCons
      simpa [d] using heNeDefault
  | s, SmtDatatype.sum c (SmtDatatype.sum cTail dTail), refs, _hInh, hRec,
      hFinite, _hNonUnit => by
      let d := SmtDatatype.sum c (SmtDatatype.sum cTail dTail)
      let refsD := native_reflist_insert refs s
      let e :=
        __smtx_datatype_cons_default s d (SmtValue.DtCons s d 1) cTail
      refine ⟨e, ?_, ?_, ?_⟩
      · have hDtWf : __smtx_dt_wf_rec d refsD = true := by
          have hParts :
              ¬ s ∈ refs ∧ __smtx_dt_wf_rec d refsD = true := by
            simpa [d, refsD, __smtx_type_wf_rec, native_reflist_contains,
              native_reflist_insert, native_ite] using hRec
          exact hParts.2
        have hFinDt : __smtx_is_finite_datatype d = true := by
          simpa [d, __smtx_is_finite_type] using hFinite
        have hTailWf :
            __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refsD =
              true :=
          dt_wf_tail_of_nonempty_tail_wf hDtWf
        have hTailConsWf :
            __smtx_dt_cons_wf_rec cTail refsD = true :=
          dt_wf_cons_of_wf hTailWf
        have hTailFin :
            __smtx_is_finite_datatype
                (SmtDatatype.sum cTail dTail) = true :=
          finite_dt_tail_of_finite_sum hFinDt
        have hTailConsFin :
            __smtx_is_finite_datatype_cons cTail = true :=
          finite_dt_cons_of_finite_sum hTailFin
        have hHeadTy :
            __smtx_typeof_value (SmtValue.DtCons s d 1) =
              dtc_type_chain s d cTail (SmtType.Datatype s d) := by
          simpa [d] using typeof_dt_cons_second_eq_dtc_type_chain
            s c cTail dTail
        have hRoot : native_reflist_contains refsD s = true := by
          simp [refsD, native_reflist_contains, native_reflist_insert]
        exact datatype_cons_default_typeof_of_wf_finite_direct
          s d refsD hRoot cTail (SmtValue.DtCons s d 1)
          (SmtType.Datatype s d) hTailConsWf hTailConsFin hHeadTy
      · have hDtWf : __smtx_dt_wf_rec d refsD = true := by
          have hParts :
              ¬ s ∈ refs ∧ __smtx_dt_wf_rec d refsD = true := by
            simpa [d, refsD, __smtx_type_wf_rec, native_reflist_contains,
              native_reflist_insert, native_ite] using hRec
          exact hParts.2
        have hTailWf :
            __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refsD = true :=
          dt_wf_tail_of_nonempty_tail_wf hDtWf
        have hTailConsWf :
            __smtx_dt_cons_wf_rec cTail refsD = true :=
          dt_wf_cons_of_wf hTailWf
        exact datatype_cons_default_canonical_of_wf
          s d refsD cTail (SmtValue.DtCons s d 1) hTailConsWf (by
            simp [__smtx_value_canonical_bool])
      · have hDtWf : __smtx_dt_wf_rec d refsD = true := by
          have hParts :
              ¬ s ∈ refs ∧ __smtx_dt_wf_rec d refsD = true := by
            simpa [d, refsD, __smtx_type_wf_rec, native_reflist_contains,
              native_reflist_insert, native_ite] using hRec
          exact hParts.2
        have hFinDt : __smtx_is_finite_datatype d = true := by
          simpa [d, __smtx_is_finite_type] using hFinite
        have hFirstWf : __smtx_dt_cons_wf_rec c refsD = true :=
          dt_wf_cons_of_wf hDtWf
        have hFirstFin : __smtx_is_finite_datatype_cons c = true :=
          finite_dt_cons_of_finite_sum hFinDt
        have hFirstNe :
            __smtx_datatype_cons_default s d (SmtValue.DtCons s d 0) c ≠
              SmtValue.NotValue :=
          datatype_cons_default_ne_notValue_of_wf_finite
            s d refsD c (SmtValue.DtCons s d 0)
            hFirstWf hFirstFin (by intro hEq; cases hEq)
        have hDefaultEq :
            __smtx_type_default (SmtType.Datatype s d) =
              __smtx_datatype_cons_default s d (SmtValue.DtCons s d 0) c := by
          simpa [__smtx_type_default, d] using
            datatype_default_sum_first_of_cons_default_ne_notValue
              s d c (SmtDatatype.sum cTail dTail) 0 hFirstNe
        have hTailWf :
            __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refsD = true :=
          dt_wf_tail_of_nonempty_tail_wf hDtWf
        have hTailConsWf :
            __smtx_dt_cons_wf_rec cTail refsD = true :=
          dt_wf_cons_of_wf hTailWf
        have hTailFin :
            __smtx_is_finite_datatype (SmtDatatype.sum cTail dTail) = true :=
          finite_dt_tail_of_finite_sum hFinDt
        have hTailConsFin :
            __smtx_is_finite_datatype_cons cTail = true :=
          finite_dt_cons_of_finite_sum hTailFin
        have hCandNe : e ≠ SmtValue.NotValue :=
          datatype_cons_default_ne_notValue_of_wf_finite
            s d refsD cTail (SmtValue.DtCons s d 1)
            hTailConsWf hTailConsFin (by intro hEq; cases hEq)
        have hFirstHead :
            __vsm_apply_head
                (__smtx_datatype_cons_default s d (SmtValue.DtCons s d 0) c) =
              SmtValue.DtCons s d 0 :=
          by
            simpa [__vsm_apply_head] using
              datatype_cons_default_head_of_ne_notValue
                s d c (SmtValue.DtCons s d 0) hFirstNe
        have hCandHead :
            __vsm_apply_head e = SmtValue.DtCons s d 1 :=
          by
            simpa [e, __vsm_apply_head] using
              datatype_cons_default_head_of_ne_notValue
                s d cTail (SmtValue.DtCons s d 1) hCandNe
        exact native_veq_eq_false_of_ne (by
          intro hEq
          have hHeadEq := congrArg __vsm_apply_head hEq
          rw [hDefaultEq, hCandHead, hFirstHead] at hHeadEq
          simp at hHeadEq)
termination_by s d refs _ _ _ _ => sizeOf d
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

private theorem finite_nonunit_datatype_cons_nondefault_value
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_dt_cons_wf_rec c refs = true ->
        __smtx_is_finite_datatype_cons c = true ->
          __smtx_is_unit_datatype_cons c = false ->
            __smtx_typeof_value v = dtc_type_chain s d c (SmtType.Datatype s d) ->
              __smtx_value_canonical_bool v = true ->
                ∃ e : SmtValue,
                  __smtx_typeof_value e = SmtType.Datatype s d ∧
                    __smtx_value_canonical_bool e = true ∧
                      native_veq e
                        (__smtx_datatype_cons_default s d v c) = false
  | SmtDatatypeCons.unit, _v, _hWf, _hFin, hNonUnit, _hvTy, _hvCan => by
      simp [__smtx_is_unit_datatype_cons] at hNonUnit
  | SmtDatatypeCons.cons T c, v, hWf, hFin, hNonUnit, hvTy, hvCan => by
      have hTailWf : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      have hTailFin : __smtx_is_finite_datatype_cons c = true :=
        dt_cons_finite_tail_of_true hFin
      have hHeadFin : __smtx_is_finite_type T = true :=
        dt_cons_finite_head_of_true hFin
      have hTypeWf : __smtx_type_wf_rec T refs = true :=
        dt_cons_wf_head_type_wf_rec_of_finite hWf hFin
      have hTypeInh : native_inhabited_type T = true := by
        cases T <;>
          simp [__smtx_dt_cons_wf_rec, __smtx_is_finite_datatype_cons,
            __smtx_is_finite_type, native_and, native_ite] at hWf hFin ⊢
        all_goals first | exact hWf.1 | exact hWf.2.1
      by_cases hHeadNonUnit : __smtx_is_unit_type T = false
      · rcases finite_nonunit_type_nondefault_value
            T refs hTypeInh hTypeWf hHeadFin hHeadNonUnit with
          ⟨arg, hArgTy0, hArgCan, hArgNeDefault0⟩
        let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
        let e := __smtx_datatype_cons_default s d (SmtValue.Apply v arg) c
        have hFieldEq :
            dtc_substitute_field_type s d T = T :=
          dtc_substitute_field_type_eq_self_of_wf_rec_finite_contains
            s d T refs hRoot hTypeWf hHeadFin
        have hDefaultStable :
            __smtx_value_dt_substitute s d (__smtx_type_default T) =
              __smtx_type_default T :=
          type_default_value_dt_substitute_eq_self_of_wf_rec_finite_contains
            s d T refs hRoot hTypeWf hHeadFin
        have hArgTy :
            __smtx_typeof_value arg = dtc_substitute_field_type s d T := by
          simpa [hFieldEq] using hArgTy0
        have hArgNeDefault :
            native_veq arg v0 = false := by
          simpa [v0, hDefaultStable] using hArgNeDefault0
        have hArgNeProp : arg ≠ v0 := by
          intro hEq
          subst arg
          simp [native_veq] at hArgNeDefault
        have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None :=
          dtc_substitute_field_type_ne_none_of_finite_type s d hHeadFin
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v arg) =
              dtc_type_chain s d c (SmtType.Datatype s d) := by
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          change
            __smtx_typeof_apply_value
                (__smtx_typeof_value v) (__smtx_typeof_value arg) =
              dtc_type_chain s d c (SmtType.Datatype s d)
          rw [hvTy', hArgTy]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            native_Teq, native_ite, hFieldNeNone]
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
          simp [__smtx_value_canonical_bool, native_and, hvCan, hArgCan]
        have hV0Ne : v0 ≠ SmtValue.NotValue := by
          simpa [v0] using
            dt_cons_wf_finite_head_default_substitute_ne_notValue
              s d (T := T) (c := c) hWf hHeadFin
        have hV0False : native_veq v0 SmtValue.NotValue = false :=
          native_veq_eq_false_of_ne hV0Ne
        have hDefaultCons :
            __smtx_datatype_cons_default s d v
                (SmtDatatypeCons.cons T c) =
              __smtx_datatype_cons_default s d (SmtValue.Apply v v0) c := by
          simp [__smtx_datatype_cons_default, v0, native_ite, hV0False]
        refine ⟨e, ?_, ?_, ?_⟩
        · simpa [e] using
            datatype_cons_default_typeof_of_wf_finite_direct
              s d refs hRoot c (SmtValue.Apply v arg)
              (SmtType.Datatype s d) hTailWf hTailFin hApplyTy
        · simpa [e] using
            datatype_cons_default_canonical_of_wf
              s d refs c (SmtValue.Apply v arg) hTailWf hApplyCan
        · have hApplyNe :
              SmtValue.Apply v arg ≠ SmtValue.Apply v v0 := by
            intro hEq
            exact hArgNeProp (SmtValue.Apply.inj hEq).2
          have hTailNe :
              e ≠ __smtx_datatype_cons_default s d
                (SmtValue.Apply v v0) c := by
            simpa [e] using
              datatype_cons_default_ne_of_ne
                s d refs c (SmtValue.Apply v arg)
                (SmtValue.Apply v v0) hTailWf hTailFin hApplyNe
          exact native_veq_eq_false_of_ne (by
            intro hEq
            apply hTailNe
            simpa [hDefaultCons] using hEq)
      · have hHeadUnit : __smtx_is_unit_type T = true := by
          cases h : __smtx_is_unit_type T <;>
            simp [h] at hHeadNonUnit ⊢
        have hTailNonUnit : __smtx_is_unit_datatype_cons c = false := by
          cases hc : __smtx_is_unit_datatype_cons c <;>
            simp [__smtx_is_unit_datatype_cons, hHeadUnit, hc,
              native_and] at hNonUnit ⊢
        let v0 := __smtx_value_dt_substitute s d (__smtx_type_default T)
        have hV0Ty :
            __smtx_typeof_value v0 = dtc_substitute_field_type s d T := by
          simpa [v0] using
            dtc_head_default_substitute_typeof_of_wf_finite_head
              s d (T := T) (c := c) hRoot hWf hHeadFin
        have hFieldNeNone : dtc_substitute_field_type s d T ≠ SmtType.None :=
          dtc_substitute_field_type_ne_none_of_finite_type s d hHeadFin
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v v0) =
              dtc_type_chain s d c (SmtType.Datatype s d) := by
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType (dtc_substitute_field_type s d T)
                  (dtc_type_chain s d c (SmtType.Datatype s d)) := by
            simpa [dtc_type_chain] using hvTy
          change
            __smtx_typeof_apply_value
                (__smtx_typeof_value v) (__smtx_typeof_value v0) =
              dtc_type_chain s d c (SmtType.Datatype s d)
          rw [hvTy', hV0Ty]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            native_Teq, native_ite, hFieldNeNone]
        have hV0Can :
            __smtx_value_canonical_bool v0 = true := by
          simpa [v0] using
            dt_cons_wf_field_default_substitute_canonical
              s d (T := T) (c := c) hWf
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v v0) = true := by
          simp [__smtx_value_canonical_bool, native_and, hvCan, hV0Can]
        have hV0Ne : v0 ≠ SmtValue.NotValue := by
          simpa [v0] using
            dt_cons_wf_finite_head_default_substitute_ne_notValue
              s d (T := T) (c := c) hWf hHeadFin
        have hV0False : native_veq v0 SmtValue.NotValue = false :=
          native_veq_eq_false_of_ne hV0Ne
        have hDefaultCons :
            __smtx_datatype_cons_default s d v
                (SmtDatatypeCons.cons T c) =
              __smtx_datatype_cons_default s d (SmtValue.Apply v v0) c := by
          simp [__smtx_datatype_cons_default, v0, native_ite, hV0False]
        rcases finite_nonunit_datatype_cons_nondefault_value
            s d refs hRoot c (SmtValue.Apply v v0)
            hTailWf hTailFin hTailNonUnit hApplyTy hApplyCan with
          ⟨e, heTy, heCan, heNeTailDefault⟩
        refine ⟨e, heTy, heCan, ?_⟩
        simpa [hDefaultCons] using heNeTailDefault
termination_by c v _ _ _ _ _ => sizeOf c
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

end

/--
Residual low-level datatype/cardinality support.  The first component handles
fresh witnesses for infinite datatypes.  The second handles the single
constructor finite non-unit case.  The third is the remaining datatype-field
typing fact for substituted defaults.
-/
theorem cpc_datatype_cardinality_residual_assumption :
    (∀ (s : native_String) (d : SmtDatatype),
      native_inhabited_type (SmtType.Datatype s d) = true ->
        __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
          __smtx_is_finite_type (SmtType.Datatype s d) = false ->
            ∀ avoid : List SmtValue,
              ∃ i : SmtValue,
                __smtx_typeof_value i = SmtType.Datatype s d ∧
                  __smtx_value_canonical_bool i = true ∧
                    ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false) ∧
      (∀ (s : native_String) (c : SmtDatatypeCons),
        native_inhabited_type
            (SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null)) = true ->
          __smtx_type_wf_rec
              (SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null))
              native_reflist_nil = true ->
            __smtx_is_finite_type
                (SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null)) = true ->
              __smtx_is_unit_type
                  (SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null)) = false ->
                ∃ e : SmtValue,
                  __smtx_typeof_value e =
                      SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null) ∧
                    __smtx_value_canonical_bool e = true ∧
                      native_veq e
                        (__smtx_type_default
                          (SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null))) =
                        false) ∧
        (∀ (s : native_String) (d : SmtDatatype)
            (sField : native_String) (dField : SmtDatatype) (refs : RefList),
          ¬ dt_first_constructor_all_fields_non_datatype dField ->
            native_reflist_contains refs s = true ->
            native_inhabited_type (SmtType.Datatype sField dField) = true ->
              __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true ->
                __smtx_is_finite_type (SmtType.Datatype sField dField) = true ->
                  __smtx_typeof_value
                      (__smtx_value_dt_substitute s d
                        (__smtx_type_default (SmtType.Datatype sField dField))) =
                    dtc_substitute_field_type s d
                      (SmtType.Datatype sField dField)) := by
  constructor
  · intro s d hInh hRec hInfinite avoid
    exact datatype_fresh_of_size_bound
      (infinite_datatype_large_witness_residual
        s d hInh hRec hInfinite (smt_value_size_bound avoid))
  · constructor
    · intro s c hInh hRec hFinite hNonUnit
      exact finite_nonunit_datatype_nondefault_value
        s (SmtDatatype.sum c SmtDatatype.null) native_reflist_nil
        hInh hRec hFinite hNonUnit
    · intro s d sField dField refs _hHasDatatypeField hRoot hInh hRec hFinite
      exact datatype_type_default_substitute_typeof_of_wf_rec_finite_contains
        s d sField dField refs hRoot hInh hRec hFinite

private theorem dtc_field_default_substitute_typeof_of_residual
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hRoot : native_reflist_contains refs s = true)
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hFin :
      __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = true) :
    __smtx_typeof_value
        (__smtx_value_dt_substitute s d (__smtx_type_default T)) =
      dtc_substitute_field_type s d T := by
  exact dtc_field_default_substitute_typeof_direct
    s d (T := T) (c := c) hRoot hWf hFin

private theorem datatype_cons_default_typeof_of_wf_finite
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (hRoot : native_reflist_contains refs s = true) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue) (R : SmtType),
      __smtx_dt_cons_wf_rec c refs = true ->
        __smtx_is_finite_datatype_cons c = true ->
          __smtx_typeof_value v = dtc_type_chain s d c R ->
            __smtx_typeof_value (__smtx_datatype_cons_default s d v c) = R
    := datatype_cons_default_typeof_of_wf_finite_direct s d refs hRoot

/--
Datatype cardinality support derived from the residual facts above.  The
multi-constructor finite case is constructive: use the concrete default value
of constructor `1`, whose apply-head cannot equal the datatype default's
constructor-`0` head.
-/
theorem cpc_datatype_cardinality_support_assumption :
    (∀ (s : native_String) (d : SmtDatatype),
      native_inhabited_type (SmtType.Datatype s d) = true ->
        __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
          __smtx_is_finite_type (SmtType.Datatype s d) = false ->
            ∀ avoid : List SmtValue,
              ∃ i : SmtValue,
                __smtx_typeof_value i = SmtType.Datatype s d ∧
                  __smtx_value_canonical_bool i = true ∧
                    ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false) ∧
      (∀ (s : native_String) (d : SmtDatatype),
        native_inhabited_type (SmtType.Datatype s d) = true ->
          __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
            __smtx_is_finite_type (SmtType.Datatype s d) = true ->
              __smtx_is_unit_type (SmtType.Datatype s d) = false ->
                ∃ e : SmtValue,
                  __smtx_typeof_value e = SmtType.Datatype s d ∧
                    __smtx_value_canonical_bool e = true ∧
                      native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false) := by
  constructor
  · exact (cpc_datatype_cardinality_residual_assumption).1
  · intro s d hInh hRec hFinite hNonUnit
    cases d with
    | null =>
        simp [__smtx_type_wf_rec, __smtx_dt_wf_rec, native_reflist_contains,
          native_ite] at hRec
    | sum c rest =>
        cases rest with
        | null =>
            exact (cpc_datatype_cardinality_residual_assumption).2.1
              s c hInh hRec hFinite hNonUnit
        | sum cTail dTail =>
            let d := SmtDatatype.sum c (SmtDatatype.sum cTail dTail)
            let refs := native_reflist_insert native_reflist_nil s
            let e :=
              __smtx_datatype_cons_default s d (SmtValue.DtCons s d 1) cTail
            refine ⟨e, ?_, ?_, ?_⟩
            · have hDtWf : __smtx_dt_wf_rec d refs = true := by
                have hParts :
                    ¬ s ∈ native_reflist_nil ∧
                      __smtx_dt_wf_rec d refs = true := by
                  simpa [d, refs, __smtx_type_wf_rec,
                    native_reflist_contains, native_reflist_insert,
                    native_ite] using hRec
                exact hParts.2
              have hFinDt : __smtx_is_finite_datatype d = true := by
                simpa [d, __smtx_is_finite_type] using hFinite
              have hTailWf :
                  __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs =
                    true :=
                dt_wf_tail_of_nonempty_tail_wf hDtWf
              have hTailConsWf :
                  __smtx_dt_cons_wf_rec cTail refs = true :=
                dt_wf_cons_of_wf hTailWf
              have hTailFin :
                  __smtx_is_finite_datatype
                      (SmtDatatype.sum cTail dTail) = true :=
                finite_dt_tail_of_finite_sum hFinDt
              have hTailConsFin :
                  __smtx_is_finite_datatype_cons cTail = true :=
                finite_dt_cons_of_finite_sum hTailFin
              have hHeadTy :
                  __smtx_typeof_value (SmtValue.DtCons s d 1) =
                    dtc_type_chain s d cTail (SmtType.Datatype s d) := by
                exact typeof_dt_cons_second_eq_dtc_type_chain
                  s c cTail dTail
              have hRoot : native_reflist_contains refs s = true := by
                simp [refs, native_reflist_contains, native_reflist_insert]
              exact datatype_cons_default_typeof_of_wf_finite
                s d refs hRoot cTail (SmtValue.DtCons s d 1)
                (SmtType.Datatype s d) hTailConsWf hTailConsFin hHeadTy
            · have hDtWf : __smtx_dt_wf_rec d refs = true := by
                have hParts :
                    ¬ s ∈ native_reflist_nil ∧
                      __smtx_dt_wf_rec d refs = true := by
                  simpa [d, refs, __smtx_type_wf_rec, native_reflist_contains,
                    native_reflist_insert, native_ite] using hRec
                exact hParts.2
              have hTailWf :
                  __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true :=
                dt_wf_tail_of_nonempty_tail_wf hDtWf
              have hTailConsWf :
                  __smtx_dt_cons_wf_rec cTail refs = true :=
                dt_wf_cons_of_wf hTailWf
              exact datatype_cons_default_canonical_of_wf
                s d refs cTail (SmtValue.DtCons s d 1) hTailConsWf (by
                  simp [__smtx_value_canonical_bool])
            · have hDtWf : __smtx_dt_wf_rec d refs = true := by
                have hParts :
                    ¬ s ∈ native_reflist_nil ∧
                      __smtx_dt_wf_rec d refs = true := by
                  simpa [d, refs, __smtx_type_wf_rec, native_reflist_contains,
                    native_reflist_insert, native_ite] using hRec
                exact hParts.2
              have hFinDt : __smtx_is_finite_datatype d = true := by
                simpa [d, __smtx_is_finite_type] using hFinite
              have hFirstWf : __smtx_dt_cons_wf_rec c refs = true :=
                dt_wf_cons_of_wf hDtWf
              have hFirstFin : __smtx_is_finite_datatype_cons c = true :=
                finite_dt_cons_of_finite_sum hFinDt
              have hFirstNe :
                  __smtx_datatype_cons_default s d (SmtValue.DtCons s d 0) c ≠
                    SmtValue.NotValue :=
                datatype_cons_default_ne_notValue_of_wf_finite
                  s d refs c (SmtValue.DtCons s d 0)
                  hFirstWf hFirstFin (by intro hEq; cases hEq)
              have hDefaultEq :
                  __smtx_type_default (SmtType.Datatype s d) =
                    __smtx_datatype_cons_default s d (SmtValue.DtCons s d 0) c := by
                simpa [__smtx_type_default, d] using
                  datatype_default_sum_first_of_cons_default_ne_notValue
                    s d c (SmtDatatype.sum cTail dTail) 0 hFirstNe
              have hTailWf :
                  __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true :=
                dt_wf_tail_of_nonempty_tail_wf hDtWf
              have hTailConsWf :
                  __smtx_dt_cons_wf_rec cTail refs = true :=
                dt_wf_cons_of_wf hTailWf
              have hTailFin :
                  __smtx_is_finite_datatype (SmtDatatype.sum cTail dTail) = true :=
                finite_dt_tail_of_finite_sum hFinDt
              have hTailConsFin :
                  __smtx_is_finite_datatype_cons cTail = true :=
                finite_dt_cons_of_finite_sum hTailFin
              have hCandNe : e ≠ SmtValue.NotValue :=
                datatype_cons_default_ne_notValue_of_wf_finite
                  s d refs cTail (SmtValue.DtCons s d 1)
                  hTailConsWf hTailConsFin (by intro hEq; cases hEq)
              have hFirstHead :
                  __vsm_apply_head
                      (__smtx_datatype_cons_default s d (SmtValue.DtCons s d 0) c) =
                    SmtValue.DtCons s d 0 :=
                by
                  simpa [__vsm_apply_head] using
                    datatype_cons_default_head_of_ne_notValue
                      s d c (SmtValue.DtCons s d 0) hFirstNe
              have hCandHead :
                  __vsm_apply_head e = SmtValue.DtCons s d 1 :=
                by
                  simpa [e, __vsm_apply_head] using
                    datatype_cons_default_head_of_ne_notValue
                      s d cTail (SmtValue.DtCons s d 1) hCandNe
              exact native_veq_eq_false_of_ne (by
                intro hEq
                have hHeadEq := congrArg __vsm_apply_head hEq
                rw [hDefaultEq, hCandHead, hFirstHead] at hHeadEq
                simp at hHeadEq)

/--
Residual datatype/cardinality support for infinite datatypes: a finite list of
values can always be avoided by some typed canonical inhabitant.
-/
theorem cpc_infinite_datatype_fresh_value_assumption
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec :
      __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true)
    (_hInfinite : __smtx_is_finite_type (SmtType.Datatype s d) = false)
    (avoid : List SmtValue) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  exact (cpc_datatype_cardinality_support_assumption).1
    s d _hInh _hRec _hInfinite avoid

/--
Residual datatype/cardinality support for the finite datatype case: a non-unit
datatype has a typed canonical inhabitant distinct from its default.
-/
theorem cpc_finite_nonunit_datatype_nondefault_value_assumption
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec :
      __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true)
    (_hFinite : __smtx_is_finite_type (SmtType.Datatype s d) = true)
    (_hNonUnit : __smtx_is_unit_type (SmtType.Datatype s d) = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool e = true ∧
          native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false := by
  exact (cpc_datatype_cardinality_support_assumption).2
    s d _hInh _hRec _hFinite _hNonUnit

/--
Residual datatype/cardinality support facts. The first component is datatype
infinitude; the second says non-unit datatypes have a non-default canonical
value.  The non-unit part is now proved from infinite freshness plus the
finite-specific residual fact above.
-/
theorem cpc_datatype_value_support_assumption :
    (∀ (s : native_String) (d : SmtDatatype),
      native_inhabited_type (SmtType.Datatype s d) = true ->
        __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
          __smtx_is_finite_type (SmtType.Datatype s d) = false ->
            ∀ avoid : List SmtValue,
              ∃ i : SmtValue,
                __smtx_typeof_value i = SmtType.Datatype s d ∧
                  __smtx_value_canonical_bool i = true ∧
                    ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false) ∧
      (∀ (s : native_String) (d : SmtDatatype),
        native_inhabited_type (SmtType.Datatype s d) = true ->
          __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
            __smtx_is_unit_type (SmtType.Datatype s d) = false ->
              ∃ e : SmtValue,
                __smtx_typeof_value e = SmtType.Datatype s d ∧
                  __smtx_value_canonical_bool e = true ∧
                    native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false) := by
  constructor
  · intro s d hInh hRec hInfinite avoid
    exact cpc_infinite_datatype_fresh_value_assumption
      s d hInh hRec hInfinite avoid
  · intro s d hInh hRec hNonUnit
    by_cases hFinite :
        __smtx_is_finite_type (SmtType.Datatype s d) = true
    · exact cpc_finite_nonunit_datatype_nondefault_value_assumption
        s d hInh hRec hFinite hNonUnit
    · have hInfinite :
          __smtx_is_finite_type (SmtType.Datatype s d) = false := by
        cases h : __smtx_is_finite_type (SmtType.Datatype s d) <;>
          simp [h] at hFinite ⊢
      rcases cpc_infinite_datatype_fresh_value_assumption
          s d hInh hRec hInfinite
          [__smtx_type_default (SmtType.Datatype s d)] with
        ⟨e, heTy, heCan, heFresh⟩
      refine ⟨e, heTy, heCan, ?_⟩
      exact native_veq_false_symm
        (heFresh (__smtx_type_default (SmtType.Datatype s d)) (by simp))

theorem cpc_nonunit_typed_canonical_nondefault_value
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A native_reflist_nil = true)
    (_hNonUnit : __smtx_is_unit_type A = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = A ∧
        __smtx_value_canonical_bool e = true ∧
          native_veq e (__smtx_type_default A) = false := by
  classical
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at _hRec
  | Bool =>
      refine ⟨SmtValue.Boolean true, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_veq]
  | Int =>
      refine ⟨SmtValue.Numeral 1, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_veq]
  | Real =>
      refine ⟨SmtValue.Rational (1 : native_Rat), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical_bool]
      · exact native_veq_eq_false_of_ne (by native_decide)
  | RegLan =>
      simp [__smtx_type_wf_rec] at _hRec
  | BitVec w =>
      cases w with
      | zero =>
          simp [__smtx_is_unit_type, native_nateq] at _hNonUnit
      | succ w =>
          refine
            ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1, ?_, ?_, ?_⟩
          · exact bitvec_succ_one_typeof w
          · exact bitvec_succ_one_canonical w
          · exact bitvec_succ_one_ne_default w
  | Map T U =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hUNonUnit : __smtx_is_unit_type U = false := by
        simpa [__smtx_is_unit_type] using _hNonUnit
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      have hUDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.2.2.1
      rcases cpc_nonunit_typed_canonical_nondefault_value
          U hRecParts.2.2.1 hRecParts.2.2.2 hUNonUnit with
        ⟨e, heTy, heCan, heNeDefault⟩
      have heNeDefaultProp : e ≠ __smtx_type_default U := by
        intro hEq
        subst e
        simp [native_veq] at heNeDefault
      refine
        ⟨SmtValue.Map
          (SmtMap.cons (__smtx_type_default T) e
            (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          hTDefault.1, heTy, hUDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hTDefault.2, heCan, hUDefault.1,
          hUDefault.2, heNeDefaultProp, native_and, native_ite, native_not,
          native_veq]
      · simp [__smtx_type_default, native_veq]
  | Set T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      refine
        ⟨SmtValue.Set
          (SmtMap.cons (__smtx_type_default T) (SmtValue.Boolean true)
            (SmtMap.default T (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hTDefault.1, native_ite, native_Teq]
      · cases hFin : __smtx_is_finite_type T <;>
          simp [__smtx_value_canonical_bool, __smtx_map_canonical,
            __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
            __smtx_msm_get_default, hTDefault.2, hFin, native_and, native_ite,
            native_not, native_veq, __smtx_typeof_value, __smtx_type_default]
      · simp [__smtx_type_default, native_veq]
  | Seq T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      refine
        ⟨SmtValue.Seq (SmtSeq.cons (__smtx_type_default T) (SmtSeq.empty T)),
          ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_seq_value,
          hTDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_seq_canonical,
          hTDefault.2, native_and]
      · simp [__smtx_type_default, native_veq]
  | Char =>
      refine ⟨SmtValue.Char (Char.ofNat 1), ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_nat_to_char, native_veq]
  | Datatype s d =>
      by_cases hFinite :
          __smtx_is_finite_type (SmtType.Datatype s d) = true
      · exact cpc_finite_nonunit_datatype_nondefault_value_assumption
          s d _hInh _hRec hFinite _hNonUnit
      · have hInfinite :
            __smtx_is_finite_type (SmtType.Datatype s d) = false := by
          cases h : __smtx_is_finite_type (SmtType.Datatype s d) <;>
            simp [h] at hFinite ⊢
        rcases cpc_infinite_datatype_fresh_value_assumption
            s d _hInh _hRec hInfinite
            [__smtx_type_default (SmtType.Datatype s d)] with
          ⟨e, heTy, heCan, heFresh⟩
        refine ⟨e, heTy, heCan, ?_⟩
        exact native_veq_false_symm
          (heFresh (__smtx_type_default (SmtType.Datatype s d)) (by simp))
  | TypeRef s =>
      simp [__smtx_type_wf_rec] at _hRec
  | USort u =>
      refine ⟨SmtValue.UValue u 1, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_veq]
  | FunType T U =>
      simp [__smtx_type_wf_rec] at _hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at _hRec
termination_by sizeOf A

/--
Fresh value assumption for well-formed infinite SMT types.

This is the real infinitude/cardinality statement needed by array extensionality:
given a finite avoid list, an inhabited recursively well-formed type classified
as infinite has a typed canonical value syntactically distinct from every value
in the avoid list.
-/
theorem cpc_fresh_typed_canonical_value_for_infinite_type_assumption
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A native_reflist_nil = true)
    (_hInfinite : __smtx_is_finite_type A = false)
    (avoid : List SmtValue) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical_bool i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  classical
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at _hRec
  | Bool =>
      simp [__smtx_is_finite_type] at _hInfinite
  | Int =>
      refine ⟨SmtValue.Numeral (Int.ofNat (fresh_numeral_index avoid)), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical_bool]
      · exact fresh_numeral_veq_false_of_mem avoid
  | Real =>
      refine ⟨SmtValue.Rational (Int.ofNat (fresh_rational_index avoid)), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical_bool]
      · exact fresh_rational_veq_false_of_mem avoid
  | RegLan =>
      simp [__smtx_type_wf_rec] at _hRec
  | BitVec w =>
      simp [__smtx_is_finite_type] at _hInfinite
  | Map T U =>
      by_cases hUInfinite : __smtx_is_finite_type U = false
      · have hRecParts :
            native_inhabited_type T = true ∧
              __smtx_type_wf_rec T native_reflist_nil = true ∧
                native_inhabited_type U = true ∧
                  __smtx_type_wf_rec U native_reflist_nil = true := by
          simpa [__smtx_type_wf_rec, native_and] using _hRec
        have hTDefault :
            __smtx_typeof_value (__smtx_type_default T) = T ∧
              __smtx_value_canonical_bool (__smtx_type_default T) = true := by
          exact type_default_typed_canonical_of_native_inhabited hRecParts.1
        have hUDefault :
            __smtx_typeof_value (__smtx_type_default U) = U ∧
              __smtx_value_canonical_bool (__smtx_type_default U) = true := by
          exact type_default_typed_canonical_of_native_inhabited hRecParts.2.2.1
        rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
            U hRecParts.2.2.1 hRecParts.2.2.2 hUInfinite
              (__smtx_type_default U :: smt_map_head_values avoid) with
          ⟨e, heTy, heCan, heFresh⟩
        have hDefaultNe : native_veq (__smtx_type_default U) e = false :=
          heFresh (__smtx_type_default U) (by simp)
        have hEntryNe : native_veq e (__smtx_type_default U) = false :=
          native_veq_false_symm hDefaultNe
        have hEntryNeProp : e ≠ __smtx_type_default U := by
          intro hEq
          subst e
          simp [native_veq] at hEntryNe
        refine
          ⟨SmtValue.Map
            (SmtMap.cons (__smtx_type_default T) e
              (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
        · simp [__smtx_typeof_value, __smtx_typeof_map_value,
            hTDefault.1, hUDefault.1, heTy, native_ite, native_Teq]
        · by_cases hTFinite : __smtx_is_finite_type T = true
          · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
              __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
              __smtx_msm_get_default, hTDefault.2, hUDefault.1, hUDefault.2,
              heCan, hTFinite, hEntryNeProp, native_and, native_ite, native_not,
              native_veq]
          · have hTFiniteFalse : __smtx_is_finite_type T = false := by
              cases hTF : __smtx_is_finite_type T <;> simp [hTF] at hTFinite ⊢
            simp [__smtx_value_canonical_bool, __smtx_map_canonical,
              __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
              __smtx_msm_get_default, hTDefault.2, hUDefault.2, heCan,
              hTFiniteFalse, hEntryNeProp, native_and, native_ite, native_not,
              native_veq]
        · intro j hj
          exact native_veq_eq_false_of_ne (by
            intro hEq
            subst j
            have heMem : e ∈ smt_map_head_values avoid :=
              smt_map_head_value_mem_of_mem (__smtx_type_default T) e
                (SmtMap.default T (__smtx_type_default U)) hj
            have heFalse := heFresh e (by simp [heMem])
            simp [native_veq] at heFalse)
      · exact
          by
            have hRecParts :
                native_inhabited_type T = true ∧
                  __smtx_type_wf_rec T native_reflist_nil = true ∧
                    native_inhabited_type U = true ∧
                      __smtx_type_wf_rec U native_reflist_nil = true := by
              simpa [__smtx_type_wf_rec, native_and] using _hRec
            have hUFinite : __smtx_is_finite_type U = true := by
              cases hUF : __smtx_is_finite_type U <;> simp [hUF] at hUInfinite ⊢
            have hFiniteParts :
                __smtx_is_unit_type U = false ∧
                  __smtx_is_finite_type T = false := by
              cases hUnit : __smtx_is_unit_type U <;>
                cases hTFin : __smtx_is_finite_type T <;>
                  simp [__smtx_is_finite_type, hUnit, hTFin, hUFinite,
                    native_or, native_and] at _hInfinite ⊢
            have hUDefault :
                __smtx_typeof_value (__smtx_type_default U) = U ∧
                  __smtx_value_canonical_bool (__smtx_type_default U) = true := by
              exact type_default_typed_canonical_of_native_inhabited hRecParts.2.2.1
            rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
                T hRecParts.1 hRecParts.2.1 hFiniteParts.2
                  (smt_map_head_keys avoid) with
              ⟨k, hkTy, hkCan, hkFresh⟩
            rcases cpc_nonunit_typed_canonical_nondefault_value
                U hRecParts.2.2.1 hRecParts.2.2.2 hFiniteParts.1 with
              ⟨e, heTy, heCan, heNeDefault⟩
            have heNeDefaultProp : e ≠ __smtx_type_default U := by
              intro hEq
              subst e
              simp [native_veq] at heNeDefault
            refine
              ⟨SmtValue.Map
                (SmtMap.cons k e
                  (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
            · simp [__smtx_typeof_value, __smtx_typeof_map_value,
                hkTy, heTy, hUDefault.1, native_ite, native_Teq]
            · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
                __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
                __smtx_msm_get_default, hkCan, heCan, hUDefault.2,
                hFiniteParts.2, heNeDefaultProp, native_and, native_ite,
                native_not, native_veq]
            · intro j hj
              exact native_veq_eq_false_of_ne (by
                intro hEq
                subst j
                have hkMem : k ∈ smt_map_head_keys avoid :=
                  smt_map_head_key_mem_of_mem k e
                    (SmtMap.default T (__smtx_type_default U)) hj
                have hkFalse := hkFresh k hkMem
                simp [native_veq] at hkFalse)
  | Set T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hTInfinite : __smtx_is_finite_type T = false := by
        simpa [__smtx_is_finite_type] using _hInfinite
      rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
          T hRecParts.1 hRecParts.2 hTInfinite (smt_set_head_keys avoid) with
        ⟨x, hxTy, hxCan, hxFresh⟩
      refine
        ⟨SmtValue.Set
          (SmtMap.cons x (SmtValue.Boolean true)
            (SmtMap.default T (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hxTy, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hxCan, hTInfinite, native_and, native_ite,
          native_not, native_veq]
      · intro j hj
        exact native_veq_eq_false_of_ne (by
          intro hEq
          subst j
          have hxMem : x ∈ smt_set_head_keys avoid :=
            smt_set_head_key_mem_of_mem x (SmtValue.Boolean true)
              (SmtMap.default T (SmtValue.Boolean false)) hj
          have hxFalse := hxFresh x hxMem
          simp [native_veq] at hxFalse)
  | Seq T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hTInfinite : __smtx_is_finite_type T = false := by
        simpa [__smtx_is_finite_type] using _hInfinite
      rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
          T hRecParts.1 hRecParts.2 hTInfinite (smt_seq_heads avoid) with
        ⟨x, hxTy, hxCan, hxFresh⟩
      refine ⟨SmtValue.Seq (SmtSeq.cons x (SmtSeq.empty T)), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_seq_value,
          hxTy, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_seq_canonical,
          hxCan, native_and]
      · intro j hj
        exact native_veq_eq_false_of_ne (by
          intro hEq
          subst j
          have hxMem : x ∈ smt_seq_heads avoid :=
            smt_seq_head_mem_of_mem x (SmtSeq.empty T) hj
          have hxFalse := hxFresh x hxMem
          simp [native_veq] at hxFalse)
  | Char =>
      simp [__smtx_is_finite_type] at _hInfinite
  | Datatype s d =>
      exact
        cpc_infinite_datatype_fresh_value_assumption
          s d _hInh _hRec _hInfinite avoid
  | TypeRef s =>
      simp [__smtx_type_wf_rec] at _hRec
  | USort u =>
      refine ⟨SmtValue.UValue u (fresh_usort_index u avoid), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical_bool]
      · exact fresh_usort_veq_false_of_mem u avoid
  | FunType T U =>
      simp [__smtx_type_wf_rec] at _hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at _hRec
termination_by sizeOf A

private theorem msm_lookup_eq_default_of_fresh_keys :
    ∀ (m : SmtMap) (i : SmtValue),
      (∀ j : SmtValue, j ∈ smt_map_keys m -> native_veq j i = false) ->
        __smtx_msm_lookup m i = __smtx_msm_get_default m
  | SmtMap.default T e, i, _hFresh => by
      simp [__smtx_msm_lookup, __smtx_msm_get_default]
  | SmtMap.cons j e m, i, hFresh => by
      have hj : native_veq j i = false := hFresh j (by simp [smt_map_keys])
      have hmFresh :
          ∀ k : SmtValue, k ∈ smt_map_keys m -> native_veq k i = false := by
        intro k hk
        exact hFresh k (by simp [smt_map_keys, hk])
      have hmLookup :
          __smtx_msm_lookup m i = __smtx_msm_get_default m :=
        msm_lookup_eq_default_of_fresh_keys m i hmFresh
      simpa [smt_map_keys, __smtx_msm_lookup, __smtx_msm_get_default,
        native_ite, hj] using hmLookup

/--
Fresh-index theorem for infinite map domains.

When the executable map-difference proof needs to compare the two default
payloads of canonical maps over an infinite domain, it needs a typed canonical
index outside both finite spines.
-/
theorem cpc_fresh_default_lookup_for_infinite_map_domain_assumption
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical m1 = true)
    (_hm2Can : __smtx_map_canonical m2 = true)
    (hAInh : native_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A native_reflist_nil = true)
    (_hInfinite : __smtx_is_finite_type A = false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical_bool i = true ∧
          __smtx_msm_lookup m1 i = __smtx_msm_get_default m1 ∧
            __smtx_msm_lookup m2 i = __smtx_msm_get_default m2 := by
  rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
      A hAInh hARec _hInfinite (smt_map_keys m1 ++ smt_map_keys m2) with
    ⟨i, hiTy, hiCan, hiFresh⟩
  refine ⟨i, hiTy, hiCan, ?_, ?_⟩
  · exact msm_lookup_eq_default_of_fresh_keys m1 i (by
      intro j hj
      exact hiFresh j (by simp [hj]))
  · exact msm_lookup_eq_default_of_fresh_keys m2 i (by
      intro j hj
      exact hiFresh j (by simp [hj]))

end Smtm
