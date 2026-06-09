import Cpc.Proofs.TypePreservation.Predicates

/-!
Canonical/cardinality and freshness witnesses used by datatype cardinality
reasoning and array extensionality.

This module is the intended boundary for the current residual assumption in
that support development.
-/

open SmtEval
open Smtm

namespace Smtm

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
  | SmtType.TypeRef s' =>
      native_ite (native_streq s s') (SmtType.Datatype s d)
        (SmtType.TypeRef s')
  | T => T

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
          __smtx_type_substitute, dtc_type_chain, dtc_substitute_field_type,
          native_ite, native_streq,
          typeof_dt_cons_value_rec_substitute_zero_eq_chain s d0 c dTail]

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
      __smtx_is_finite_type, native_and] at hFin hNotDatatype ⊢

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
      __smtx_is_finite_type, native_and, native_ite] at hFin ⊢

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
          __smtx_type_substitute, __smtx_is_finite_datatype_cons,
          __smtx_is_finite_type, native_and, hTail]
          at hAll hFin ⊢

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
        simp [__smtx_dtc_substitute, __smtx_type_substitute,
          __smtx_is_finite_datatype_cons, __smtx_is_finite_type,
          native_and, native_streq, hTailSub] at hWf hFin ⊢
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
        simp [native_ite, hDtSub]

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
        simp [__smtx_dtc_substitute, __smtx_type_substitute,
          native_streq, hTailSub]
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
        have hNe' : s ≠ r := fun hEq => hNe hEq.symm
        simp [native_ite, hNe']
      case Datatype sField dField =>
        have hParts :
            native_inhabited_type (SmtType.Datatype sField dField) = true ∧
              __smtx_type_wf_rec (SmtType.Datatype sField dField) refs = true ∧
                __smtx_dt_cons_wf_rec c refs = true := by
          simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
        by_cases hEq : s = sField
        · subst sField
          simp [native_ite]
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
          simp [native_ite, hEq, hDtSub]

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
    simp [dtc_substitute_field_type, __smtx_is_finite_type, native_ite]
      at hRec hFinite ⊢
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

private theorem dtc_substitute_field_type_ne_none_of_finite_type
    (s : native_String)
    (d : SmtDatatype)
    {T : SmtType}
    (hFin : __smtx_is_finite_type T = true) :
    dtc_substitute_field_type s d T ≠ SmtType.None := by
  cases T <;> simp [dtc_substitute_field_type, __smtx_is_finite_type,
    native_ite] at hFin ⊢

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
      dtc_substitute_field_type, native_ite, native_and] at hWf hFin ⊢
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

/-!
### Pumping architecture for infinite datatypes

The development below proves that every well-formed inhabited infinite
datatype has typed canonical values of arbitrarily large size, including
datatypes whose infinitude arises through nested datatype fields (mutual
recursion via `TypeRef` back-references).

Key design points:

* Values are constructed explicitly as `DtCons`/`Apply` chains; the spec's
  default/substitution machinery on values is never invoked, so no
  `__smtx_value_dt_substitute` commutation lemmas are needed.
* Scope stacks ("environments") record the enclosing datatype levels as
  `(name, raw body, closed body)` triples, innermost first.  The closed
  body of a level is the fold of `__smtx_dt_substitute` of all outer
  levels over its raw body.  All structural recursion is on raw syntax.
* `TypeRef` leaves are resolved by an oracle providing a value of the
  referenced level of size at least `n`; the outer induction is on `n`.

`smt_*_unref s X` says that `TypeRef s` does not occur free in `X` along
the traversal performed by `__smtx_*_substitute` (nested datatypes named
`s` shadow the reference).
-/

mutual

private def smt_type_unref (s : native_String) : SmtType -> Bool
  | SmtType.TypeRef r => native_not (native_streq s r)
  | SmtType.Datatype s2 d2 =>
      native_ite (native_streq s s2) true (smt_dt_unref s d2)
  | _ => true

private def smt_dtc_unref (s : native_String) : SmtDatatypeCons -> Bool
  | SmtDatatypeCons.unit => true
  | SmtDatatypeCons.cons T c =>
      native_and (smt_type_unref s T) (smt_dtc_unref s c)

private def smt_dt_unref (s : native_String) : SmtDatatype -> Bool
  | SmtDatatype.null => true
  | SmtDatatype.sum c d =>
      native_and (smt_dtc_unref s c) (smt_dt_unref s d)

end

mutual

private theorem type_substitute_eq_self_of_unref
    (s : native_String) (d : SmtDatatype) :
    ∀ T : SmtType,
      smt_type_unref s T = true -> __smtx_type_substitute s d T = T
  | SmtType.TypeRef r, h => by
      have hr : native_streq s r = false := by
        cases hsr : native_streq s r <;>
          simp [smt_type_unref, native_not, hsr] at h ⊢
      simp [__smtx_type_substitute, native_ite, hr]
  | SmtType.Datatype s2 d2, h => by
      cases hs : native_streq s s2 with
      | true =>
          simp [__smtx_type_substitute, native_ite, hs]
      | false =>
          have h2 : smt_dt_unref s d2 = true := by
            simpa [smt_type_unref, native_ite, hs] using h
          simp [__smtx_type_substitute, native_ite, hs,
            dt_substitute_eq_self_of_unref s d d2 h2]
  | SmtType.None, _ => by simp [__smtx_type_substitute]
  | SmtType.Bool, _ => by simp [__smtx_type_substitute]
  | SmtType.Int, _ => by simp [__smtx_type_substitute]
  | SmtType.Real, _ => by simp [__smtx_type_substitute]
  | SmtType.RegLan, _ => by simp [__smtx_type_substitute]
  | SmtType.BitVec _, _ => by simp [__smtx_type_substitute]
  | SmtType.Map _ _, _ => by simp [__smtx_type_substitute]
  | SmtType.Set _, _ => by simp [__smtx_type_substitute]
  | SmtType.Seq _, _ => by simp [__smtx_type_substitute]
  | SmtType.Char, _ => by simp [__smtx_type_substitute]
  | SmtType.USort _, _ => by simp [__smtx_type_substitute]
  | SmtType.FunType _ _, _ => by simp [__smtx_type_substitute]
  | SmtType.DtcAppType _ _, _ => by simp [__smtx_type_substitute]

private theorem dtc_substitute_eq_self_of_unref
    (s : native_String) (d : SmtDatatype) :
    ∀ c : SmtDatatypeCons,
      smt_dtc_unref s c = true -> __smtx_dtc_substitute s d c = c
  | SmtDatatypeCons.unit, _ => by
      simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, h => by
      have hParts : smt_type_unref s T = true ∧ smt_dtc_unref s c = true := by
        simpa [smt_dtc_unref, native_and] using h
      simp [__smtx_dtc_substitute,
        type_substitute_eq_self_of_unref s d T hParts.1,
        dtc_substitute_eq_self_of_unref s d c hParts.2]

private theorem dt_substitute_eq_self_of_unref
    (s : native_String) (d : SmtDatatype) :
    ∀ d0 : SmtDatatype,
      smt_dt_unref s d0 = true -> __smtx_dt_substitute s d d0 = d0
  | SmtDatatype.null, _ => by
      simp [__smtx_dt_substitute]
  | SmtDatatype.sum c d0, h => by
      have hParts : smt_dtc_unref s c = true ∧ smt_dt_unref s d0 = true := by
        simpa [smt_dt_unref, native_and] using h
      simp [__smtx_dt_substitute,
        dtc_substitute_eq_self_of_unref s d c hParts.1,
        dt_substitute_eq_self_of_unref s d d0 hParts.2]

end

mutual

private theorem type_unref_substitute_self
    (s : native_String) (d : SmtDatatype) :
    ∀ T : SmtType, smt_type_unref s (__smtx_type_substitute s d T) = true
  | SmtType.TypeRef r => by
      cases hr : native_streq s r with
      | true =>
          have hsr : s = r := by simpa [native_streq] using hr
          subst hsr
          simp [__smtx_type_substitute, native_ite, smt_type_unref,
            native_streq]
      | false =>
          simp [__smtx_type_substitute, native_ite, hr, smt_type_unref,
            native_not]
  | SmtType.Datatype s2 d2 => by
      cases hs : native_streq s s2 with
      | true =>
          simp [__smtx_type_substitute, native_ite, hs, smt_type_unref]
      | false =>
          simp [__smtx_type_substitute, native_ite, hs, smt_type_unref,
            dt_unref_substitute_self s d d2]
  | SmtType.None => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Bool => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Int => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Real => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.RegLan => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.BitVec _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Map _ _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Set _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Seq _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Char => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.USort _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.FunType _ _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.DtcAppType _ _ => by
      simp [__smtx_type_substitute, smt_type_unref]

private theorem dtc_unref_substitute_self
    (s : native_String) (d : SmtDatatype) :
    ∀ c : SmtDatatypeCons,
      smt_dtc_unref s (__smtx_dtc_substitute s d c) = true
  | SmtDatatypeCons.unit => by
      simp [__smtx_dtc_substitute, smt_dtc_unref]
  | SmtDatatypeCons.cons T c => by
      simp [__smtx_dtc_substitute, smt_dtc_unref, native_and,
        type_unref_substitute_self s d T,
        dtc_unref_substitute_self s d c]

private theorem dt_unref_substitute_self
    (s : native_String) (d : SmtDatatype) :
    ∀ d0 : SmtDatatype,
      smt_dt_unref s (__smtx_dt_substitute s d d0) = true
  | SmtDatatype.null => by
      simp [__smtx_dt_substitute, smt_dt_unref]
  | SmtDatatype.sum c d0 => by
      simp [__smtx_dt_substitute, smt_dt_unref, native_and,
        dtc_unref_substitute_self s d c,
        dt_unref_substitute_self s d d0]

end

mutual

private theorem type_unref_substitute_other
    (s : native_String) (d : SmtDatatype) (t : native_String)
    (hd : smt_dt_unref t d = true) :
    ∀ T : SmtType,
      smt_type_unref t T = true ->
        smt_type_unref t (__smtx_type_substitute s d T) = true
  | SmtType.TypeRef r, h => by
      cases hr : native_streq s r with
      | true =>
          cases hts : native_streq t s <;>
            simp [__smtx_type_substitute, native_ite, hr, smt_type_unref,
              hts, hd]
      | false =>
          simpa [__smtx_type_substitute, native_ite, hr] using h
  | SmtType.Datatype s2 d2, h => by
      cases hs : native_streq s s2 with
      | true =>
          simpa [__smtx_type_substitute, native_ite, hs] using h
      | false =>
          cases hts : native_streq t s2 with
          | true =>
              simp [__smtx_type_substitute, native_ite, hs, smt_type_unref,
                hts]
          | false =>
              have h2 : smt_dt_unref t d2 = true := by
                simpa [smt_type_unref, native_ite, hts] using h
              simp [__smtx_type_substitute, native_ite, hs, smt_type_unref,
                hts, dt_unref_substitute_other s d t hd d2 h2]
  | SmtType.None, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Bool, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Int, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Real, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.RegLan, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.BitVec _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Map _ _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Set _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Seq _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.Char, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.USort _, _ => by simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.FunType _ _, _ => by
      simp [__smtx_type_substitute, smt_type_unref]
  | SmtType.DtcAppType _ _, _ => by
      simp [__smtx_type_substitute, smt_type_unref]

private theorem dtc_unref_substitute_other
    (s : native_String) (d : SmtDatatype) (t : native_String)
    (hd : smt_dt_unref t d = true) :
    ∀ c : SmtDatatypeCons,
      smt_dtc_unref t c = true ->
        smt_dtc_unref t (__smtx_dtc_substitute s d c) = true
  | SmtDatatypeCons.unit, _ => by
      simp [__smtx_dtc_substitute, smt_dtc_unref]
  | SmtDatatypeCons.cons T c, h => by
      have hParts : smt_type_unref t T = true ∧ smt_dtc_unref t c = true := by
        simpa [smt_dtc_unref, native_and] using h
      simp [__smtx_dtc_substitute, smt_dtc_unref, native_and,
        type_unref_substitute_other s d t hd T hParts.1,
        dtc_unref_substitute_other s d t hd c hParts.2]

private theorem dt_unref_substitute_other
    (s : native_String) (d : SmtDatatype) (t : native_String)
    (hd : smt_dt_unref t d = true) :
    ∀ d0 : SmtDatatype,
      smt_dt_unref t d0 = true ->
        smt_dt_unref t (__smtx_dt_substitute s d d0) = true
  | SmtDatatype.null, _ => by
      simp [__smtx_dt_substitute, smt_dt_unref]
  | SmtDatatype.sum c d0, h => by
      have hParts : smt_dtc_unref t c = true ∧ smt_dt_unref t d0 = true := by
        simpa [smt_dt_unref, native_and] using h
      simp [__smtx_dt_substitute, smt_dt_unref, native_and,
        dtc_unref_substitute_other s d t hd c hParts.1,
        dt_unref_substitute_other s d t hd d0 hParts.2]

end

mutual

private theorem type_unref_of_wf_not_contains
    (t : native_String) :
    ∀ (T : SmtType) (refs : RefList),
      native_reflist_contains refs t = false ->
        __smtx_type_wf_rec T refs = true ->
          smt_type_unref t T = true
  | SmtType.TypeRef _r, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Datatype s2 d2, refs, hNot, hWf => by
      cases hts : native_streq t s2 with
      | true =>
          simp [smt_type_unref, native_ite, hts]
      | false =>
          have hParts :
              ¬ s2 ∈ refs ∧
                __smtx_dt_wf_rec d2 (native_reflist_insert refs s2) = true := by
            simpa [__smtx_type_wf_rec, native_reflist_contains,
              native_ite] using hWf
          have hNot2 :
              native_reflist_contains (native_reflist_insert refs s2) t =
                false := by
            have hts' : t ≠ s2 := by
              intro hEq
              subst hEq
              simp [native_streq] at hts
            simp [native_reflist_contains, native_reflist_insert] at hNot ⊢
            exact ⟨hts', hNot⟩
          simp [smt_type_unref, native_ite, hts,
            dt_unref_of_wf_not_contains t d2
              (native_reflist_insert refs s2) hNot2 hParts.2]
  | SmtType.None, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Bool, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Int, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Real, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.RegLan, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.BitVec _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Map _ _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Set _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Seq _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.Char, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.USort _, _refs, _hNot, _hWf => by simp [smt_type_unref]
  | SmtType.FunType _ _, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType _ _, _refs, _hNot, hWf => by
      simp [__smtx_type_wf_rec] at hWf

private theorem dtc_unref_of_wf_not_contains
    (t : native_String) :
    ∀ (c : SmtDatatypeCons) (refs : RefList),
      native_reflist_contains refs t = false ->
        __smtx_dt_cons_wf_rec c refs = true ->
          smt_dtc_unref t c = true
  | SmtDatatypeCons.unit, _refs, _hNot, _hWf => by
      simp [smt_dtc_unref]
  | SmtDatatypeCons.cons (SmtType.TypeRef r) c, refs, hNot, hWf => by
      have hParts :
          native_reflist_contains refs r = true ∧
            __smtx_dt_cons_wf_rec c refs = true := by
        cases hr : native_reflist_contains refs r <;>
          simp [__smtx_dt_cons_wf_rec, native_ite, hr] at hWf ⊢
        exact hWf
      have htr : native_streq t r = false := by
        cases htr : native_streq t r <;> simp [native_streq] at htr ⊢
        subst htr
        rw [hNot] at hParts
        simp at hParts
      simp [smt_dtc_unref, native_and, smt_type_unref, native_not, htr,
        dtc_unref_of_wf_not_contains t c refs hNot hParts.2]
  | SmtDatatypeCons.cons (SmtType.Datatype s2 d2) c, refs, hNot, hWf => by
      have hParts :
          native_inhabited_type (SmtType.Datatype s2 d2) = true ∧
            __smtx_type_wf_rec (SmtType.Datatype s2 d2) refs = true ∧
              __smtx_dt_cons_wf_rec c refs = true := by
        simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
      simp [smt_dtc_unref, native_and,
        type_unref_of_wf_not_contains t (SmtType.Datatype s2 d2) refs
          hNot hParts.2.1,
        dtc_unref_of_wf_not_contains t c refs hNot hParts.2.2]
  | SmtDatatypeCons.cons SmtType.None c, refs, hNot, hWf => by
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
  | SmtDatatypeCons.cons SmtType.Bool c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons SmtType.Int c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons SmtType.Real c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons SmtType.RegLan c, refs, hNot, hWf => by
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
  | SmtDatatypeCons.cons (SmtType.BitVec _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.Map _ _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.Set _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.Seq _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons SmtType.Char c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.USort _) c, refs, hNot, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      simp [smt_dtc_unref, native_and, smt_type_unref,
        dtc_unref_of_wf_not_contains t c refs hNot hTail]
  | SmtDatatypeCons.cons (SmtType.FunType _ _) c, refs, hNot, hWf => by
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
  | SmtDatatypeCons.cons (SmtType.DtcAppType _ _) c, refs, hNot, hWf => by
      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf

private theorem dt_unref_of_wf_not_contains
    (t : native_String) :
    ∀ (d0 : SmtDatatype) (refs : RefList),
      native_reflist_contains refs t = false ->
        __smtx_dt_wf_rec d0 refs = true ->
          smt_dt_unref t d0 = true
  | SmtDatatype.null, _refs, _hNot, hWf => by
      simp [__smtx_dt_wf_rec] at hWf
  | SmtDatatype.sum c SmtDatatype.null, refs, hNot, hWf => by
      have hCons : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      simp [smt_dt_unref, native_and,
        dtc_unref_of_wf_not_contains t c refs hNot hCons]
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), refs, hNot, hWf => by
      have hCons : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      have hTail :
          __smtx_dt_wf_rec (SmtDatatype.sum c2 d2) refs = true :=
        dt_wf_tail_of_nonempty_tail_wf hWf
      have hTailUnref :=
        dt_unref_of_wf_not_contains t (SmtDatatype.sum c2 d2) refs hNot hTail
      simp [smt_dt_unref, native_and,
        dtc_unref_of_wf_not_contains t c refs hNot hCons] at hTailUnref ⊢
      exact hTailUnref

end

/--
A scope stack for nested datatype pumping, innermost level first.  Each
entry `(s, dr, D)` records a datatype level: its name `s`, its raw body
`dr` (a subterm of the original program syntax, well-formed with respect
to the names of the outer levels plus `s`), and its closed body `D`
obtained by substituting all outer levels into `dr`.
-/
private abbrev PumpEnv := List (native_String × SmtDatatype × SmtDatatype)

private def env_refs : PumpEnv -> RefList
  | [] => native_reflist_nil
  | (s, _, _) :: E => native_reflist_insert (env_refs E) s

private def env_close_dt : PumpEnv -> SmtDatatype -> SmtDatatype
  | [], X => X
  | (s, _, D) :: E, X => __smtx_dt_substitute s D (env_close_dt E X)

private def env_close_dtc : PumpEnv -> SmtDatatypeCons -> SmtDatatypeCons
  | [], X => X
  | (s, _, D) :: E, X => __smtx_dtc_substitute s D (env_close_dtc E X)

private def env_close_ty : PumpEnv -> SmtType -> SmtType
  | [], X => X
  | (s, _, D) :: E, X => __smtx_type_substitute s D (env_close_ty E X)

private def env_ok : PumpEnv -> Prop
  | [] => True
  | (s, dr, D) :: E =>
      native_reflist_contains (env_refs E) s = false ∧
      __smtx_dt_wf_rec dr (native_reflist_insert (env_refs E) s) = true ∧
      D = env_close_dt E dr ∧
      env_ok E

private def env_pump : PumpEnv -> Prop
  | [] => True
  | (s, dr, _D) :: E =>
      native_inhabited_type (SmtType.Datatype s dr) = true ∧
      __smtx_is_finite_datatype dr = false ∧
      env_pump E

private theorem env_refs_append :
    ∀ (E1 E2 : PumpEnv),
      env_refs (E1 ++ E2) = env_refs E1 ++ env_refs E2
  | [], _E2 => rfl
  | (s, dr, D) :: E1, E2 => by
      simp [env_refs, native_reflist_insert, env_refs_append E1 E2]

private theorem env_ok_append_right :
    ∀ (E1 E2 : PumpEnv), env_ok (E1 ++ E2) -> env_ok E2
  | [], _E2, h => h
  | (_s, _dr, _D) :: E1, E2, h => env_ok_append_right E1 E2 h.2.2.2

private theorem env_pump_append_right :
    ∀ (E1 E2 : PumpEnv), env_pump (E1 ++ E2) -> env_pump E2
  | [], _E2, h => h
  | (_s, _dr, _D) :: E1, E2, h => env_pump_append_right E1 E2 h.2.2

private theorem env_mem_split :
    ∀ (E : PumpEnv) (r : native_String),
      native_reflist_contains (env_refs E) r = true ->
        ∃ (E1 : PumpEnv) (dr D : SmtDatatype) (E2 : PumpEnv),
          E = E1 ++ (r, dr, D) :: E2
  | [], r, h => by
      simp [env_refs, native_reflist_nil, native_reflist_contains] at h
  | (s, dr, D) :: E, r, h => by
      by_cases hrs : r = s
      · subst hrs
        exact ⟨[], dr, D, E, rfl⟩
      · have hE : native_reflist_contains (env_refs E) r = true := by
          simp [env_refs, native_reflist_insert,
            native_reflist_contains] at h ⊢
          rcases h with h | h
          · exact False.elim (hrs h)
          · exact h
        rcases env_mem_split E r hE with ⟨E1, dr2, D2, E2, hEq⟩
        exact ⟨(s, dr, D) :: E1, dr2, D2, E2, by simp [hEq]⟩

private theorem env_close_dt_unref_of_not_contains (t : native_String) :
    ∀ (E : PumpEnv) (X : SmtDatatype),
      env_ok E ->
        native_reflist_contains (env_refs E) t = false ->
          smt_dt_unref t X = true ->
            smt_dt_unref t (env_close_dt E X) = true
  | [], _X, _hok, _ht, hX => hX
  | (s, dr, D) :: E, X, hok, ht, hX => by
      have htParts :
          t ≠ s ∧ native_reflist_contains (env_refs E) t = false := by
        simp [env_refs, native_reflist_insert,
          native_reflist_contains] at ht ⊢
        exact ht
      have hdrUnref : smt_dt_unref t dr = true := by
        apply dt_unref_of_wf_not_contains t dr
          (native_reflist_insert (env_refs E) s)
        · simp [native_reflist_insert, native_reflist_contains]
          exact ⟨htParts.1, by
            simpa [native_reflist_contains] using htParts.2⟩
        · exact hok.2.1
      have hDUnref : smt_dt_unref t D = true := by
        rw [hok.2.2.1]
        exact env_close_dt_unref_of_not_contains t E dr
          hok.2.2.2 htParts.2 hdrUnref
      have hXUnref : smt_dt_unref t (env_close_dt E X) = true :=
        env_close_dt_unref_of_not_contains t E X
          hok.2.2.2 htParts.2 hX
      exact dt_unref_substitute_other s D t hDUnref
        (env_close_dt E X) hXUnref

private theorem env_close_dt_unref_of_contains (t : native_String) :
    ∀ (E : PumpEnv) (X : SmtDatatype),
      env_ok E ->
        native_reflist_contains (env_refs E) t = true ->
          smt_dt_unref t (env_close_dt E X) = true
  | [], _X, _hok, ht => by
      simp [env_refs, native_reflist_nil, native_reflist_contains] at ht
  | (s, dr, D) :: E, X, hok, ht => by
      by_cases hts : t = s
      · subst hts
        exact dt_unref_substitute_self _ D (env_close_dt E X)
      · have htE : native_reflist_contains (env_refs E) t = true := by
          simp [env_refs, native_reflist_insert,
            native_reflist_contains] at ht ⊢
          rcases ht with h | h
          · exact False.elim (hts h)
          · exact h
        have hDUnref : smt_dt_unref t D = true := by
          rw [hok.2.2.1]
          exact env_close_dt_unref_of_contains t E dr hok.2.2.2 htE
        have hXUnref : smt_dt_unref t (env_close_dt E X) = true :=
          env_close_dt_unref_of_contains t E X hok.2.2.2 htE
        exact dt_unref_substitute_other s D t hDUnref
          (env_close_dt E X) hXUnref

/--
Self-containedness of closed bodies: the closed body of a coherent stack
level mentions no free type reference other than the level's own name.
-/
private theorem env_closed_body_unref
    (t s : native_String) (dr D : SmtDatatype) (E : PumpEnv)
    (hok : env_ok ((s, dr, D) :: E))
    (hts : t ≠ s) :
    smt_dt_unref t D = true := by
  rw [hok.2.2.1]
  by_cases htE : native_reflist_contains (env_refs E) t = true
  · exact env_close_dt_unref_of_contains t E dr hok.2.2.2 htE
  · have htE' : native_reflist_contains (env_refs E) t = false := by
      cases h : native_reflist_contains (env_refs E) t <;>
        simp [h] at htE ⊢
    have hdrUnref : smt_dt_unref t dr = true := by
      apply dt_unref_of_wf_not_contains t dr
        (native_reflist_insert (env_refs E) s)
      · simp [native_reflist_insert, native_reflist_contains]
        exact ⟨hts, by simpa [native_reflist_contains] using htE'⟩
      · exact hok.2.1
    exact env_close_dt_unref_of_not_contains t E dr
      hok.2.2.2 htE' hdrUnref

private theorem env_close_ty_typeref_not_contains :
    ∀ (E : PumpEnv) (r : native_String),
      native_reflist_contains (env_refs E) r = false ->
        env_close_ty E (SmtType.TypeRef r) = SmtType.TypeRef r
  | [], _r, _h => rfl
  | (s, dr, D) :: E, r, h => by
      have hParts :
          r ≠ s ∧ native_reflist_contains (env_refs E) r = false := by
        simp [env_refs, native_reflist_insert,
          native_reflist_contains] at h ⊢
        exact h
      have hsr : native_streq s r = false := by
        simp [native_streq]
        intro hEq
        exact hParts.1 hEq.symm
      rw [env_close_ty, env_close_ty_typeref_not_contains E r hParts.2]
      simp [__smtx_type_substitute, native_ite, hsr]

/--
Resolution of a legal type reference through a coherent stack: the
closure of `TypeRef r` is the closed datatype of the level named `r`.
-/
private theorem env_close_ty_typeref_resolve :
    ∀ (E1 : PumpEnv) (r : native_String) (dr D : SmtDatatype) (E2 : PumpEnv),
      env_ok (E1 ++ (r, dr, D) :: E2) ->
        env_close_ty (E1 ++ (r, dr, D) :: E2) (SmtType.TypeRef r) =
          SmtType.Datatype r D
  | [], r, dr, D, E2, hok => by
      have hNotE2 : native_reflist_contains (env_refs E2) r = false :=
        hok.1
      rw [List.nil_append, env_close_ty,
        env_close_ty_typeref_not_contains E2 r hNotE2]
      simp [__smtx_type_substitute, native_ite, native_streq]
  | (s1, dr1, D1) :: E1, r, dr, D, E2, hok => by
      have hok' : env_ok (E1 ++ (r, dr, D) :: E2) := hok.2.2.2
      have hMem :
          native_reflist_contains
            (env_refs (E1 ++ (r, dr, D) :: E2)) r = true := by
        rw [env_refs_append]
        simp [env_refs, native_reflist_insert, native_reflist_contains]
      have hs1r : s1 ≠ r := by
        intro hEq
        subst hEq
        have h1 :
            native_reflist_contains
              (env_refs (E1 ++ (s1, dr, D) :: E2)) s1 = false := hok.1
        rw [h1] at hMem
        simp at hMem
      have hs1rStr : native_streq s1 r = false := by
        simp [native_streq, hs1r]
      have hRec :=
        env_close_ty_typeref_resolve E1 r dr D E2 hok'
      rw [List.cons_append, env_close_ty, hRec]
      have hDUnref : smt_dt_unref s1 D = true := by
        rcases env_mem_split (E1 ++ (r, dr, D) :: E2) r hMem with
          ⟨F1, dr2, D2, F2, hEq⟩
        -- We resolve self-containedness directly on the given entry.
        have hokEntry : env_ok ((r, dr, D) :: E2) :=
          env_ok_append_right E1 _ hok'
        exact env_closed_body_unref s1 r dr D E2 hokEntry hs1r
      simp [__smtx_type_substitute, native_ite, hs1rStr,
        dt_substitute_eq_self_of_unref s1 D1 D hDUnref]

private theorem env_close_dt_null :
    ∀ E : PumpEnv, env_close_dt E SmtDatatype.null = SmtDatatype.null
  | [] => rfl
  | (s, _, D) :: E => by
      rw [env_close_dt, env_close_dt_null E]
      rfl

private theorem env_close_dtc_unit :
    ∀ E : PumpEnv,
      env_close_dtc E SmtDatatypeCons.unit = SmtDatatypeCons.unit
  | [] => rfl
  | (s, _, D) :: E => by
      rw [env_close_dtc, env_close_dtc_unit E]
      rfl

private theorem env_close_dt_sum :
    ∀ (E : PumpEnv) (c : SmtDatatypeCons) (d : SmtDatatype),
      env_close_dt E (SmtDatatype.sum c d) =
        SmtDatatype.sum (env_close_dtc E c) (env_close_dt E d)
  | [], _c, _d => rfl
  | (s, _, D) :: E, c, d => by
      rw [env_close_dt, env_close_dt_sum E]
      rfl

private theorem env_close_dtc_cons :
    ∀ (E : PumpEnv) (T : SmtType) (c : SmtDatatypeCons),
      env_close_dtc E (SmtDatatypeCons.cons T c) =
        SmtDatatypeCons.cons (env_close_ty E T) (env_close_dtc E c)
  | [], _T, _c => rfl
  | (s, _, D) :: E, T, c => by
      rw [env_close_dtc, env_close_dtc_cons E]
      rfl

private theorem env_close_dt_append :
    ∀ (E : PumpEnv) (p q : SmtDatatype),
      env_close_dt E (dt_append p q) =
        dt_append (env_close_dt E p) (env_close_dt E q)
  | E, SmtDatatype.null, q => by
      rw [env_close_dt_null]
      rfl
  | E, SmtDatatype.sum c p, q => by
      rw [show dt_append (SmtDatatype.sum c p) q =
        SmtDatatype.sum c (dt_append p q) by rfl]
      rw [env_close_dt_sum, env_close_dt_sum, env_close_dt_append E p q]
      rfl

private theorem dt_constructor_offset_env_close :
    ∀ (E : PumpEnv) (p : SmtDatatype),
      dt_constructor_offset (env_close_dt E p) = dt_constructor_offset p
  | _E, SmtDatatype.null => by
      rw [env_close_dt_null]
  | E, SmtDatatype.sum c p => by
      rw [env_close_dt_sum]
      simp [dt_constructor_offset, dt_constructor_offset_env_close E p]

private theorem env_close_ty_eq_self_of_substitute_fix
    (T : SmtType)
    (hFix : ∀ (s : native_String) (d : SmtDatatype),
      __smtx_type_substitute s d T = T) :
    ∀ E : PumpEnv, env_close_ty E T = T
  | [] => rfl
  | (s, _, D) :: E => by
      rw [env_close_ty, env_close_ty_eq_self_of_substitute_fix T hFix E,
        hFix s D]

private theorem env_close_ty_datatype :
    ∀ (E : PumpEnv) (s2 : native_String) (d2 : SmtDatatype),
      native_reflist_contains (env_refs E) s2 = false ->
        env_close_ty E (SmtType.Datatype s2 d2) =
          SmtType.Datatype s2 (env_close_dt E d2)
  | [], _s2, _d2, _h => rfl
  | (s, dr, D) :: E, s2, d2, h => by
      have hParts :
          s2 ≠ s ∧ native_reflist_contains (env_refs E) s2 = false := by
        simp [env_refs, native_reflist_insert,
          native_reflist_contains] at h ⊢
        exact h
      have hss2 : native_streq s s2 = false := by
        simp [native_streq]
        intro hEq
        exact hParts.1 hEq.symm
      rw [env_close_ty, env_close_ty_datatype E s2 d2 hParts.2]
      simp [__smtx_type_substitute, native_ite, hss2, env_close_dt]

private theorem dtc_substitute_field_type_eq_type_substitute
    (s : native_String) (d : SmtDatatype) :
    ∀ T : SmtType,
      dtc_substitute_field_type s d T = __smtx_type_substitute s d T
  | SmtType.None => rfl
  | SmtType.Bool => rfl
  | SmtType.Int => rfl
  | SmtType.Real => rfl
  | SmtType.RegLan => rfl
  | SmtType.BitVec _ => rfl
  | SmtType.Map _ _ => rfl
  | SmtType.Set _ => rfl
  | SmtType.Seq _ => rfl
  | SmtType.Char => rfl
  | SmtType.Datatype _ _ => rfl
  | SmtType.TypeRef _ => rfl
  | SmtType.USort _ => rfl
  | SmtType.FunType _ _ => rfl
  | SmtType.DtcAppType _ _ => rfl

/-- All fields of a constructor have non-failing defaults. -/
private def dtc_fields_defaultable : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons T c =>
      __smtx_type_default T ≠ SmtValue.NotValue ∧ dtc_fields_defaultable c

private theorem cons_default_fields_defaultable
    (s0 : native_String) (d0 : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_datatype_cons_default s0 d0 v c ≠ SmtValue.NotValue ->
        dtc_fields_defaultable c
  | SmtDatatypeCons.unit, _v, _h => trivial
  | SmtDatatypeCons.cons T c, v, h => by
      by_cases h0 :
          native_veq (__smtx_value_dt_substitute s0 d0 (__smtx_type_default T))
            SmtValue.NotValue = true
      · exact False.elim (h (by
          simp [__smtx_datatype_cons_default, native_ite, h0]))
      · have h0' :
            native_veq
              (__smtx_value_dt_substitute s0 d0 (__smtx_type_default T))
              SmtValue.NotValue = false := by
          cases hv :
              native_veq
                (__smtx_value_dt_substitute s0 d0 (__smtx_type_default T))
                SmtValue.NotValue <;> simp [hv] at h0 ⊢
        have hTd : __smtx_type_default T ≠ SmtValue.NotValue := by
          intro hEq
          rw [hEq] at h0'
          simp [__smtx_value_dt_substitute, native_veq] at h0'
        have hTail :
            __smtx_datatype_cons_default s0 d0
                (SmtValue.Apply v
                  (__smtx_value_dt_substitute s0 d0 (__smtx_type_default T)))
                c ≠
              SmtValue.NotValue := by
          intro hEq
          apply h
          simpa [__smtx_datatype_cons_default, native_ite, h0'] using hEq
        exact ⟨hTd, cons_default_fields_defaultable s0 d0 c _ hTail⟩

/--
Per-field witnesses available for a (closed) constructor: every field has
a typed canonical value at its substituted field type, and the field type
is well-defined.
-/
private def cons_args_available
    (s0 : native_String) (B : SmtDatatype) : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons T c =>
      (dtc_substitute_field_type s0 B T ≠ SmtType.None ∧
        ∃ w : SmtValue,
          __smtx_typeof_value w = dtc_substitute_field_type s0 B T ∧
            __smtx_value_canonical_bool w = true) ∧
      cons_args_available s0 B c

/--
Build a value of a datatype by applying the remaining fields of a
(closed) constructor to a partial application `v`, given typed canonical
witnesses for every field.
-/
private theorem cons_apply_complete
    (s0 : native_String) (B : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (v : SmtValue),
      __smtx_typeof_value v =
          dtc_type_chain s0 B c (SmtType.Datatype s0 B) ->
        __smtx_value_canonical_bool v = true ->
          cons_args_available s0 B c ->
            ∃ e : SmtValue,
              __smtx_typeof_value e = SmtType.Datatype s0 B ∧
                __smtx_value_canonical_bool e = true ∧
                  sizeOf v ≤ sizeOf e
  | SmtDatatypeCons.unit, v, hvTy, hvCan, _hArgs =>
      ⟨v, by simpa [dtc_type_chain] using hvTy, hvCan, Nat.le_refl _⟩
  | SmtDatatypeCons.cons T c, v, hvTy, hvCan, hArgs => by
      obtain ⟨⟨hTNe, w, hwTy, hwCan⟩, hRest⟩ := hArgs
      have hvTy' :
          __smtx_typeof_value v =
            SmtType.DtcAppType (dtc_substitute_field_type s0 B T)
              (dtc_type_chain s0 B c (SmtType.Datatype s0 B)) := by
        simpa [dtc_type_chain] using hvTy
      have hApplyTy :
          __smtx_typeof_value (SmtValue.Apply v w) =
            dtc_type_chain s0 B c (SmtType.Datatype s0 B) := by
        change
          __smtx_typeof_apply_value
              (__smtx_typeof_value v) (__smtx_typeof_value w) =
            dtc_type_chain s0 B c (SmtType.Datatype s0 B)
        rw [hvTy', hwTy]
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
          native_Teq, native_ite, hTNe]
      have hApplyCan :
          __smtx_value_canonical_bool (SmtValue.Apply v w) = true := by
        simp [__smtx_value_canonical_bool, native_and, hvCan, hwCan]
      rcases cons_apply_complete s0 B c (SmtValue.Apply v w)
          hApplyTy hApplyCan hRest with ⟨e, heTy, heCan, heSize⟩
      refine ⟨e, heTy, heCan, ?_⟩
      have hStep : sizeOf v < sizeOf (SmtValue.Apply v w) :=
        sizeOf_lt_apply_left v w
      omega

private theorem env_close_ty_ne_none :
    ∀ (T : SmtType) (E : PumpEnv),
      __smtx_type_wf_rec T (env_refs E) = true ->
        env_close_ty E T ≠ SmtType.None
  | SmtType.None, _E, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.TypeRef _r, _E, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.RegLan, _E, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.FunType _ _, _E, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType _ _, _E, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Datatype s2 d2, E, hWf => by
      have hNot : native_reflist_contains (env_refs E) s2 = false := by
        cases h : native_reflist_contains (env_refs E) s2 <;>
          simp [__smtx_type_wf_rec, native_ite, h] at hWf ⊢
      rw [env_close_ty_datatype E s2 d2 hNot]
      intro h
      cases h
  | SmtType.Bool, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h
  | SmtType.Int, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h
  | SmtType.Real, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h
  | SmtType.BitVec _, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h
  | SmtType.Map _ _, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h
  | SmtType.Set _, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h
  | SmtType.Seq _, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h
  | SmtType.Char, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h
  | SmtType.USort _, E, _hWf => by
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      intro h; cases h

private theorem dt_constructor_offset_append :
    ∀ (p q : SmtDatatype),
      dt_constructor_offset (dt_append p q) =
        dt_constructor_offset p + dt_constructor_offset q
  | SmtDatatype.null, q => by
      simp [dt_append, dt_constructor_offset]
  | SmtDatatype.sum c p, q => by
      simp [dt_append, dt_constructor_offset,
        dt_constructor_offset_append p q]
      omega

private def smt_seq_repeat (T : SmtType) (x : SmtValue) : Nat -> SmtSeq
  | 0 => SmtSeq.empty T
  | Nat.succ n => SmtSeq.cons x (smt_seq_repeat T x n)

private theorem smt_seq_repeat_typeof
    (T : SmtType) (x : SmtValue) (hx : __smtx_typeof_value x = T) :
    ∀ n : Nat,
      __smtx_typeof_seq_value (smt_seq_repeat T x n) = SmtType.Seq T
  | 0 => by
      simp [smt_seq_repeat, __smtx_typeof_seq_value]
  | Nat.succ n => by
      simp [smt_seq_repeat, __smtx_typeof_seq_value,
        smt_seq_repeat_typeof T x hx n, hx, native_ite, native_Teq]

private theorem smt_seq_repeat_canonical
    (T : SmtType) (x : SmtValue) (hx : __smtx_value_canonical_bool x = true) :
    ∀ n : Nat,
      __smtx_seq_canonical (smt_seq_repeat T x n) = true
  | 0 => by
      simp [smt_seq_repeat, __smtx_seq_canonical]
  | Nat.succ n => by
      simp [smt_seq_repeat, __smtx_seq_canonical, native_and, hx,
        smt_seq_repeat_canonical T x hx n]

private theorem smt_seq_repeat_size_ge
    (T : SmtType) (x : SmtValue) :
    ∀ n : Nat, n ≤ sizeOf (smt_seq_repeat T x n)
  | 0 => Nat.zero_le _
  | Nat.succ n => by
      have hRec := smt_seq_repeat_size_ge T x n
      rw [show smt_seq_repeat T x (Nat.succ n) =
        SmtSeq.cons x (smt_seq_repeat T x n) by rfl]
      rw [show sizeOf (SmtSeq.cons x (smt_seq_repeat T x n)) =
        1 + sizeOf x + sizeOf (smt_seq_repeat T x n) by rfl]
      omega

/--
A sequence type over any inhabited element type has typed canonical values of
arbitrarily large size: repeat the default element.
-/
private theorem seq_inhabited_large_witness
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Seq T ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  have hDef := type_default_typed_canonical_of_native_inhabited hInh
  refine
    ⟨SmtValue.Seq (smt_seq_repeat T (__smtx_type_default T) minSize),
      ?_, ?_, ?_⟩
  · simpa [__smtx_typeof_value] using
      smt_seq_repeat_typeof T (__smtx_type_default T) hDef.1 minSize
  · simpa [__smtx_value_canonical_bool] using
      smt_seq_repeat_canonical T (__smtx_type_default T) hDef.2 minSize
  · rw [show
      sizeOf
          (SmtValue.Seq (smt_seq_repeat T (__smtx_type_default T) minSize)) =
        1 + sizeOf (smt_seq_repeat T (__smtx_type_default T) minSize) by rfl]
    have := smt_seq_repeat_size_ge T (__smtx_type_default T) minSize
    omega

private theorem datatype_default_step_fail
    (s0 : native_String) (d0 : SmtDatatype) (c : SmtDatatypeCons)
    (d : SmtDatatype) (n : Nat)
    (hFail :
      __smtx_datatype_cons_default s0 d0 (SmtValue.DtCons s0 d0 n) c =
        SmtValue.NotValue) :
    __smtx_datatype_default s0 d0 (SmtDatatype.sum c d) n =
      __smtx_datatype_default s0 d0 d (Nat.succ n) := by
  simp [__smtx_datatype_default, native_ite, native_not, native_veq, hFail]

private theorem inhabit_field_fix
    (T : SmtType) (E : PumpEnv)
    (hFix : ∀ (s : native_String) (d : SmtDatatype),
      __smtx_type_substitute s d T = T)
    (hInh : native_inhabited_type T = true) :
    ∃ w : SmtValue,
      __smtx_typeof_value w = env_close_ty E T ∧
        __smtx_value_canonical_bool w = true := by
  have hDef := type_default_typed_canonical_of_native_inhabited hInh
  rw [env_close_ty_eq_self_of_substitute_fix T hFix E]
  exact ⟨__smtx_type_default T, hDef.1, hDef.2⟩

private theorem dt_cons_wf_head_parts_of_defaultable
    {T : SmtType} {c : SmtDatatypeCons} {refs : RefList}
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hDef : __smtx_type_default T ≠ SmtValue.NotValue) :
    native_inhabited_type T = true ∧
      __smtx_type_wf_rec T refs = true ∧
        __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;>
    first
      | (exfalso; apply hDef; simp [__smtx_type_default]; done)
      | simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf

mutual

/--
Construct a typed canonical inhabitant of the closure of an inhabited
well-formed raw field type.
-/
private theorem inhabit_field :
    ∀ (T : SmtType) (E : PumpEnv),
      env_ok E ->
        __smtx_type_wf_rec T (env_refs E) = true ->
          native_inhabited_type T = true ->
            ∃ w : SmtValue,
              __smtx_typeof_value w = env_close_ty E T ∧
                __smtx_value_canonical_bool w = true
  | SmtType.Datatype s2 d2, E, hok, hWf, hInh => by
      have hNot : native_reflist_contains (env_refs E) s2 = false := by
        cases h : native_reflist_contains (env_refs E) s2 <;>
          simp [__smtx_type_wf_rec, native_ite, h] at hWf ⊢
      have hDtWf :
          __smtx_dt_wf_rec d2 (native_reflist_insert (env_refs E) s2) =
            true := by
        simpa [__smtx_type_wf_rec, native_ite, hNot] using hWf
      have hok' : env_ok ((s2, d2, env_close_dt E d2) :: E) :=
        ⟨hNot, hDtWf, rfl, hok⟩
      have hDefNe :
          __smtx_type_default (SmtType.Datatype s2 d2) ≠
            SmtValue.NotValue :=
        type_default_ne_notValue_of_native_inhabited hInh
          (by intro h; cases h)
      have hDefNe' :
          __smtx_datatype_default s2 d2 d2 0 ≠ SmtValue.NotValue := by
        simpa [__smtx_type_default] using hDefNe
      rcases inhabit_dt d2 s2 d2 SmtDatatype.null E 0 hok'
          rfl rfl hDtWf hDefNe' with ⟨w, hwTy, hwCan⟩
      refine ⟨w, ?_, hwCan⟩
      rw [env_close_ty_datatype E s2 d2 hNot]
      exact hwTy
  | SmtType.None, _E, _hok, hWf, _hInh => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.TypeRef _r, _E, _hok, hWf, _hInh => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.RegLan, _E, _hok, hWf, _hInh => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.FunType _ _, _E, _hok, hWf, _hInh => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType _ _, _E, _hok, hWf, _hInh => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Bool, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
  | SmtType.Int, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
  | SmtType.Real, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
  | SmtType.BitVec _, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
  | SmtType.Map _ _, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
  | SmtType.Set _, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
  | SmtType.Seq _, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
  | SmtType.Char, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
  | SmtType.USort _, E, _hok, _hWf, hInh =>
      inhabit_field_fix _ E (by intro s d; simp [__smtx_type_substitute]) hInh
termination_by T _ _ _ _ => sizeOf T
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

/--
Walk the constructor list of a raw datatype level looking for the first
constructor whose default computation succeeds, and build an inhabitant
of the closed datatype from it.
-/
private theorem inhabit_dt :
    ∀ (dsuf : SmtDatatype) (s2 : native_String) (d2 : SmtDatatype)
      (pre : SmtDatatype) (E : PumpEnv) (n : Nat),
      env_ok ((s2, d2, env_close_dt E d2) :: E) ->
        d2 = dt_append pre dsuf ->
          n = dt_constructor_offset pre ->
            __smtx_dt_wf_rec dsuf
                (env_refs ((s2, d2, env_close_dt E d2) :: E)) = true ->
              __smtx_datatype_default s2 d2 dsuf n ≠ SmtValue.NotValue ->
                ∃ w : SmtValue,
                  __smtx_typeof_value w =
                      SmtType.Datatype s2 (env_close_dt E d2) ∧
                    __smtx_value_canonical_bool w = true
  | SmtDatatype.null, _s2, _d2, _pre, _E, _n, _hok, _hSplit, _hOff,
      hWf, _hNe => by
      simp [__smtx_dt_wf_rec] at hWf
  | SmtDatatype.sum c SmtDatatype.null, s2, d2, pre, E, n, hok, hSplit,
      hOff, hWf, hNe => by
      have hConsWf :
          __smtx_dt_cons_wf_rec c
              (env_refs ((s2, d2, env_close_dt E d2) :: E)) = true :=
        dt_wf_cons_of_wf hWf
      have hSucc :
          ¬ __smtx_datatype_cons_default s2 d2 (SmtValue.DtCons s2 d2 n) c =
            SmtValue.NotValue := by
        intro hFail
        apply hNe
        rw [datatype_default_step_fail s2 d2 c SmtDatatype.null n hFail]
        simp [__smtx_datatype_default]
      have hFields : dtc_fields_defaultable c :=
        cons_default_fields_defaultable s2 d2 c _ hSucc
      have hArgs :
          cons_args_available s2 (env_close_dt E d2)
            (env_close_dtc E c) :=
        inhabit_cons_args c s2 d2 E hok hConsWf hFields
      have hRoot :
          env_close_dt E d2 =
            dt_append (env_close_dt E pre)
              (SmtDatatype.sum (env_close_dtc E c)
                (env_close_dt E SmtDatatype.null)) := by
        have h := congrArg (env_close_dt E) hSplit
        rw [env_close_dt_append, env_close_dt_sum] at h
        exact h
      have hOffC : n = dt_constructor_offset (env_close_dt E pre) := by
        rw [dt_constructor_offset_env_close]
        exact hOff
      have hHeadTy :
          __smtx_typeof_value
              (SmtValue.DtCons s2 (env_close_dt E d2) n) =
            dtc_type_chain s2 (env_close_dt E d2) (env_close_dtc E c)
              (SmtType.Datatype s2 (env_close_dt E d2)) := by
        rw [hOffC]
        exact typeof_dt_cons_append_offset_eq_dtc_type_chain
          s2 (env_close_dt E d2) (env_close_dt E pre)
          (env_close_dtc E c) (env_close_dt E SmtDatatype.null) hRoot
      rcases cons_apply_complete s2 (env_close_dt E d2)
          (env_close_dtc E c)
          (SmtValue.DtCons s2 (env_close_dt E d2) n)
          hHeadTy (by simp [__smtx_value_canonical_bool]) hArgs with
        ⟨e, heTy, heCan, _heSize⟩
      exact ⟨e, heTy, heCan⟩
  | SmtDatatype.sum c (SmtDatatype.sum c2 t2), s2, d2, pre, E, n, hok,
      hSplit, hOff, hWf, hNe => by
      have hConsWf :
          __smtx_dt_cons_wf_rec c
              (env_refs ((s2, d2, env_close_dt E d2) :: E)) = true :=
        dt_wf_cons_of_wf hWf
      by_cases hSucc :
          __smtx_datatype_cons_default s2 d2 (SmtValue.DtCons s2 d2 n) c =
            SmtValue.NotValue
      · have hNe' :
            __smtx_datatype_default s2 d2 (SmtDatatype.sum c2 t2)
                (Nat.succ n) ≠
              SmtValue.NotValue := by
          rw [<- datatype_default_step_fail s2 d2 c
            (SmtDatatype.sum c2 t2) n hSucc]
          exact hNe
        have hTailWf :
            __smtx_dt_wf_rec (SmtDatatype.sum c2 t2)
                (env_refs ((s2, d2, env_close_dt E d2) :: E)) = true :=
          dt_wf_tail_of_nonempty_tail_wf hWf
        have hSplit' :
            d2 =
              dt_append
                (dt_append pre (SmtDatatype.sum c SmtDatatype.null))
                (SmtDatatype.sum c2 t2) := by
          rw [dt_append_singleton_tail pre c (SmtDatatype.sum c2 t2)]
          exact hSplit
        have hOff' :
            Nat.succ n =
              dt_constructor_offset
                (dt_append pre (SmtDatatype.sum c SmtDatatype.null)) := by
          rw [dt_constructor_offset_append]
          simp [dt_constructor_offset]
          omega
        exact inhabit_dt (SmtDatatype.sum c2 t2) s2 d2
          (dt_append pre (SmtDatatype.sum c SmtDatatype.null)) E
          (Nat.succ n) hok hSplit' hOff' hTailWf hNe'
      · have hFields : dtc_fields_defaultable c :=
          cons_default_fields_defaultable s2 d2 c _ hSucc
        have hArgs :
            cons_args_available s2 (env_close_dt E d2)
              (env_close_dtc E c) :=
          inhabit_cons_args c s2 d2 E hok hConsWf hFields
        have hRoot :
            env_close_dt E d2 =
              dt_append (env_close_dt E pre)
                (SmtDatatype.sum (env_close_dtc E c)
                  (env_close_dt E (SmtDatatype.sum c2 t2))) := by
          have h := congrArg (env_close_dt E) hSplit
          rw [env_close_dt_append, env_close_dt_sum] at h
          exact h
        have hOffC : n = dt_constructor_offset (env_close_dt E pre) := by
          rw [dt_constructor_offset_env_close]
          exact hOff
        have hHeadTy :
            __smtx_typeof_value
                (SmtValue.DtCons s2 (env_close_dt E d2) n) =
              dtc_type_chain s2 (env_close_dt E d2) (env_close_dtc E c)
                (SmtType.Datatype s2 (env_close_dt E d2)) := by
          rw [hOffC]
          exact typeof_dt_cons_append_offset_eq_dtc_type_chain
            s2 (env_close_dt E d2) (env_close_dt E pre)
            (env_close_dtc E c) (env_close_dt E (SmtDatatype.sum c2 t2))
            hRoot
        rcases cons_apply_complete s2 (env_close_dt E d2)
            (env_close_dtc E c)
            (SmtValue.DtCons s2 (env_close_dt E d2) n)
            hHeadTy (by simp [__smtx_value_canonical_bool]) hArgs with
          ⟨e, heTy, heCan, _heSize⟩
        exact ⟨e, heTy, heCan⟩
termination_by dsuf _ _ _ _ _ _ _ _ _ _ => sizeOf dsuf
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

/--
Provide typed canonical witnesses for every field of a constructor whose
defaults all succeed.
-/
private theorem inhabit_cons_args :
    ∀ (c : SmtDatatypeCons) (s2 : native_String) (d2 : SmtDatatype)
      (E : PumpEnv),
      env_ok ((s2, d2, env_close_dt E d2) :: E) ->
        __smtx_dt_cons_wf_rec c
            (env_refs ((s2, d2, env_close_dt E d2) :: E)) = true ->
          dtc_fields_defaultable c ->
            cons_args_available s2 (env_close_dt E d2) (env_close_dtc E c)
  | SmtDatatypeCons.unit, s2, d2, E, _hok, _hWf, _hFields => by
      rw [env_close_dtc_unit]
      trivial
  | SmtDatatypeCons.cons T c, s2, d2, E, hok, hWf, hFields => by
      have hParts := dt_cons_wf_head_parts_of_defaultable hWf hFields.1
      have hTailArgs :
          cons_args_available s2 (env_close_dt E d2)
            (env_close_dtc E c) :=
        inhabit_cons_args c s2 d2 E hok hParts.2.2 hFields.2
      rcases inhabit_field T ((s2, d2, env_close_dt E d2) :: E) hok
          hParts.2.1 hParts.1 with ⟨w, hwTy, hwCan⟩
      have hNe :
          env_close_ty ((s2, d2, env_close_dt E d2) :: E) T ≠
            SmtType.None :=
        env_close_ty_ne_none T ((s2, d2, env_close_dt E d2) :: E)
          hParts.2.1
      rw [env_close_dtc_cons]
      refine ⟨⟨?_, w, ?_, hwCan⟩, hTailArgs⟩
      · rw [dtc_substitute_field_type_eq_type_substitute]
        exact hNe
      · rw [dtc_substitute_field_type_eq_type_substitute]
        exact hwTy
termination_by c _ _ _ _ _ _ => sizeOf c
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

end

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
      refine ⟨SmtValue.Char 1, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_char_valid, native_ite, native_veq]
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

private theorem env_close_ty_cons_step
    (s : native_String) (dr D : SmtDatatype) (E : PumpEnv) (T : SmtType) :
    env_close_ty ((s, dr, D) :: E) T =
      __smtx_type_substitute s D (env_close_ty E T) := rfl

private theorem dt_cons_wf_head_parts_of_not_typeref
    {T : SmtType} {c : SmtDatatypeCons} {refs : RefList}
    (hWf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hNotRef : ∀ r, T ≠ SmtType.TypeRef r) :
    native_inhabited_type T = true ∧
      __smtx_type_wf_rec T refs = true ∧
        __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;>
    first
      | (exfalso; exact hNotRef _ rfl)
      | simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf

private theorem dt_cons_wf_typeref_parts
    {r : native_String} {c : SmtDatatypeCons} {refs : RefList}
    (hWf :
      __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons (SmtType.TypeRef r) c)
        refs = true) :
    native_reflist_contains refs r = true ∧
      __smtx_dt_cons_wf_rec c refs = true := by
  cases hr : native_reflist_contains refs r <;>
    simp [__smtx_dt_cons_wf_rec, native_ite, hr] at hWf ⊢
  exact hWf

/--
The pumping oracle at size `n`: every coherent all-infinite stack level
has a typed canonical value of size at least `n`.
-/
private def PumpOracle (n : Nat) : Prop :=
  ∀ (s : native_String) (dr D : SmtDatatype) (E : PumpEnv),
    env_ok ((s, dr, D) :: E) ->
      env_pump ((s, dr, D) :: E) ->
        ∃ v : SmtValue,
          __smtx_typeof_value v = SmtType.Datatype s D ∧
            __smtx_value_canonical_bool v = true ∧
              n ≤ sizeOf v

/--
Provide typed canonical witnesses for every field of a well-formed
constructor: type references are filled from the oracle, all other
fields by constructed inhabitants.
-/
private theorem pump_cons_args (n : Nat) (oracle : PumpOracle n) :
    ∀ (c : SmtDatatypeCons) (s : native_String) (dr : SmtDatatype)
      (E : PumpEnv),
      env_ok ((s, dr, env_close_dt E dr) :: E) ->
        env_pump ((s, dr, env_close_dt E dr) :: E) ->
          __smtx_dt_cons_wf_rec c
              (env_refs ((s, dr, env_close_dt E dr) :: E)) = true ->
            cons_args_available s (env_close_dt E dr) (env_close_dtc E c)
  | SmtDatatypeCons.unit, _s, _dr, _E, _hok, _hpump, _hWf => by
      rw [env_close_dtc_unit]
      trivial
  | SmtDatatypeCons.cons T c, s, dr, E, hok, hpump, hWf => by
      cases T
      case TypeRef r =>
          have hParts := dt_cons_wf_typeref_parts hWf
          have hTailArgs :=
            pump_cons_args n oracle c s dr E hok hpump hParts.2
          rcases env_mem_split ((s, dr, env_close_dt E dr) :: E) r
              hParts.1 with ⟨E1, drr, Dr, E2, hEq⟩
          have hokSuf : env_ok ((r, drr, Dr) :: E2) := by
            rw [hEq] at hok
            exact env_ok_append_right E1 _ hok
          have hpumpSuf : env_pump ((r, drr, Dr) :: E2) := by
            rw [hEq] at hpump
            exact env_pump_append_right E1 _ hpump
          rcases oracle r drr Dr E2 hokSuf hpumpSuf with
            ⟨w, hwTy, hwCan, _hwSize⟩
          have hResolve :
              env_close_ty ((s, dr, env_close_dt E dr) :: E)
                  (SmtType.TypeRef r) =
                SmtType.Datatype r Dr := by
            rw [hEq] at hok ⊢
            exact env_close_ty_typeref_resolve E1 r drr Dr E2 hok
          rw [env_close_dtc_cons]
          refine ⟨⟨?_, w, ?_, hwCan⟩, hTailArgs⟩
          · rw [dtc_substitute_field_type_eq_type_substitute,
              <- env_close_ty_cons_step, hResolve]
            intro h
            cases h
          · rw [dtc_substitute_field_type_eq_type_substitute,
              <- env_close_ty_cons_step, hResolve]
            exact hwTy
      all_goals (
        first
        | (have hParts := dt_cons_wf_head_parts_of_not_typeref hWf
            (by intro r h; cases h)
           have hTailArgs :=
             pump_cons_args n oracle c s dr E hok hpump hParts.2.2
           rcases inhabit_field _ ((s, dr, env_close_dt E dr) :: E) hok
               hParts.2.1 hParts.1 with ⟨w, hwTy, hwCan⟩
           have hNe :=
             env_close_ty_ne_none _ ((s, dr, env_close_dt E dr) :: E)
               hParts.2.1
           rw [env_close_dtc_cons]
           refine ⟨⟨?_, w, ?_, hwCan⟩, hTailArgs⟩
           · rw [dtc_substitute_field_type_eq_type_substitute,
               <- env_close_ty_cons_step]
             exact hNe
           · rw [dtc_substitute_field_type_eq_type_substitute,
               <- env_close_ty_cons_step]
             exact hwTy))

private def smt_type_is_typeref : SmtType -> Bool
  | SmtType.TypeRef _ => true
  | _ => false

private theorem smt_type_is_typeref_spec :
    ∀ T : SmtType,
      smt_type_is_typeref T = true -> ∃ r, T = SmtType.TypeRef r
  | SmtType.TypeRef r, _ => ⟨r, rfl⟩
  | SmtType.None, h => by simp [smt_type_is_typeref] at h
  | SmtType.Bool, h => by simp [smt_type_is_typeref] at h
  | SmtType.Int, h => by simp [smt_type_is_typeref] at h
  | SmtType.Real, h => by simp [smt_type_is_typeref] at h
  | SmtType.RegLan, h => by simp [smt_type_is_typeref] at h
  | SmtType.BitVec _, h => by simp [smt_type_is_typeref] at h
  | SmtType.Map _ _, h => by simp [smt_type_is_typeref] at h
  | SmtType.Set _, h => by simp [smt_type_is_typeref] at h
  | SmtType.Seq _, h => by simp [smt_type_is_typeref] at h
  | SmtType.Char, h => by simp [smt_type_is_typeref] at h
  | SmtType.Datatype _ _, h => by simp [smt_type_is_typeref] at h
  | SmtType.USort _, h => by simp [smt_type_is_typeref] at h
  | SmtType.FunType _ _, h => by simp [smt_type_is_typeref] at h
  | SmtType.DtcAppType _ _, h => by simp [smt_type_is_typeref] at h

/--
Grow at a non-type-reference infinite path field (with the grown field
value supplied) and complete the constructor.
-/
private theorem pump_cons_path_field (n : Nat) (oracle : PumpOracle n)
    (T : SmtType) (c : SmtDatatypeCons) (s : native_String)
    (dr : SmtDatatype) (E : PumpEnv) (v : SmtValue)
    (hok : env_ok ((s, dr, env_close_dt E dr) :: E))
    (hpump : env_pump ((s, dr, env_close_dt E dr) :: E))
    (hWf :
      __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c)
        (env_refs ((s, dr, env_close_dt E dr) :: E)) = true)
    (hvTy :
      __smtx_typeof_value v =
        dtc_type_chain s (env_close_dt E dr)
          (env_close_dtc E (SmtDatatypeCons.cons T c))
          (SmtType.Datatype s (env_close_dt E dr)))
    (hvCan : __smtx_value_canonical_bool v = true)
    (hNotRef : ∀ r, T ≠ SmtType.TypeRef r)
    (w : SmtValue)
    (hwTy :
      __smtx_typeof_value w =
        env_close_ty ((s, dr, env_close_dt E dr) :: E) T)
    (hwCan : __smtx_value_canonical_bool w = true)
    (hwSize : n + 1 ≤ sizeOf w) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = SmtType.Datatype s (env_close_dt E dr) ∧
        __smtx_value_canonical_bool e = true ∧
          n + 1 ≤ sizeOf e := by
  have hParts := dt_cons_wf_head_parts_of_not_typeref hWf hNotRef
  have hNe :=
    env_close_ty_ne_none T ((s, dr, env_close_dt E dr) :: E) hParts.2.1
  have hvTy' :
      __smtx_typeof_value v =
        SmtType.DtcAppType
          (env_close_ty ((s, dr, env_close_dt E dr) :: E) T)
          (dtc_type_chain s (env_close_dt E dr) (env_close_dtc E c)
            (SmtType.Datatype s (env_close_dt E dr))) := by
    rw [env_close_dtc_cons] at hvTy
    rw [env_close_ty_cons_step,
      <- dtc_substitute_field_type_eq_type_substitute]
    simpa [dtc_type_chain] using hvTy
  have hApplyTy :
      __smtx_typeof_value (SmtValue.Apply v w) =
        dtc_type_chain s (env_close_dt E dr) (env_close_dtc E c)
          (SmtType.Datatype s (env_close_dt E dr)) := by
    change
      __smtx_typeof_apply_value
          (__smtx_typeof_value v) (__smtx_typeof_value w) = _
    rw [hvTy', hwTy]
    simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_Teq,
      native_ite, hNe]
  have hApplyCan :
      __smtx_value_canonical_bool (SmtValue.Apply v w) = true := by
    simp [__smtx_value_canonical_bool, native_and, hvCan, hwCan]
  have hArgs := pump_cons_args n oracle c s dr E hok hpump hParts.2.2
  rcases cons_apply_complete s (env_close_dt E dr) (env_close_dtc E c)
      (SmtValue.Apply v w) hApplyTy hApplyCan hArgs with ⟨e, h1, h2, h3⟩
  refine ⟨e, h1, h2, ?_⟩
  have hStep : sizeOf w < sizeOf (SmtValue.Apply v w) :=
    sizeOf_lt_apply_right v w
  omega

mutual

/--
Produce a typed canonical value of the closure of an infinite raw field
type, of size at least `n + 1`.
-/
private theorem pump_field (n : Nat) (oracle : PumpOracle n) :
    ∀ (T : SmtType) (E : PumpEnv),
      env_ok E ->
        env_pump E ->
          __smtx_type_wf_rec T (env_refs E) = true ->
            native_inhabited_type T = true ->
              __smtx_is_finite_type T = false ->
                ∃ w : SmtValue,
                  __smtx_typeof_value w = env_close_ty E T ∧
                    __smtx_value_canonical_bool w = true ∧
                      n + 1 ≤ sizeOf w
  | SmtType.Int, E, _hok, _hpump, _hWf, _hInh, _hFin => by
      rcases int_large_witness (n + 1) with ⟨w, h1, h2, h3⟩
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      exact ⟨w, h1, h2, h3⟩
  | SmtType.Real, E, _hok, _hpump, _hWf, _hInh, _hFin => by
      rcases real_large_witness (n + 1) with ⟨w, h1, h2, h3⟩
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      exact ⟨w, h1, h2, h3⟩
  | SmtType.USort u, E, _hok, _hpump, _hWf, _hInh, _hFin => by
      rcases usort_large_witness u (n + 1) with ⟨w, h1, h2, h3⟩
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      exact ⟨w, h1, h2, h3⟩
  | SmtType.Seq X, E, _hok, _hpump, hWf, _hInh, _hFin => by
      have hParts :
          native_inhabited_type X = true ∧
            __smtx_type_wf_rec X native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      rcases seq_inhabited_large_witness X hParts.1 (n + 1) with
        ⟨w, h1, h2, h3⟩
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      exact ⟨w, h1, h2, h3⟩
  | SmtType.Set X, E, _hok, _hpump, hWf, _hInh, hFin => by
      have hParts :
          native_inhabited_type X = true ∧
            __smtx_type_wf_rec X native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      have hXInf : __smtx_is_finite_type X = false := by
        simpa [__smtx_is_finite_type] using hFin
      rcases pump_field n oracle X [] trivial trivial hParts.2
          hParts.1 hXInf with ⟨x, hxTy0, hxCan, hxSize⟩
      have hxTy : __smtx_typeof_value x = X := hxTy0
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      refine
        ⟨SmtValue.Set
          (SmtMap.cons x (SmtValue.Boolean true)
            (SmtMap.default X (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hxTy, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hxCan, hXInf, native_and, native_ite,
          native_not, native_veq]
      · rw [show
          sizeOf
              (SmtValue.Set
                (SmtMap.cons x (SmtValue.Boolean true)
                  (SmtMap.default X (SmtValue.Boolean false)))) =
            1 + (1 + sizeOf x + sizeOf (SmtValue.Boolean true) +
              sizeOf (SmtMap.default X (SmtValue.Boolean false))) by rfl]
        omega
  | SmtType.Map K V, E, _hok, _hpump, hWf, hInh, hFin => by
      have hParts :
          native_inhabited_type K = true ∧
            __smtx_type_wf_rec K native_reflist_nil = true ∧
              native_inhabited_type V = true ∧
                __smtx_type_wf_rec V native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      have hUnitV : __smtx_is_unit_type V = false := by
        cases h : __smtx_is_unit_type V
        · rfl
        · simp [__smtx_is_finite_type, native_or, native_and, h] at hFin
      have hKDefault :=
        type_default_typed_canonical_of_native_inhabited hParts.1
      have hVDefault :=
        type_default_typed_canonical_of_native_inhabited hParts.2.2.1
      rw [env_close_ty_eq_self_of_substitute_fix _
        (by intro s d; simp [__smtx_type_substitute]) E]
      by_cases hVFin : __smtx_is_finite_type V = true
      · have hKInf : __smtx_is_finite_type K = false := by
          cases h : __smtx_is_finite_type K
          · rfl
          · simp [__smtx_is_finite_type, native_or, native_and, h, hVFin,
              hUnitV] at hFin
        rcases pump_field n oracle K [] trivial trivial hParts.2.1
            hParts.1 hKInf with ⟨k, hkTy0, hkCan, hkSize⟩
        have hkTy : __smtx_typeof_value k = K := hkTy0
        rcases finite_nonunit_type_nondefault_value V native_reflist_nil
            hParts.2.2.1 hParts.2.2.2 hVFin hUnitV with
          ⟨val, hValTy, hValCan, hValNeDef⟩
        have hValNeProp : val ≠ __smtx_type_default V := by
          intro hEq
          subst hEq
          simp [native_veq] at hValNeDef
        refine
          ⟨SmtValue.Map
            (SmtMap.cons k val
              (SmtMap.default K (__smtx_type_default V))), ?_, ?_, ?_⟩
        · simp [__smtx_typeof_value, __smtx_typeof_map_value,
            hkTy, hValTy, hVDefault.1, native_ite, native_Teq]
        · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
            __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
            __smtx_msm_get_default, hkCan, hValCan, hVDefault.2, hKInf,
            hValNeProp, native_and, native_ite, native_not, native_veq]
        · rw [show
            sizeOf
                (SmtValue.Map
                  (SmtMap.cons k val
                    (SmtMap.default K (__smtx_type_default V)))) =
              1 + (1 + sizeOf k + sizeOf val +
                sizeOf (SmtMap.default K (__smtx_type_default V))) by rfl]
          omega
      · have hVInf : __smtx_is_finite_type V = false := by
          cases h : __smtx_is_finite_type V <;> simp [h] at hVFin ⊢
        rcases pump_field n oracle V [] trivial trivial hParts.2.2.2
            hParts.2.2.1 hVInf with ⟨w, hwTy0, hwCan, hwSize⟩
        have hwTy : __smtx_typeof_value w = V := hwTy0
        by_cases hwDef : w = __smtx_type_default V
        · have hDef := type_default_typed_canonical_of_native_inhabited hInh
          refine ⟨__smtx_type_default (SmtType.Map K V), hDef.1, hDef.2, ?_⟩
          rw [show
            __smtx_type_default (SmtType.Map K V) =
              SmtValue.Map (SmtMap.default K (__smtx_type_default V)) by
            simp [__smtx_type_default]]
          rw [show
            sizeOf
                (SmtValue.Map (SmtMap.default K (__smtx_type_default V))) =
              1 + (1 + sizeOf K + sizeOf (__smtx_type_default V)) by rfl]
          rw [<- hwDef]
          omega
        · refine
            ⟨SmtValue.Map
              (SmtMap.cons (__smtx_type_default K) w
                (SmtMap.default K (__smtx_type_default V))), ?_, ?_, ?_⟩
          · simp [__smtx_typeof_value, __smtx_typeof_map_value,
              hKDefault.1, hwTy, hVDefault.1, native_ite, native_Teq]
          · by_cases hKFin : __smtx_is_finite_type K = true
            · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
                __smtx_map_default_canonical,
                __smtx_map_entries_ordered_after, __smtx_msm_get_default,
                hKDefault.2, hwCan, hVDefault.1, hVDefault.2, hKFin,
                hwDef, native_and, native_ite, native_not, native_veq]
            · have hKInf : __smtx_is_finite_type K = false := by
                cases h : __smtx_is_finite_type K <;> simp [h] at hKFin ⊢
              simp [__smtx_value_canonical_bool, __smtx_map_canonical,
                __smtx_map_default_canonical,
                __smtx_map_entries_ordered_after, __smtx_msm_get_default,
                hKDefault.2, hwCan, hVDefault.2, hKInf, hwDef,
                native_and, native_ite, native_not, native_veq]
          · rw [show
              sizeOf
                  (SmtValue.Map
                    (SmtMap.cons (__smtx_type_default K) w
                      (SmtMap.default K (__smtx_type_default V)))) =
                1 + (1 + sizeOf (__smtx_type_default K) + sizeOf w +
                  sizeOf (SmtMap.default K (__smtx_type_default V))) by rfl]
            omega
  | SmtType.Datatype s2 d2, E, hok, hpump, hWf, hInh, hFin => by
      have hNot : native_reflist_contains (env_refs E) s2 = false := by
        cases h : native_reflist_contains (env_refs E) s2 <;>
          simp [__smtx_type_wf_rec, native_ite, h] at hWf ⊢
      have hDtWf :
          __smtx_dt_wf_rec d2 (native_reflist_insert (env_refs E) s2) =
            true := by
        simpa [__smtx_type_wf_rec, native_ite, hNot] using hWf
      have hok' : env_ok ((s2, d2, env_close_dt E d2) :: E) :=
        ⟨hNot, hDtWf, rfl, hok⟩
      have hDtInf : __smtx_is_finite_datatype d2 = false := by
        simpa [__smtx_is_finite_type] using hFin
      have hpump' : env_pump ((s2, d2, env_close_dt E d2) :: E) :=
        ⟨hInh, hDtInf, hpump⟩
      rcases pump_dt n oracle d2 s2 d2 SmtDatatype.null E 0 hok' hpump'
          rfl rfl hDtWf hDtInf with ⟨w, h1, h2, h3⟩
      rw [env_close_ty_datatype E s2 d2 hNot]
      exact ⟨w, h1, h2, h3⟩
  | SmtType.None, _E, _hok, _hpump, hWf, _hInh, _hFin => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.TypeRef _r, _E, _hok, _hpump, hWf, _hInh, _hFin => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.RegLan, _E, _hok, _hpump, hWf, _hInh, _hFin => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.FunType _ _, _E, _hok, _hpump, hWf, _hInh, _hFin => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType _ _, _E, _hok, _hpump, hWf, _hInh, _hFin => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Bool, _E, _hok, _hpump, _hWf, _hInh, hFin => by
      simp [__smtx_is_finite_type] at hFin
  | SmtType.BitVec _, _E, _hok, _hpump, _hWf, _hInh, hFin => by
      simp [__smtx_is_finite_type] at hFin
  | SmtType.Char, _E, _hok, _hpump, _hWf, _hInh, hFin => by
      simp [__smtx_is_finite_type] at hFin
termination_by T _ _ _ _ _ _ => sizeOf T
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

/--
Walk an infinite raw datatype level to its first infinite constructor and
pump it.
-/
private theorem pump_dt (n : Nat) (oracle : PumpOracle n) :
    ∀ (dsuf : SmtDatatype) (s : native_String) (dr pre : SmtDatatype)
      (E : PumpEnv) (idx : Nat),
      env_ok ((s, dr, env_close_dt E dr) :: E) ->
        env_pump ((s, dr, env_close_dt E dr) :: E) ->
          dr = dt_append pre dsuf ->
            idx = dt_constructor_offset pre ->
              __smtx_dt_wf_rec dsuf
                  (env_refs ((s, dr, env_close_dt E dr) :: E)) = true ->
                __smtx_is_finite_datatype dsuf = false ->
                  ∃ v : SmtValue,
                    __smtx_typeof_value v =
                        SmtType.Datatype s (env_close_dt E dr) ∧
                      __smtx_value_canonical_bool v = true ∧
                        n + 1 ≤ sizeOf v
  | SmtDatatype.null, _s, _dr, _pre, _E, _idx, _hok, _hpump, _hSplit,
      _hOff, _hWf, hInf => by
      simp [__smtx_is_finite_datatype] at hInf
  | SmtDatatype.sum c SmtDatatype.null, s, dr, pre, E, idx, hok, hpump,
      hSplit, hOff, hWf, hInf => by
      have hConsWf :
          __smtx_dt_cons_wf_rec c
              (env_refs ((s, dr, env_close_dt E dr) :: E)) = true :=
        dt_wf_cons_of_wf hWf
      have hConsInf : __smtx_is_finite_datatype_cons c = false := by
        rcases finite_datatype_sum_false_cases hInf with h | h
        · exact h
        · simp [__smtx_is_finite_datatype] at h
      have hRoot :
          env_close_dt E dr =
            dt_append (env_close_dt E pre)
              (SmtDatatype.sum (env_close_dtc E c)
                (env_close_dt E SmtDatatype.null)) := by
        have h := congrArg (env_close_dt E) hSplit
        rw [env_close_dt_append, env_close_dt_sum] at h
        exact h
      have hOffC : idx = dt_constructor_offset (env_close_dt E pre) := by
        rw [dt_constructor_offset_env_close]
        exact hOff
      have hHeadTy :
          __smtx_typeof_value
              (SmtValue.DtCons s (env_close_dt E dr) idx) =
            dtc_type_chain s (env_close_dt E dr) (env_close_dtc E c)
              (SmtType.Datatype s (env_close_dt E dr)) := by
        rw [hOffC]
        exact typeof_dt_cons_append_offset_eq_dtc_type_chain
          s (env_close_dt E dr) (env_close_dt E pre)
          (env_close_dtc E c) (env_close_dt E SmtDatatype.null) hRoot
      exact pump_cons n oracle c s dr E
        (SmtValue.DtCons s (env_close_dt E dr) idx) hok hpump hConsWf
        hConsInf hHeadTy (by simp [__smtx_value_canonical_bool])
  | SmtDatatype.sum c (SmtDatatype.sum c2 t2), s, dr, pre, E, idx, hok,
      hpump, hSplit, hOff, hWf, hInf => by
      have hConsWf :
          __smtx_dt_cons_wf_rec c
              (env_refs ((s, dr, env_close_dt E dr) :: E)) = true :=
        dt_wf_cons_of_wf hWf
      by_cases hConsFin : __smtx_is_finite_datatype_cons c = true
      · have hTailInf :
            __smtx_is_finite_datatype (SmtDatatype.sum c2 t2) = false := by
          rcases finite_datatype_sum_false_cases hInf with h | h
          · rw [hConsFin] at h
            simp at h
          · exact h
        have hTailWf :
            __smtx_dt_wf_rec (SmtDatatype.sum c2 t2)
                (env_refs ((s, dr, env_close_dt E dr) :: E)) = true :=
          dt_wf_tail_of_nonempty_tail_wf hWf
        have hSplit' :
            dr =
              dt_append
                (dt_append pre (SmtDatatype.sum c SmtDatatype.null))
                (SmtDatatype.sum c2 t2) := by
          rw [dt_append_singleton_tail pre c (SmtDatatype.sum c2 t2)]
          exact hSplit
        have hOff' :
            Nat.succ idx =
              dt_constructor_offset
                (dt_append pre (SmtDatatype.sum c SmtDatatype.null)) := by
          rw [dt_constructor_offset_append]
          simp [dt_constructor_offset]
          omega
        exact pump_dt n oracle (SmtDatatype.sum c2 t2) s dr
          (dt_append pre (SmtDatatype.sum c SmtDatatype.null)) E
          (Nat.succ idx) hok hpump hSplit' hOff' hTailWf hTailInf
      · have hConsInf : __smtx_is_finite_datatype_cons c = false := by
          cases h : __smtx_is_finite_datatype_cons c <;>
            simp [h] at hConsFin ⊢
        have hRoot :
            env_close_dt E dr =
              dt_append (env_close_dt E pre)
                (SmtDatatype.sum (env_close_dtc E c)
                  (env_close_dt E (SmtDatatype.sum c2 t2))) := by
          have h := congrArg (env_close_dt E) hSplit
          rw [env_close_dt_append, env_close_dt_sum] at h
          exact h
        have hOffC : idx = dt_constructor_offset (env_close_dt E pre) := by
          rw [dt_constructor_offset_env_close]
          exact hOff
        have hHeadTy :
            __smtx_typeof_value
                (SmtValue.DtCons s (env_close_dt E dr) idx) =
              dtc_type_chain s (env_close_dt E dr) (env_close_dtc E c)
                (SmtType.Datatype s (env_close_dt E dr)) := by
          rw [hOffC]
          exact typeof_dt_cons_append_offset_eq_dtc_type_chain
            s (env_close_dt E dr) (env_close_dt E pre)
            (env_close_dtc E c) (env_close_dt E (SmtDatatype.sum c2 t2))
            hRoot
        exact pump_cons n oracle c s dr E
          (SmtValue.DtCons s (env_close_dt E dr) idx) hok hpump hConsWf
          hConsInf hHeadTy (by simp [__smtx_value_canonical_bool])
termination_by dsuf _ _ _ _ _ _ _ _ _ _ _ => sizeOf dsuf
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega

/--
Pump an infinite constructor: cross finite fields with inhabitants until
the first infinite field, grow there (recursively, or from the oracle at
a self/outer type reference), then complete the remaining fields.
-/
private theorem pump_cons (n : Nat) (oracle : PumpOracle n) :
    ∀ (c : SmtDatatypeCons) (s : native_String) (dr : SmtDatatype)
      (E : PumpEnv) (v : SmtValue),
      env_ok ((s, dr, env_close_dt E dr) :: E) ->
        env_pump ((s, dr, env_close_dt E dr) :: E) ->
          __smtx_dt_cons_wf_rec c
              (env_refs ((s, dr, env_close_dt E dr) :: E)) = true ->
            __smtx_is_finite_datatype_cons c = false ->
              __smtx_typeof_value v =
                  dtc_type_chain s (env_close_dt E dr) (env_close_dtc E c)
                    (SmtType.Datatype s (env_close_dt E dr)) ->
                __smtx_value_canonical_bool v = true ->
                  ∃ e : SmtValue,
                    __smtx_typeof_value e =
                        SmtType.Datatype s (env_close_dt E dr) ∧
                      __smtx_value_canonical_bool e = true ∧
                        n + 1 ≤ sizeOf e
  | SmtDatatypeCons.unit, _s, _dr, _E, _v, _hok, _hpump, _hWf, hInf,
      _hvTy, _hvCan => by
      simp [__smtx_is_finite_datatype_cons] at hInf
  | SmtDatatypeCons.cons T c, s, dr, E, v, hok, hpump, hWf, hInf, hvTy,
      hvCan => by
      by_cases hTfin : __smtx_is_finite_type T = true
      · have hNotRef : ∀ r, T ≠ SmtType.TypeRef r := by
          intro r hEq
          rw [hEq] at hTfin
          simp [__smtx_is_finite_type] at hTfin
        have hParts := dt_cons_wf_head_parts_of_not_typeref hWf hNotRef
        have hTailInf : __smtx_is_finite_datatype_cons c = false := by
          cases hc : __smtx_is_finite_datatype_cons c
          · rfl
          · simp [__smtx_is_finite_datatype_cons, native_and, hTfin,
              hc] at hInf
        rcases inhabit_field T ((s, dr, env_close_dt E dr) :: E) hok
            hParts.2.1 hParts.1 with ⟨w, hwTy, hwCan⟩
        have hNe :=
          env_close_ty_ne_none T ((s, dr, env_close_dt E dr) :: E)
            hParts.2.1
        have hvTy' :
            __smtx_typeof_value v =
              SmtType.DtcAppType
                (env_close_ty ((s, dr, env_close_dt E dr) :: E) T)
                (dtc_type_chain s (env_close_dt E dr) (env_close_dtc E c)
                  (SmtType.Datatype s (env_close_dt E dr))) := by
          rw [env_close_dtc_cons] at hvTy
          rw [env_close_ty_cons_step,
            <- dtc_substitute_field_type_eq_type_substitute]
          simpa [dtc_type_chain] using hvTy
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v w) =
              dtc_type_chain s (env_close_dt E dr) (env_close_dtc E c)
                (SmtType.Datatype s (env_close_dt E dr)) := by
          change
            __smtx_typeof_apply_value
                (__smtx_typeof_value v) (__smtx_typeof_value w) = _
          rw [hvTy', hwTy]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            native_Teq, native_ite, hNe]
        have hApplyCan :
            __smtx_value_canonical_bool (SmtValue.Apply v w) = true := by
          simp [__smtx_value_canonical_bool, native_and, hvCan, hwCan]
        exact pump_cons n oracle c s dr E (SmtValue.Apply v w) hok hpump
          hParts.2.2 hTailInf hApplyTy hApplyCan
      · have hTinf : __smtx_is_finite_type T = false := by
          cases h : __smtx_is_finite_type T <;> simp [h] at hTfin ⊢
        by_cases hRef : smt_type_is_typeref T = true
        · rcases smt_type_is_typeref_spec T hRef with ⟨r, hTr⟩
          subst hTr
          have hParts := dt_cons_wf_typeref_parts hWf
          rcases env_mem_split ((s, dr, env_close_dt E dr) :: E) r
              hParts.1 with ⟨E1, drr, Dr, E2, hEq⟩
          have hokSuf : env_ok ((r, drr, Dr) :: E2) := by
            rw [hEq] at hok
            exact env_ok_append_right E1 _ hok
          have hpumpSuf : env_pump ((r, drr, Dr) :: E2) := by
            rw [hEq] at hpump
            exact env_pump_append_right E1 _ hpump
          rcases oracle r drr Dr E2 hokSuf hpumpSuf with
            ⟨w, hwTy, hwCan, hwSize⟩
          have hResolve :
              env_close_ty ((s, dr, env_close_dt E dr) :: E)
                  (SmtType.TypeRef r) =
                SmtType.Datatype r Dr := by
            rw [hEq] at hok ⊢
            exact env_close_ty_typeref_resolve E1 r drr Dr E2 hok
          have hvTy' :
              __smtx_typeof_value v =
                SmtType.DtcAppType
                  (env_close_ty ((s, dr, env_close_dt E dr) :: E)
                    (SmtType.TypeRef r))
                  (dtc_type_chain s (env_close_dt E dr)
                    (env_close_dtc E c)
                    (SmtType.Datatype s (env_close_dt E dr))) := by
            rw [env_close_dtc_cons] at hvTy
            rw [env_close_ty_cons_step,
              <- dtc_substitute_field_type_eq_type_substitute]
            simpa [dtc_type_chain] using hvTy
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply v w) =
                dtc_type_chain s (env_close_dt E dr)
                  (env_close_dtc E c)
                  (SmtType.Datatype s (env_close_dt E dr)) := by
            change
              __smtx_typeof_apply_value
                  (__smtx_typeof_value v) (__smtx_typeof_value w) = _
            rw [hvTy', hResolve, hwTy]
            simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
              native_Teq, native_ite]
          have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply v w) =
                true := by
            simp [__smtx_value_canonical_bool, native_and, hvCan, hwCan]
          have hArgs :=
            pump_cons_args n oracle c s dr E hok hpump hParts.2
          rcases cons_apply_complete s (env_close_dt E dr)
              (env_close_dtc E c) (SmtValue.Apply v w) hApplyTy
              hApplyCan hArgs with ⟨e, h1, h2, h3⟩
          refine ⟨e, h1, h2, ?_⟩
          have hStep : sizeOf w < sizeOf (SmtValue.Apply v w) :=
            sizeOf_lt_apply_right v w
          omega
        · have hNotRef : ∀ r, T ≠ SmtType.TypeRef r := by
            intro r hEq
            rw [hEq] at hRef
            simp [smt_type_is_typeref] at hRef
          have hParts := dt_cons_wf_head_parts_of_not_typeref hWf hNotRef
          rcases pump_field n oracle T
              ((s, dr, env_close_dt E dr) :: E) hok hpump hParts.2.1
              hParts.1 hTinf with ⟨w, hwTy, hwCan, hwSize⟩
          exact pump_cons_path_field n oracle T c s dr E v hok hpump
            hWf hvTy hvCan hNotRef w hwTy hwCan hwSize
termination_by c _ _ _ _ _ _ _ _ _ _ => sizeOf c
decreasing_by
  all_goals try simp_wf
  all_goals try simp [sizeOf]
  all_goals omega


end

/-- The pumping oracle holds at every size. -/
private theorem pump_main : ∀ n : Nat, PumpOracle n
  | 0 => by
      intro s dr D E hok hpump
      have hWfTy :
          __smtx_type_wf_rec (SmtType.Datatype s dr) (env_refs E) =
            true := by
        simp [__smtx_type_wf_rec, native_ite, hok.1]
        exact hok.2.1
      rcases inhabit_field (SmtType.Datatype s dr) E hok.2.2.2 hWfTy
          hpump.1 with ⟨w, hwTy, hwCan⟩
      refine ⟨w, ?_, hwCan, Nat.zero_le _⟩
      rw [env_close_ty_datatype E s dr hok.1] at hwTy
      rw [hok.2.2.1]
      exact hwTy
  | Nat.succ n => by
      intro s dr D E hok hpump
      have hD : D = env_close_dt E dr := hok.2.2.1
      subst hD
      exact pump_dt n (pump_main n) dr s dr SmtDatatype.null E 0 hok
        hpump rfl rfl hok.2.1 hpump.2.1


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
  have hNot :
      native_reflist_contains (env_refs []) s = false := by
    simp [env_refs, native_reflist_nil, native_reflist_contains]
  have hDtWf :
      __smtx_dt_wf_rec d (native_reflist_insert (env_refs []) s) =
        true := by
    have hParts :
        ¬ s ∈ native_reflist_nil ∧
          __smtx_dt_wf_rec d
            (native_reflist_insert native_reflist_nil s) = true := by
      simpa [__smtx_type_wf_rec, native_reflist_contains,
        native_reflist_insert, native_ite] using hRec
    exact hParts.2
  have hok : env_ok [(s, d, d)] := ⟨hNot, hDtWf, rfl, trivial⟩
  have hpump : env_pump [(s, d, d)] :=
    ⟨hInh, by simpa [__smtx_is_finite_type] using hInfinite, trivial⟩
  exact pump_main minSize s d d [] hok hpump

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
      refine ⟨SmtValue.Char 1, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, native_char_valid, native_ite, native_veq]
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
      rcases seq_inhabited_large_witness T hRecParts.1
          (smt_value_size_bound avoid) with
        ⟨i, hiTy, hiCan, hiSize⟩
      refine ⟨i, hiTy, hiCan, ?_⟩
      intro j hj
      exact native_veq_false_of_mem_and_size_bound hj hiSize
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
