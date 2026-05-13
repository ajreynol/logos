import Cpc.Proofs.TypePreservation.Support

open SmtEval
open Smtm

namespace Smtm

/-- Describes how `model_total_typed` behaves under lookup for well-formed types. -/
theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_typeof_value (__smtx_model_lookup M s T) = T :=
  hM.1 s T hT

/-- Describes how `model_total_typed` preserves canonical lookup values for well-formed types. -/
theorem model_total_typed_lookup_canonical
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical (__smtx_model_lookup M s T) :=
  hM.2.1 s T hT

/-- Describes how `model_total_typed` behaves under lookup for non-well-formed types. -/
theorem model_total_typed_lookup_not_wf
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = false) :
    __smtx_model_lookup M s T = SmtValue.NotValue :=
  hM.2.2 s T hT

theorem model_total_typed_lookup_uninhabited
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = false) :
    __smtx_model_lookup M s T = SmtValue.NotValue :=
  model_total_typed_lookup_not_wf hM s T hT

/-- Describes how `model_typed_at` behaves under `push`. -/
theorem model_typed_at_push
    {M : SmtModel}
    {s : native_String}
    {T : SmtType}
    {v : SmtValue}
    (hWF : __smtx_type_wf T = true)
    (hv : __smtx_typeof_value v = T) :
    model_typed_at (__smtx_model_push M s T v) s T := by
  constructor
  · intro hT
    simp [__smtx_model_lookup, __smtx_model_push, __smtx_model_key, hv]
  · intro hT
    rw [hWF] at hT
    cases hT

/-- Describes how `model_total_typed` behaves under `push`. -/
theorem model_total_typed_push
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (v : SmtValue)
    (hWF : __smtx_type_wf T = true)
    (hv : __smtx_typeof_value v = T)
    (hvCanon : __smtx_value_canonical v) :
    model_total_typed (__smtx_model_push M s T v) := by
  constructor
  · intro s' T' hT'
    unfold __smtx_model_lookup __smtx_model_push
    by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
    · cases h
      simp [hv]
    · simp [h]
      exact model_total_typed_lookup hM s' T' hT'
  · constructor
    · intro s' T' hT'
      unfold __smtx_model_lookup __smtx_model_push
      by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
      · cases h
        simp [hvCanon]
      · simp [h]
        exact model_total_typed_lookup_canonical hM s' T' hT'
    · intro s' T' hT'
      unfold __smtx_model_lookup __smtx_model_push
      by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
      · cases h
        rw [hWF] at hT'
        cases hT'
      · simp [h]
        exact model_total_typed_lookup_uninhabited hM s' T' hT'

/-- Choice-based model from canonical witnesses for every well-formed SMT type. -/
noncomputable def default_typed_model_of
    (hCan :
      ∀ T : SmtType,
        __smtx_type_wf T = true ->
          ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v) :
    SmtModel := by
  classical
  exact fun k =>
    if hWF : __smtx_type_wf k.ty = true then
      some (Classical.choose (hCan k.ty hWF))
    else
      none

/--
Reduces nonvacuity of total typed models to the canonical-inhabitant theorem
for well-formed SMT types.
-/
theorem exists_total_typed_model_of_canonical_type_inhabited
    (hCan :
      ∀ T : SmtType,
        __smtx_type_wf T = true ->
          ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v) :
    ∃ M : SmtModel, model_total_typed M := by
  classical
  refine ⟨default_typed_model_of hCan, ?_⟩
  constructor
  · intro s T hT
    simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT,
      (Classical.choose_spec (hCan T hT)).1]
  · constructor
    · intro s T hT
      simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT,
        (Classical.choose_spec (hCan T hT)).2]
    · intro s T hT
      simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT]

private theorem value_dt_substitute_canonical
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
      __smtx_value_canonical v ->
        __smtx_value_canonical (__smtx_value_dt_substitute s d v)
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
  | SmtValue.Fun m, h => by
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
      simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_and] at h
      have hOrig : __smtx_value_canonical (SmtValue.Apply f a) := by
        simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_and]
        exact h
      have hf := value_dt_substitute_canonical s d f h.1
      have ha := value_dt_substitute_canonical s d a h.2
      cases hHead : __vsm_apply_head f with
      | DtCons s' d' i =>
          cases hShadow : native_streq s s'
          · simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
              hHead, hShadow, native_ite,
              __smtx_value_canonical, __smtx_value_canonical_bool, native_and]
            exact ⟨by simpa [__smtx_value_canonical] using hf,
              by simpa [__smtx_value_canonical] using ha⟩
          · simpa [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
              hHead, hShadow, native_ite] using hOrig
      | _ =>
          simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
            hHead, __smtx_value_canonical, __smtx_value_canonical_bool,
            native_and] at hf ha ⊢
          exact ⟨hf, ha⟩

private theorem value_dt_substitute_eq_notValue
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
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
  | SmtValue.Fun m => by
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
      cases hHead : __vsm_apply_head f with
      | DtCons s' d' i =>
          cases hShadow : native_streq s s' <;>
            simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
              hHead, hShadow, native_ite]
      | _ =>
          simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
            hHead]

private theorem value_dt_substitute_ne_notValue
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    __smtx_value_dt_substitute s d v ≠ SmtValue.NotValue := by
  intro hSub
  exact h ((value_dt_substitute_eq_notValue s d v).1 hSub)

private theorem native_veq_notValue_false_of_ne
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    native_veq v SmtValue.NotValue = false := by
  simpa [native_veq] using h

private theorem native_veq_value_dt_substitute_notValue_false
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    native_veq (__smtx_value_dt_substitute s d v) SmtValue.NotValue = false := by
  have hSub := value_dt_substitute_ne_notValue s d h
  exact native_veq_notValue_false_of_ne hSub

private theorem value_dt_substitute_apply_shadow
    (s : native_String)
    (d d' : SmtDatatype)
    (f a : SmtValue)
    (i : native_Nat)
    (hHead : __vsm_apply_head f = SmtValue.DtCons s d' i) :
    __smtx_value_dt_substitute s d (SmtValue.Apply f a) = SmtValue.Apply f a := by
  simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
    hHead, native_streq, native_ite]

private theorem value_dt_substitute_apply_no_shadow
    (s s' : native_String)
    (d d' : SmtDatatype)
    (f a : SmtValue)
    (i : native_Nat)
    (hHead : __vsm_apply_head f = SmtValue.DtCons s' d' i)
    (hNe : s ≠ s') :
    __smtx_value_dt_substitute s d (SmtValue.Apply f a) =
      SmtValue.Apply (__smtx_value_dt_substitute s d f) (__smtx_value_dt_substitute s d a) := by
  have hShadow : native_streq s s' = false := by
    simp [native_streq, hNe]
  simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
    hHead, hShadow, native_ite]

private theorem datatype_type_default_typed_canonical_of_wf_rec
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  sorry

private theorem type_default_typed_canonical_of_wf_rec :
    (T : SmtType) ->
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T native_reflist_nil = true ->
          __smtx_typeof_value (__smtx_type_default T) = T ∧
            __smtx_value_canonical (__smtx_type_default T)
  | SmtType.None, hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, hInh, hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Int, hInh, hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Real, hInh, hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.RegLan, hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, hInh, hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, native_ite, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total,
          native_nat_to_int, native_int_to_nat]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, native_ite, native_zleq, native_zeq,
          native_mod_total, native_int_pow2, native_zexp_total, native_nat_to_int]
  | SmtType.Map A B, hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB := type_default_typed_canonical_of_wf_rec B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.Set A, hInh, hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq, __smtx_typeof_value, __smtx_type_default]
  | SmtType.Seq A, hInh, hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_seq_value,
        __smtx_value_canonical, __smtx_value_canonical_bool, __smtx_seq_canonical]
  | SmtType.Char, hInh, hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Datatype s d, hInh, hRec => by
      exact datatype_type_default_typed_canonical_of_wf_rec s d hInh hRec
  | SmtType.TypeRef s, hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.USort i, hInh, hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.FunType A B, hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB := type_default_typed_canonical_of_wf_rec B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_fun_type, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.DtcAppType A B, hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
termination_by T _ _ => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals omega

/--
Every well-formed SMT type has a canonical inhabitant.

The proof reduces finite-domain map/function defaults to canonicality of
`__smtx_type_default`; the remaining isolated gap is generated datatype
defaults.
-/
theorem canonical_type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl, by
      simp [__smtx_value_canonical, __smtx_value_canonical_bool]⟩
  · have hParts :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T native_reflist_nil = true := by
      cases T <;> simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hWF hReg ⊢ <;>
        exact hWF
    have hDef :=
      type_default_typed_canonical_of_wf_rec T hParts.1 hParts.2
    exact ⟨__smtx_type_default T, hDef.1, hDef.2⟩

/-- Choice-based model that returns a canonical inhabitant for every well-formed SMT type. -/
noncomputable def default_typed_model : SmtModel :=
  default_typed_model_of canonical_type_inhabited_of_type_wf

/-- Shows that `default_typed_model` is total and type-correct on every well-formed SMT type. -/
theorem default_typed_model_total_typed :
    model_total_typed default_typed_model := by
  classical
  unfold default_typed_model
  constructor
  · intro s T hT
    simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT,
      (Classical.choose_spec (canonical_type_inhabited_of_type_wf T hT)).1]
  · constructor
    · intro s T hT
      simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT,
        (Classical.choose_spec (canonical_type_inhabited_of_type_wf T hT)).2]
    · intro s T hT
      simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT]

/-- Constructs a total typed SMT model. -/
theorem exists_total_typed_model :
    ∃ M : SmtModel, model_total_typed M :=
  ⟨default_typed_model, default_typed_model_total_typed⟩

end Smtm
