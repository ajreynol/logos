import Cpc.Proofs.TypePreservation.Support
import Cpc.Proofs.TypePreservation.CanonicalAssumptions

open SmtEval
open Smtm

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

namespace Smtm

private theorem model_total_typed_lookup_canonical_bool
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical_bool (native_model_lookup M s T) = true := by
  have hAll :
      ∀ s T, __smtx_type_wf T = true ->
        __smtx_value_canonical_bool (native_model_lookup M s T) = true := by
    rw [hM.2.1]
  exact hAll s T hT

/-- Describes how `model_total_typed` behaves under lookup for well-formed types. -/
theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_typeof_value (native_model_lookup M s T) = T :=
  hM.1 s T hT

/-- Describes how `model_total_typed` preserves canonical lookup values for well-formed types. -/
theorem model_total_typed_lookup_canonical
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical (native_model_lookup M s T) :=
  by
    simpa [__smtx_value_canonical]
      using model_total_typed_lookup_canonical_bool hM s T hT

/-- Describes how `model_total_typed` behaves under lookup for non-well-formed types. -/
theorem model_total_typed_lookup_not_wf
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = false) :
    native_model_lookup M s T = SmtValue.NotValue :=
  hM.2.2.1 s T hT

/-- Describes how `model_total_typed` constrains native functions. -/
theorem model_total_typed_native_fun_typed
    {M : SmtModel}
    (hM : model_total_typed M) :
    native_fun_typed M :=
  hM.2.2.2

theorem model_total_typed_lookup_uninhabited
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = false) :
    native_model_lookup M s T = SmtValue.NotValue :=
  model_total_typed_lookup_not_wf hM s T hT

/-- Describes how `model_typed_at` behaves under `push`. -/
theorem model_typed_at_push
    {M : SmtModel}
    {s : native_String}
    {T : SmtType}
    {v : SmtValue}
    (hWF : __smtx_type_wf T = true)
    (hv : __smtx_typeof_value v = T) :
    model_typed_at (native_model_push M s T v) s T := by
  constructor
  · intro hT
    simp [native_model_lookup, native_model_push, native_model_key, hv]
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
    model_total_typed (native_model_push M s T v) := by
  constructor
  · intro s' T' hT'
    by_cases h : s' = s ∧ T' = T
    · rcases h with ⟨rfl, rfl⟩
      simp [native_model_lookup, native_model_push, native_model_key, hv]
    · simp [native_model_lookup, native_model_push, native_model_key, h]
      exact model_total_typed_lookup hM s' T' hT'
  · constructor
    · apply propext
      constructor
      · intro _
        rfl
      · intro _
        intro s' T' hT'
        by_cases h : s' = s ∧ T' = T
        · rcases h with ⟨rfl, rfl⟩
          simpa [native_model_lookup, native_model_push, native_model_key,
            __smtx_value_canonical]
            using hvCanon
        · simp [native_model_lookup, native_model_push, native_model_key, h]
          exact model_total_typed_lookup_canonical_bool hM s' T' hT'
    · constructor
      · intro s' T' hT'
        by_cases h : s' = s ∧ T' = T
        · rcases h with ⟨rfl, rfl⟩
          rw [hWF] at hT'
          cases hT'
        · simp [native_model_lookup, native_model_push, native_model_key, h]
          exact model_total_typed_lookup_uninhabited hM s' T' hT'
      · intro fid A B i hFunWF hi
        simpa [native_fun_typed, native_eval_ifun_apply, native_model_fun_lookup,
          native_model_push]
          using model_total_typed_native_fun_typed hM fid A B i hFunWF hi

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
  | SmtValue.Fun fid T U => by
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
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c (SmtDatatype.sum cTail dTail)) refs = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true := by
  have hc : __smtx_dt_cons_wf_rec c refs = true :=
    dt_wf_cons_of_wf h
  simpa [__smtx_dt_wf_rec, native_ite, hc] using h

private theorem datatype_type_default_typed_canonical_of_wf_rec_deferred
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  exact cpc_datatype_type_default_typed_canonical_assumption s d _hInh _hRec

private theorem type_default_typed_canonical_of_wf_rec_deferred_datatype :
    (T : SmtType) ->
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T native_reflist_nil = true ->
          __smtx_typeof_value (__smtx_type_default T) = T ∧
            __smtx_value_canonical (__smtx_type_default T)
  | T, hInh, _hRec => by
      exact type_default_typed_canonical_of_native_inhabited_type T hInh

private theorem datatype_type_default_typed_canonical_of_wf_rec
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  exact datatype_type_default_typed_canonical_of_wf_rec_deferred s d _hInh _hRec

private theorem type_default_typed_canonical_of_wf_rec :
    (T : SmtType) ->
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T native_reflist_nil = true ->
          __smtx_typeof_value (__smtx_type_default T) = T ∧
            __smtx_value_canonical (__smtx_type_default T)
  | T, hInh, _hRec => by
      exact type_default_typed_canonical_of_native_inhabited_type T hInh

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
  · by_cases hFun : ∃ A B, T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, rfl⟩
      have hParts :
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B native_reflist_nil = true := by
        exact fun_type_wf_parts hWF
      have hDef :=
        type_default_typed_canonical_of_native_inhabited_type
          (SmtType.FunType A B) (native_inhabited_type_fun hParts.2.2.1)
      exact ⟨__smtx_type_default (SmtType.FunType A B), hDef.1, hDef.2⟩
    · have hComp : __smtx_type_wf_component T = true := by
        cases T <;> try exact hWF
        · exact False.elim (hReg rfl)
        · exact False.elim (hFun ⟨_, _, rfl⟩)
      have hParts :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T native_reflist_nil = true :=
        smtx_type_wf_component_parts hComp
      have hDef :=
        type_default_typed_canonical_of_wf_rec T hParts.1 hParts.2
      exact ⟨__smtx_type_default T, hDef.1, hDef.2⟩

/-- The syntactic default is well-typed and canonical for recursively well-formed inhabited types. -/
theorem type_default_typed_canonical_of_inhabited_wf_rec
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical (__smtx_type_default T) :=
  type_default_typed_canonical_of_wf_rec T hInh hRec

/-- The syntactic default is well-typed for types whose recursive well-formedness is known. -/
theorem type_default_typed_of_inhabited_wf_rec
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default T) = T :=
  (type_default_typed_canonical_of_inhabited_wf_rec T hInh hRec).1

end Smtm
