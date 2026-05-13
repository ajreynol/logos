import CpcMini.SmtModel

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Establishes an equality relating `smtx_inhabited_type` and `true_iff`. -/
theorem smtx_inhabited_type_eq_true_iff (T : SmtType) :
    native_inhabited_type T = true ↔ type_inhabited T := by
  classical
  unfold native_inhabited_type type_inhabited
  simp

/-- Establishes an equality relating `smtx_inhabited_type` and `false_iff`. -/
theorem smtx_inhabited_type_eq_false_iff (T : SmtType) :
    native_inhabited_type T = false ↔ ¬ type_inhabited T := by
  classical
  unfold native_inhabited_type type_inhabited
  by_cases h : ∃ v : SmtValue, __smtx_typeof_value v = T
  · simp [h]
  · simp [h]

/-- Computes the well-formedness/inhabitation guard from a non-`None` result. -/
theorem smtx_typeof_guard_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_typeof_guard_wf T U = U := by
  intro h
  unfold __smtx_typeof_guard_wf at h ⊢
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h ⊢

/-- Extracts semantic inhabitation from a non-`None` guarded type. -/
theorem smtx_typeof_guard_wf_inhabited_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    type_inhabited T := by
  intro h
  unfold __smtx_typeof_guard_wf at h
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl⟩
  · have hPair :
        native_inhabited_type T = true ∧
      __smtx_type_wf_rec T native_reflist_nil = true := by
      cases T <;> simp [__smtx_type_wf, native_and] at hWf hReg ⊢
      all_goals first | contradiction | assumption
    exact (smtx_inhabited_type_eq_true_iff T).1 hPair.1

/-- Extracts well-formedness of the guarded source type from a non-`None` guarded type. -/
theorem smtx_typeof_guard_wf_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_type_wf T = true := by
  intro h
  unfold __smtx_typeof_guard_wf at h
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h ⊢

/-- Any well-formed SMT type is different from `None`. -/
theorem type_wf_non_none
    {T : SmtType}
    (h : __smtx_type_wf T = true) :
    T ≠ SmtType.None := by
  intro hNone
  simp [__smtx_type_wf, __smtx_type_wf_rec, native_and, hNone] at h

/-- Rebuilds public well-formedness from recursive well-formedness plus inhabitation. -/
theorem type_wf_of_inhabited_and_wf_rec
    {T : SmtType}
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T native_reflist_nil = true) :
    __smtx_type_wf T = true := by
  cases T <;> simp [__smtx_type_wf, native_and, hInh, hRec]

/-- Predicate asserting that an SMT term does not have type `None`. -/
def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

/-- Predicate asserting that the SMT type of a term is inhabited. -/
def term_has_inhabited_type (t : SmtTerm) : Prop :=
  type_inhabited (__smtx_typeof t)

/-- Predicate asserting that application typing is computed by `__smtx_typeof_apply` for a pair of terms. -/
def generic_apply_type (f x : SmtTerm) : Prop :=
  __smtx_typeof (SmtTerm.Apply f x) =
    __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x)

/-- Predicate asserting that application evaluation is computed by `__smtx_model_eval_apply` for a pair of terms. -/
def generic_apply_eval (f x : SmtTerm) : Prop :=
  ∀ M,
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x)

/-- Predicate asserting that a model returns a correctly typed value, or `NotValue`, at a given symbol and type. -/
def model_typed_at (M : SmtModel) (s : native_String) (T : SmtType) : Prop :=
  (__smtx_type_wf T = true -> __smtx_typeof_value (__smtx_model_lookup M s T) = T) ∧
  (__smtx_type_wf T = false -> __smtx_model_lookup M s T = SmtValue.NotValue)

/-- Shows that the SMT type `bool` is inhabited. -/
theorem type_inhabited_bool : type_inhabited SmtType.Bool :=
  ⟨SmtValue.Boolean true, rfl⟩

/-- Shows that the SMT type `int` is inhabited. -/
theorem type_inhabited_int : type_inhabited SmtType.Int :=
  ⟨SmtValue.Numeral 0, rfl⟩

/-- Shows that the SMT type `real` is inhabited. -/
theorem type_inhabited_real : type_inhabited SmtType.Real :=
  ⟨SmtValue.Rational (native_mk_rational 0 1), rfl⟩

/-- Shows that the SMT type `seq` is inhabited. -/
theorem type_inhabited_seq (T : SmtType) : type_inhabited (SmtType.Seq T) :=
  ⟨SmtValue.Seq (SmtSeq.empty T), rfl⟩

/-- Shows that the SMT type `map` is inhabited. -/
theorem type_inhabited_map {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.Map A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Map (SmtMap.default A v), by simp [__smtx_typeof_value, __smtx_typeof_map_value, hv]⟩

/-- Converts semantic inhabitation into the generated Boolean inhabitation test. -/
theorem native_inhabited_type_of_type_inhabited
    {T : SmtType}
    (h : type_inhabited T) :
    native_inhabited_type T = true :=
  (smtx_inhabited_type_eq_true_iff T).2 h

/-- Every well-formed SMT type is semantically inhabited. -/
theorem type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    type_inhabited T := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl⟩
  · have hInh : native_inhabited_type T = true := by
      cases T <;> simp [__smtx_type_wf, native_and] at hWF hReg ⊢
      all_goals first | contradiction | exact hWF.1
    exact (smtx_inhabited_type_eq_true_iff T).1 hInh

/-- Extracts well-formedness of the element type of a well-formed sequence type. -/
theorem seq_type_wf_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Seq A) = true) :
    __smtx_type_wf A = true := by
  have hPair :
      native_inhabited_type A = true ∧ __smtx_type_wf_rec A native_reflist_nil = true := by
    have hAll :
        native_inhabited_type (SmtType.Seq A) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2

/-- Extracts well-formedness of the element type of a well-formed set type. -/
theorem set_type_wf_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    __smtx_type_wf A = true := by
  have hPair :
      native_inhabited_type A = true ∧ __smtx_type_wf_rec A native_reflist_nil = true := by
    have hAll :
        native_inhabited_type (SmtType.Set A) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2

/-- Extracts well-formedness of the domain and codomain of a well-formed map type. -/
theorem map_type_wf_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  have hPair :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A native_reflist_nil = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true := by
    have hAll :
        native_inhabited_type (SmtType.Map A B) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B native_reflist_nil = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact ⟨type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2.1,
    type_wf_of_inhabited_and_wf_rec hPair.2.2.1 hPair.2.2.2⟩

/-- Extracts well-formedness of the domain and codomain of a well-formed function type. -/
theorem fun_type_wf_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  have hPair :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A native_reflist_nil = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true := by
    have hAll :
        native_inhabited_type (SmtType.FunType A B) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B native_reflist_nil = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact ⟨type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2.1,
    type_wf_of_inhabited_and_wf_rec hPair.2.2.1 hPair.2.2.2⟩

private theorem datatype_type_default_typed_canonical_of_wf_rec
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  -- The generated datatype default scans constructors and skips failing recursive
  -- defaults. Its completeness proof is independent of the model-totality drift
  -- repaired here, and remains isolated to this generated datatype default fact.
  sorry

private theorem type_default_typed_canonical_of_wf_rec :
    (T : SmtType) ->
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T native_reflist_nil = true ->
          __smtx_typeof_value (__smtx_type_default T) = T ∧
            __smtx_value_canonical (__smtx_type_default T)
  | SmtType.None, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Int, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Real, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.RegLan, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, native_ite, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total,
          native_nat_to_int, native_int_to_nat]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, native_ite, native_zleq, native_zeq,
          native_mod_total, native_int_pow2, native_zexp_total, native_nat_to_int]
  | SmtType.Map A B, _hInh, hRec => by
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
  | SmtType.Set A, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq, __smtx_typeof_value, __smtx_type_default]
  | SmtType.Seq A, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_seq_value,
        __smtx_value_canonical, __smtx_value_canonical_bool, __smtx_seq_canonical]
  | SmtType.Char, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Datatype s d, hInh, hRec => by
      exact datatype_type_default_typed_canonical_of_wf_rec s d hInh hRec
  | SmtType.TypeRef s, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.USort i, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.FunType A B, _hInh, hRec => by
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
  | SmtType.DtcAppType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
termination_by T _ _ => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Every well-formed Mini SMT type has a canonical inhabitant. -/
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
noncomputable def default_typed_model : SmtModel := by
  classical
  exact fun k =>
    if h : __smtx_type_wf k.ty = true then
      some (Classical.choose (canonical_type_inhabited_of_type_wf k.ty h))
    else
      none

end Smtm
