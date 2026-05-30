import CpcMini.Proofs.TypePreservation.Support

open SmtEval
open Smtm

namespace Smtm

private theorem model_total_typed_lookup_canonical_bool
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical_bool (native_model_lookup M s T) = true := by
  simpa [native_model_lookup, native_model_key] using
    hM.2.1 false s T hT

/-- Describes how `model_total_typed` behaves under `lookup`. -/
theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_typeof_value (native_model_lookup M s T) = T :=
  by
    simpa [native_model_lookup, native_model_key] using
      hM.1 false s T hT

/-- Describes how `model_total_typed` preserves canonical lookup values. -/
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
  by
    simpa [native_model_lookup, native_model_key] using
      hM.2.2.1 false s T hT

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

private theorem model_total_typed_var_lookup_canonical_bool
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical_bool (native_model_var_lookup M s T) = true := by
  simpa [native_model_var_lookup] using
    hM.2.1 true s T hT

theorem model_total_typed_var_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_typeof_value (native_model_var_lookup M s T) = T := by
  simpa [native_model_var_lookup] using
    hM.1 true s T hT

theorem model_total_typed_var_lookup_canonical
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical (native_model_var_lookup M s T) := by
  simpa [__smtx_value_canonical]
    using model_total_typed_var_lookup_canonical_bool hM s T hT

theorem model_total_typed_var_lookup_uninhabited
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = false) :
    native_model_var_lookup M s T = SmtValue.NotValue := by
  simpa [native_model_var_lookup] using
    hM.2.2.1 true s T hT

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
    simp [native_model_var_lookup, native_model_push, hv]
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
  · intro isVar s' T' hT'
    by_cases hKey :
        ({ isVar := isVar, name := s', ty := T' } : SmtModelKey) =
          { isVar := true, name := s, ty := T }
    · cases hKey
      simp [native_model_push, hv]
    · simp [native_model_push, hKey]
      exact hM.1 isVar s' T' hT'
  · constructor
    · intro isVar s' T' hT'
      by_cases hKey :
          ({ isVar := isVar, name := s', ty := T' } : SmtModelKey) =
            { isVar := true, name := s, ty := T }
      · cases hKey
        simpa [native_model_push, __smtx_value_canonical] using hvCanon
      · simp [native_model_push, hKey]
        exact hM.2.1 isVar s' T' hT'
    · constructor
      · intro isVar s' T' hT'
        by_cases hKey :
            ({ isVar := isVar, name := s', ty := T' } : SmtModelKey) =
              { isVar := true, name := s, ty := T }
        · cases hKey
          rw [hWF] at hT'
          cases hT'
        · simp [native_model_push, hKey]
          exact hM.2.2.1 isVar s' T' hT'
      · intro fid A B i hFunWF hi
        simpa [native_fun_typed, native_eval_ifun_apply, native_model_fun_lookup,
          native_model_push]
          using model_total_typed_native_fun_typed hM fid A B i hFunWF hi

end Smtm
