import CpcMicro.Proofs.TypePreservation.Helpers

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

/-- Characterizes the non-`None` cases of `__smtx_typeof_apply`. -/
theorem typeof_apply_non_none_cases
    {F X : SmtType}
    (h : __smtx_typeof_apply F X ≠ SmtType.None) :
    ∃ A B,
      F = SmtType.Map A B ∧
      X = A ∧
      A ≠ SmtType.None ∧
      B ≠ SmtType.None := by
  cases F with
  | None => simp [__smtx_typeof_apply] at h
  | Bool => simp [__smtx_typeof_apply] at h
  | Int => simp [__smtx_typeof_apply] at h
  | Real => simp [__smtx_typeof_apply] at h
  | RegLan => simp [__smtx_typeof_apply] at h
  | BitVec w => simp [__smtx_typeof_apply] at h
  | Set T => simp [__smtx_typeof_apply] at h
  | Seq T => simp [__smtx_typeof_apply] at h
  | Char => simp [__smtx_typeof_apply] at h
  | USort n => simp [__smtx_typeof_apply] at h
  | Map A B =>
      cases X <;> simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at h
      all_goals
        first
          | contradiction
          | exact ⟨A, B, rfl, h.2.1.symm, h.1, h.2.2⟩

/-- Shows that evaluating `apply_map` terms produces values of the expected type. -/
theorem typeof_value_model_eval_apply_map
    {f i : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value f = SmtType.Map A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply f i) = B := by
  have hiNN : i ≠ SmtValue.NotValue := by
    intro h
    cases h
    simp [__smtx_typeof_value] at hi
    exact hA hi.symm
  rcases map_value_canonical hf with ⟨m, rfl⟩
  have hApply :
      __smtx_model_eval_apply (SmtValue.Map m) i =
        __smtx_map_select (SmtValue.Map m) i := by
    cases i with
    | NotValue =>
        exact (hiNN rfl).elim
    | Boolean _
    | Numeral _
    | Rational _
    | Binary _ _
    | Map _
    | Set _
    | Seq _
    | Char _
    | RegLan _ =>
        simp [__smtx_model_eval_apply, __smtx_map_select]
  rw [hApply]
  simpa [__smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := B)
      (by simp [__smtx_typeof_value] at hf; simpa using hf) hi

/-- Shows that evaluating `apply_generic` terms produces values of the expected type. -/
theorem typeof_value_model_eval_apply_generic
    (M : SmtModel)
    (f x : SmtTerm)
    (hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hpresf : __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f)
    (hpresx : __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x) :
    __smtx_typeof_value (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x)) =
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
  rcases typeof_apply_non_none_cases hNN with ⟨A, B, hF, hX, hA, _hB⟩
  rw [hF, hX]
  have hFun : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.Map A B := by
    simpa [hF] using hpresf
  have hArg : __smtx_typeof_value (__smtx_model_eval M x) = A := by
    simpa [hX] using hpresx
  simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA] using
    typeof_value_model_eval_apply_map hA hFun hArg

end Smtm
