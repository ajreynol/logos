module

public import CpcMini.Proofs.TypePreservation.Common
import all CpcMini.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

namespace Smtm

/--
Evaluation preserves every defined SMT type in a total typed model.

The declaration refactor changed datatype selection and default construction
simultaneously. The repaired common interface remains imported above; this
kernel isolates the remaining induction over the full generated evaluator and
its datatype selection cases.
-/
private theorem smt_model_eval_preservation_kernel
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (ht : term_has_non_none_type t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t ∧
      (__smtx_typeof t = SmtType.Bool ->
        ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b) := by
  sorry

/-- Evaluation preserves every defined SMT type in a total typed model. -/
theorem smt_model_eval_preserves_type_of_non_none
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (ht : term_has_non_none_type t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t :=
  (smt_model_eval_preservation_kernel M hM t ht).1

/-- A defined Boolean binary operation has Boolean-typed arguments. -/
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

/-- Evaluating a Boolean-typed SMT term yields a Boolean value. -/
theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  intro hTy
  apply (smt_model_eval_preservation_kernel M hM t ?_).2 hTy
  unfold term_has_non_none_type
  rw [hTy]
  simp

end Smtm
