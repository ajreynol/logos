import Cpc.Proofs.TypePreservation
import Cpc.Proofs.Canonical.Basic

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Boolean-typed terms evaluate to canonical values in total typed models. -/
theorem model_eval_canonical_of_bool_type
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool) :
    __smtx_value_canonical (__smtx_model_eval M t) := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact value_canonical_of_bool_type hValTy

/-- Integer-typed terms evaluate to canonical values in total typed models. -/
theorem model_eval_canonical_of_int_type
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Int) :
    __smtx_value_canonical (__smtx_model_eval M t) := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Int := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact value_canonical_of_int_type hValTy

/-- Real-typed terms evaluate to canonical values in total typed models. -/
theorem model_eval_canonical_of_real_type
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Real) :
    __smtx_value_canonical (__smtx_model_eval M t) := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Real := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact value_canonical_of_real_type hValTy

/-- Bit-vector-typed terms evaluate to canonical values in total typed models. -/
theorem model_eval_canonical_of_bitvec_type
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (w : native_Nat)
    (hTy : __smtx_typeof t = SmtType.BitVec w) :
    __smtx_value_canonical (__smtx_model_eval M t) := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.BitVec w := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact value_canonical_of_bitvec_type hValTy

/-- Regex-typed terms evaluate to canonical values when their evaluated value is canonical. -/
theorem model_eval_canonical_of_reglan_type
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.RegLan)
    (hCan : __smtx_value_canonical_bool (__smtx_model_eval M t) = true) :
    __smtx_value_canonical (__smtx_model_eval M t) := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact value_canonical_of_reglan_type hValTy hCan

end Smtm
