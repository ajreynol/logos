import Cpc.Proofs.TypePreservation

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Value equality reflected from `native_veq`. -/
theorem eq_of_native_veq_true {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = true) :
    v1 = v2 := by
  simpa [native_veq] using h

/-- Disequality reflected from `native_veq`. -/
theorem ne_of_native_veq_false {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    v1 = v2 -> False := by
  intro hEq
  subst v2
  simp [native_veq] at h

/-- `native_veq` is symmetric on false results. -/
theorem native_veq_false_symm {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    native_veq v2 v1 = false := by
  simp [native_veq] at h ⊢
  intro hEq
  exact h hEq.symm

/-- Unfolding helper for the canonicality predicate. -/
theorem value_canonical_bool_eq_true {v : SmtValue} :
    __smtx_value_canonical v = (__smtx_value_canonical_bool v = true) := by
  rfl

/-- `NotValue` is canonical as a value constructor, although it is not well typed. -/
theorem value_canonical_notValue :
    __smtx_value_canonical SmtValue.NotValue := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

theorem value_canonical_boolean (b : native_Bool) :
    __smtx_value_canonical (SmtValue.Boolean b) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

theorem value_canonical_numeral (n : native_Int) :
    __smtx_value_canonical (SmtValue.Numeral n) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

theorem value_canonical_rational (q : native_Rat) :
    __smtx_value_canonical (SmtValue.Rational q) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

theorem value_canonical_char (c : native_Char) :
    __smtx_value_canonical (SmtValue.Char c) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

theorem value_canonical_reglan (r : native_RegLan) :
    __smtx_value_canonical (SmtValue.RegLan r) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

theorem value_canonical_uvalue (u n : native_Nat) :
    __smtx_value_canonical (SmtValue.UValue u n) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

theorem value_canonical_dt_cons (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __smtx_value_canonical (SmtValue.DtCons s d i) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

/-- Boolean-typed values are canonical. -/
theorem value_canonical_of_bool_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Bool) :
    __smtx_value_canonical v := by
  rcases bool_value_canonical h with ⟨b, rfl⟩
  exact value_canonical_boolean b

/-- Integer-typed values are canonical. -/
theorem value_canonical_of_int_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Int) :
    __smtx_value_canonical v := by
  rcases int_value_canonical h with ⟨n, rfl⟩
  exact value_canonical_numeral n

/-- Real-typed values are canonical. -/
theorem value_canonical_of_real_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Real) :
    __smtx_value_canonical v := by
  rcases real_value_canonical h with ⟨q, rfl⟩
  exact value_canonical_rational q

/-- Bit-vector typing includes the payload normalization condition, so typed bit-vectors are canonical. -/
theorem value_canonical_of_bitvec_type
    {v : SmtValue}
    {w : native_Nat}
    (h : __smtx_typeof_value v = SmtType.BitVec w) :
    __smtx_value_canonical v := by
  rcases bitvec_value_canonical h with ⟨n, rfl⟩
  have hPayload :
      native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true :=
    bitvec_payload_canonical h
  simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_ite,
    hPayload]

/-- Regex-typed values are canonical. -/
theorem value_canonical_of_reglan_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.RegLan) :
    __smtx_value_canonical v := by
  rcases reglan_value_canonical h with ⟨r, rfl⟩
  exact value_canonical_reglan r

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

/-- Regex-typed terms evaluate to canonical values in total typed models. -/
theorem model_eval_canonical_of_reglan_type
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.RegLan) :
    __smtx_value_canonical (__smtx_model_eval M t) := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact value_canonical_of_reglan_type hValTy

end Smtm
