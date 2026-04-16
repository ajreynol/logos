import CpcMini.Spec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `boolean`. -/
@[simp] theorem eo_to_smt_boolean (b : native_Bool) :
    __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `var`. -/
@[simp] theorem eo_to_smt_var (s : native_String) (T : Term) :
    __eo_to_smt (Term.Var (Term.String s) T) = SmtTerm.Var s (__eo_to_smt_type T) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `uconst`. -/
@[simp] theorem eo_to_smt_uconst (i : native_Nat) (T : Term) :
    __eo_to_smt (Term.UConst i T) = SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T) := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT type translation for `bool`. -/
@[simp] theorem eo_to_smt_type_bool :
    __eo_to_smt_type Term.Bool = SmtType.Bool := rfl

/-- Simplifies EO-to-SMT type translation for `int`. -/
@[simp] theorem eo_to_smt_type_int :
    __eo_to_smt_type Term.Int = SmtType.Int := rfl

/-- Simplifies EO-to-SMT type translation for `real`. -/
@[simp] theorem eo_to_smt_type_real :
    __eo_to_smt_type Term.Real = SmtType.Real := rfl

/-- Simplifies EO-to-SMT type translation for `fun`. -/
@[simp] theorem eo_to_smt_type_fun (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) =
      __smtx_typeof_guard (__eo_to_smt_type T)
        (__smtx_typeof_guard (__eo_to_smt_type U)
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U))) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
@[simp] theorem eo_to_smt_type_dtc_app (T U : Term) :
    __eo_to_smt_type (Term.DtcAppType T U) =
      __smtx_typeof_guard (__eo_to_smt_type T)
        (__smtx_typeof_guard (__eo_to_smt_type U)
          (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U))) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `bitvec`. -/
@[simp] theorem eo_to_smt_type_bitvec (n : native_Int) :
    __eo_to_smt_type (Term.Apply Term.BitVec (Term.Numeral n)) =
      native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `char`. -/
@[simp] theorem eo_to_smt_type_char :
    __eo_to_smt_type Term.Char = SmtType.Char := rfl

/-- Simplifies EO-to-SMT type translation for `seq`. -/
@[simp] theorem eo_to_smt_type_seq (T : Term) :
    __eo_to_smt_type (Term.Apply Term.Seq T) =
      __smtx_typeof_guard (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) := by
  simp [__eo_to_smt_type]

/-- Computes `__smtx_typeof` for `guard_wf_of_non_none`. -/
theorem smtx_typeof_guard_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_typeof_guard_wf T U = U := by
  intro h
  unfold __smtx_typeof_guard_wf at h ⊢
  cases hInh : native_inhabited_type T <;> simp [native_ite, hInh] at h ⊢
  cases hWf : __smtx_type_wf T <;> simp [hWf] at h ⊢

/-- Computes `__smtx_typeof` for `var_of_non_none`. -/
theorem smtx_typeof_var_of_non_none
    (s : native_String) (T : SmtType) :
  __smtx_typeof (SmtTerm.Var s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.Var s T) = T := by
  intro h
  change __smtx_typeof_guard_wf T T = T
  exact smtx_typeof_guard_wf_of_non_none T T (by simpa [__smtx_typeof] using h)

/-- Computes `__smtx_typeof` for `uconst_of_non_none`. -/
theorem smtx_typeof_uconst_of_non_none
    (s : native_String) (T : SmtType) :
  __smtx_typeof (SmtTerm.UConst s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.UConst s T) = T := by
  intro h
  change __smtx_typeof_guard_wf T T = T
  exact smtx_typeof_guard_wf_of_non_none T T (by simpa [__smtx_typeof] using h)

/-- Derives `smtx_binary_well_formed` from `non_none`. -/
theorem smtx_binary_well_formed_of_non_none
    (w n : native_Int) :
    __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None ->
    native_zleq 0 w = true ∧
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
  intro h
  let g :=
    native_and (native_zleq 0 w)
      (native_zeq n (native_mod_total n (native_int_pow2 w)))
  have hg : g = true := by
    by_cases h' : g = true
    · exact h'
    · exfalso
      apply h
      change native_ite g (SmtType.BitVec (native_int_to_nat w)) SmtType.None = SmtType.None
      simp [native_ite, h']
  have hWidth : native_zleq 0 w = true := by
    cases hw : native_zleq 0 w <;> simp [g, SmtEval.native_and, hw] at hg
    rfl
  have hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
    cases hm : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [g, SmtEval.native_and, hWidth, hm] at hg
    rfl
  exact ⟨hWidth, hMod⟩

/-- Computes `__smtx_typeof` for `binary_of_non_none`. -/
theorem smtx_typeof_binary_of_non_none
    (w n : native_Int) :
    __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec (native_int_to_nat w) := by
  intro h
  obtain ⟨hWidth, hMod⟩ := smtx_binary_well_formed_of_non_none w n h
  simp [__smtx_typeof, native_ite, SmtEval.native_and, hWidth, hMod]

end TranslationProofs
