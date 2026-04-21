import Cpc.Spec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Computes `__eo_typeof` for `boolean`. -/
@[simp] theorem eo_typeof_boolean (b : native_Bool) :
    __eo_typeof (Term.Boolean b) = Term.Bool := by
  cases b <;> native_decide

/-- Computes `__eo_typeof` for `re_allchar`. -/
@[simp] theorem eo_typeof_re_allchar :
    __eo_typeof (Term.UOp UserOp.re_allchar) = Term.UOp UserOp.RegLan := by
  native_decide

/-- Computes `__eo_typeof` for `re_none`. -/
@[simp] theorem eo_typeof_re_none :
    __eo_typeof (Term.UOp UserOp.re_none) = Term.UOp UserOp.RegLan := by
  native_decide

/-- Computes `__eo_typeof` for `re_all`. -/
@[simp] theorem eo_typeof_re_all :
    __eo_typeof (Term.UOp UserOp.re_all) = Term.UOp UserOp.RegLan := by
  native_decide

/-- Simplifies EO-to-SMT translation for `boolean`. -/
@[simp] theorem eo_to_smt_boolean (b : native_Bool) :
    __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `re_allchar`. -/
@[simp] theorem eo_to_smt_re_allchar :
    __eo_to_smt (Term.UOp UserOp.re_allchar) = SmtTerm.re_allchar := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `re_none`. -/
@[simp] theorem eo_to_smt_re_none :
    __eo_to_smt (Term.UOp UserOp.re_none) = SmtTerm.re_none := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `re_all`. -/
@[simp] theorem eo_to_smt_re_all :
    __eo_to_smt (Term.UOp UserOp.re_all) = SmtTerm.re_all := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `var`. -/
@[simp] theorem eo_to_smt_var (s : native_String) (T : Term) :
    __eo_to_smt (Term.Var (Term.String s) T) = SmtTerm.Var s (__eo_to_smt_type T) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `uconst`. -/
@[simp] theorem eo_to_smt_uconst (i : native_Nat) (T : Term) :
    __eo_to_smt (Term.UConst i T) = SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T) := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `set_empty`. -/
@[simp] theorem eo_to_smt_set_empty (T : Term) :
    __eo_to_smt (Term.set_empty T) = __eo_to_smt_set_empty (__eo_to_smt_type T) := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT type translation for `bool`. -/
@[simp] theorem eo_to_smt_type_bool :
    __eo_to_smt_type Term.Bool = SmtType.Bool := rfl

/-- Simplifies EO-to-SMT type translation for `int`. -/
@[simp] theorem eo_to_smt_type_int :
    __eo_to_smt_type (Term.UOp UserOp.Int) = SmtType.Int := rfl

/-- Simplifies EO-to-SMT type translation for `real`. -/
@[simp] theorem eo_to_smt_type_real :
    __eo_to_smt_type (Term.UOp UserOp.Real) = SmtType.Real := rfl

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
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n)) =
      native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `char`. -/
@[simp] theorem eo_to_smt_type_char :
    __eo_to_smt_type (Term.UOp UserOp.Char) = SmtType.Char := rfl

/-- Simplifies EO-to-SMT type translation for `reglan`. -/
@[simp] theorem eo_to_smt_type_reglan :
    __eo_to_smt_type (Term.UOp UserOp.RegLan) = SmtType.RegLan := rfl

/-- Simplifies EO-to-SMT type translation for `seq`. -/
@[simp] theorem eo_to_smt_type_seq (T : Term) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) =
      __smtx_typeof_guard (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `array`. -/
@[simp] theorem eo_to_smt_type_array (A B : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) A) B) =
      __smtx_typeof_guard (__eo_to_smt_type A)
        (__smtx_typeof_guard (__eo_to_smt_type B)
          (SmtType.Map (__eo_to_smt_type A) (__eo_to_smt_type B))) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `set`. -/
@[simp] theorem eo_to_smt_type_set (T : Term) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
      __smtx_typeof_guard (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) := by
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
  unfold __smtx_typeof at h ⊢
  exact smtx_typeof_guard_wf_of_non_none T T h

/-- Computes `__smtx_typeof` for `uconst_of_non_none`. -/
theorem smtx_typeof_uconst_of_non_none
    (s : native_String) (T : SmtType) :
    __smtx_typeof (SmtTerm.UConst s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.UConst s T) = T := by
  intro h
  unfold __smtx_typeof at h ⊢
  exact smtx_typeof_guard_wf_of_non_none T T h

/-- Computes `__smtx_typeof` for `seq_empty_of_non_none`. -/
theorem smtx_typeof_seq_empty_of_non_none
    (T : SmtType) :
    __smtx_typeof (SmtTerm.seq_empty T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq T := by
  intro h
  unfold __smtx_typeof at h ⊢
  exact smtx_typeof_guard_wf_of_non_none T (SmtType.Seq T) h

/-- Computes `__smtx_typeof` for `set_empty_of_non_none`. -/
theorem smtx_typeof_set_empty_of_non_none
    (T : SmtType) :
    __smtx_typeof (SmtTerm.set_empty T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.set_empty T) = SmtType.Set T := by
  intro h
  unfold __smtx_typeof at h ⊢
  exact smtx_typeof_guard_wf_of_non_none T (SmtType.Set T) h

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
    cases h' : g with
    | false =>
        exfalso
        apply h
        unfold __smtx_typeof
        simp [g, native_ite, h']
    | true =>
        rfl
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
  have hAnd :
      native_and (native_zleq 0 w)
        (native_zeq n (native_mod_total n (native_int_pow2 w))) = true := by
    simp [SmtEval.native_and, hWidth, hMod]
  unfold __smtx_typeof
  simp [hAnd, native_ite]

end TranslationProofs
