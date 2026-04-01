import CpcMini.Spec

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

@[simp] theorem eo_to_smt_boolean (b : eo_lit_Bool) :
    __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_var (s : eo_lit_String) (T : Term) :
    __eo_to_smt (Term.Var s T) = SmtTerm.Var s (__eo_to_smt_type T) := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_uconst (i : eo_lit_Nat) (T : Term) :
    __eo_to_smt (Term.UConst i T) = SmtTerm.UConst (smt_lit_uconst_id i) (__eo_to_smt_type T) := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_type_bool :
    __eo_to_smt_type Term.Bool = SmtType.Bool := rfl

@[simp] theorem eo_to_smt_type_int :
    __eo_to_smt_type Term.Int = SmtType.Int := rfl

@[simp] theorem eo_to_smt_type_real :
    __eo_to_smt_type Term.Real = SmtType.Real := rfl

@[simp] theorem eo_to_smt_type_bitvec (n : eo_lit_Int) :
    __eo_to_smt_type (Term.Apply Term.BitVec (Term.Numeral n)) = SmtType.BitVec n := by
  simp [__eo_to_smt_type]

@[simp] theorem eo_to_smt_type_char :
    __eo_to_smt_type Term.Char = SmtType.Char := rfl

@[simp] theorem eo_to_smt_type_seq (T : Term) :
    __eo_to_smt_type (Term.Apply Term.Seq T) = SmtType.Seq (__eo_to_smt_type T) := by
  simp [__eo_to_smt_type]

theorem smtx_typeof_guard_inhabited_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_inhabited T U ≠ SmtType.None ->
    __smtx_typeof_guard_inhabited T U = U := by
  intro h
  unfold __smtx_typeof_guard_inhabited at h ⊢
  cases hInh : smt_lit_inhabited_type T <;> simp [smt_lit_ite, hInh] at h ⊢

theorem smtx_typeof_var_of_non_none
    (s : smt_lit_String) (T : SmtType) :
    __smtx_typeof (SmtTerm.Var s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.Var s T) = T := by
  intro h
  change __smtx_typeof_guard_inhabited T T = T
  exact smtx_typeof_guard_inhabited_of_non_none T T (by simpa [__smtx_typeof] using h)

theorem smtx_typeof_uconst_of_non_none
    (s : smt_lit_String) (T : SmtType) :
    __smtx_typeof (SmtTerm.UConst s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.UConst s T) = T := by
  intro h
  change __smtx_typeof_guard_inhabited T T = T
  exact smtx_typeof_guard_inhabited_of_non_none T T (by simpa [__smtx_typeof] using h)

theorem smtx_binary_well_formed_of_non_none
    (w n : smt_lit_Int) :
    __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None ->
    smt_lit_zleq 0 w = true ∧
      smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)) = true := by
  intro h
  let g :=
    smt_lit_and (smt_lit_zleq 0 w)
      (smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)))
  have hg : g = true := by
    by_cases h' : g = true
    · exact h'
    · exfalso
      apply h
      change smt_lit_ite g (SmtType.BitVec w) SmtType.None = SmtType.None
      simp [smt_lit_ite, h']
  have hWidth : smt_lit_zleq 0 w = true := by
    cases hw : smt_lit_zleq 0 w <;> simp [g, SmtEval.smt_lit_and, hw] at hg
    rfl
  have hMod : smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)) = true := by
    cases hm : smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)) <;>
      simp [g, SmtEval.smt_lit_and, hWidth, hm] at hg
    rfl
  exact ⟨hWidth, hMod⟩

theorem smtx_typeof_binary_of_non_none
    (w n : smt_lit_Int) :
    __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec w := by
  intro h
  obtain ⟨hWidth, hMod⟩ := smtx_binary_well_formed_of_non_none w n h
  simp [__smtx_typeof, smt_lit_ite, SmtEval.smt_lit_and, hWidth, hMod]

end TranslationProofs
