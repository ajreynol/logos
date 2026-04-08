import Cpc.Proofs.Translation.Base

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `is_var_self`. -/
@[simp] theorem eo_to_smt_is_var_self (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt_is_var s T (SmtTerm.Var s T) = true := by
  simp [__eo_to_smt_is_var, smt_lit_and, smt_lit_Teq, SmtEval.smt_lit_and,
    SmtEval.smt_lit_streq]

/-- Simplifies EO-to-SMT translation for `is_binder_x_exists`. -/
@[simp] theorem eo_to_smt_is_binder_x_exists (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt_is_binder_x s T (SmtTerm.exists s T) = true := by
  simp [__eo_to_smt_is_binder_x]

/-- Simplifies EO-to-SMT translation for `is_binder_x_forall`. -/
@[simp] theorem eo_to_smt_is_binder_x_forall (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt_is_binder_x s T (SmtTerm.forall s T) = true := by
  simp [__eo_to_smt_is_binder_x]

/-- Simplifies EO-to-SMT translation for `is_binder_x_choice`. -/
@[simp] theorem eo_to_smt_is_binder_x_choice (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt_is_binder_x s T (SmtTerm.choice s T) = true := by
  simp [__eo_to_smt_is_binder_x]

/-- Simplifies EO-to-SMT translation for `substitute_var_hit`. -/
@[simp] theorem eo_to_smt_substitute_var_hit
    (s : smt_lit_String) (T : SmtType) (u : SmtTerm) :
    __eo_to_smt_substitute s T u (SmtTerm.Var s T) = u := by
  simp [__eo_to_smt_substitute, smt_lit_ite]

/-- Simplifies EO-to-SMT translation for `substitute_var_miss`. -/
theorem eo_to_smt_substitute_var_miss
    (s1 s2 : smt_lit_String) (T1 T2 : SmtType) (u : SmtTerm) :
    s1 ≠ s2 ∨ T1 ≠ T2 ->
    __eo_to_smt_substitute s1 T1 u (SmtTerm.Var s2 T2) = SmtTerm.Var s2 T2 := by
  intro h
  cases h with
  | inl hs =>
      have hVar : __eo_to_smt_is_var s1 T1 (SmtTerm.Var s2 T2) = false := by
        simp [__eo_to_smt_is_var, smt_lit_and, smt_lit_Teq, SmtEval.smt_lit_and,
          SmtEval.smt_lit_streq, hs]
      simp [__eo_to_smt_substitute, smt_lit_ite, hVar]
  | inr hT =>
      have hVar : __eo_to_smt_is_var s1 T1 (SmtTerm.Var s2 T2) = false := by
        simp [__eo_to_smt_is_var, smt_lit_and, smt_lit_Teq, SmtEval.smt_lit_and,
          SmtEval.smt_lit_streq, hT]
      simp [__eo_to_smt_substitute, smt_lit_ite, hVar]

/-- Simplifies EO-to-SMT translation for `exists_nil`. -/
@[simp] theorem eo_to_smt_exists_nil (F : SmtTerm) :
    __eo_to_smt_exists Term.__eo_List_nil F = F := rfl

/-- Simplifies EO-to-SMT translation for `exists_cons`. -/
@[simp] theorem eo_to_smt_exists_cons
    (s : eo_lit_String) (T vs : Term) (F : SmtTerm) :
    __eo_to_smt_exists (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var s T)) vs) F =
      SmtTerm.Apply (SmtTerm.exists s (__eo_to_smt_type T)) (__eo_to_smt_exists vs F) := rfl

/-- Simplifies EO-to-SMT translation for `quantifiers_skolemize_zero`. -/
@[simp] theorem eo_to_smt_quantifiers_skolemize_zero
    (s : smt_lit_String) (T : SmtType) (F : SmtTerm) :
    __eo_to_smt_quantifiers_skolemize (SmtTerm.Apply (SmtTerm.exists s T) F) 0 =
      SmtTerm.Apply (SmtTerm.choice s T) F := by
  simp [__eo_to_smt_quantifiers_skolemize]

end TranslationProofs
