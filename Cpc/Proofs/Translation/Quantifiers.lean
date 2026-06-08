import Cpc.Proofs.Translation.Base

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `exists_nil`. -/
@[simp] theorem eo_to_smt_exists_nil (F : SmtTerm) :
    __eo_to_smt_exists Term.__eo_List_nil F = F := rfl

/-- Simplifies EO-to-SMT translation for `exists_cons`. -/
@[simp] theorem eo_to_smt_exists_cons
    (s : native_String) (T vs : Term) (F : SmtTerm) :
    __eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs) F =
      SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists vs F) := by
  rfl

/-- Simplifies `exists_cons` when the translated binder type is well formed. -/
theorem eo_to_smt_exists_cons_of_type_wf
    (s : native_String) (T vs : Term) (F : SmtTerm)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    __eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) vs) F =
      SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists vs F) := by
  exact eo_to_smt_exists_cons s T vs F

/-- Simplifies the term-level helper for `quantifiers_skolemize` on `forall`. -/
@[simp] theorem eo_to_smt_quantifiers_skolemize_forall
    (xs body : Term) (n : native_Nat) :
    __eo_to_smt_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) n =
      __eo_to_smt_qs_choice
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body)) n := by
  simp [__eo_to_smt_quantifiers_skolemize]

end TranslationProofs
