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
      native_ite (__eo_reserved_var_name s) SmtTerm.None
        (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists vs F)) := rfl

/-- Simplifies EO-to-SMT translation for `quantifiers_skolemize_zero`. -/
@[simp] theorem eo_to_smt_quantifiers_skolemize_zero
    (s : native_String) (T : SmtType) (F : SmtTerm) :
    __eo_to_smt_quantifiers_skolemize (SmtTerm.exists s T F) 0 =
      SmtTerm.choice_nth s T F 0 := by
  simp [__eo_to_smt_quantifiers_skolemize]

end TranslationProofs
