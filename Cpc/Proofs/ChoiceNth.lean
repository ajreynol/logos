import Cpc.SmtModel

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- The zeroth choice helper evaluates the current choice. -/
theorem native_eval_tchoice_nth_zero
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm) :
    native_eval_tchoice_nth M s T body native_nat_zero =
      native_eval_tchoice M s T body := by
  change __smtx_model_eval.native_eval_tchoice_nth M s T body native_nat_zero =
    native_eval_tchoice M s T body
  rw [__smtx_model_eval.native_eval_tchoice_nth.eq_1]

/-- A successor choice helper descends through one leading existential. -/
theorem native_eval_tchoice_nth_succ
    (M : SmtModel) (s : native_String) (T : SmtType)
    (body : SmtTerm) (n : native_Nat) :
    native_eval_tchoice_nth M s T body (native_nat_succ n) =
      let v := native_eval_tchoice M s T body
      match body with
      | SmtTerm.exists s' T' body' =>
          native_eval_tchoice_nth (native_model_push M s T v) s' T' body' n
      | _ => SmtValue.NotValue := by
  change __smtx_model_eval.native_eval_tchoice_nth M s T body (native_nat_succ n) =
    let v := native_eval_tchoice M s T body
    match body with
    | SmtTerm.exists s' T' body' =>
        native_eval_tchoice_nth (native_model_push M s T v) s' T' body' n
    | _ => SmtValue.NotValue
  rw [__smtx_model_eval.native_eval_tchoice_nth.eq_def]
  cases body <;> simp [native_eval_tchoice_nth]

/-- Evaluating the zeroth `choice_nth` selects the first choice witness. -/
theorem smtx_model_eval_choice_nth_zero
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_model_eval M (SmtTerm.choice_nth s T body native_nat_zero) =
      native_eval_tchoice M s T body := by
  rw [__smtx_model_eval.eq_137,
    __smtx_model_eval.native_eval_tchoice_nth.eq_1]

/-- Evaluating a successor `choice_nth` descends through one leading existential. -/
theorem smtx_model_eval_choice_nth_succ
    (M : SmtModel) (s : native_String) (T : SmtType)
    (body : SmtTerm) (n : native_Nat) :
    __smtx_model_eval M (SmtTerm.choice_nth s T body (native_nat_succ n)) =
      let v := native_eval_tchoice M s T body
      match body with
      | SmtTerm.exists s' T' body' =>
          __smtx_model_eval (native_model_push M s T v)
            (SmtTerm.choice_nth s' T' body' n)
      | _ => SmtValue.NotValue := by
  rw [__smtx_model_eval.eq_137]
  rw [__smtx_model_eval.native_eval_tchoice_nth.eq_def]
  cases body <;> simp [__smtx_model_eval.eq_137]

/-- Specialized successor equation for the existential branch. -/
theorem smtx_model_eval_choice_nth_succ_exists
    (M : SmtModel) (s : native_String) (T : SmtType)
    (s' : native_String) (T' : SmtType) (body' : SmtTerm)
    (n : native_Nat) :
    __smtx_model_eval M
        (SmtTerm.choice_nth s T (SmtTerm.exists s' T' body') (native_nat_succ n)) =
      __smtx_model_eval
        (native_model_push M s T
          (native_eval_tchoice M s T (SmtTerm.exists s' T' body')))
        (SmtTerm.choice_nth s' T' body' n) := by
  simpa using
    smtx_model_eval_choice_nth_succ
      (M := M) (s := s) (T := T)
      (body := SmtTerm.exists s' T' body') (n := n)

end Smtm
