import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Closed.UOpIndices

open Eo
open SmtEval
open Smtm
open TranslationProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/--
Bridge from the native standalone-closed checker to the Logos closedness checker.

This is the theorem that lets opaque UOp indices reuse the existing closed-term
SMT evaluator invariants. Its proof should proceed by relating the native
`List Term` environment in `native_eo_to_smt_closed_rec` with the EO list
environment consumed by `__eo_is_closed_rec`.
-/
private theorem native_eo_to_smt_closed_implies_eo_is_closed
    (t : Term)
    (hClosed : native_eo_to_smt_closed t = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe t) :
    __eo_is_closed t = Term.Boolean true := by
  sorry

private theorem smtx_model_eval_eq_push_of_native_closed_safe
    (M : SmtModel) (F : Term) (s : native_String) (T : SmtType)
    (v : SmtValue)
    (hClosed : native_eo_to_smt_closed F = true)
    (hSafe : NativeEoToSmtUOpIndicesSafe F) :
    __smtx_model_eval (native_model_push M s T v) (__eo_to_smt F) =
      __smtx_model_eval M (__eo_to_smt F) := by
  have hEoClosed :=
    native_eo_to_smt_closed_implies_eo_is_closed F hClosed hSafe
  exact
    (smt_model_eval_eq_of_eo_closed F hEoClosed M
      (native_model_push M s T v)
      (model_agrees_on_globals_push M s T v)).symm

/--
If `contains_atomic_term` says an EO body does not mention a binder variable,
then changing only that SMT variable assignment does not change the evaluation
of the translated body.

The `NativeEoToSmtUOpIndicesSafe` hypothesis is the bridge that makes the Logos
syntactic check sound for indexed operators: opaque indices cannot hide an
occurrence of the binder because every UOp index is standalone closed.
-/
theorem smtx_model_eval_eq_push_of_contains_atomic_term_false
    (M : SmtModel) (F : Term) (s : native_String) (T : Term)
    (v : SmtValue)
    (hTWF : smtx_type_field_wf_rec (__eo_to_smt_type T) native_reflist_nil)
    (hNoOccur :
      __contains_atomic_term F (Term.Var (Term.String s) T) =
        Term.Boolean false)
    (hSafe : NativeEoToSmtUOpIndicesSafe F) :
    __smtx_model_eval
        (native_model_push M s (__eo_to_smt_type T) v)
        (__eo_to_smt F) =
      __smtx_model_eval M (__eo_to_smt F) := by
  sorry

/--
Semantic core for `quant_unused_vars`: rebuilding the quantifier with
`__mk_quant_unused_vars_rec` preserves the translated SMT evaluation.

This is intentionally phrased below the checker-rule layer. The proof should be
by induction over the EO binder list, using
`smtx_model_eval_eq_push_of_contains_atomic_term_false` for dropped binders and
the usual shadowing/idempotence lemmas for duplicate binders.
-/
theorem smtx_model_eval_quant_unused_vars_mk_core
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F : Term)
    (hQ :
      Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply Q x) F))
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F)))
    (hSafe :
      NativeEoToSmtUOpIndicesSafe
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply Q x) F))
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F))) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply Q x) F)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F)) := by
  sorry
