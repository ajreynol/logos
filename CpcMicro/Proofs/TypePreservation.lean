import CpcMicro.Proofs.TypePreservation.Support
import CpcMicro.Proofs.TypePreservation.CoreArith
import CpcMicro.Proofs.TypePreservation.Datatypes

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Derives `inhabited_type` from `guard_inhabited_self_non_none`. -/
theorem inhabited_type_of_guard_inhabited_self_non_none
    {T : SmtType}
    (ht : __smtx_typeof_guard_inhabited T T ≠ SmtType.None) :
    type_inhabited T := by
  cases h : native_inhabited_type T
  · simp [__smtx_typeof_guard_inhabited, native_ite, h] at ht
  · exact (smtx_inhabited_type_eq_true_iff T).mp h

/-- Derives `var_type_inhabited` from `non_none`. -/
theorem var_type_inhabited_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.Var s T)) :
    type_inhabited T := by
  exact inhabited_type_of_guard_inhabited_self_non_none
    (by simpa [term_has_non_none_type, __smtx_typeof] using ht)

/-- Derives `uconst_type_inhabited` from `non_none`. -/
theorem uconst_type_inhabited_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.UConst s T)) :
    type_inhabited T := by
  exact inhabited_type_of_guard_inhabited_self_non_none
    (by simpa [term_has_non_none_type, __smtx_typeof] using ht)

/-- Derives `not_arg_bool` from `non_none`. -/
theorem not_arg_bool_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.not t)) :
    __smtx_typeof t = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht
  rfl

/-- Shows that a well-typed generic application has well-typed children. -/
theorem generic_apply_children_non_none
    {f x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hTy : generic_apply_type f x) :
    term_has_non_none_type f ∧ term_has_non_none_type x := by
  have hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    intro hNone
    apply ht
    unfold generic_apply_type at hTy
    rw [hTy]
    exact hNone
  rcases typeof_apply_non_none_cases hNN with ⟨A, B, hF, hX, hA, _hB⟩
  constructor
  · unfold term_has_non_none_type
    cases hF with
    | inl hMap =>
        rw [hMap]
        simp
    | inr hFun =>
        rw [hFun]
        simp
  · unfold term_has_non_none_type
    rw [hX]
    exact hA

/-- Builds the supported-preservation witness for any SMT term whose type is not `None`. -/
private theorem supported_preservation_term_of_non_none :
    ∀ (t : SmtTerm), term_has_non_none_type t -> supported_preservation_term t
  | SmtTerm.None, ht => by
      exact False.elim (ht rfl)
  | SmtTerm.Boolean b, _ => by
      exact supported_preservation_term.boolean b
  | SmtTerm.Numeral n, _ => by
      exact supported_preservation_term.numeral n
  | SmtTerm.Rational q, _ => by
      exact supported_preservation_term.rational q
  | SmtTerm.String s, _ => by
      exact supported_preservation_term.string s
  | SmtTerm.Binary w n, _ => by
      exact supported_preservation_term.binary w n
  | SmtTerm.not t, ht => by
      have htxTy : __smtx_typeof t = SmtType.Bool :=
        not_arg_bool_of_non_none ht
      have htx : term_has_non_none_type t := by
        unfold term_has_non_none_type
        rw [htxTy]
        simp
      exact supported_preservation_term.not htx
        (supported_preservation_term_of_non_none t htx)
  | SmtTerm.or t1 t2, ht => by
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl ht
      have ht1 : term_has_non_none_type t1 := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      have ht2 : term_has_non_none_type t2 := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        simp
      exact supported_preservation_term.or ht1
        (supported_preservation_term_of_non_none t1 ht1)
        ht2
        (supported_preservation_term_of_non_none t2 ht2)
  | SmtTerm.and t1 t2, ht => by
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl ht
      have ht1 : term_has_non_none_type t1 := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      have ht2 : term_has_non_none_type t2 := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        simp
      exact supported_preservation_term.and ht1
        (supported_preservation_term_of_non_none t1 ht1)
        ht2
        (supported_preservation_term_of_non_none t2 ht2)
  | SmtTerm.imp t1 t2, ht => by
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl ht
      have ht1 : term_has_non_none_type t1 := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      have ht2 : term_has_non_none_type t2 := by
        unfold term_has_non_none_type
        rw [hArgs.2]
        simp
      exact supported_preservation_term.imp ht1
        (supported_preservation_term_of_non_none t1 ht1)
        ht2
        (supported_preservation_term_of_non_none t2 ht2)
  | SmtTerm.Apply f x, ht => by
      cases supported_preservation_apply_cases f x with
      | eq_case t1 =>
          subst_vars
          exact supported_preservation_term.eq t1 x
      | ite_case c t1 =>
          subst_vars
          rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
          have htc : term_has_non_none_type c := by
            unfold term_has_non_none_type
            rw [hc]
            simp
          have ht1 : term_has_non_none_type t1 := by
            unfold term_has_non_none_type
            rw [h1]
            exact hT
          have ht2 : term_has_non_none_type x := by
            unfold term_has_non_none_type
            rw [h2]
            exact hT
          exact supported_preservation_term.ite htc
            (supported_preservation_term_of_non_none c htc)
            ht1
            (supported_preservation_term_of_non_none t1 ht1)
            ht2
            (supported_preservation_term_of_non_none x ht2)
      | exists_case s T =>
          subst_vars
          exact supported_preservation_term.exists s T x
      | forall_case s T =>
          subst_vars
          exact supported_preservation_term.forall s T x
      | choice_case s T =>
          subst_vars
          exact supported_preservation_term.choice s T x
      | generic hTy hEval =>
          subst_vars
          rcases generic_apply_children_non_none ht hTy with ⟨htf, htx⟩
          exact supported_preservation_term.apply hTy hEval htf
            (supported_preservation_term_of_non_none f htf)
            htx
            (supported_preservation_term_of_non_none x htx)
  | SmtTerm.Var s T, ht => by
      exact supported_preservation_term.var s T
        (var_type_inhabited_of_non_none ht)
  | SmtTerm.ite, ht => by
      exact False.elim (ht rfl)
  | SmtTerm.eq, ht => by
      exact False.elim (ht rfl)
  | SmtTerm.exists s T, ht => by
      exact False.elim (ht rfl)
  | SmtTerm.forall s T, ht => by
      exact False.elim (ht rfl)
  | SmtTerm.choice s T, ht => by
      exact False.elim (ht rfl)
  | SmtTerm.UConst s T, ht => by
      exact supported_preservation_term.uconst s T
        (uconst_type_inhabited_of_non_none ht)
termination_by t _ => sizeOf t
decreasing_by
  all_goals
    subst_vars
    simp_wf
  all_goals
    omega

/-- Proves type preservation for SMT terms covered by `supported_preservation_term`. -/
private theorem supported_type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  cases hs with
  | boolean b =>
      exact typeof_value_model_eval_boolean M b
  | numeral n =>
      exact typeof_value_model_eval_numeral M n
  | rational q =>
      exact typeof_value_model_eval_rational M q
  | string s =>
      exact typeof_value_model_eval_string M s
  | binary w n =>
      exact typeof_value_model_eval_binary M w n ht
  | var s T hT =>
      exact typeof_value_model_eval_var M hM s T hT
  | uconst s T hT =>
      exact typeof_value_model_eval_uconst M hM s T hT
  | ite htc hsc ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_ite M _ _ _ ht
        (supported_type_preservation M hM _ htc hsc)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «exists» s T body =>
      exact typeof_value_model_eval_exists M s T body ht
  | «forall» s T body =>
      exact typeof_value_model_eval_forall M s T body ht
  | choice s T body =>
      exact typeof_value_model_eval_choice M s T body ht
  | «not» ht1 hs1 =>
      exact typeof_value_model_eval_not M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | «or» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_or M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «and» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_and M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «imp» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_imp M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | eq t1 t2 =>
      exact typeof_value_model_eval_eq M t1 t2 ht
  | @apply f x hTy hEval htf hsf htx hsx =>
      have hTy' :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTy']
        exact hNone
      rw [hEval M, hTy']
      exact typeof_value_model_eval_apply_generic M f x hNN
        (supported_type_preservation M hM f htf hsf)
        (supported_type_preservation M hM x htx hsx)

/-- Main type-preservation theorem for evaluation of non-`None` SMT terms in total typed models. -/
theorem type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  exact supported_type_preservation M hM t ht
    (supported_preservation_term_of_non_none t ht)

/-- Shows that evaluating a Boolean-typed SMT term yields a Boolean value in a total typed model. -/
theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
  __smtx_typeof t = SmtType.Bool ->
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool := by
    simpa [hTy] using type_preservation M hM t hNN
  exact bool_value_canonical hPres

/-- Shows that total typed SMT models exist. -/
theorem total_typed_model_nonvacuous :
    ∃ M : SmtModel, model_total_typed M :=
  exists_total_typed_model

end Smtm
