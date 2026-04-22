import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Translation.Quantifiers

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool := by
  simp [TranslationProofs.smtx_typeof_none]

private theorem eo_to_smt_exists_body_bool_of_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body = SmtType.Bool := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    simpa [__eo_to_smt_exists] using hTy
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            exact eo_to_smt_exists_body_bool_of_bool a body hSub
          all_goals
            subst hname
            have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            exact False.elim (smtx_typeof_none_ne_bool hNone)
        all_goals
          subst hy
          have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
            simpa [__eo_to_smt_exists] using hTy
          exact False.elim (smtx_typeof_none_ne_bool hNone)
      all_goals
        subst hg
        have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
          simpa [__eo_to_smt_exists] using hTy
        exact False.elim (smtx_typeof_none_ne_bool hNone)
    all_goals
      subst hf
      have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
        simpa [__eo_to_smt_exists] using hTy
      exact False.elim (smtx_typeof_none_ne_bool hNone)
  all_goals
    subst hxs
    have hNone : __smtx_typeof SmtTerm.None = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    exact False.elim (smtx_typeof_none_ne_bool hNone)

private theorem smtx_model_eval_eo_to_smt_exists_double_not_body
    (M : SmtModel) (hM : model_total_typed M)
    (xs : Term) (body : SmtTerm)
    (hBody : __smtx_typeof body = SmtType.Bool) :
    __smtx_model_eval M (__eo_to_smt_exists xs (SmtTerm.not (SmtTerm.not body))) =
      __smtx_model_eval M (__eo_to_smt_exists xs body) := by
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    rcases smt_model_eval_bool_is_boolean M hM body hBody with ⟨b, hb⟩
    simp [__eo_to_smt_exists, __smtx_model_eval, hb, __smtx_model_eval_not,
      SmtEval.native_not]
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            classical
            let P : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_model_eval (__smtx_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a (SmtTerm.not (SmtTerm.not body))) =
                    SmtValue.Boolean true
            let Q : Prop :=
              ∃ v : SmtValue,
                __smtx_typeof_value v = __eo_to_smt_type T ∧
                  __smtx_model_eval (__smtx_model_push M s (__eo_to_smt_type T) v)
                    (__eo_to_smt_exists a body) = SmtValue.Boolean true
            have hPQ : P ↔ Q := by
              constructor
              · intro hSat
                rcases hSat with ⟨v, hv, hEval⟩
                refine ⟨v, hv, ?_⟩
                have hRec :=
                    smtx_model_eval_eo_to_smt_exists_double_not_body
                      (__smtx_model_push M s (__eo_to_smt_type T) v)
                      (model_total_typed_push hM s (__eo_to_smt_type T) v hv)
                      a body hBody
                rw [hRec] at hEval
                exact hEval
              · intro hSat
                rcases hSat with ⟨v, hv, hEval⟩
                refine ⟨v, hv, ?_⟩
                have hRec :=
                    smtx_model_eval_eo_to_smt_exists_double_not_body
                      (__smtx_model_push M s (__eo_to_smt_type T) v)
                      (model_total_typed_push hM s (__eo_to_smt_type T) v hv)
                      a body hBody
                rw [← hRec] at hEval
                exact hEval
            have hPropEq : P = Q := propext hPQ
            simp [P, Q, __eo_to_smt_exists, __smtx_model_eval, hPropEq]
          all_goals
            subst hname
            simp [__eo_to_smt_exists, __smtx_model_eval]
        all_goals
          subst hy
          simp [__eo_to_smt_exists, __smtx_model_eval]
      all_goals
        subst hg
        simp [__eo_to_smt_exists, __smtx_model_eval]
    all_goals
      subst hf
      simp [__eo_to_smt_exists, __smtx_model_eval]
  all_goals
    subst hxs
    simp [__eo_to_smt_exists, __smtx_model_eval]

theorem cmd_step_exists_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.exists_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.exists_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.exists_elim args premises) :=
by
  sorry
