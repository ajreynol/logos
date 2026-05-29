import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

private theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq] at h'
  rcases h' with ⟨hxy, hxOk, _hz⟩
  subst y
  simp [__eo_requires, native_ite, native_teq, hxOk]

private axiom str_indexof_re_eval_side_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (s r n m : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m))
    (hProgNe :
      __eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m) ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)) =
      __smtx_model_eval M (__eo_to_smt m)

private theorem str_indexof_re_eval_valid_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s r n m : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m))
    (hProgNe :
      __eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m) ≠ Term.Stuck)
    (hProgTy :
      __eo_typeof
        (__eo_prog_str_indexof_re_eval
          (Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
            m)) =
        Term.Bool) :
    StepRuleProperties M []
      (__eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m)) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n
  let body := Term.Apply (Term.Apply Term.eq lhs) m
  let lenTerm := __eo_len s
  let tail := __eo_extract s n lenTerm
  let matchTerm :=
    __eo_requires (__eo_is_str tail) (Term.Boolean true)
      (__str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (Term.Numeral 0))
  let idxTerm := __pair_first matchTerm
  let side :=
    __eo_ite (__eo_or (__eo_gt n lenTerm) (__eo_is_neg n))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
        (Term.Numeral (-1 : native_Int))
        (__eo_add n idxTerm))
  have hReqEq : __eo_requires side m body = body := by
    change __eo_requires side m body ≠ Term.Stuck at hProgNe
    exact eo_requires_result_eq_of_ne_stuck side m body hProgNe
  have hBodyTy : __eo_typeof body = Term.Bool := by
    change __eo_typeof (__eo_requires side m body) = Term.Bool at hProgTy
    rw [hReqEq] at hProgTy
    exact hProgTy
  change StepRuleProperties M [] (__eo_requires side m body)
  rw [hReqEq]
  have hBool : RuleProofs.eo_has_bool_type body :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type body hArgTrans hBodyTy
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type body hBool⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M lhs m hBool <| by
    have hEval :=
      str_indexof_re_eval_side_model_eval M hM s r n m hArgTrans hProgNe
    rw [hEval]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt m))

end RuleProofs

theorem cmd_step_str_indexof_re_eval_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_re_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_re_eval args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_re_eval args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_indexof_re_eval args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp m =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply idxApp n =>
                                  cases idxApp with
                                  | Apply idxApp2 r =>
                                      cases idxApp2 with
                                      | Apply idxOp sArg =>
                                          cases idxOp with
                                          | UOp idxOpName =>
                                              cases idxOpName with
                                              | str_indexof_re =>
                                                  have hProps :=
                                                    RuleProofs.str_indexof_re_eval_valid_properties
                                                      M hM sArg r n m (by
                                                        simpa using hA1Trans) (by
                                                        change
                                                          __eo_prog_str_indexof_re_eval
                                                            (Term.Apply
                                                              (Term.Apply Term.eq
                                                                (Term.Apply
                                                                  (Term.Apply
                                                                    (Term.Apply Term.str_indexof_re
                                                                      sArg) r) n))
                                                              m) ≠
                                                            Term.Stuck at hProg
                                                        exact hProg) (by
                                                        change
                                                          __eo_typeof
                                                            (__eo_prog_str_indexof_re_eval
                                                              (Term.Apply
                                                                (Term.Apply Term.eq
                                                                  (Term.Apply
                                                                    (Term.Apply
                                                                      (Term.Apply Term.str_indexof_re
                                                                        sArg) r) n))
                                                                m)) =
                                                            Term.Bool at hResultTy
                                                        exact hResultTy)
                                                  change StepRuleProperties M []
                                                    (__eo_prog_str_indexof_re_eval
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply
                                                            (Term.Apply
                                                              (Term.Apply Term.str_indexof_re
                                                                sArg) r) n))
                                                        m))
                                                  simpa [premiseTermList] using hProps
                                              | _ =>
                                                  change Term.Stuck ≠ Term.Stuck at hProg
                                                  exact False.elim (hProg rfl)
                                          | _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
