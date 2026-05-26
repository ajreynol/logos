import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_re_allchar_eq :
    __eo_to_smt (Term.UOp UserOp.re_allchar) = SmtTerm.re_allchar := by
  rfl

private theorem eo_to_smt_re_none_eq :
    __eo_to_smt (Term.UOp UserOp.re_none) = SmtTerm.re_none := by
  rfl

private theorem eo_to_smt_re_all_eq :
    __eo_to_smt (Term.UOp UserOp.re_all) = SmtTerm.re_all := by
  rfl

private theorem eo_to_smt_str_to_re_eq (s : native_String) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String s)) =
      SmtTerm.str_to_re (SmtTerm.String s) := by
  rfl

private theorem eo_to_smt_re_mult_eq (r : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) r) =
      SmtTerm.re_mult (__eo_to_smt r) := by
  rfl

private theorem eo_to_smt_re_plus_eq (r : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.re_plus) r) =
      SmtTerm.re_plus (__eo_to_smt r) := by
  rfl

private theorem eo_to_smt_re_opt_eq (r : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.re_opt) r) =
      SmtTerm.re_opt (__eo_to_smt r) := by
  rfl

private theorem eo_to_smt_re_comp_eq (r : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.re_comp) r) =
      SmtTerm.re_comp (__eo_to_smt r) := by
  rfl

private theorem eo_to_smt_re_exp_eq (n r : Term) :
    __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp n) r) =
      SmtTerm.re_exp (__eo_to_smt n) (__eo_to_smt r) := by
  rfl

private theorem eo_to_smt_re_range_eq (lo hi : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) lo) hi) =
      SmtTerm.re_range (__eo_to_smt lo) (__eo_to_smt hi) := by
  rfl

private theorem eo_to_smt_re_concat_eq (r1 r2 : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2) =
      SmtTerm.re_concat (__eo_to_smt r1) (__eo_to_smt r2) := by
  rfl

private theorem eo_to_smt_re_inter_eq (r1 r2 : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) r1) r2) =
      SmtTerm.re_inter (__eo_to_smt r1) (__eo_to_smt r2) := by
  rfl

private theorem eo_to_smt_re_union_eq (r1 r2 : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) r1) r2) =
      SmtTerm.re_union (__eo_to_smt r1) (__eo_to_smt r2) := by
  rfl

private theorem eo_to_smt_re_diff_eq (r1 r2 : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) r1) r2) =
      SmtTerm.re_diff (__eo_to_smt r1) (__eo_to_smt r2) := by
  rfl

private theorem eo_to_smt_re_loop_eq (lo hi r : Term) :
    __eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) r) =
      SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi) (__eo_to_smt r) := by
  rfl

private theorem eo_to_smt_numeral_eq (n : native_Int) :
    __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n := by
  rfl

private theorem eo_to_smt_string_eq (s : native_String) :
    __eo_to_smt (Term.String s) = SmtTerm.String s := by
  rfl

private theorem eo_to_smt_str_indexof_re_eq (s r n : Term) :
    __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) r) n) =
      SmtTerm.str_indexof_re (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt n) := by
  rfl

private theorem eo_reglan_value_to_option_eq_some {v : SmtValue} {rr : native_RegLan} :
    __eo_reglan_value_to_option v = some rr ->
      v = SmtValue.RegLan rr := by
  intro h
  cases v <;> simp [__eo_reglan_value_to_option] at h ⊢
  assumption

private theorem eo_eval_regex_sound
    (M : SmtModel) (r : Term) (rr : native_RegLan)
    (h : __eo_eval_regex r = some rr) :
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rr := by
  cases r with
  | UOp op =>
      cases op <;> simp [__eo_eval_regex] at h
      · rw [eo_to_smt_re_allchar_eq, __smtx_model_eval.eq_103]
        change SmtValue.RegLan native_re_allchar = SmtValue.RegLan rr
        simpa using h
      · rw [eo_to_smt_re_none_eq, __smtx_model_eval.eq_104]
        change SmtValue.RegLan native_re_none = SmtValue.RegLan rr
        simpa using h
      · rw [eo_to_smt_re_all_eq, __smtx_model_eval.eq_105]
        change SmtValue.RegLan native_re_all = SmtValue.RegLan rr
        simpa using h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try (simp [__eo_eval_regex] at h)
          case str_to_re =>
            cases x with
            | String s =>
                have hOpt :
                    __eo_reglan_value_to_option
                      (__smtx_model_eval_str_to_re (SmtValue.Seq (native_pack_string s))) =
                      some rr := by
                  simpa [__eo_eval_regex] using h
                rw [eo_to_smt_str_to_re_eq, __smtx_model_eval.eq_106,
                  __smtx_model_eval.eq_4]
                change __smtx_model_eval_str_to_re (SmtValue.Seq (native_pack_string s)) =
                  SmtValue.RegLan rr
                exact eo_reglan_value_to_option_eq_some hOpt
            | _ => simp [__eo_eval_regex] at h
          case re_mult =>
            cases hr : __eo_eval_regex x with
            | none => simp [__eo_eval_regex, hr] at h
            | some rx =>
                have hOpt :
                    __eo_reglan_value_to_option
                      (__smtx_model_eval_re_mult (SmtValue.RegLan rx)) = some rr := by
                  simpa [__eo_eval_regex, hr] using h
                have hx := eo_eval_regex_sound M x rx hr
                rw [eo_to_smt_re_mult_eq, __smtx_model_eval.eq_107]
                change __smtx_model_eval_re_mult (__smtx_model_eval M (__eo_to_smt x)) =
                  SmtValue.RegLan rr
                rw [hx]
                exact eo_reglan_value_to_option_eq_some hOpt
          case re_plus =>
            cases hr : __eo_eval_regex x with
            | none => simp [__eo_eval_regex, hr] at h
            | some rx =>
                have hOpt :
                    __eo_reglan_value_to_option
                      (__smtx_model_eval_re_plus (SmtValue.RegLan rx)) = some rr := by
                  simpa [__eo_eval_regex, hr] using h
                have hx := eo_eval_regex_sound M x rx hr
                rw [eo_to_smt_re_plus_eq, __smtx_model_eval.eq_108]
                change __smtx_model_eval_re_plus (__smtx_model_eval M (__eo_to_smt x)) =
                  SmtValue.RegLan rr
                rw [hx]
                exact eo_reglan_value_to_option_eq_some hOpt
          case re_opt =>
            cases hr : __eo_eval_regex x with
            | none => simp [__eo_eval_regex, hr] at h
            | some rx =>
                have hOpt :
                    __eo_reglan_value_to_option
                      (__smtx_model_eval_re_opt (SmtValue.RegLan rx)) = some rr := by
                  simpa [__eo_eval_regex, hr] using h
                have hx := eo_eval_regex_sound M x rx hr
                rw [eo_to_smt_re_opt_eq, __smtx_model_eval.eq_110]
                change __smtx_model_eval_re_opt (__smtx_model_eval M (__eo_to_smt x)) =
                  SmtValue.RegLan rr
                rw [hx]
                exact eo_reglan_value_to_option_eq_some hOpt
          case re_comp =>
            cases hr : __eo_eval_regex x with
            | none => simp [__eo_eval_regex, hr] at h
            | some rx =>
                have hOpt :
                    __eo_reglan_value_to_option
                      (__smtx_model_eval_re_comp (SmtValue.RegLan rx)) = some rr := by
                  simpa [__eo_eval_regex, hr] using h
                have hx := eo_eval_regex_sound M x rx hr
                rw [eo_to_smt_re_comp_eq, __smtx_model_eval.eq_111]
                change __smtx_model_eval_re_comp (__smtx_model_eval M (__eo_to_smt x)) =
                  SmtValue.RegLan rr
                rw [hx]
                exact eo_reglan_value_to_option_eq_some hOpt
      | UOp1 op n =>
          cases op <;> try (simp [__eo_eval_regex] at h)
          case re_exp =>
            cases n with
            | Numeral i =>
                cases hr : __eo_eval_regex x with
                | none => simp [__eo_eval_regex, hr] at h
                | some rx =>
                    have hOpt :
                        __eo_reglan_value_to_option
                          (__smtx_model_eval_re_exp (SmtValue.Numeral i)
                            (SmtValue.RegLan rx)) = some rr := by
                      simpa [__eo_eval_regex, hr] using h
                    have hx := eo_eval_regex_sound M x rx hr
                    rw [eo_to_smt_re_exp_eq, __smtx_model_eval.eq_109,
                      eo_to_smt_numeral_eq, __smtx_model_eval.eq_2]
                    change __smtx_model_eval_re_exp (SmtValue.Numeral i)
                        (__smtx_model_eval M (__eo_to_smt x)) =
                      SmtValue.RegLan rr
                    rw [hx]
                    exact eo_reglan_value_to_option_eq_some hOpt
            | _ => simp [__eo_eval_regex] at h
      | UOp2 op l u =>
          cases op <;> try (simp [__eo_eval_regex] at h)
          case re_loop =>
            cases l with
            | Numeral lo =>
                cases u with
                | Numeral hi =>
                    cases hr : __eo_eval_regex x with
                    | none => simp [__eo_eval_regex, hr] at h
                    | some rx =>
                        have hOpt :
                            __eo_reglan_value_to_option
                              (__smtx_model_eval_re_loop
                                (SmtValue.Numeral lo) (SmtValue.Numeral hi)
                                (SmtValue.RegLan rx)) = some rr := by
                          simpa [__eo_eval_regex, hr] using h
                        have hx := eo_eval_regex_sound M x rx hr
                        rw [eo_to_smt_re_loop_eq, __smtx_model_eval.eq_117,
                          eo_to_smt_numeral_eq, eo_to_smt_numeral_eq,
                          __smtx_model_eval.eq_2, __smtx_model_eval.eq_2]
                        change __smtx_model_eval_re_loop
                            (SmtValue.Numeral lo) (SmtValue.Numeral hi)
                            (__smtx_model_eval M (__eo_to_smt x)) =
                          SmtValue.RegLan rr
                        rw [hx]
                        exact eo_reglan_value_to_option_eq_some hOpt
                | _ => simp [__eo_eval_regex] at h
            | _ => simp [__eo_eval_regex] at h
      | Apply f₁ x₁ =>
          cases f₁ with
          | UOp op =>
              cases op <;> try (simp [__eo_eval_regex] at h)
              case re_range =>
                cases x₁ with
                | String lo =>
                    cases x with
                    | String hi =>
                        have hOpt :
                            __eo_reglan_value_to_option
                              (__smtx_model_eval_re_range
                                (SmtValue.Seq (native_pack_string lo))
                                (SmtValue.Seq (native_pack_string hi))) = some rr := by
                          simpa [__eo_eval_regex] using h
                        rw [eo_to_smt_re_range_eq, __smtx_model_eval.eq_112,
                          eo_to_smt_string_eq, eo_to_smt_string_eq,
                          __smtx_model_eval.eq_4, __smtx_model_eval.eq_4]
                        change __smtx_model_eval_re_range
                            (SmtValue.Seq (native_pack_string lo))
                            (SmtValue.Seq (native_pack_string hi)) =
                          SmtValue.RegLan rr
                        exact eo_reglan_value_to_option_eq_some hOpt
                    | _ => simp [__eo_eval_regex] at h
                | _ => simp [__eo_eval_regex] at h
              case re_concat =>
                cases hr1 : __eo_eval_regex x₁ with
                | none => simp [__eo_eval_regex, hr1] at h
                | some rx1 =>
                    cases hr2 : __eo_eval_regex x with
                    | none => simp [__eo_eval_regex, hr1, hr2] at h
                    | some rx2 =>
                        have hOpt :
                            __eo_reglan_value_to_option
                              (__smtx_model_eval_re_concat
                                (SmtValue.RegLan rx1) (SmtValue.RegLan rx2)) =
                                some rr := by
                          simpa [__eo_eval_regex, hr1, hr2] using h
                        have hx1 := eo_eval_regex_sound M x₁ rx1 hr1
                        have hx2 := eo_eval_regex_sound M x rx2 hr2
                        rw [eo_to_smt_re_concat_eq, __smtx_model_eval.eq_113]
                        change __smtx_model_eval_re_concat
                            (__smtx_model_eval M (__eo_to_smt x₁))
                            (__smtx_model_eval M (__eo_to_smt x)) =
                          SmtValue.RegLan rr
                        rw [hx1, hx2]
                        exact eo_reglan_value_to_option_eq_some hOpt
              case re_inter =>
                cases hr1 : __eo_eval_regex x₁ with
                | none => simp [__eo_eval_regex, hr1] at h
                | some rx1 =>
                    cases hr2 : __eo_eval_regex x with
                    | none => simp [__eo_eval_regex, hr1, hr2] at h
                    | some rx2 =>
                        have hOpt :
                            __eo_reglan_value_to_option
                              (__smtx_model_eval_re_inter
                                (SmtValue.RegLan rx1) (SmtValue.RegLan rx2)) =
                                some rr := by
                          simpa [__eo_eval_regex, hr1, hr2] using h
                        have hx1 := eo_eval_regex_sound M x₁ rx1 hr1
                        have hx2 := eo_eval_regex_sound M x rx2 hr2
                        rw [eo_to_smt_re_inter_eq, __smtx_model_eval.eq_114]
                        change __smtx_model_eval_re_inter
                            (__smtx_model_eval M (__eo_to_smt x₁))
                            (__smtx_model_eval M (__eo_to_smt x)) =
                          SmtValue.RegLan rr
                        rw [hx1, hx2]
                        exact eo_reglan_value_to_option_eq_some hOpt
              case re_union =>
                cases hr1 : __eo_eval_regex x₁ with
                | none => simp [__eo_eval_regex, hr1] at h
                | some rx1 =>
                    cases hr2 : __eo_eval_regex x with
                    | none => simp [__eo_eval_regex, hr1, hr2] at h
                    | some rx2 =>
                        have hOpt :
                            __eo_reglan_value_to_option
                              (__smtx_model_eval_re_union
                                (SmtValue.RegLan rx1) (SmtValue.RegLan rx2)) =
                                some rr := by
                          simpa [__eo_eval_regex, hr1, hr2] using h
                        have hx1 := eo_eval_regex_sound M x₁ rx1 hr1
                        have hx2 := eo_eval_regex_sound M x rx2 hr2
                        rw [eo_to_smt_re_union_eq, __smtx_model_eval.eq_115]
                        change __smtx_model_eval_re_union
                            (__smtx_model_eval M (__eo_to_smt x₁))
                            (__smtx_model_eval M (__eo_to_smt x)) =
                          SmtValue.RegLan rr
                        rw [hx1, hx2]
                        exact eo_reglan_value_to_option_eq_some hOpt
              case re_diff =>
                cases hr1 : __eo_eval_regex x₁ with
                | none => simp [__eo_eval_regex, hr1] at h
                | some rx1 =>
                    cases hr2 : __eo_eval_regex x with
                    | none => simp [__eo_eval_regex, hr1, hr2] at h
                    | some rx2 =>
                        have hOpt :
                            __eo_reglan_value_to_option
                              (__smtx_model_eval_re_diff
                                (SmtValue.RegLan rx1) (SmtValue.RegLan rx2)) =
                                some rr := by
                          simpa [__eo_eval_regex, hr1, hr2] using h
                        have hx1 := eo_eval_regex_sound M x₁ rx1 hr1
                        have hx2 := eo_eval_regex_sound M x rx2 hr2
                        rw [eo_to_smt_re_diff_eq, __smtx_model_eval.eq_116]
                        change __smtx_model_eval_re_diff
                            (__smtx_model_eval M (__eo_to_smt x₁))
                            (__smtx_model_eval M (__eo_to_smt x)) =
                          SmtValue.RegLan rr
                        rw [hx1, hx2]
                        exact eo_reglan_value_to_option_eq_some hOpt
          | _ => simp [__eo_eval_regex] at h
      | _ => simp [__eo_eval_regex] at h
  | _ => simp [__eo_eval_regex] at h
termination_by r

private theorem str_indexof_re_eval_requires_eq
    (idx m : native_Int) (body : Term)
    (hNe : __eo_requires (Term.Numeral idx) (Term.Numeral m) body ≠ Term.Stuck) :
    __eo_requires (Term.Numeral idx) (Term.Numeral m) body = body ∧ idx = m := by
  by_cases hIdx : idx = m
  · simp [__eo_requires, hIdx, native_ite, native_teq, native_not,
      SmtEval.native_not]
  · have hStuck :
        __eo_requires (Term.Numeral idx) (Term.Numeral m) body = Term.Stuck := by
      simp [__eo_requires, hIdx, native_ite, native_teq]
    exact False.elim (hNe hStuck)

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
  have hCmdNe : __eo_cmd_step_proven s CRule.str_indexof_re_eval args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hCmdNe
      exact False.elim (hCmdNe rfl)
  | cons a args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hCmdNe
          exact False.elim (hCmdNe rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hCmdNe
              exact False.elim (hCmdNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation a := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change __eo_typeof (__eo_prog_str_indexof_re_eval a) = Term.Bool
                at hResultTy
              change StepRuleProperties M [] (__eo_prog_str_indexof_re_eval a)
              change __eo_prog_str_indexof_re_eval a ≠ Term.Stuck at hCmdNe
              cases a <;> try (simp [__eo_prog_str_indexof_re_eval] at hResultTy hCmdNe ⊢)
              case Apply eqApp rhs =>
                cases eqApp <;> try (simp [__eo_prog_str_indexof_re_eval] at hResultTy hCmdNe ⊢)
                case Apply eqHead lhs =>
                  cases eqHead <;> try (simp [__eo_prog_str_indexof_re_eval] at hResultTy hCmdNe ⊢)
                  case UOp op =>
                    cases op <;> try (simp [__eo_prog_str_indexof_re_eval] at hResultTy hCmdNe ⊢)
                    case eq =>
                      cases rhs <;> try (simp [__eo_prog_str_indexof_re_eval] at hResultTy hCmdNe ⊢)
                      case Numeral m =>
                        cases lhs <;> try (simp [__eo_prog_str_indexof_re_eval] at hResultTy hCmdNe ⊢)
                        case Apply lhsFn nTerm =>
                          cases nTerm <;> try (simp [__eo_prog_str_indexof_re_eval]
                            at hResultTy hCmdNe ⊢
                          )
                          case Numeral n =>
                            cases lhsFn <;> try (simp [__eo_prog_str_indexof_re_eval]
                              at hResultTy hCmdNe ⊢
                            )
                            case Apply lhsFn₂ r =>
                              cases lhsFn₂ <;> try (simp [__eo_prog_str_indexof_re_eval]
                                at hResultTy hCmdNe ⊢
                              )
                              case Apply lhsHead strTerm =>
                                cases lhsHead <;> try (simp [__eo_prog_str_indexof_re_eval]
                                  at hResultTy hCmdNe ⊢
                                )
                                case UOp op₂ =>
                                  cases op₂ <;> try (simp [__eo_prog_str_indexof_re_eval]
                                    at hResultTy hCmdNe ⊢
                                  )
                                  case str_indexof_re =>
                                    cases strTerm <;> try (simp [__eo_prog_str_indexof_re_eval]
                                      at hResultTy hCmdNe ⊢
                                    )
                                    case String str =>
                                      cases hRegex : __eo_eval_regex r with
                                      | none =>
                                          simp [__eo_prog_str_indexof_re_eval, hRegex]
                                            at hResultTy
                                          cases hResultTy
                                      | some rr =>
                                          simp [__eo_prog_str_indexof_re_eval, hRegex]
                                            at hResultTy hCmdNe ⊢
                                          let idx :=
                                            native_str_indexof_re
                                              (native_unpack_string (native_pack_string str)) rr n
                                          let body :=
                                            Term.Apply
                                              (Term.Apply (Term.UOp UserOp.eq)
                                                (Term.Apply
                                                  (Term.Apply
                                                    (Term.Apply
                                                      (Term.UOp UserOp.str_indexof_re)
                                                      (Term.String str))
                                                    r)
                                                  (Term.Numeral n)))
                                              (Term.Numeral m)
                                          have hReqNe :
                                              __eo_requires (Term.Numeral idx)
                                                  (Term.Numeral m) body ≠
                                                Term.Stuck := by
                                            simpa [idx, body] using hCmdNe
                                          rcases str_indexof_re_eval_requires_eq idx m body hReqNe with
                                            ⟨hReqEq, hIdx⟩
                                          rw [show
                                            __eo_requires (Term.Numeral idx)
                                                (Term.Numeral m) body =
                                              body by simpa using hReqEq] at hResultTy ⊢
                                          have hBodyTrans :
                                              RuleProofs.eo_has_smt_translation body := by
                                            simpa [body] using hATrans
                                          have hBodyBool : RuleProofs.eo_has_bool_type body :=
                                            RuleProofs.eo_typeof_bool_implies_has_bool_type body
                                              hBodyTrans hResultTy
                                          refine ⟨?_,
                                            RuleProofs.eo_has_smt_translation_of_has_bool_type
                                              body hBodyBool⟩
                                          intro _hPremisesTrue
                                          have hRegexEval :
                                              __smtx_model_eval M (__eo_to_smt r) =
                                                SmtValue.RegLan rr :=
                                            eo_eval_regex_sound M r rr hRegex
                                          let lhs :=
                                            Term.Apply
                                              (Term.Apply
                                                (Term.Apply (Term.UOp UserOp.str_indexof_re)
                                                  (Term.String str))
                                                r)
                                              (Term.Numeral n)
                                          change eo_interprets M
                                            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs)
                                              (Term.Numeral m)) true
                                          exact RuleProofs.eo_interprets_eq_of_rel M lhs
                                            (Term.Numeral m) hBodyBool <| by
                                            rw [show __eo_to_smt lhs =
                                                SmtTerm.str_indexof_re
                                                  (SmtTerm.String str) (__eo_to_smt r)
                                                  (SmtTerm.Numeral n) by
                                              simp [lhs, eo_to_smt_str_indexof_re_eq,
                                                eo_to_smt_string_eq, eo_to_smt_numeral_eq]]
                                            rw [eo_to_smt_numeral_eq, __smtx_model_eval.eq_2]
                                            change RuleProofs.smt_value_rel
                                              (__smtx_model_eval M
                                                (SmtTerm.str_indexof_re
                                                  (SmtTerm.String str) (__eo_to_smt r)
                                                  (SmtTerm.Numeral n)))
                                              (SmtValue.Numeral m)
                                            rw [__smtx_model_eval.eq_102,
                                              __smtx_model_eval.eq_4, hRegexEval,
                                              __smtx_model_eval.eq_2]
                                            change RuleProofs.smt_value_rel
                                              (SmtValue.Numeral idx) (SmtValue.Numeral m)
                                            rw [hIdx]
                                            exact RuleProofs.smt_value_rel_refl
                                              (SmtValue.Numeral m)
