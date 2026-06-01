import Cpc.Proofs.RuleSupport.ConcatSplitSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev concatCPropNormalize (rev x : Term) : Term :=
  concatSplitNormalize rev x

private abbrev concatCPropHead (rev x : Term) : Term :=
  concatSplitHead rev x

private abbrev concatCPropSecond (rev x : Term) : Term :=
  __eo_list_nth (Term.UOp UserOp.str_concat) (concatCPropNormalize rev x)
    (Term.Numeral 1)

private abbrev concatCPropFlatSecond (rev x : Term) : Term :=
  __str_flatten (__str_nary_intro (concatCPropSecond rev x))

private abbrev concatCPropSHeadTailWord (rev s : Term) : Term :=
  let sHead := concatCPropHead rev s
  let sHeadLen := __eo_len sHead
  __str_flatten
    (__str_nary_intro
      (__eo_ite rev
        (__eo_extract sHead (Term.Numeral 0)
          (__eo_add sHeadLen (Term.Numeral (-2 : native_Int))))
        (__eo_extract sHead (Term.Numeral 1) sHeadLen)))

private abbrev concatCPropOverlapLen (rev t s : Term) : Term :=
  __eo_add (Term.Numeral 1)
    (__str_overlap_rec
      (__eo_ite rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (concatCPropSHeadTailWord rev s))
        (concatCPropSHeadTailWord rev s))
      (__eo_ite rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (concatCPropFlatSecond rev t))
        (concatCPropFlatSecond rev t)))

private abbrev concatCPropPrefix (rev t s : Term) : Term :=
  let sHead := concatCPropHead rev s
  __eo_mk_apply
    (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
      (Term.Numeral 0))
    (concatCPropOverlapLen rev t s)

private abbrev concatCPropSuffix (rev t s tc : Term) : Term :=
  let pfx := concatCPropPrefix rev t s
  Term.UOp1 UserOp1._at_purify
    (__eo_mk_apply
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (__eo_mk_apply (Term.UOp UserOp.str_len) pfx))
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.neg) (Term.Apply (Term.UOp UserOp.str_len) tc))
        (__eo_mk_apply (Term.UOp UserOp.str_len) pfx)))

private abbrev concatCPropReverseSuffix (rev t s tc : Term) : Term :=
  let sHead := concatCPropHead rev s
  let k := concatCPropOverlapLen rev t s
  let endPart :=
    __eo_mk_apply
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.neg)
            (__eo_mk_apply (Term.UOp UserOp.str_len) sHead))
          k))
      k
  Term.UOp1 UserOp1._at_purify
    (__eo_mk_apply
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) tc)
        (Term.Numeral 0))
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.neg) (Term.Apply (Term.UOp UserOp.str_len) tc))
        (__eo_mk_apply (Term.UOp UserOp.str_len) endPart)))

private abbrev concatCPropReverseEnd (rev t s : Term) : Term :=
  let sHead := concatCPropHead rev s
  let k := concatCPropOverlapLen rev t s
  __eo_mk_apply
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.str_substr) sHead)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.neg)
          (__eo_mk_apply (Term.UOp UserOp.str_len) sHead))
        k))
    k

private abbrev concatCPropFormula (rev t s tc : Term) : Term :=
  __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) tc)
    (__eo_ite rev
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (concatCPropReverseSuffix rev t s tc))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropReverseEnd rev t s))
          (__eo_nil (Term.UOp UserOp.str_concat)
            (__eo_typeof (concatCPropReverseSuffix rev t s tc)))))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.str_concat)
          (concatCPropPrefix rev t s))
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.str_concat)
            (concatCPropSuffix rev t s tc))
          (__eo_nil (Term.UOp UserOp.str_concat)
            (__eo_typeof (concatCPropPrefix rev t s))))))

private abbrev concatCPropBody (rev t s tc : Term) : Term :=
  __eo_requires (concatCPropHead rev t) tc (concatCPropFormula rev t s tc)

private theorem len_nonzero_seq_type_of_bool (u : Term)
    (hNonzeroBool :
      RuleProofs.eo_has_bool_type (mkNot (mkEq (mkStrLen u) (Term.Numeral 0)))) :
    ∃ T, __smtx_typeof (__eo_to_smt u) = SmtType.Seq T := by
  have hEqBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen u) (Term.Numeral 0)) :=
    RuleProofs.eo_has_bool_type_not_arg
      (mkEq (mkStrLen u) (Term.Numeral 0)) hNonzeroBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkStrLen u) (Term.Numeral 0) hEqBool with
    ⟨_hSame, hLeftNN⟩
  have hLenTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt u)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen] using hLeftNN
  exact seq_arg_of_non_none_ret (op := SmtTerm.str_len)
    (typeof_str_len_eq (__eo_to_smt u)) hLenTerm

private theorem eo_prog_concat_cprop_eq_of_ne_stuck
    (rev t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck) :
    __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
        (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) =
      concatCPropFormula rev t s tc ∧
      concatCPropHead rev t = tc := by
  have hProgBody :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) =
        concatCPropBody rev t s tc := by
    cases rev
    case Stuck =>
      exact False.elim (hProg rfl)
    all_goals rfl
  have hBodyNe : concatCPropBody rev t s tc ≠ Term.Stuck := by
    simpa [hProgBody] using hProg
  have hHeadT : concatCPropHead rev t = tc :=
    eo_requires_eq_of_ne_stuck (concatCPropHead rev t) tc
      (concatCPropFormula rev t s tc) hBodyNe
  have hFormulaEq :
      concatCPropBody rev t s tc = concatCPropFormula rev t s tc :=
    eo_requires_eq_result_of_ne_stuck (concatCPropHead rev t) tc
      (concatCPropFormula rev t s tc) hBodyNe
  exact ⟨by rw [hProgBody, hFormulaEq], hHeadT⟩

private theorem eo_prog_concat_cprop_premise_shapes_of_ne_stuck
    (rev x1 x2 : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf x1) (Proof.pf x2) ≠
        Term.Stuck) :
    ∃ t s tc,
      x1 = mkEq t s ∧ x2 = mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)) := by
  cases x1 with
  | Apply lhs1 rhs1 =>
      cases lhs1 with
      | Apply op1 t =>
          cases op1 with
          | UOp u1 =>
              cases u1 with
              | eq =>
                  cases x2 with
                  | Apply notOp eqTerm =>
                      cases notOp with
                      | UOp notU =>
                          cases notU with
                          | not =>
                              cases eqTerm with
                              | Apply lhs2 zero =>
                                  cases lhs2 with
                                  | Apply op2 lenTerm =>
                                      cases op2 with
                                      | UOp eqU =>
                                          cases eqU with
                                          | eq =>
                                              cases lenTerm with
                                              | Apply lenOp tc =>
                                                  cases lenOp with
                                                  | UOp lenU =>
                                                      cases lenU with
                                                      | str_len =>
                                                          cases zero with
                                                          | Numeral z =>
                                                              by_cases hz : z = 0
                                                              · subst z
                                                                exact
                                                                  ⟨t, rhs1, tc,
                                                                    rfl, rfl⟩
                                                              · cases rev <;>
                                                                  simp [__eo_prog_concat_cprop, hz]
                                                                    at hProg
                                                          | _ =>
                                                              cases rev <;>
                                                                simp [__eo_prog_concat_cprop]
                                                                  at hProg
                                                      | _ =>
                                                          cases rev <;>
                                                            simp [__eo_prog_concat_cprop]
                                                              at hProg
                                                  | _ =>
                                                      cases rev <;>
                                                        simp [__eo_prog_concat_cprop]
                                                          at hProg
                                              | _ =>
                                                  cases rev <;>
                                                    simp [__eo_prog_concat_cprop]
                                                      at hProg
                                          | _ =>
                                              cases rev <;>
                                                simp [__eo_prog_concat_cprop] at hProg
                                      | _ =>
                                          cases rev <;>
                                            simp [__eo_prog_concat_cprop] at hProg
                                  | _ =>
                                      cases rev <;>
                                        simp [__eo_prog_concat_cprop] at hProg
                              | _ =>
                                  cases rev <;>
                                    simp [__eo_prog_concat_cprop] at hProg
                          | _ =>
                              cases rev <;>
                                simp [__eo_prog_concat_cprop] at hProg
                      | _ =>
                          cases rev <;> simp [__eo_prog_concat_cprop] at hProg
                  | _ =>
                      cases rev <;> simp [__eo_prog_concat_cprop] at hProg
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_cprop] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_cprop] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_cprop] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_cprop] at hProg

private theorem concatCProp_rev_cases_of_prog_ne_stuck
    (rev t s tc : Term)
    (hProg :
      __eo_prog_concat_cprop rev (Proof.pf (mkEq t s))
          (Proof.pf (mkNot (mkEq (mkStrLen tc) (Term.Numeral 0)))) ≠
        Term.Stuck)
    (htcNe : tc ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  rcases eo_prog_concat_cprop_eq_of_ne_stuck rev t s tc hProg with
    ⟨_, hHeadT⟩
  have hHeadNe : concatCPropHead rev t ≠ Term.Stuck := by
    rw [hHeadT]
    exact htcNe
  have hNormNe : concatCPropNormalize rev t ≠ Term.Stuck :=
    concatSplitNormalize_ne_stuck_of_head_ne_stuck rev t hHeadNe
  have hIteNe :
      __eo_ite rev
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
          (__str_nary_intro t) ≠ Term.Stuck := by
    simpa [concatCPropNormalize, concatSplitNormalize] using hNormNe
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
    (__str_nary_intro t) hIteNe

theorem cmd_step_concat_cprop_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_cprop args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_cprop args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_cprop args premises) :=
by
  sorry
