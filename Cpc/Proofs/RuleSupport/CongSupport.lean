import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Translation.Apply
import Cpc.Proofs.Translation.Inversions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace CongSupport

private abbrev mkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private theorem eo_mk_apply_eq_of_ne_stuck (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hf hx
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_mk_apply_left_ne_stuck_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    f ≠ Term.Stuck := by
  intro h hF
  subst hF
  exact h (by simp [__eo_mk_apply])

private theorem eo_mk_apply_right_ne_stuck_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h hX
  subst hX
  cases f <;> simp [__eo_mk_apply] at h

private theorem eq_of_eo_eq_true (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    y = x := by
  intro h
  cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢
  all_goals exact h

private theorem eo_get_nil_rec_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        Term.Boolean true := by
  intro ps
  induction ps with
  | nil =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not]
  | cons p ps ih =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires, ih,
        native_ite, native_teq, native_not, SmtEval.native_not]

private theorem eo_list_rev_rec_and_premiseAndFormulaList :
    ∀ xs ys : List Term,
      __eo_list_rev_rec (premiseAndFormulaList xs) (premiseAndFormulaList ys) =
        premiseAndFormulaList (xs.reverse ++ ys) := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      cases ys <;> rfl
  | cons p xs ih =>
      cases ys with
      | nil =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih [p]
      | cons y ys =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih (p :: y :: ys)

private theorem eo_list_rev_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_list_rev (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        premiseAndFormulaList ps.reverse := by
  intro ps
  unfold __eo_list_rev
  simp [__eo_requires, premiseAndFormulaList_is_and_list,
    eo_get_nil_rec_and_premiseAndFormulaList, native_ite, native_teq,
    native_not, SmtEval.native_not]
  simpa using eo_list_rev_rec_and_premiseAndFormulaList ps []

private theorem all_interpreted_true_reverse
    (M : SmtModel) (ps : List Term) :
    AllInterpretedTrue M ps ->
    AllInterpretedTrue M ps.reverse := by
  intro h t ht
  exact h t (by simpa using List.mem_reverse.mp ht)

private theorem all_have_bool_type_reverse
    (ps : List Term) :
    AllHaveBoolType ps ->
    AllHaveBoolType ps.reverse := by
  intro h t ht
  exact h t (by simpa using List.mem_reverse.mp ht)

inductive CongTrueSpine (M : SmtModel) : Term -> Term -> Prop where
  | refl (t : Term) : CongTrueSpine M t t
  | app {f g x y : Term} :
      CongTrueSpine M f g ->
      eo_interprets M (mkEq x y) true ->
      CongTrueSpine M (Term.Apply f x) (Term.Apply g y)

inductive CongTypeSpine : Term -> Term -> Prop where
  | refl (t : Term) : CongTypeSpine t t
  | app {f g x y : Term} :
      CongTypeSpine f g ->
      RuleProofs.eo_has_bool_type (mkEq x y) ->
      CongTypeSpine (Term.Apply f x) (Term.Apply g y)

private theorem mk_cong_rhs_step_eq_of_eo_eq_true
    (f x y z tail : Term) :
    __eo_eq x y = Term.Boolean true ->
    __mk_cong_rhs (Term.Apply f x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq y z)) tail) =
      __eo_mk_apply (__mk_cong_rhs f tail) z := by
  intro hEq
  simp [mkEq, __mk_cong_rhs, __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
    native_teq, native_ite]

private theorem mk_cong_rhs_false_branch_stuck
    (f x y z tail : Term) :
    __eo_l_1___mk_cong_rhs (Term.Apply f x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq y z)) tail) =
      Term.Stuck := by
  simp [mkEq, __eo_l_1___mk_cong_rhs]

private theorem mk_cong_rhs_congTrueSpine_of_list
    (M : SmtModel) :
    ∀ (ps : List Term) (t : Term),
      AllInterpretedTrue M ps ->
      __mk_cong_rhs t (premiseAndFormulaList ps) ≠ Term.Stuck ->
      CongTrueSpine M t (__mk_cong_rhs t (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro t _ hProg
      cases t <;>
        simp [premiseAndFormulaList, __mk_cong_rhs, __eo_l_1___mk_cong_rhs] at hProg ⊢
      all_goals exact CongTrueSpine.refl _
  | cons p ps ih =>
      intro t hTrue hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    cases t with
                    | Apply f x =>
                        have hHeadTrue :
                            eo_interprets M (mkEq lhs tail) true := by
                          simpa [premiseAndFormulaList, mkEq] using
                            hTrue (mkEq lhs tail) (by simp [mkEq])
                        have hRestTrue : AllInterpretedTrue M ps := by
                          intro q hq
                          exact hTrue q (by simp [premiseAndFormulaList, hq])
                        have hCond :
                            __eo_eq x lhs = Term.Boolean true := by
                          cases hEq : __eo_eq x lhs <;>
                            simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                              __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                              native_teq, native_ite] at hProg
                          case Boolean b =>
                            cases b with
                            | false =>
                                simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                                  __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                                  native_teq, native_ite] at hProg
                            | true =>
                                rfl
                        have hStepEq :=
                          mk_cong_rhs_step_eq_of_eo_eq_true f x lhs tail
                            (premiseAndFormulaList ps) hCond
                        have hMkApplyNN :
                            __eo_mk_apply
                                (__mk_cong_rhs f (premiseAndFormulaList ps)) tail ≠
                              Term.Stuck := by
                          rw [← hStepEq]
                          exact hProg
                        have hRecNN :
                            __mk_cong_rhs f (premiseAndFormulaList ps) ≠
                              Term.Stuck :=
                          eo_mk_apply_left_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hTailNN : tail ≠ Term.Stuck :=
                          eo_mk_apply_right_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hRec :=
                          ih f hRestTrue hRecNN
                        have hLhs : lhs = x :=
                          eq_of_eo_eq_true x lhs hCond
                        subst lhs
                        change CongTrueSpine M (Term.Apply f x)
                          (__mk_cong_rhs (Term.Apply f x)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                              (mkEq x tail)) (premiseAndFormulaList ps)))
                        rw [hStepEq]
                        rw [eo_mk_apply_eq_of_ne_stuck
                          (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                          hRecNN hTailNN]
                        exact CongTrueSpine.app hRec hHeadTrue
                    | _ =>
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                            __eo_l_1___mk_cong_rhs]))
                  all_goals
                    exact False.elim (hProg (by
                      cases t <;>
                        simp [premiseAndFormulaList, __mk_cong_rhs,
                          __eo_l_1___mk_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    cases t <;>
                      simp [premiseAndFormulaList, __mk_cong_rhs,
                        __eo_l_1___mk_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                cases t <;>
                  simp [premiseAndFormulaList, __mk_cong_rhs,
                    __eo_l_1___mk_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by
            cases t <;>
              simp [premiseAndFormulaList, __mk_cong_rhs,
                __eo_l_1___mk_cong_rhs]))

private theorem mk_cong_rhs_congTypeSpine_of_list :
    ∀ (ps : List Term) (t : Term),
      AllHaveBoolType ps ->
      __mk_cong_rhs t (premiseAndFormulaList ps) ≠ Term.Stuck ->
      CongTypeSpine t (__mk_cong_rhs t (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro t _ hProg
      cases t <;>
        simp [premiseAndFormulaList, __mk_cong_rhs, __eo_l_1___mk_cong_rhs] at hProg ⊢
      all_goals exact CongTypeSpine.refl _
  | cons p ps ih =>
      intro t hBool hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    cases t with
                    | Apply f x =>
                        have hHeadBool :
                            RuleProofs.eo_has_bool_type (mkEq lhs tail) := by
                          simpa [premiseAndFormulaList, mkEq] using
                            hBool (mkEq lhs tail) (by simp [mkEq])
                        have hRestBool : AllHaveBoolType ps := by
                          intro q hq
                          exact hBool q (by simp [premiseAndFormulaList, hq])
                        have hCond :
                            __eo_eq x lhs = Term.Boolean true := by
                          cases hEq : __eo_eq x lhs <;>
                            simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                              __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                              native_teq, native_ite] at hProg
                          case Boolean b =>
                            cases b with
                            | false =>
                                simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                                  __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                                  native_teq, native_ite] at hProg
                            | true =>
                                rfl
                        have hStepEq :=
                          mk_cong_rhs_step_eq_of_eo_eq_true f x lhs tail
                            (premiseAndFormulaList ps) hCond
                        have hMkApplyNN :
                            __eo_mk_apply
                                (__mk_cong_rhs f (premiseAndFormulaList ps)) tail ≠
                              Term.Stuck := by
                          rw [← hStepEq]
                          exact hProg
                        have hRecNN :
                            __mk_cong_rhs f (premiseAndFormulaList ps) ≠
                              Term.Stuck :=
                          eo_mk_apply_left_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hTailNN : tail ≠ Term.Stuck :=
                          eo_mk_apply_right_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hRec :=
                          ih f hRestBool hRecNN
                        have hLhs : lhs = x :=
                          eq_of_eo_eq_true x lhs hCond
                        subst lhs
                        change CongTypeSpine (Term.Apply f x)
                          (__mk_cong_rhs (Term.Apply f x)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                              (mkEq x tail)) (premiseAndFormulaList ps)))
                        rw [hStepEq]
                        rw [eo_mk_apply_eq_of_ne_stuck
                          (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                          hRecNN hTailNN]
                        exact CongTypeSpine.app hRec hHeadBool
                    | _ =>
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                            __eo_l_1___mk_cong_rhs]))
                  all_goals
                    exact False.elim (hProg (by
                      cases t <;>
                        simp [premiseAndFormulaList, __mk_cong_rhs,
                          __eo_l_1___mk_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    cases t <;>
                      simp [premiseAndFormulaList, __mk_cong_rhs,
                        __eo_l_1___mk_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                cases t <;>
                  simp [premiseAndFormulaList, __mk_cong_rhs,
                    __eo_l_1___mk_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by
            cases t <;>
              simp [premiseAndFormulaList, __mk_cong_rhs,
                __eo_l_1___mk_cong_rhs]))

private theorem eo_prog_cong_pf_eq_of_ne_stuck (t E : Term) :
    t ≠ Term.Stuck ->
    __eo_prog_cong t (Proof.pf E) =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (__eo_list_rev (Term.UOp UserOp.and) E)) := by
  intro ht
  cases t <;> simp [__eo_prog_cong] at ht ⊢

private theorem eo_typeof_eq_bool_operands_eq (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

private theorem mkEq_typeof_bool_operands_typeof_eq (x y : Term)
    (h : __eo_typeof (mkEq x y) = Term.Bool) :
    __eo_typeof x = __eo_typeof y := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at h
  exact eo_typeof_eq_bool_operands_eq (__eo_typeof x) (__eo_typeof y) h

/--
The remaining typing core for congruence: once the generated program has been
reduced to a spine of congruent applications, the equality between the original
spine and the rewritten spine is Boolean.
-/
private axiom congTypeSpine_eq_has_bool_type (t rhs : Term) :
  RuleProofs.eo_has_smt_translation t ->
  CongTypeSpine t rhs ->
  RuleProofs.eo_has_bool_type (mkEq t rhs)

/--
The remaining semantic core for congruence: a syntactic congruence spine
preserves SMT equality in a total typed model.
-/
private axiom congTrueSpine_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t rhs : Term) :
  RuleProofs.eo_has_smt_translation t ->
  CongTrueSpine M t rhs ->
  eo_interprets M (mkEq t rhs) true

/-- Typing for the generated EO implementation of `cong` over a premise list. -/
theorem typed___eo_prog_cong_impl (t : Term) (premises : List Term) :
  RuleProofs.eo_has_smt_translation t ->
  AllHaveBoolType premises ->
  __eo_prog_cong t (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) := by
  intro hTrans hPremisesBool hProg
  have htNN : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  let rhs := __mk_cong_rhs t (premiseAndFormulaList premises.reverse)
  have hProgEq :=
    eo_prog_cong_pf_eq_of_ne_stuck t (premiseAndFormulaList premises) htNN
  have hProgNN :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs ≠ Term.Stuck := by
    change
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (premiseAndFormulaList premises.reverse)) ≠
        Term.Stuck
    rw [← eo_list_rev_and_premiseAndFormulaList premises]
    rw [← hProgEq]
    exact hProg
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) rhs hProgNN
  have hSpine :
      CongTypeSpine t rhs := by
    simpa [rhs] using
      mk_cong_rhs_congTypeSpine_of_list premises.reverse t
        (all_have_bool_type_reverse premises hPremisesBool) hRhsNN
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs) :=
    congTypeSpine_eq_has_bool_type t rhs hTrans hSpine
  rw [hProgEq]
  rw [eo_list_rev_and_premiseAndFormulaList]
  change RuleProofs.eo_has_bool_type
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs)
  rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
    (by simp) hRhsNN]
  exact hEqBool

/-- Correctness for the generated EO implementation of `cong` over a premise list. -/
theorem facts___eo_prog_cong_impl
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (premises : List Term) :
  RuleProofs.eo_has_smt_translation t ->
  AllInterpretedTrue M premises ->
  __eo_prog_cong t (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  eo_interprets M
    (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) true := by
  intro hTrans hPremisesTrue hProg
  have htNN : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  let rhs := __mk_cong_rhs t (premiseAndFormulaList premises.reverse)
  have hProgEq :=
    eo_prog_cong_pf_eq_of_ne_stuck t (premiseAndFormulaList premises) htNN
  have hProgNN :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs ≠ Term.Stuck := by
    change
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (premiseAndFormulaList premises.reverse)) ≠
        Term.Stuck
    rw [← eo_list_rev_and_premiseAndFormulaList premises]
    rw [← hProgEq]
    exact hProg
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) rhs hProgNN
  have hSpine :
      CongTrueSpine M t rhs := by
    simpa [rhs] using
      mk_cong_rhs_congTrueSpine_of_list M premises.reverse t
        (all_interpreted_true_reverse M premises hPremisesTrue) hRhsNN
  have hEqTrue : eo_interprets M (mkEq t rhs) true :=
    congTrueSpine_eq_true M hM t rhs hTrans hSpine
  rw [hProgEq]
  rw [eo_list_rev_and_premiseAndFormulaList]
  change eo_interprets M
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs) true
  rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
    (by simp) hRhsNN]
  exact hEqTrue

theorem smt_value_rel_model_eval_apply_of_rel
    (M : SmtModel) (hM : model_total_typed M)
    (f g x y : SmtTerm)
    (hAppNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hFy : __smtx_typeof f = __smtx_typeof g)
    (hXy : __smtx_typeof x = __smtx_typeof y)
    (hFRel : RuleProofs.smt_value_rel (__smtx_model_eval M f) (__smtx_model_eval M g))
    (hXRel : RuleProofs.smt_value_rel (__smtx_model_eval M x) (__smtx_model_eval M y)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x))
      (__smtx_model_eval_apply (__smtx_model_eval M g) (__smtx_model_eval M y)) := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, B, hHead, hX, hA, _hB⟩
  have hFNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hGNN : term_has_non_none_type g := by
    unfold term_has_non_none_type
    rw [← hFy]
    exact hFNN
  have hXNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hX]
    exact hA
  have hYNN : term_has_non_none_type y := by
    unfold term_has_non_none_type
    rw [← hXy]
    exact hXNN
  have hFPres :
      __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
    smt_model_eval_preserves_type_of_non_none M hM f hFNN
  have hGPres :
      __smtx_typeof_value (__smtx_model_eval M g) = __smtx_typeof g :=
    smt_model_eval_preserves_type_of_non_none M hM g hGNN
  have hXPres :
      __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
    smt_model_eval_preserves_type_of_non_none M hM x hXNN
  have hYPres :
      __smtx_typeof_value (__smtx_model_eval M y) = __smtx_typeof y :=
    smt_model_eval_preserves_type_of_non_none M hM y hYNN
  have hFNeReg : __smtx_typeof f ≠ SmtType.RegLan := by
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hArgField :
      TranslationProofs.smtx_type_field_wf_rec A native_reflist_nil := by
    have hDomains :=
      TranslationProofs.smtx_term_fun_like_domains_wf_of_non_none f hFNN
    exact TranslationProofs.smtx_type_fun_like_arg_field_wf_of_domains_wf hDomains hHead
  have hANeReg : A ≠ SmtType.RegLan :=
    TranslationProofs.smtx_type_field_wf_rec_ne_reglan hArgField
  have hFEq : __smtx_model_eval M f = __smtx_model_eval M g :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      hFPres (by simpa [hFy] using hGPres) hFNeReg hFRel
  have hXEq : __smtx_model_eval M x = __smtx_model_eval M y :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      (by simpa [hX] using hXPres)
      (by
        rw [← hXy, hX] at hYPres
        exact hYPres)
      hANeReg hXRel
  rw [hFEq, hXEq]
  exact RuleProofs.smt_value_rel_refl _

end CongSupport
