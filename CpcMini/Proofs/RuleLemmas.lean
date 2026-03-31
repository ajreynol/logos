import CpcMini.Proofs.Rules.Common
import CpcMini.Proofs.Rules.Scope
import CpcMini.Proofs.Rules.Contra
import CpcMini.Proofs.Rules.Refl
import CpcMini.Proofs.Rules.Symm
import CpcMini.Proofs.Rules.Trans

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- The theorem statements -/

def cmdTranslationOk : CCmd -> Prop
  | CCmd.assume_push A => RuleProofs.eo_has_smt_translation A
  | CCmd.step CRule.refl (CArgList.cons a1 CArgList.nil) CIndexList.nil =>
      RuleProofs.eo_has_smt_translation a1
  | _ => True

inductive CmdListTranslationOk : CCmdList -> Prop
  | nil : CmdListTranslationOk CCmdList.nil
  | cons (c : CCmd) (cs : CCmdList) :
      cmdTranslationOk c ->
      CmdListTranslationOk cs ->
      CmdListTranslationOk (CCmdList.cons c cs)

def premiseAndFormulaList : List Term -> Term
  | [] => Term.Boolean true
  | p :: ps => Term.Apply (Term.Apply Term.and p) (premiseAndFormulaList ps)

def premiseTermList (s : CState) : CIndexList -> List Term
  | CIndexList.nil => []
  | CIndexList.cons n premises =>
      __eo_state_proven_nth s n :: premiseTermList s premises

def AllInterpretedTrue (M : SmtModel) (ts : List Term) : Prop :=
  ∀ t ∈ ts, eo_interprets M t true

def AllHaveSmtTranslation (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_smt_translation t

def AllHaveBoolType (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_bool_type t

theorem premiseAndFormulaList_true_of_all_true
    (M : SmtModel) :
  ∀ premises : List Term,
    AllInterpretedTrue M premises ->
    eo_interprets M (premiseAndFormulaList premises) true :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using RuleProofs.eo_interprets_true M
  | cons p premises ih =>
      apply RuleProofs.eo_interprets_and_intro
      · exact hPremises p (by simp)
      · apply ih
        intro t ht
        exact hPremises t (by simp [ht])

theorem premiseAndFormulaList_has_bool_type :
  ∀ premises : List Term,
    AllHaveBoolType premises ->
    RuleProofs.eo_has_bool_type (premiseAndFormulaList premises) :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using RuleProofs.eo_has_bool_type_true
  | cons p premises ih =>
      apply RuleProofs.eo_has_bool_type_and_of_bool_args
      · exact hPremises p (by simp)
      · apply ih
        intro t ht
        exact hPremises t (by simp [ht])

theorem premiseAndFormulaList_is_and_list :
  ∀ premises : List Term,
    __eo_is_list Term.and (premiseAndFormulaList premises) = Term.Boolean true
:=
by
  have hGetNil :
      ∀ premises : List Term,
        __eo_get_nil_rec Term.and (premiseAndFormulaList premises) ≠ Term.Stuck
  :=
  by
    intro premises
    induction premises with
    | nil =>
        unfold premiseAndFormulaList
        unfold __eo_get_nil_rec
        unfold __eo_requires
        unfold __eo_is_list_nil
        simp [eo_lit_ite, eo_lit_teq, eo_lit_not, SmtEval.smt_lit_not]
    | cons p premises ih =>
        unfold premiseAndFormulaList
        unfold __eo_get_nil_rec
        unfold __eo_requires
        simpa [eo_lit_ite, eo_lit_teq, eo_lit_not, SmtEval.smt_lit_not] using ih
  intro premises
  have hNotStuck :
      __eo_get_nil_rec Term.and (premiseAndFormulaList premises) ≠ Term.Stuck :=
    hGetNil premises
  have hPremNotStuck : premiseAndFormulaList premises ≠ Term.Stuck :=
    by
      induction premises with
      | nil =>
          simp [premiseAndFormulaList]
      | cons p premises ih =>
          simp [premiseAndFormulaList]
  unfold __eo_is_list
  unfold __eo_is_ok
  simpa [eo_lit_teq, eo_lit_not, SmtEval.smt_lit_not] using hNotStuck

theorem mk_premise_list_and_eq_premiseAndFormulaList :
  ∀ (s : CState) (premises : CIndexList),
    __eo_mk_premise_list Term.and premises s =
      premiseAndFormulaList (premiseTermList s premises)
:=
by
  intro s premises
  induction premises with
  | nil =>
      simp [__eo_mk_premise_list, premiseAndFormulaList, premiseTermList, __eo_nil]
  | cons n premises ih =>
      simp [__eo_mk_premise_list, premiseAndFormulaList, premiseTermList, __eo_cons,
        __eo_requires, eo_lit_ite, eo_lit_teq, eo_lit_not, ih,
        premiseAndFormulaList_is_and_list, SmtEval.smt_lit_not]

structure StepRuleSpecNArgMPrem
    (M : SmtModel) (mk : List Term -> List Term -> Term) : Prop where
  facts_of_true :
    ∀ args premises,
      AllHaveSmtTranslation args ->
      AllInterpretedTrue M premises ->
      mk args premises ≠ Term.Stuck ->
      RuleProofs.RuleResultFacts M (mk args premises)
  bool_of_translation :
    ∀ args premises,
      AllHaveSmtTranslation args ->
      AllHaveBoolType premises ->
      mk args premises ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type (mk args premises)

structure StepRuleProperties
    (M : SmtModel) (premises : List Term) (P : Term) : Prop where
  facts_of_true :
    AllInterpretedTrue M premises ->
    RuleProofs.RuleResultFacts M P
  has_bool_type :
    RuleProofs.eo_has_bool_type P

theorem typed___eo_prog_scope
    (x1 x2 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  RuleProofs.eo_has_bool_type x2 ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) :=
by
  intro hBool1 hBool2 hProg
  exact typed___eo_prog_scope_of_bool_args x1 x2 hBool1 hBool2 hProg

theorem facts___eo_prog_scope
    (M : SmtModel) (hM : model_total_typed M) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation x2 ->
  __eo_typeof x1 = Term.Bool ->
  __eo_typeof x2 = Term.Bool ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.RuleResultFacts M (__eo_prog_scope x1 (Proof.pf x2)) :=
by
  intro hImp hTrans1 hTrans2 hTy1 hTy2 hProg
  exact facts___eo_prog_scope_impl M hM x1 x2 hImp hTrans1 hTrans2 hTy1 hTy2 hProg

theorem spec___eo_prog_contra
    (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M
    (fun
      | [], [X1, X2] => __eo_prog_contra (Proof.pf X1) (Proof.pf X2)
      | _, _ => Term.Stuck) :=
by
  refine ⟨?_, ?_⟩
  · intro args premises hArgs hTrue hProg
    cases args with
    | nil =>
        cases premises with
        | nil =>
            exact False.elim (hProg (by simp))
        | cons X1 premises =>
            cases premises with
            | nil =>
                exact False.elim (hProg (by simp))
            | cons X2 premises =>
                cases premises with
                | nil =>
                    exact facts___eo_prog_contra_impl M hM X1 X2
                      (hTrue X1 (by simp))
                      (hTrue X2 (by simp))
                      (by simpa using hProg)
                | cons X3 premises =>
                    exact False.elim (hProg (by simp))
    | cons a args =>
        exact False.elim (hProg (by simp))
  · intro args premises hArgs hPremises hProg
    cases args with
    | nil =>
        cases premises with
        | nil =>
            exact False.elim (hProg (by simp))
        | cons X1 premises =>
            cases premises with
            | nil =>
                exact False.elim (hProg (by simp))
            | cons X2 premises =>
                cases premises with
                | nil =>
                    exact typed___eo_prog_contra_impl X1 X2
                      (hPremises X1 (by simp))
                      (hPremises X2 (by simp))
                      (by simpa using hProg)
                | cons X3 premises =>
                    exact False.elim (hProg (by simp))
    | cons a args =>
        exact False.elim (hProg (by simp))

theorem spec___eo_prog_refl
    (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M
    (fun
      | [a1], [] => __eo_prog_refl a1
      | _, _ => Term.Stuck) :=
by
  refine ⟨?_, ?_⟩
  · intro args premises hArgs hTrue hProg
    cases args with
    | nil =>
        exact False.elim (hProg (by simp))
    | cons a1 args =>
        cases args with
        | nil =>
            cases premises with
            | nil =>
                exact facts___eo_prog_refl_impl M hM a1
                  (hArgs a1 (by simp))
                  (by simpa using hProg)
            | cons X premises =>
                exact False.elim (hProg (by simp))
        | cons a2 args =>
            exact False.elim (hProg (by simp))
  · intro args premises hArgs hPremises hProg
    cases args with
    | nil =>
        exact False.elim (hProg (by simp))
    | cons a1 args =>
        cases args with
        | nil =>
            cases premises with
            | nil =>
                exact typed___eo_prog_refl_impl a1
                  (hArgs a1 (by simp))
                  (by simpa using hProg)
            | cons X premises =>
                exact False.elim (hProg (by simp))
        | cons a2 args =>
            exact False.elim (hProg (by simp))

theorem spec___eo_prog_symm
    (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M
    (fun
      | [], [X] => __eo_prog_symm (Proof.pf X)
      | _, _ => Term.Stuck) :=
by
  refine ⟨?_, ?_⟩
  · intro args premises hArgs hTrue hProg
    cases args with
    | nil =>
        cases premises with
        | nil =>
            exact False.elim (hProg (by simp))
        | cons X premises =>
            cases premises with
            | nil =>
                exact facts___eo_prog_symm_impl M hM X
                  (hTrue X (by simp))
                  (by simpa using hProg)
            | cons Y premises =>
                exact False.elim (hProg (by simp))
    | cons a args =>
        exact False.elim (hProg (by simp))
  · intro args premises hArgs hPremises hProg
    cases args with
    | nil =>
        cases premises with
        | nil =>
            exact False.elim (hProg (by simp))
        | cons X premises =>
            cases premises with
            | nil =>
                exact typed___eo_prog_symm_impl X
                  (hPremises X (by simp))
                  (by simpa using hProg)
            | cons Y premises =>
                exact False.elim (hProg (by simp))
    | cons a args =>
        exact False.elim (hProg (by simp))

theorem spec___eo_prog_trans
    (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M
    (fun
      | [], premises => __eo_prog_trans (Proof.pf (premiseAndFormulaList premises))
      | _, _ => Term.Stuck) :=
by
  refine ⟨?_, ?_⟩
  · intro args premises hArgs hTrue hProg
    cases args with
    | nil =>
        exact facts___eo_prog_trans_impl M hM (premiseAndFormulaList premises)
          (premiseAndFormulaList_true_of_all_true M premises hTrue)
          (by simpa using hProg)
    | cons a args =>
        exact False.elim (hProg (by simp))
  · intro args premises hArgs hPremises hProg
    cases args with
    | nil =>
        exact typed___eo_prog_trans_impl (premiseAndFormulaList premises)
          (premiseAndFormulaList_has_bool_type premises hPremises)
          (by simpa using hProg)
    | cons a args =>
        exact False.elim (hProg (by simp))

theorem step_rule_properties_narg_mprem
    (M : SmtModel)
    (args premises : List Term) (mk : List Term -> List Term -> Term) :
  AllHaveSmtTranslation args ->
  AllHaveBoolType premises ->
  StepRuleSpecNArgMPrem M mk ->
  mk args premises ≠ Term.Stuck ->
  StepRuleProperties M premises (mk args premises) :=
by
  intro hArgs hPremBool hSpec hProg
  refine ⟨?_, hSpec.bool_of_translation args premises hArgs hPremBool hProg⟩
  intro hPremTrue
  exact hSpec.facts_of_true args premises hArgs hPremTrue hProg

theorem cmd_step_proven_contra_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.contra args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.contra args premises) :=
by
  intro _hCmdTrans hPremisesBool hProg
  cases args with
  | nil =>
      cases premises with
      | nil =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons n1 premises =>
          cases premises with
          | nil =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
          | cons n2 premises =>
              cases premises with
              | nil =>
                  have hArgsTrans : AllHaveSmtTranslation [] := by
                    intro t ht
                    cases ht
                  simpa [premiseTermList, __eo_cmd_step_proven] using
                    (step_rule_properties_narg_mprem M [] (premiseTermList s
                        (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil)))
                      (fun
                        | [], [X1, X2] => __eo_prog_contra (Proof.pf X1) (Proof.pf X2)
                        | _, _ => Term.Stuck)
                      hArgsTrans hPremisesBool (spec___eo_prog_contra M hM)
                      (by simpa [premiseTermList, __eo_cmd_step_proven] using hProg))
              | cons n3 premises =>
                  exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))

theorem cmd_step_proven_refl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.refl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.refl args premises) :=
by
  intro hCmdTrans hPremisesBool hProg
  cases args with
  | nil =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hArgsTrans : AllHaveSmtTranslation [a1] := by
                intro t ht
                simp at ht
                rcases ht with rfl
                simpa [cmdTranslationOk] using hCmdTrans
              simpa [__eo_cmd_step_proven] using
                (step_rule_properties_narg_mprem M [a1] []
                  (fun
                    | [a1], [] => __eo_prog_refl a1
                    | _, _ => Term.Stuck)
                  hArgsTrans
                  hPremisesBool
                  (spec___eo_prog_refl M hM)
                  (by simpa [__eo_cmd_step_proven] using hProg))
          | cons n premises =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons a2 args =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))

theorem cmd_step_proven_symm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.symm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.symm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.symm args premises) :=
by
  intro _hCmdTrans hPremisesBool hProg
  cases args with
  | nil =>
      cases premises with
      | nil =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons n1 premises =>
          cases premises with
          | nil =>
              have hArgsTrans : AllHaveSmtTranslation [] := by
                intro t ht
                cases ht
              simpa [premiseTermList, __eo_cmd_step_proven] using
                (step_rule_properties_narg_mprem M [] (premiseTermList s
                    (CIndexList.cons n1 CIndexList.nil))
                  (fun
                    | [], [X] => __eo_prog_symm (Proof.pf X)
                    | _, _ => Term.Stuck)
                  hArgsTrans hPremisesBool (spec___eo_prog_symm M hM)
                  (by simpa [premiseTermList, __eo_cmd_step_proven] using hProg))
          | cons n2 premises =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))

theorem cmd_step_proven_trans_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.trans args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.trans args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.trans args premises) :=
by
  intro _hCmdTrans hPremises hProg
  cases args with
  | nil =>
      have hArgsTrans : AllHaveSmtTranslation [] := by
        intro t ht
        cases ht
      simpa [__eo_cmd_step_proven, mk_premise_list_and_eq_premiseAndFormulaList] using
        (step_rule_properties_narg_mprem M [] (premiseTermList s premises)
          (fun
            | [], premises => __eo_prog_trans (Proof.pf (premiseAndFormulaList premises))
            | _, _ => Term.Stuck)
          hArgsTrans hPremises (spec___eo_prog_trans M hM)
          (by
            simpa [__eo_cmd_step_proven, mk_premise_list_and_eq_premiseAndFormulaList]
              using hProg))
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
