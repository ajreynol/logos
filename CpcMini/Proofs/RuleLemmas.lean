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

structure StepRuleProperties
    (M : SmtModel) (premises : List Term) (P : Term) : Prop where
  facts_of_true :
    AllInterpretedTrue M premises ->
    RuleProofs.RuleResultFacts M P
  has_bool_type :
    RuleProofs.eo_has_bool_type P

structure ScopeRuleProperties
    (x1 x2 P : Term) : Prop where
  facts_of_imp :
    forall (M : SmtModel), model_total_typed M ->
      ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
      RuleProofs.RuleResultFacts M P
  has_bool_type :
    RuleProofs.eo_has_bool_type P

theorem cmd_step_pop_proven_scope_properties
    (x1 x2 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation x2 ->
  __eo_typeof x1 = Term.Bool ->
  __eo_typeof x2 = Term.Bool ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  ScopeRuleProperties x1 x2 (__eo_prog_scope x1 (Proof.pf x2)) :=
by
  intro hTrans1 hTrans2 hTy1 hTy2 hProg
  have hBool1 : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type x1 hTrans1 hTy1
  have hBool2 : RuleProofs.eo_has_bool_type x2 :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type x2 hTrans2 hTy2
  constructor
  · intro M hM hImp
    exact facts___eo_prog_scope_impl M hM x1 x2 hImp hTrans1 hTrans2 hTy1 hTy2 hProg
  · exact typed___eo_prog_scope_of_bool_args x1 x2 hBool1 hBool2 hProg

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
                  let X1 := __eo_state_proven_nth s n1
                  let X2 := __eo_state_proven_nth s n2
                  constructor
                  · intro hTrue
                    exact facts___eo_prog_contra_impl M hM X1 X2
                      (hTrue X1 (by simp [X1, premiseTermList]))
                      (hTrue X2 (by simp [X2, premiseTermList]))
                      (by simpa [X1, X2, premiseTermList, __eo_cmd_step_proven] using hProg)
                  · exact typed___eo_prog_contra_impl X1 X2
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      (hPremisesBool X2 (by simp [X2, premiseTermList]))
                      (by simpa [X1, X2, premiseTermList, __eo_cmd_step_proven] using hProg)
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
              have hATrans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk] using hCmdTrans
              refine ⟨?_, ?_⟩
              · intro _hTrue
                exact facts___eo_prog_refl_impl M hM a1 hATrans
                  (by simpa [__eo_cmd_step_proven] using hProg)
              · exact typed___eo_prog_refl_impl a1 hATrans
                  (by simpa [__eo_cmd_step_proven] using hProg)
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
              let X := __eo_state_proven_nth s n1
              refine ⟨?_, ?_⟩
              · intro hTrue
                exact facts___eo_prog_symm_impl M hM X
                  (hTrue X (by simp [X, premiseTermList]))
                  (by simpa [X, premiseTermList, __eo_cmd_step_proven] using hProg)
              · exact typed___eo_prog_symm_impl X
                  (hPremisesBool X (by simp [X, premiseTermList]))
                  (by simpa [X, premiseTermList, __eo_cmd_step_proven] using hProg)
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
      let premisesL := premiseTermList s premises
      have hProps :
          StepRuleProperties M premisesL
            (__eo_prog_trans (Proof.pf (premiseAndFormulaList premisesL))) := by
        refine ⟨?_, ?_⟩
        · intro hTrue
          exact facts___eo_prog_trans_impl M hM (premiseAndFormulaList premisesL)
            (premiseAndFormulaList_true_of_all_true M premisesL hTrue)
            (by
              simpa [premisesL, __eo_cmd_step_proven, mk_premise_list_and_eq_premiseAndFormulaList]
                using hProg)
        · exact typed___eo_prog_trans_impl (premiseAndFormulaList premisesL)
            (premiseAndFormulaList_has_bool_type premisesL (by simpa [premisesL] using hPremises))
            (by
              simpa [premisesL, __eo_cmd_step_proven, mk_premise_list_and_eq_premiseAndFormulaList]
                using hProg)
      simpa [premisesL, __eo_cmd_step_proven, mk_premise_list_and_eq_premiseAndFormulaList] using hProps
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
