import CpcMicro.Proofs.Rules.Common

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

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

def AllTypeofBool (ts : List Term) : Prop :=
  ∀ t ∈ ts, __eo_typeof t = Term.Bool

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
    eo_interprets M P true
  has_bool_type :
    RuleProofs.eo_has_bool_type P

def StepPopRuleProperties
    (x1 : Term) (premises : List Term) (P : Term) : Prop :=
  ∃ x2,
    x2 ∈ premises ∧
    (forall (M : SmtModel), model_total_typed M ->
      ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
      eo_interprets M P true) ∧
    RuleProofs.eo_has_bool_type P
