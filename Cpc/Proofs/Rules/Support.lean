import Cpc.Proofs.Rules.Common

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

structure StepRuleProperties
    (M : SmtModel) (premises : List Term) (P : Term) : Prop where
  facts_of_true :
    AllInterpretedTrue M premises ->
    RuleProofs.RuleResultFacts M P
  has_bool_type :
    RuleProofs.eo_has_bool_type P

def StepPopRuleProperties
    (x1 : Term) (premises : List Term) (P : Term) : Prop :=
  ∃ x2,
    x2 ∈ premises ∧
    (forall (M : SmtModel), model_total_typed M ->
      ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
      RuleProofs.RuleResultFacts M P) ∧
    RuleProofs.eo_has_bool_type P
