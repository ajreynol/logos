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

def premiseAndFormulaList : List Term -> Term
  | [] => Term.Boolean true
  | p :: ps => Term.Apply (Term.Apply Term.and p) (premiseAndFormulaList ps)

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
