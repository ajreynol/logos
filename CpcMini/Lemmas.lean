import CpcMini.Rules.Common
import CpcMini.Rules.Scope
import CpcMini.Rules.Contra
import CpcMini.Rules.Refl
import CpcMini.Rules.Symm
import CpcMini.Rules.Trans

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- The theorem statements -/

structure StepRuleSpec1Arg0Prem (M : SmtModel) (mk : Term -> Term) : Prop where
  true_of_translation :
    ∀ a1 : Term,
      RuleProofs.eo_has_smt_translation a1 ->
      mk a1 ≠ Term.Stuck ->
      eo_interprets M (mk a1) true
  bool_of_translation :
    ∀ a1 : Term,
      RuleProofs.eo_has_smt_translation a1 ->
      mk a1 ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type (mk a1)

structure StepRuleSpec0Arg1Prem (M : SmtModel) (mk : Term -> Term) : Prop where
  true_of_true :
    ∀ X : Term,
      eo_interprets M X true ->
      mk X ≠ Term.Stuck ->
      eo_interprets M (mk X) true
  bool_of_bool :
    ∀ X : Term,
      RuleProofs.eo_has_bool_type X ->
      mk X ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type (mk X)

structure StepRuleSpec0Arg2Prem (M : SmtModel) (mk : Term -> Term -> Term) : Prop where
  true_of_true :
    ∀ X1 X2 : Term,
      eo_interprets M X1 true ->
      eo_interprets M X2 true ->
      mk X1 X2 ≠ Term.Stuck ->
      eo_interprets M (mk X1 X2) true
  bool_of_bool :
    ∀ X1 X2 : Term,
      RuleProofs.eo_has_bool_type X1 ->
      RuleProofs.eo_has_bool_type X2 ->
      mk X1 X2 ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type (mk X1 X2)

structure StepRuleSpec0ArgNPremAnd (M : SmtModel) (mk : Term -> Term) : Prop where
  true_of_true :
    ∀ X : Term,
      eo_interprets M X true ->
      mk X ≠ Term.Stuck ->
      eo_interprets M (mk X) true
  bool_of_bool :
    ∀ X : Term,
      RuleProofs.eo_has_bool_type X ->
      mk X ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type (mk X)

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
    (M : SmtModel) (hM : smt_model_well_typed M) (x1 x2 : Term) :
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
    (M : SmtModel) (hM : smt_model_well_typed M) :
  StepRuleSpec0Arg2Prem M (fun X1 X2 => __eo_prog_contra (Proof.pf X1) (Proof.pf X2)) :=
by
  refine ⟨?_, ?_⟩
  · intro X1 X2 hX1True hX2True hProg
    have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
      RuleProofs.eo_has_bool_type_of_interprets_true M X1 hX1True
    have hX2Bool : RuleProofs.eo_has_bool_type X2 :=
      RuleProofs.eo_has_bool_type_of_interprets_true M X2 hX2True
    have hBool :
        RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf X1) (Proof.pf X2)) :=
      typed___eo_prog_contra_impl X1 X2 hX1Bool hX2Bool hProg
    exact correct___eo_prog_contra_impl M hM X1 X2 hX1True hX2True hBool
  · intro X1 X2 hX1Bool hX2Bool hProg
    exact typed___eo_prog_contra_impl X1 X2 hX1Bool hX2Bool hProg

theorem spec___eo_prog_refl
    (M : SmtModel) (hM : smt_model_well_typed M) :
  StepRuleSpec1Arg0Prem M __eo_prog_refl :=
by
  refine ⟨?_, ?_⟩
  · intro a1 hTrans hProg
    have hBool : RuleProofs.eo_has_bool_type (__eo_prog_refl a1) :=
      typed___eo_prog_refl_impl a1 hTrans hProg
    exact correct___eo_prog_refl_impl M hM a1 hTrans hBool
  · intro a1 hTrans hProg
    exact typed___eo_prog_refl_impl a1 hTrans hProg

theorem spec___eo_prog_symm
    (M : SmtModel) (hM : smt_model_well_typed M) :
  StepRuleSpec0Arg1Prem M (fun X => __eo_prog_symm (Proof.pf X)) :=
by
  refine ⟨?_, ?_⟩
  · intro X hXTrue hProg
    have hXBool : RuleProofs.eo_has_bool_type X :=
      RuleProofs.eo_has_bool_type_of_interprets_true M X hXTrue
    have hBool :
        RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf X)) :=
      typed___eo_prog_symm_impl X hXBool hProg
    exact correct___eo_prog_symm_impl M hM X hXTrue hBool
  · intro X hXBool hProg
    exact typed___eo_prog_symm_impl X hXBool hProg

theorem spec___eo_prog_trans
    (M : SmtModel) (hM : smt_model_well_typed M) :
  StepRuleSpec0ArgNPremAnd M (fun X => __eo_prog_trans (Proof.pf X)) :=
by
  refine ⟨?_, ?_⟩
  · intro X hXTrue hProg
    have hXBool : RuleProofs.eo_has_bool_type X :=
      RuleProofs.eo_has_bool_type_of_interprets_true M X hXTrue
    have hBool :
        RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf X)) :=
      typed___eo_prog_trans_impl X hXBool hProg
    exact correct___eo_prog_trans_impl M hM X hXTrue hBool
  · intro X hXBool hProg
    exact typed___eo_prog_trans_impl X hXBool hProg
