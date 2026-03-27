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

theorem correct___eo_prog_scope
    (M : SmtModel) (hM : smt_model_well_typed M) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation x2 ->
  __eo_typeof x1 = Term.Bool ->
  __eo_typeof x2 = Term.Bool ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true) :=
by
  intro hImp hTrans1 hTrans2 hTy1 hTy2 hProg
  have hBool :
      RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) :=
    typed___eo_prog_scope_impl M x1 x2 hImp hTrans1 hTrans2 hTy1 hTy2 hProg
  exact correct___eo_prog_scope_impl M hM x1 x2 hImp hBool

theorem correct___eo_prog_contra
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true) :=
by
  intro hX1True hX2True hProg
  have hBool :
      RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) :=
    typed___eo_prog_contra_impl M x1 x2 hX1True hX2True hProg
  exact correct___eo_prog_contra_impl M _hM x1 x2 hX1True hX2True hBool

theorem correct___eo_prog_refl
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_prog_refl x1 ≠ Term.Stuck ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  intro hTrans hProg
  have hBool :
      RuleProofs.eo_has_bool_type (__eo_prog_refl x1) :=
    typed___eo_prog_refl_impl x1 hTrans hProg
  exact correct___eo_prog_refl_impl M _hM x1 hTrans hBool

theorem correct___eo_prog_symm
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  (eo_interprets M x1 true) ->
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  (eo_interprets M (__eo_prog_symm (Proof.pf x1)) true) :=
by
  intro hXTrue hProg
  have hBool :
      RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) :=
    typed___eo_prog_symm_impl M x1 hXTrue hProg
  exact correct___eo_prog_symm_impl M _hM x1 hXTrue hBool

theorem correct___eo_prog_trans
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  (eo_interprets M x1 true) ->
  __eo_prog_trans (Proof.pf x1) ≠ Term.Stuck ->
  (eo_interprets M (__eo_prog_trans (Proof.pf x1)) true) :=
by
  intro hXTrue hProg
  have hBool :
      RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf x1)) :=
    typed___eo_prog_trans_impl M x1 hXTrue hProg
  exact correct___eo_prog_trans_impl M _hM x1 hXTrue hBool
