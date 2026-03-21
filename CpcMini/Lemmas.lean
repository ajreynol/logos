import CpcMini.SmtModel
import CpcMini.Logos
import CpcMini.Spec

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


/- The theorem statements -/

/- correctness theorem for __eo_prog_scope -/
theorem correct___eo_prog_scope (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_contra -/
theorem correct___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  (Not (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_refl -/
theorem correct___eo_prog_refl (M : SmtModel) (x1 : Term) :
  (Not (eo_interprets M (__eo_prog_refl x1) false)) :=
by
  sorry

/- correctness theorem for __eo_prog_symm -/
theorem correct___eo_prog_symm (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not (eo_interprets M (__eo_prog_symm (Proof.pf x1)) false)) :=
by
  sorry




/- Helper definitions -/

def __eo_lem_state_to_formula_rec : CState -> Term -> Term
  | _ , Term.Stuck  => Term.Stuck
  | CState.nil, F => F
  | (CState.cons (CStateObj.assume F) s), (Term.Apply (Term.Apply Term.imp F1) (Term.Apply (Term.Apply Term.imp F2) F3)) => (Term.Apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.and F) F1)) (Term.Apply (Term.Apply Term.imp F2) F3))
  | (CState.cons (CStateObj.assume_push F) s), (Term.Apply (Term.Apply Term.imp F1) (Term.Apply (Term.Apply Term.imp F2) F3)) => (Term.Apply (Term.Apply Term.imp F1) (Term.Apply (Term.Apply Term.imp (Term.Apply (Term.Apply Term.and F) F2)) F3))
  | (CState.cons (CStateObj.proven F) s), (Term.Apply (Term.Apply Term.imp F1) (Term.Apply (Term.Apply Term.imp F2) F3)) => (Term.Apply (Term.Apply Term.imp F1) (Term.Apply (Term.Apply Term.imp F2) (Term.Apply (Term.Apply Term.and F) F3)))
  | s, F => Term.Stuck


def __eo_lem_state_to_formula (s : CState) : Term :=
  
    let _v0 := (Term.Apply Term.imp (Term.Boolean true))
    (__eo_lem_state_to_formula_rec s (Term.Apply _v0 (Term.Apply _v0 (Term.Boolean true))))


