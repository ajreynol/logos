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
  (__eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck) ->
  (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true) :=
by
  sorry

/- If `symm` succeeds, its referenced premise was a usable term. -/
theorem eo_prog_symm_premises_not_stuck (x1 : Term) :
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  x1 ≠ Term.Stuck :=
by
  intro hProg
  intro hx1
  apply hProg
  simp [__eo_prog_symm, __mk_symm, hx1]

/- If `contra` succeeds, both referenced premises were usable terms. -/
theorem eo_prog_contra_premises_not_stuck (x1 x2 : Term) :
  __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  x1 ≠ Term.Stuck ∧ x2 ≠ Term.Stuck :=
by
  intro hProg
  constructor
  · intro hx1
    apply hProg
    cases hx2 : x2 with
    | Apply f a =>
        cases f <;>
          simpa [__eo_prog_contra, __eo_requires, __eo_eq, eo_lit_teq, eo_lit_ite, hx1, hx2]
    | _ =>
        simpa [__eo_prog_contra, __eo_requires, __eo_eq, eo_lit_teq, eo_lit_ite, hx1, hx2]
  · intro hx2
    apply hProg
    simp [__eo_prog_contra, __eo_requires, __eo_eq, hx2]

/- correctness theorem for __eo_prog_contra -/
theorem correct___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  (__eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck) ->
  (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_refl -/
theorem correct___eo_prog_refl (M : SmtModel) (x1 : Term) :
  (__eo_prog_refl x1 ≠ Term.Stuck) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_symm -/
theorem correct___eo_prog_symm (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (__eo_prog_symm (Proof.pf x1) ≠ Term.Stuck) ->
  (eo_interprets M (__eo_prog_symm (Proof.pf x1)) true) :=
by
  sorry
