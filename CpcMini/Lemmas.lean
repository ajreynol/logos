import CpcMini.SmtModel
import CpcMini.SmtModelLemmas
import CpcMini.Logos
import CpcMini.Spec
import CpcMini.Rules

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


/- The theorem statements -/

/- correctness theorem for __eo_prog_scope -/
theorem typed___eo_prog_scope (M : SmtModel) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) :=
by
  sorry

theorem correct___eo_prog_scope
    (M : SmtModel) (hM : smt_model_well_typed M) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) ->
  (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true) :=
by
  exact RuleProofs.correct___eo_prog_scope M hM x1 x2

/- correctness theorem for __eo_prog_contra -/
theorem typed___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) :=
by
  intro hX1True _hX2True hProg
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_interprets_true M x1 hX1True
  cases x2 with
  | Apply f a =>
      cases f with
      | not =>
          by_cases hEq : x1 = a
          · subst hEq
            have hEqTerm : __eo_eq x1 x1 = Term.Boolean true := by
              by_cases hStuck : x1 = Term.Stuck
              · exact False.elim (hX1NotStuck hStuck)
              · simp [__eo_eq, hStuck, eo_lit_teq]
            have hContraFalse :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply Term.not x1)) =
                  Term.Boolean false := by
              rw [__eo_prog_contra, hEqTerm]
              simp [__eo_requires, eo_lit_teq, eo_lit_ite, eo_lit_not, SmtEval.smt_lit_not]
            simpa [RuleProofs.eo_has_bool_type, hContraFalse, __eo_to_smt, __smtx_typeof]
          · have hEqNe : __eo_eq x1 a ≠ Term.Boolean true := by
              intro hEqTerm
              by_cases hXStuck : x1 = Term.Stuck
              · subst hXStuck
                simp [__eo_eq] at hEqTerm
              · by_cases hAStuck : a = Term.Stuck
                · subst hAStuck
                  simp [__eo_eq] at hEqTerm
                · simp [__eo_eq, hXStuck, hAStuck, eo_lit_teq] at hEqTerm
                  exact hEq hEqTerm.symm
            have hContraStuck :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply Term.not a)) = Term.Stuck := by
              rw [__eo_prog_contra]
              simp [__eo_requires, eo_lit_teq, eo_lit_ite, hEqNe]
            exact False.elim (hProg hContraStuck)
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_contra]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_contra]))

theorem correct___eo_prog_contra
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) ->
  (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true) :=
by
  exact RuleProofs.correct___eo_prog_contra M x1 x2

/- correctness theorem for __eo_prog_refl -/
theorem typed___eo_prog_refl (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_prog_refl x1 ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) :=
by
  intro hTrans _hProg
  by_cases hStuck : x1 = Term.Stuck
  · exfalso
    apply hTrans
    simp [RuleProofs.eo_has_smt_translation, hStuck, __eo_to_smt, __smtx_typeof]
  · have hRefl :
        __eo_prog_refl x1 = Term.Apply (Term.Apply Term.eq x1) x1 := by
      simp [__eo_prog_refl, hStuck]
    rw [hRefl]
    unfold RuleProofs.eo_has_bool_type
    simpa [__eo_to_smt, __smtx_typeof] using
      RuleProofs.smtx_typeof_eq_refl (__smtx_typeof (__eo_to_smt x1)) hTrans

theorem correct___eo_prog_refl
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  exact RuleProofs.correct___eo_prog_refl_of_smt_translation M x1

/- A typed version of `refl` that is actually provable.
   This is the candidate replacement template if we decide to strengthen the
   rule assumptions in the checker proof. -/
theorem correct___eo_prog_refl_of_smt_translation
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  exact RuleProofs.correct___eo_prog_refl_of_smt_translation M x1

/- correctness theorem for __eo_prog_symm -/
theorem typed___eo_prog_symm (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) :=
by
  intro hXTrue hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | Apply g b =>
          cases g with
          | eq =>
              rcases RuleProofs.eo_eq_operands_same_smt_type M b a hXTrue with
                ⟨hTy, hNonNone⟩
              have hNonNone' : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                simpa [hTy] using hNonNone
              have hEqTy :
                  __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a))
                    (__smtx_typeof (__eo_to_smt b)) = SmtType.Bool := by
                exact (RuleProofs.smtx_typeof_eq_bool_iff
                  (__smtx_typeof (__eo_to_smt a))
                  (__smtx_typeof (__eo_to_smt b))).mpr ⟨hTy.symm, hNonNone'⟩
              exact by
                simp [RuleProofs.eo_has_bool_type, __eo_prog_symm, __mk_symm, __eo_to_smt,
                  __smtx_typeof, hEqTy]
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
      | not =>
          cases a with
          | Apply f2 a2 =>
              cases f2 with
              | Apply g2 b2 =>
                  cases g2 with
                  | eq =>
                      have hEqFalse :
                          eo_interprets M (Term.Apply (Term.Apply Term.eq b2) a2) false :=
                        RuleProofs.eo_interprets_not_true_implies_false M _ hXTrue
                      rcases RuleProofs.eo_eq_operands_same_smt_type_of_false M b2 a2 hEqFalse with
                        ⟨hTy, hNonNone⟩
                      have hNonNone' : __smtx_typeof (__eo_to_smt a2) ≠ SmtType.None := by
                        simpa [hTy] using hNonNone
                      have hEqTy :
                          __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a2))
                            (__smtx_typeof (__eo_to_smt b2)) = SmtType.Bool := by
                        exact (RuleProofs.smtx_typeof_eq_bool_iff
                          (__smtx_typeof (__eo_to_smt a2))
                          (__smtx_typeof (__eo_to_smt b2))).mpr ⟨hTy.symm, hNonNone'⟩
                      exact by
                        simp [RuleProofs.eo_has_bool_type, __eo_prog_symm, __mk_symm, __eo_to_smt,
                          __smtx_typeof, hEqTy, smt_lit_ite, smt_lit_Teq]
                  | _ =>
                      exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
              | _ =>
                  exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))

theorem correct___eo_prog_symm
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  (eo_interprets M x1 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) ->
  (eo_interprets M (__eo_prog_symm (Proof.pf x1)) true) :=
by
  sorry

theorem eo_requires_not_stuck (x1 x2 x3 : Term) :
  __eo_requires x1 x2 x3 ≠ Term.Stuck ->
  x1 = x2 ∧ x1 ≠ Term.Stuck ∧ x3 ≠ Term.Stuck := by
  intro hReq
  by_cases hEq : x1 = x2
  · by_cases hStuck : x1 = Term.Stuck
    · have hX2Stuck : x2 = Term.Stuck := by simpa [hEq] using hStuck
      exact False.elim <| hReq (by
        simp [__eo_requires, eo_lit_teq, hEq, hStuck, hX2Stuck, eo_lit_ite, eo_lit_not,
          SmtEval.smt_lit_not])
    · refine ⟨hEq, hStuck, ?_⟩
      intro hX3
      exact hReq (by
        simp [__eo_requires, eo_lit_teq, hEq, hStuck, hX3, eo_lit_ite, eo_lit_not,
          SmtEval.smt_lit_not])
  · exact False.elim <| hReq (by
      simp [__eo_requires, eo_lit_teq, hEq, eo_lit_ite])

theorem eo_requires_eq_of_eq_not_stuck (x1 x2 x3 : Term) :
  x1 = x2 ->
  x1 ≠ Term.Stuck ->
  __eo_requires x1 x2 x3 = x3 := by
  intro hEq hNotStuck
  subst x2
  cases x1 <;> simp [__eo_requires, eo_lit_teq, eo_lit_ite, eo_lit_not, SmtEval.smt_lit_not] at hNotStuck ⊢

theorem mk_trans_step_eq (t1 t2 t3 t4 tail : Term) :
  t1 ≠ Term.Stuck ->
  t2 ≠ Term.Stuck ->
  __mk_trans t1 t2 (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t3) t4)) tail) =
    __eo_requires t2 t3 (__mk_trans t1 t4 tail) := by
  sorry

theorem mk_trans_base_eq (t1 t2 : Term) :
  t1 ≠ Term.Stuck ->
  t2 ≠ Term.Stuck ->
  __mk_trans t1 t2 (Term.Boolean true) = Term.Apply (Term.Apply Term.eq t1) t2 := by
  sorry

theorem term_ne_stuck_of_smt_type_not_none (t : Term) :
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
  t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  simp [__eo_to_smt, __smtx_typeof] at hTy

private theorem mk_trans_shape_of_not_stuck (t1 t2 tail : Term) :
  t1 ≠ Term.Stuck ->
  t2 ≠ Term.Stuck ->
  __mk_trans t1 t2 tail ≠ Term.Stuck ->
  tail = Term.Boolean true ∨
    ∃ t3 t4 tail', tail = Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t3) t4)) tail' := by
  sorry

private theorem sizeOf_lt_trans_tail (t3 t4 tail : Term) :
  sizeOf tail <
    sizeOf (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t3) t4)) tail) := by
  simp
  omega

private theorem typed_mk_trans (M : SmtModel) (t1 t2 tail : Term) :
    eo_interprets M
      (Term.Apply
        (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t1) t2))
        tail) true ->
    __mk_trans t1 t2 tail ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__mk_trans t1 t2 tail) := by
  intro hChainTrue hProg
  let eq12 := Term.Apply (Term.Apply Term.eq t1) t2
  have hEq12True : eo_interprets M eq12 true := by
    simpa [eq12] using RuleProofs.eo_interprets_and_left M eq12 tail hChainTrue
  rcases RuleProofs.eo_eq_operands_same_smt_type M t1 t2 hEq12True with ⟨hTy12, hT1Ty⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_not_none t1 hT1Ty
  have hT2Ty : __smtx_typeof (__eo_to_smt t2) ≠ SmtType.None := by
    rwa [← hTy12]
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_not_none t2 hT2Ty
  rcases mk_trans_shape_of_not_stuck t1 t2 tail hT1NotStuck hT2NotStuck hProg with hTail
  cases hTail with
  | inl hBase =>
      subst hBase
      rw [mk_trans_base_eq t1 t2 hT1NotStuck hT2NotStuck]
      exact RuleProofs.eo_has_bool_type_eq_of_true M t1 t2 hEq12True
  | inr hStep =>
      rcases hStep with ⟨t3, t4, tail', hTail⟩
      subst hTail
      let eq34 := Term.Apply (Term.Apply Term.eq t3) t4
      have hTailTrue :
          eo_interprets M (Term.Apply (Term.Apply Term.and eq34) tail') true := by
        simpa [eq12, eq34] using
          RuleProofs.eo_interprets_and_right M eq12
            (Term.Apply (Term.Apply Term.and eq34) tail') hChainTrue
      have hEq34True : eo_interprets M eq34 true := by
        simpa [eq34] using
          RuleProofs.eo_interprets_and_left M eq34 tail' hTailTrue
      have hRestTrue : eo_interprets M tail' true := by
        simpa [eq34] using
          RuleProofs.eo_interprets_and_right M eq34 tail' hTailTrue
      have hReqNotStuck :
          __eo_requires t2 t3 (__mk_trans t1 t4 tail') ≠ Term.Stuck := by
        rw [← mk_trans_step_eq t1 t2 t3 t4 tail' hT1NotStuck hT2NotStuck]
        exact hProg
      rcases eo_requires_not_stuck t2 t3 (__mk_trans t1 t4 tail') hReqNotStuck with
        ⟨h23, _hT2NotStuck, hRecNotStuck⟩
      have hEq24True :
          eo_interprets M (Term.Apply (Term.Apply Term.eq t2) t4) true := by
        simpa [eq34, h23] using hEq34True
      have hEq14True :
          eo_interprets M (Term.Apply (Term.Apply Term.eq t1) t4) true :=
        RuleProofs.eo_interprets_eq_trans M t1 t2 t4 hEq12True hEq24True
      have hCompressedTrue :
          eo_interprets M
            (Term.Apply
              (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t1) t4))
              tail') true :=
        RuleProofs.eo_interprets_and_intro M
          (Term.Apply (Term.Apply Term.eq t1) t4) tail'
          hEq14True hRestTrue
      rw [mk_trans_step_eq t1 t2 t3 t4 tail' hT1NotStuck hT2NotStuck]
      rw [eo_requires_eq_of_eq_not_stuck t2 t3 (__mk_trans t1 t4 tail') h23 hT2NotStuck]
      exact typed_mk_trans M t1 t4 tail' hCompressedTrue hRecNotStuck
termination_by sizeOf tail
decreasing_by
  simpa [hTail] using sizeOf_lt_trans_tail t3 t4 tail'

/- correctness theorem for __eo_prog_trans -/
theorem typed___eo_prog_trans (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  __eo_prog_trans (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf x1)) :=
by
  intro hX1True hProg
  cases x1 with
  | Apply f tail =>
      cases f with
      | Apply g eq12 =>
          cases g with
          | and =>
              cases eq12 with
              | Apply g2 t2 =>
                  cases g2 with
                  | Apply g3 t1 =>
                      cases g3 with
                      | eq =>
                          simpa [__eo_prog_trans] using
                            typed_mk_trans M t1 t2 tail hX1True hProg
                      | _ =>
                          exact False.elim (hProg (by simp [__eo_prog_trans]))
                  | _ =>
                      exact False.elim (hProg (by simp [__eo_prog_trans]))
              | _ =>
                  exact False.elim (hProg (by simp [__eo_prog_trans]))
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_trans]))
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_trans]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_trans]))

theorem correct___eo_prog_trans
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  (eo_interprets M x1 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf x1)) ->
  (eo_interprets M (__eo_prog_trans (Proof.pf x1)) true) :=
by
  sorry




/- Helper definitions -/
