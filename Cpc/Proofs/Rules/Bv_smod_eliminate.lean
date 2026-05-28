import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_requires_arg_eq_of_ne_stuck
    {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_eq_true_eq {x y : Term} :
    __eo_eq x y = Term.Boolean true ->
    y = x := by
  intro h
  cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢
  all_goals simpa using h

private theorem eo_and_eq_true_left {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_and] at h ⊢
  · exact h.1
  · split at h <;> cases h

private theorem eo_and_eq_true_right {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_and] at h ⊢
  · exact h.2
  · split at h <;> cases h

private theorem bv_smod_guard_eqs_of_ne_stuck
    {x w wm pw px pwm px' body : Term} :
    __eo_requires
        (__eo_and
          (__eo_and (__eo_and (__eo_eq w pw) (__eo_eq x px))
            (__eo_eq wm pwm))
          (__eo_eq x px'))
        (Term.Boolean true) body ≠ Term.Stuck ->
    pw = w ∧ px = x ∧ pwm = wm ∧ px' = x := by
  intro hReq
  have hGuard :
      __eo_and
          (__eo_and (__eo_and (__eo_eq w pw) (__eo_eq x px))
            (__eo_eq wm pwm))
          (__eo_eq x px') =
        Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReq
  have hLeft :
      __eo_and (__eo_and (__eo_eq w pw) (__eo_eq x px))
          (__eo_eq wm pwm) =
        Term.Boolean true :=
    eo_and_eq_true_left hGuard
  have hXpx' : __eo_eq x px' = Term.Boolean true :=
    eo_and_eq_true_right hGuard
  have hLeftLeft :
      __eo_and (__eo_eq w pw) (__eo_eq x px) = Term.Boolean true :=
    eo_and_eq_true_left hLeft
  have hW : __eo_eq w pw = Term.Boolean true :=
    eo_and_eq_true_left hLeftLeft
  have hX : __eo_eq x px = Term.Boolean true :=
    eo_and_eq_true_right hLeftLeft
  have hWm : __eo_eq wm pwm = Term.Boolean true :=
    eo_and_eq_true_right hLeft
  exact ⟨eo_eq_true_eq hW, eo_eq_true_eq hX, eo_eq_true_eq hWm,
    eo_eq_true_eq hXpx'⟩

private theorem bv_smod_eliminate_shape_of_ne_stuck
    (x y w wm P1 P2 : Term) :
    __eo_prog_bv_smod_eliminate x y w wm (Proof.pf P1) (Proof.pf P2) ≠
        Term.Stuck ->
    ∃ pw px pwm px',
      P1 =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) pw)
            (Term.Apply (Term.UOp UserOp._at_bvsize) px) ∧
      P2 =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) pwm)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp._at_bvsize) px'))
              (Term.Numeral 1)) := by
  intro hProg
  have hx : x ≠ Term.Stuck := by
    intro hx
    subst x
    exact hProg (__eo_prog_bv_smod_eliminate.eq_1 y w wm (Proof.pf P1) (Proof.pf P2))
  have hy : y ≠ Term.Stuck := by
    intro hy
    subst y
    exact hProg (__eo_prog_bv_smod_eliminate.eq_2 x w wm (Proof.pf P1) (Proof.pf P2) hx)
  have hw : w ≠ Term.Stuck := by
    intro hw
    subst w
    exact hProg (__eo_prog_bv_smod_eliminate.eq_3 x y wm (Proof.pf P1) (Proof.pf P2) hx hy)
  have hwm : wm ≠ Term.Stuck := by
    intro hwm
    subst wm
    exact hProg (__eo_prog_bv_smod_eliminate.eq_4 x y w (Proof.pf P1) (Proof.pf P2) hx hy hw)
  by_cases hShape :
      ∃ pw px pwm px',
        P1 =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) pw)
              (Term.Apply (Term.UOp UserOp._at_bvsize) px) ∧
        P2 =
            Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) pwm)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp._at_bvsize) px'))
                (Term.Numeral 1))
  · exact hShape
  · have hStuck :
        __eo_prog_bv_smod_eliminate x y w wm (Proof.pf P1) (Proof.pf P2) =
          Term.Stuck := by
      exact __eo_prog_bv_smod_eliminate.eq_6 x y w wm (Proof.pf P1) (Proof.pf P2)
        hx hy hw hwm (by
          intro pw px pwm px' hp1 hp2
          cases hp1
          cases hp2
          exact hShape ⟨pw, px, pwm, px', rfl, rfl⟩)
    exact False.elim (hProg hStuck)

/--
Trusted semantic core for the canonical `bv_smod_eliminate` expansion.

The surrounding theorem proves that the checker command is in this canonical
shape and that the syntactic guards in `__eo_prog_bv_smod_eliminate` have
accepted.  The remaining obligation is the bit-vector arithmetic identity
between SMT `bvsmod` and its expansion.
-/
private theorem trusted_bv_smod_eliminate_canonical_properties
    (M : SmtModel) (hM : model_total_typed M)
    (x y w wm : Term) :
    cArgListTranslationOk
        (CArgList.cons x
          (CArgList.cons y
            (CArgList.cons w (CArgList.cons wm CArgList.nil)))) ->
    AllHaveBoolType
      [Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x),
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) wm)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (Term.Numeral 1))] ->
    __eo_typeof
        (__eo_prog_bv_smod_eliminate x y w wm
          (Proof.pf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) w)
              (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
          (Proof.pf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq) wm)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                (Term.Numeral 1))))) =
      Term.Bool ->
    StepRuleProperties M
      [Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) w)
          (Term.Apply (Term.UOp UserOp._at_bvsize) x),
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq) wm)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg)
              (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (Term.Numeral 1))]
      (__eo_prog_bv_smod_eliminate x y w wm
        (Proof.pf
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) w)
            (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
        (Proof.pf
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq) wm)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp._at_bvsize) x))
              (Term.Numeral 1))))) := by
  sorry

theorem cmd_step_bv_smod_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_smod_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_smod_eliminate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_smod_eliminate args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_smod_eliminate args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons x args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons y args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons w args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons wm args =>
                  cases args with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons n1 premises =>
                          cases premises with
                          | nil =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | cons n2 premises =>
                              cases premises with
                              | cons _ _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                              | nil =>
                                  let P1 := __eo_state_proven_nth s n1
                                  let P2 := __eo_state_proven_nth s n2
                                  change
                                    StepRuleProperties M [P1, P2]
                                      (__eo_prog_bv_smod_eliminate x y w wm
                                        (Proof.pf P1) (Proof.pf P2))
                                  have hProgLocal :
                                      __eo_prog_bv_smod_eliminate x y w wm
                                          (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck := by
                                    simpa [P1, P2] using hProg
                                  rcases bv_smod_eliminate_shape_of_ne_stuck
                                      x y w wm P1 P2 hProgLocal with
                                    ⟨pw, px, pwm, px', hP1, hP2⟩
                                  subst P1
                                  subst P2
                                  have hxNe : x ≠ Term.Stuck := by
                                    intro hx
                                    subst x
                                    exact hProgLocal
                                      (__eo_prog_bv_smod_eliminate.eq_1 y w wm
                                        (Proof.pf
                                          (Term.Apply
                                            (Term.Apply (Term.UOp UserOp.eq) pw)
                                            (Term.Apply (Term.UOp UserOp._at_bvsize) px)))
                                        (Proof.pf
                                          (Term.Apply
                                            (Term.Apply (Term.UOp UserOp.eq) pwm)
                                            (Term.Apply
                                              (Term.Apply (Term.UOp UserOp.neg)
                                                (Term.Apply (Term.UOp UserOp._at_bvsize) px'))
                                              (Term.Numeral 1)))))
                                  have hyNe : y ≠ Term.Stuck := by
                                    intro hy
                                    subst y
                                    exact hProgLocal
                                      (__eo_prog_bv_smod_eliminate.eq_2 x w wm _ _ hxNe)
                                  have hwNe : w ≠ Term.Stuck := by
                                    intro hw
                                    subst w
                                    exact hProgLocal
                                      (__eo_prog_bv_smod_eliminate.eq_3 x y wm _ _ hxNe hyNe)
                                  have hwmNe : wm ≠ Term.Stuck := by
                                    intro hwm
                                    subst wm
                                    exact hProgLocal
                                      (__eo_prog_bv_smod_eliminate.eq_4 x y w _ _ hxNe hyNe hwNe)
                                  have hReqNe := by
                                    have h := hProgLocal
                                    rw [hP1, hP2] at h
                                    rw [__eo_prog_bv_smod_eliminate.eq_5
                                      x y w wm pw px pwm px' hxNe hyNe hwNe hwmNe] at h
                                    exact h
                                  rcases bv_smod_guard_eqs_of_ne_stuck hReqNe with
                                    ⟨hpw, hpx, hpwm, hpx'⟩
                                  subst pw
                                  subst px
                                  subst pwm
                                  subst px'
                                  have hArgsTrans :
                                      cArgListTranslationOk
                                        (CArgList.cons x
                                          (CArgList.cons y
                                            (CArgList.cons w
                                              (CArgList.cons wm CArgList.nil)))) := by
                                    simpa [cmdTranslationOk] using hCmdTrans
                                  have hPremisesBoolCanonical :
                                      AllHaveBoolType
                                        [Term.Apply
                                            (Term.Apply (Term.UOp UserOp.eq) w)
                                            (Term.Apply (Term.UOp UserOp._at_bvsize) x),
                                          Term.Apply
                                            (Term.Apply (Term.UOp UserOp.eq) wm)
                                            (Term.Apply
                                              (Term.Apply (Term.UOp UserOp.neg)
                                                (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                                              (Term.Numeral 1))] := by
                                    simpa [AllHaveBoolType, premiseTermList, hP1, hP2]
                                      using hPremisesBool
                                  have hResultTyCanonical :
                                      __eo_typeof
                                          (__eo_prog_bv_smod_eliminate x y w wm
                                            (Proof.pf
                                              (Term.Apply
                                                (Term.Apply (Term.UOp UserOp.eq) w)
                                                (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
                                            (Proof.pf
                                              (Term.Apply
                                                (Term.Apply (Term.UOp UserOp.eq) wm)
                                                (Term.Apply
                                                  (Term.Apply (Term.UOp UserOp.neg)
                                                  (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                                                  (Term.Numeral 1))))) =
                                        Term.Bool := by
                                    have hResultTyLocal := hResultTy
                                    change
                                      __eo_typeof
                                        (__eo_prog_bv_smod_eliminate x y w wm
                                          (Proof.pf (__eo_state_proven_nth s n1))
                                          (Proof.pf (__eo_state_proven_nth s n2))) =
                                        Term.Bool at hResultTyLocal
                                    simpa [hP1, hP2] using hResultTyLocal
                                  simpa [hP1, hP2] using
                                    trusted_bv_smod_eliminate_canonical_properties
                                      M hM x y w wm hArgsTrans
                                      hPremisesBoolCanonical hResultTyCanonical
