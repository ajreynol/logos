import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- A `true` result from `__eo_eq` forces syntactic equality of non-stuck inputs. -/
private theorem eo_eq_eq_true (x y : Term) :
  __eo_eq x y = Term.Boolean true ->
  x = y ∧ x ≠ Term.Stuck ∧ y ≠ Term.Stuck := by
  intro hEq
  by_cases hx : x = Term.Stuck
  · subst hx
    simp [__eo_eq] at hEq
  · by_cases hy : y = Term.Stuck
    · subst hy
      simp [__eo_eq] at hEq
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using hEq
      have hYX : y = x := by
        simpa [native_teq] using hDec
      exact ⟨hYX.symm, hx, hy⟩

/-- Non-stuck generic application has non-stuck head and argument. -/
private theorem eo_mk_apply_not_stuck (f x : Term) :
  __eo_mk_apply f x ≠ Term.Stuck ->
  f ≠ Term.Stuck ∧ x ≠ Term.Stuck := by
  cases f <;> cases x <;> simp [__eo_mk_apply]

/-- A non-stuck `__eo_ite` with `stuck` else-branch must take the true branch. -/
private theorem eo_ite_not_stuck_of_stuck_else (c t : Term) :
  __eo_ite c t Term.Stuck ≠ Term.Stuck ->
  c = Term.Boolean true ∧ t ≠ Term.Stuck := by
  cases c <;> cases t <;> simp [__eo_ite, native_ite, native_teq]

/-- Base simplification for `__mk_cong_rhs`. -/
private theorem mk_cong_rhs_base_eq (t : Term) :
  t ≠ Term.Stuck ->
  __mk_cong_rhs t (Term.Boolean true) = t := by
  intro hT
  cases t <;> simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs] at hT ⊢

/-- Step simplification for `__mk_cong_rhs` once the syntactic equality guard is known. -/
private theorem mk_cong_rhs_step_eq (f t1 t2 tail : Term) :
  t1 ≠ Term.Stuck ->
  __mk_cong_rhs
    (Term.Apply f t1)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2))
      tail) =
    __eo_mk_apply (__mk_cong_rhs f tail) t2 := by
  intro hT1
  cases t1 <;> simp [__mk_cong_rhs, __eo_eq, __eo_ite, native_teq, native_ite] at hT1 ⊢

/-- A non-stuck `__mk_cong_rhs` is either at the base case or at a matching step case. -/
private theorem mk_cong_rhs_shape_of_not_stuck (t tail : Term) :
  __mk_cong_rhs t tail ≠ Term.Stuck ->
  (tail = Term.Boolean true ∧ t ≠ Term.Stuck) ∨
    ∃ f t1 t2 tail',
      t = Term.Apply f t1 ∧
      tail =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2))
          tail' ∧
      t1 ≠ Term.Stuck ∧
      __eo_mk_apply (__mk_cong_rhs f tail') t2 ≠ Term.Stuck := by
  intro hProg
  cases t with
  | Stuck =>
      cases tail with
      | Boolean b =>
          cases b with
          | false =>
              exact False.elim (hProg (by simp [__mk_cong_rhs]))
          | true =>
              exact False.elim (hProg (by simp [__mk_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by simp [__mk_cong_rhs]))
  | Apply f t1 =>
      cases tail with
      | Apply g tail' =>
          cases g with
          | Apply g2 eq12 =>
              cases g2 with
              | UOp op =>
                  cases op with
                  | and =>
                      cases eq12 with
                      | Apply g3 t2 =>
                          cases g3 with
                          | Apply g4 u1 =>
                              cases g4 with
                              | UOp op2 =>
                                  cases op2 with
                                  | eq =>
                                      have hIte :
                                          __eo_ite (__eo_eq t1 u1)
                                            (__eo_mk_apply (__mk_cong_rhs f tail') t2)
                                            Term.Stuck ≠
                                            Term.Stuck := by
                                        simpa [__mk_cong_rhs, __eo_l_1___mk_cong_rhs] using hProg
                                      rcases eo_ite_not_stuck_of_stuck_else
                                          (__eo_eq t1 u1)
                                          (__eo_mk_apply (__mk_cong_rhs f tail') t2) hIte with
                                        ⟨hGuard, hThen⟩
                                      rcases eo_eq_eq_true t1 u1 hGuard with
                                        ⟨hEq, hT1, _⟩
                                      subst u1
                                      exact Or.inr ⟨f, t1, t2, tail', rfl, rfl, hT1, hThen⟩
                                  | _ =>
                                      exact False.elim (hProg (by
                                        simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
                              | _ =>
                                  exact False.elim (hProg (by
                                    simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
                          | _ =>
                              exact False.elim (hProg (by
                                simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
                      | _ =>
                          exact False.elim (hProg (by
                            simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
                  | _ =>
                      exact False.elim (hProg (by
                        simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
      | Boolean b =>
          cases b with
          | false =>
              exact False.elim (hProg (by simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
          | true =>
              exact Or.inl ⟨rfl, by simp⟩
      | _ =>
          exact False.elim (hProg (by simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
  | _ =>
      cases tail with
      | Boolean b =>
          cases b with
          | false =>
              exact False.elim (hProg (by simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))
          | true =>
              exact Or.inl ⟨rfl, by simp⟩
      | _ =>
          exact False.elim (hProg (by simp [__mk_cong_rhs, __eo_l_1___mk_cong_rhs]))

/-- The recursive tail in the step case is structurally smaller. -/
private theorem sizeOf_lt_cong_tail (t1 t2 tail : Term) :
  sizeOf tail <
    sizeOf
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2))
        tail) := by
  simp
  omega

/-- A non-stuck step case has a non-stuck recursive result. -/
private theorem mk_cong_rhs_rec_not_stuck (f t1 t2 tail : Term) :
  __mk_cong_rhs
    (Term.Apply f t1)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t1) t2))
      tail) ≠ Term.Stuck ->
  __mk_cong_rhs f tail ≠ Term.Stuck := by
  intro hProg
  have hIte :
      __eo_ite (__eo_eq t1 t1)
        (__eo_mk_apply (__mk_cong_rhs f tail) t2)
        Term.Stuck ≠
        Term.Stuck := by
    simpa [__mk_cong_rhs, __eo_l_1___mk_cong_rhs] using hProg
  have hThen :
      __eo_mk_apply (__mk_cong_rhs f tail) t2 ≠ Term.Stuck :=
    (eo_ite_not_stuck_of_stuck_else
      (__eo_eq t1 t1)
      (__eo_mk_apply (__mk_cong_rhs f tail) t2) hIte).2
  exact (eo_mk_apply_not_stuck (__mk_cong_rhs f tail) t2 hThen).1

theorem cmd_step_cong_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cong args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.cong args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cong args premises) :=
by
  sorry
