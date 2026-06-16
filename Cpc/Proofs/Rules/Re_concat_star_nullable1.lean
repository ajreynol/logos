import Cpc.Proofs.RuleSupport.ReConcatNullableSupport
import Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace ReConcatStarNullable1Proof

/-- `str.in_re "" r = true`, the premise shape. -/
abbrev mkStrInReEmpty (r : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String [])) r))
    (Term.Boolean true)

/-- LHS of the conclusion: `xs · (Σ* · (r · ys))`. -/
abbrev lhs1 (xs1 r1 ys1 : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.re_concat) xs1
    (RuleProofs.tReConcat RuleProofs.tSigma (RuleProofs.tReConcat r1 ys1))

/-- RHS of the conclusion: `singleton_elim (xs · (Σ* · ys))`. -/
abbrev rhs1 (xs1 ys1 : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_concat)
    (__eo_list_concat (Term.UOp UserOp.re_concat) xs1
      (RuleProofs.tReConcat RuleProofs.tSigma ys1))

/-- The conclusion produced by `re_concat_star_nullable1` (matching the program's
`__eo_mk_apply` shape). -/
abbrev mkConcl1 (xs1 r1 ys1 : Term) : Term :=
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (lhs1 xs1 r1 ys1)) (rhs1 xs1 ys1)

/-- Structural extraction of the program result, mirroring `Re_loop_star.prog_form`. -/
theorem prog_form (xs1 r1 ys1 P1 : Term)
    (hNe : __eo_prog_re_concat_star_nullable1 xs1 r1 ys1 (Proof.pf P1) ≠ Term.Stuck) :
    P1 = mkStrInReEmpty r1 ∧
      __eo_prog_re_concat_star_nullable1 xs1 r1 ys1 (Proof.pf P1) = mkConcl1 xs1 r1 ys1 := by
  unfold __eo_prog_re_concat_star_nullable1 at hNe ⊢
  split at hNe
  · exact absurd rfl hNe
  · exact absurd rfl hNe
  · exact absurd rfl hNe
  · rename_i heqP1
    injection heqP1 with hP1
    have hCond := RuleProofs.eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := RuleProofs.eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    have hr12 := RuleProofs.eo_eq_eq_true hCond
    rw [hr12] at hP1
    exact ⟨hP1, hReqEq⟩
  · exact absurd rfl hNe

/-- The premise yields nullability of the regex argument. -/
theorem nullable_of_premise (M : SmtModel) (r1 : Term) (r1v : native_RegLan)
    (hR1 : __smtx_model_eval M (__eo_to_smt r1) = SmtValue.RegLan r1v)
    (hP : eo_interprets M (mkStrInReEmpty r1) true) :
    native_re_nullable r1v = true := by
  have hRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String [])) r1)
      (Term.Boolean true) hP
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) (Term.String [])) r1)) =
        SmtValue.Boolean (native_str_in_re ([] : native_String) r1v) :=
    smtx_model_eval_str_in_re_string M ([] : native_String) r1 r1v hR1
  have hTrue :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) = SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = _
    rw [__smtx_model_eval.eq_1]
  rw [hEval, hTrue] at hRel
  have hEq : SmtValue.Boolean (native_str_in_re ([] : native_String) r1v) =
      SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by rintro ⟨a, b, hbad, _⟩; cases hbad)).1 hRel
  have hMem : native_str_in_re ([] : native_String) r1v = true := by
    simpa using hEq
  have : native_re_nullable r1v = true := by
    have : native_string_valid ([] : native_String) = true := by
      simp [native_string_valid]
    rw [RuleProofs.native_str_in_re_eq_nativeListInRe ([] : native_String) r1v this] at hMem
    simpa [RuleProofs.nativeListInRe] using hMem
  exact this

end ReConcatStarNullable1Proof

open ReConcatStarNullable1Proof

/-
The semantic content of this rule is fully proved by
`RuleProofs.nullable1_eval_rel` and assembled below.  The only remaining
`sorry` is a *bundle of routine typing facts* about the conclusion
(`eo_has_bool_type`, the `re_concat`-list structure of `xs1`/`ys1`, and that the
`RegLan` arguments evaluate to regular-language values).  Unlike `re_loop_star`,
this rule has **no** EO/SMT typing gap — every operation involved
(`re.concat`, `re.++`, `str.to_re`, `re.*`, `re.allchar`) is faithfully
translatable, so the bundle is genuinely provable; it is deferred only because
it requires threading the `list_concat`/`singleton_elim` typing lemmas.
-/
theorem cmd_step_re_concat_star_nullable1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_star_nullable1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_concat_star_nullable1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_star_nullable1 args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_concat_star_nullable1 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
  | cons a1 args =>
    cases args with
    | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
    | cons a2 args =>
      cases args with
      | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
      | cons a3 args =>
        cases args with
        | cons _ _ => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
        | nil =>
          cases premises with
          | nil => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
          | cons n1 premises =>
            cases premises with
            | cons _ _ => change Term.Stuck ≠ Term.Stuck at hProg; exact False.elim (hProg rfl)
            | nil =>
              show StepRuleProperties M [__eo_state_proven_nth s n1]
                  (__eo_prog_re_concat_star_nullable1 a1 a2 a3
                    (Proof.pf (__eo_state_proven_nth s n1)))
              generalize hP1 : __eo_state_proven_nth s n1 = P1
              have hProgNe :
                  __eo_prog_re_concat_star_nullable1 a1 a2 a3 (Proof.pf P1) ≠ Term.Stuck := by
                rw [← hP1]; exact hProg
              obtain ⟨hf1, hProgEq⟩ := prog_form a1 a2 a3 P1 hProgNe
              -- Routine typing bundle (no fundamental gap; see header note).
              have hTyping :
                  RuleProofs.eo_has_bool_type (mkConcl1 a1 a2 a3) ∧
                  __eo_is_list (Term.UOp UserOp.re_concat) a1 = Term.Boolean true ∧
                  __eo_is_list (Term.UOp UserOp.re_concat) a3 = Term.Boolean true ∧
                  (∃ r1v, __smtx_model_eval M (__eo_to_smt a2) = SmtValue.RegLan r1v) ∧
                  (∃ ys1v, __smtx_model_eval M (__eo_to_smt a3) = SmtValue.RegLan ys1v) ∧
                  (∃ rr, __smtx_model_eval M
                      (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.re_concat) a1
                        (RuleProofs.tReConcat RuleProofs.tSigma
                          (RuleProofs.tReConcat a2 a3)))) = SmtValue.RegLan rr) := by
                sorry
              obtain ⟨hbt, hXsList, hYsList, ⟨r1v, hR1⟩, ⟨ys1v, hYs1⟩, hLhsEval⟩ := hTyping
              rw [hProgEq]
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hbt⟩
              intro hEv
              have hPrem : eo_interprets M (mkStrInReEmpty a2) true := by
                have h := hEv.true_here P1 (by simp)
                rwa [hf1] at h
              have hNull : native_re_nullable r1v = true :=
                nullable_of_premise M a2 r1v hR1 hPrem
              have hRel := RuleProofs.nullable1_eval_rel M a1 a2 a3 r1v ys1v
                hXsList hYsList hR1 hYs1 hNull hLhsEval
              exact RuleProofs.eo_interprets_eq_of_rel M _ _ hbt hRel
