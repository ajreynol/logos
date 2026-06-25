import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.ReConcatStarSupport
import Cpc.Proofs.Closed.IsClosedRec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-! ## Term-structure abbreviations for `re_eq_elim`

The rule `__eo_prog_re_eq_elim` rewrites `(= (= r1 r2) Q)` to `(= (= r1 r2) Q)`
under the guards that `(= r1 r2)` is closed and that `Q` is syntactically the
extensionality formula `∀ x:(Seq Char). (str_in_re x r1) = (str_in_re x r2)`.
-/

private abbrev reqName : native_String :=
  native_string_lit "@var.re_eq"

private abbrev seqCharTy : Term :=
  Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)

private abbrev reqVar : Term :=
  Term.Var (Term.String reqName) seqCharTy

private abbrev reqList : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons reqVar) Term.__eo_List_nil

private abbrev mkEqT (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev mkStrInReT (s r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r

/-- The extensionality body `(= (str_in_re x r1) (str_in_re x r2))`. -/
private abbrev reEqBody (r1 r2 : Term) : Term :=
  mkEqT (mkStrInReT reqVar r1) (mkStrInReT reqVar r2)

/-- The extensionality formula `Q`, i.e. `∀ x. (str_in_re x r1) = (str_in_re x r2)`. -/
private abbrev reEqForall (r1 r2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) reqList) (reEqBody r1 r2)

/-! ## `__eo_requires` extraction helpers (mirrors `Re_loop_elim`). -/

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not,
        SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

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

private theorem eo_requires_result_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro h hz
  have hReq : __eo_requires x y z = z :=
    eo_requires_eq_result_of_ne_stuck x y z h
  exact h (by rw [hReq, hz])

/-! ## Shape extraction.

If `__eo_prog_re_eq_elim a1` is not `Stuck`, then `a1` is `(= (= r1 r2) Q)`,
the closedness guard holds, `Q` is the extensionality formula, and the result is
`(= (= r1 r2) Q)`. -/

private theorem re_eq_elim_nonstuck_shape (a1 : Term) :
    __eo_prog_re_eq_elim a1 ≠ Term.Stuck ->
    ∃ r1 r2 Q,
      a1 = mkEqT (mkEqT r1 r2) Q ∧
      __is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil = Term.Boolean true ∧
      Q = reEqForall r1 r2 ∧
      __eo_prog_re_eq_elim a1 = mkEqT (mkEqT r1 r2) Q := by
  intro hNe
  -- Only the matching shape avoids the `Term.Stuck` fall-through.
  match a1, hNe with
  | (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) r1) r2)) Q), hNe =>
    refine ⟨r1, r2, Q, rfl, ?_, ?_, ?_⟩
    · -- closedness guard
      have hProg :
          __eo_prog_re_eq_elim (mkEqT (mkEqT r1 r2) Q) =
            __eo_requires
              (__is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil)
              (Term.Boolean true)
              (__eo_requires Q (reEqForall r1 r2)
                (mkEqT (mkEqT r1 r2) Q)) := rfl
      rw [hProg] at hNe
      exact eo_requires_arg_eq_of_ne_stuck hNe
    · -- Q equals the extensionality formula
      have hProg :
          __eo_prog_re_eq_elim (mkEqT (mkEqT r1 r2) Q) =
            __eo_requires
              (__is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil)
              (Term.Boolean true)
              (__eo_requires Q (reEqForall r1 r2)
                (mkEqT (mkEqT r1 r2) Q)) := rfl
      rw [hProg] at hNe
      have hInner :
          __eo_requires Q (reEqForall r1 r2) (mkEqT (mkEqT r1 r2) Q) ≠
            Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hNe
      exact eo_requires_arg_eq_of_ne_stuck hInner
    · -- the produced term
      have hProg :
          __eo_prog_re_eq_elim (mkEqT (mkEqT r1 r2) Q) =
            __eo_requires
              (__is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil)
              (Term.Boolean true)
              (__eo_requires Q (reEqForall r1 r2)
                (mkEqT (mkEqT r1 r2) Q)) := rfl
      rw [hProg]
      rw [hProg] at hNe
      rw [eo_requires_eq_result_of_ne_stuck _ _ _ hNe]
      exact eo_requires_eq_result_of_ne_stuck _ _ _
        (eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hNe)

/-! ## Typing: the regex operands have `RegLan` type.

From `eo_has_bool_type (= (= r1 r2) Q)` with `Q` the extensionality formula, the
operands `r1`, `r2` translate to `RegLan`. -/

/-- If `ite c A None ≠ None`, the guard held and the `then`-branch is non-`None`. -/
private theorem ite_then_of_ne_none {c : native_Bool} {A : SmtType}
    (h : native_ite c A SmtType.None ≠ SmtType.None) :
    c = true ∧ A ≠ SmtType.None := by
  cases c with
  | true => exact ⟨rfl, by simpa [native_ite] using h⟩
  | false => exact absurd (by simp [native_ite]) h

private theorem eq_of_teq_true {X Y : SmtType}
    (h : native_Teq X Y = true) : X = Y :=
  of_decide_eq_true h

/-- The smt translation of the extensionality formula. -/
private theorem re_eq_forall_smt (r1 r2 : Term) :
    __eo_to_smt (reEqForall r1 r2) =
      SmtTerm.not
        (SmtTerm.exists reqName (__eo_to_smt_type seqCharTy)
          (SmtTerm.not (__eo_to_smt (reEqBody r1 r2)))) := rfl

private theorem re_eq_forall_args_reglan (r1 r2 : Term)
    (hBool : eo_has_bool_type (mkEqT (mkEqT r1 r2) (reEqForall r1 r2))) :
    __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan := by
  -- The forall operand has a non-`None` smt type.
  rcases eo_eq_operands_same_smt_type_of_has_bool_type
      (mkEqT r1 r2) (reEqForall r1 r2) hBool with ⟨hSame, hLeftNN⟩
  have hQNN : __smtx_typeof (__eo_to_smt (reEqForall r1 r2)) ≠ SmtType.None :=
    hSame ▸ hLeftNN
  rw [re_eq_forall_smt, typeof_not_eq] at hQNN
  -- Peel `not`: the inner `exists` has Bool type.
  have hExBool := (ite_then_of_ne_none hQNN).1
  have hExEq : __smtx_typeof
      (SmtTerm.exists reqName (__eo_to_smt_type seqCharTy)
        (SmtTerm.not (__eo_to_smt (reEqBody r1 r2)))) = SmtType.Bool :=
    eq_of_teq_true hExBool
  rw [smtx_typeof_exists_term_eq] at hExEq
  -- Peel `exists`: the `not body` has Bool type.
  have hNotBodyTeq :=
    (ite_then_of_ne_none (A := __smtx_typeof_guard_wf
      (__eo_to_smt_type seqCharTy) SmtType.Bool)
      (by rw [hExEq]; exact (by decide))).1
  have hNotBodyEq :
      __smtx_typeof (SmtTerm.not (__eo_to_smt (reEqBody r1 r2))) =
        SmtType.Bool :=
    eq_of_teq_true hNotBodyTeq
  rw [typeof_not_eq] at hNotBodyEq
  -- Peel `not`: the body has Bool type.
  have hBodyTeq := (ite_then_of_ne_none (A := SmtType.Bool)
    (by rw [hNotBodyEq]; exact (by decide))).1
  have hBodyBool : eo_has_bool_type (reEqBody r1 r2) := by
    unfold eo_has_bool_type
    exact eq_of_teq_true hBodyTeq
  -- The body is `(= (str_in_re x r1) (str_in_re x r2))`; both operands non-`None`.
  rcases eo_eq_operands_same_smt_type_of_has_bool_type
      (mkStrInReT reqVar r1) (mkStrInReT reqVar r2) hBodyBool with
    ⟨hSameB, hLeftBNN⟩
  have hRightBNN :
      __smtx_typeof (__eo_to_smt (mkStrInReT reqVar r2)) ≠ SmtType.None :=
    hSameB ▸ hLeftBNN
  -- Extract `RegLan` from each `str_in_re` operand.
  have hStr1 :
      __eo_to_smt (mkStrInReT reqVar r1) =
        SmtTerm.str_in_re (__eo_to_smt reqVar) (__eo_to_smt r1) := rfl
  have hStr2 :
      __eo_to_smt (mkStrInReT reqVar r2) =
        SmtTerm.str_in_re (__eo_to_smt reqVar) (__eo_to_smt r2) := rfl
  rw [hStr1, typeof_str_in_re_eq] at hLeftBNN
  rw [hStr2, typeof_str_in_re_eq] at hRightBNN
  refine ⟨?_, ?_⟩
  · exact eq_of_teq_true (ite_then_of_ne_none
      ((ite_then_of_ne_none hLeftBNN).2)).1
  · exact eq_of_teq_true (ite_then_of_ne_none
      ((ite_then_of_ne_none hRightBNN).2)).1

/-! ## Core: the produced equation evaluates true.

`(= r1 r2)` (regex extensional equality) and the extensionality formula `Q`
evaluate to the same Boolean in `M`. -/

/-
Proof plan for the core (the only remaining `sorry`).  All cited lemmas exist.

Let `R1 := eval M (smt r1)`, `R2 := eval M (smt r2)` (both `RegLan` by `hr1`/`hr2`
via `smt_eval_reglan_of_smt_type_reglan`).

1. LHS: `eval M (smt (= r1 r2)) = __smtx_model_eval_eq (RegLan R1) (RegLan R2)
   = Boolean (native_re_ext_eq R1 R2)` (SmtModel.lean:872).  And
   `native_re_ext_eq R1 R2 = true ↔ ∀ s, native_string_valid s →
   native_str_in_re s R1 = native_str_in_re s R2` (definitional, SmtModel.lean:567).

2. Freshness: from `hClosed` + `hTrans`, derive `SmtTermClosedIn [] (smt r1)` and
   `(smt r2)`:
     `is_closed_rec_eq_eo_is_closed_of_has_smt_translation` (needs
     `eoHasSmtTranslation (= r1 r2)`, = `hTrans` modulo the `eoHasSmtTranslation`
     / `eo_has_smt_translation` defeq) gives `__is_closed_rec (= r1 r2) [] =
     __eo_is_closed (= r1 r2)`; with `hClosed` ⟹ `__eo_is_closed (= r1 r2) = true`;
     `smtTermClosedIn_of_eo_is_closed` ⟹ `SmtTermClosedIn [] (eq (smt r1) (smt r2))`,
     which unfolds to closedness of `smt r1` and `smt r2`.
   Hence for every `v`, `eval (native_model_push M reqName T v) (smt r_i) =
   eval M (smt r_i)` via `smt_model_eval_eq_of_eo_smt_closed` +
   `model_agrees_on_globals_push`.

3. RHS: `smt (reEqForall r1 r2) = not (exists reqName T (not (smt body)))`
   (`re_eq_forall_smt`), so `eval RHS = __smtx_model_eval_not
   (native_eval_texists M reqName T (not (smt body)))` (SmtModel.lean:2147,2293).
   With the freshness from (2), for a value `v = Seq ss`:
     `eval (push) (smt body) =
       Boolean (decide (native_str_in_re (native_unpack_string ss) R1 =
                        native_str_in_re (native_unpack_string ss) R2))`
   (str_in_re eval SmtModel.lean:1497; eq of two Booleans).  Using `hM`
   (canonical Bool), `eval RHS = Boolean true ↔ ∀ canonical Seq-Char `v=Seq ss`,
   `native_str_in_re (unpack ss) R1 = native_str_in_re (unpack ss) R2`.

4. Domain match (`T = __eo_to_smt_type seqCharTy = Seq Char`):
   - (⟸) every valid string `s` gives a canonical value `Seq (native_pack_string s)`
     with `typeof_value = Seq Char` (`typeof_pack_string`),
     `unpack (pack_string s) = s` (roundtrip — `native_unpack_string_pack_string`,
     copyable from e.g. Str_to_upper_lower.lean:105) and `canonical_bool = true`
     (i.e. `__smtx_seq_canonical (native_pack_string s) = true` for valid `s` —
     the ONE sub-lemma with no ready-made version; prove from `native_string_valid`
     ⟹ all chars valid); so the `∀`-over-values implies the `∀`-over-valid-strings.
   - (⟹) every canonical Seq-Char value is `Seq ss` (`seq_value_canonical`) with
     `unpack ss` valid (`native_unpack_string_valid_of_typeof_seq_char`).
   Hence the two booleans of (1) and (3) coincide.

5. `rw` both evals to `Boolean (native_re_ext_eq R1 R2)` and close with
   `smt_value_rel_refl`.
-/
private theorem re_eq_elim_smt_value_rel
    (M : SmtModel) (hM : model_total_typed M) (r1 r2 : Term)
    (hClosed :
      __is_closed_rec (mkEqT r1 r2) Term.__eo_List_nil = Term.Boolean true)
    (hTrans : eo_has_smt_translation (mkEqT r1 r2))
    (hr1 : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2 : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan) :
    smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkEqT r1 r2)))
      (__smtx_model_eval M (__eo_to_smt (reEqForall r1 r2))) := by
  sorry

end RuleProofs

theorem cmd_step_re_eq_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_eq_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_eq_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_eq_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.re_eq_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons a1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              change StepRuleProperties M [] (__eo_prog_re_eq_elim a1)
              have hProgLocal : __eo_prog_re_eq_elim a1 ≠ Term.Stuck := by
                change __eo_prog_re_eq_elim a1 ≠ Term.Stuck at hProg
                exact hProg
              obtain ⟨r1, r2, Q, ha1, hClosed, hQ, hProgEq⟩ :=
                RuleProofs.re_eq_elim_nonstuck_shape a1 hProgLocal
              have hTermTrans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cArgListTranslationOk] using hArgsTrans.1
              -- the produced term equals `a1` (the rule is the identity after guards)
              have hTypeofA1 : __eo_typeof a1 = Term.Bool := by
                have : __eo_typeof (__eo_prog_re_eq_elim a1) = Term.Bool := by
                  change __eo_typeof (__eo_cmd_step_proven s CRule.re_eq_elim
                    (CArgList.cons a1 CArgList.nil) CIndexList.nil) = Term.Bool
                  exact hResultTy
                rwa [hProgEq, ← ha1] at this
              have hBool : RuleProofs.eo_has_bool_type a1 :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hTermTrans hTypeofA1
              -- rewrite everything to the destructured form
              rw [ha1] at hBool hTermTrans
              subst hQ
              -- regex operand types
              obtain ⟨hr1, hr2⟩ :=
                RuleProofs.re_eq_forall_args_reglan r1 r2 hBool
              -- translation of the inner regex equation
              have hEqTrans :
                  RuleProofs.eo_has_smt_translation
                    (RuleProofs.mkEqT r1 r2) := by
                rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    (RuleProofs.mkEqT r1 r2) (RuleProofs.reEqForall r1 r2)
                    hBool with ⟨_hSame, hLeftNN⟩
                exact hLeftNN
              refine ⟨?_, ?_⟩
              · intro _hPremisesTrue
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel M
                  (RuleProofs.mkEqT r1 r2) (RuleProofs.reEqForall r1 r2)
                  hBool
                  (RuleProofs.re_eq_elim_smt_value_rel M hM r1 r2
                    hClosed hEqTrans hr1 hr2)
              · rw [hProgEq]
                exact hTermTrans
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
