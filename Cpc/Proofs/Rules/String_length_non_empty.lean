import Cpc.Proofs.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Extracts the `__str_is_empty = true` guard from a non-stuck rule instance. -/
private theorem empty_of_prog_string_length_non_empty_not_stuck
    (s t : Term) :
  __eo_prog_string_length_non_empty
      (Proof.pf (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq s) t))) ≠
    Term.Stuck ->
  __str_is_empty t = Term.Boolean true := by
  intro hProg
  cases hE : __str_is_empty t with
  | Boolean b =>
      cases b with
      | false =>
          simp [__eo_prog_string_length_non_empty, hE, __eo_requires,
            native_ite, native_teq, native_not] at hProg
      | true =>
          simpa [hE]
  | _ =>
      simp [__eo_prog_string_length_non_empty, hE, __eo_requires,
        native_ite, native_teq, native_not] at hProg

/-- Characterizes the SMT type and evaluation of syntactically empty string terms. -/
private theorem empty_term_smt_info
    (t : Term)
    (hEmpty : __str_is_empty t = Term.Boolean true)
    (hTrans : RuleProofs.eo_has_smt_translation t) :
  ∃ T,
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ∧
    ∀ M, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq (SmtSeq.empty T) := by
  cases t with
  | String s =>
      by_cases hs : s = ""
      · subst hs
        refine ⟨SmtType.Char, ?_, ?_⟩
        · simp [__eo_to_smt.eq_def, __smtx_typeof]
        · intro M
          simp [__eo_to_smt.eq_def, __smtx_model_eval, native_pack_string, native_pack_seq,
            __smtx_ssm_char_values_of_string]
      · simp [__str_is_empty, hs] at hEmpty
  | seq_empty x =>
      cases x with
      | Apply f U =>
          cases f with
          | Seq =>
              have hTrans' : __smtx_typeof (__eo_to_smt (Term.seq_empty (Term.Apply Term.Seq U))) ≠
                  SmtType.None := hTrans
              by_cases hU : __eo_to_smt_type U = SmtType.None
              · exfalso
                apply hTrans'
                simp [__eo_to_smt.eq_def, TranslationProofs.eo_to_smt_type_seq, __eo_to_smt_seq_empty,
                  __smtx_typeof_guard, __smtx_typeof, hU, native_ite, native_Teq]
              · refine ⟨__eo_to_smt_type U, ?_, ?_⟩
                · have hGuard :
                      __smtx_typeof_guard (__eo_to_smt_type U)
                        (SmtType.Seq (__eo_to_smt_type U)) =
                        SmtType.Seq (__eo_to_smt_type U) := by
                    unfold __smtx_typeof_guard
                    simp [hU, native_ite, native_Teq]
                  have hSeqEmptyNonNone :
                      __smtx_typeof (SmtTerm.seq_empty (__eo_to_smt_type U)) ≠ SmtType.None := by
                    simpa [__eo_to_smt.eq_def, TranslationProofs.eo_to_smt_type_seq, hGuard,
                      __eo_to_smt_seq_empty] using hTrans'
                  have hSeqEmptyTy :
                      __smtx_typeof (SmtTerm.seq_empty (__eo_to_smt_type U)) =
                        SmtType.Seq (__eo_to_smt_type U) :=
                    TranslationProofs.smtx_typeof_seq_empty_of_non_none
                      (__eo_to_smt_type U) hSeqEmptyNonNone
                  simpa [__eo_to_smt.eq_def, TranslationProofs.eo_to_smt_type_seq, hGuard,
                    __eo_to_smt_seq_empty] using hSeqEmptyTy
                · intro M
                  have hGuard :
                      __smtx_typeof_guard (__eo_to_smt_type U)
                        (SmtType.Seq (__eo_to_smt_type U)) =
                        SmtType.Seq (__eo_to_smt_type U) := by
                    unfold __smtx_typeof_guard
                    simp [hU, native_ite, native_Teq]
                  simp [__eo_to_smt.eq_def, TranslationProofs.eo_to_smt_type_seq, hGuard,
                    __eo_to_smt_seq_empty, __smtx_model_eval]
          | _ =>
              simp [__str_is_empty] at hEmpty
      | _ =>
          simp [__str_is_empty] at hEmpty
  | _ =>
      simp [__str_is_empty] at hEmpty

/-- Shows that the EO program for `string_length_non_empty` is well typed. -/
private theorem typed___eo_prog_string_length_non_empty_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_string_length_non_empty (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_string_length_non_empty (Proof.pf x1)) := by
  intro hXBool hProg
  cases x1 with
  | Apply f prem =>
      cases f with
      | not =>
          cases prem with
          | Apply f2 t =>
              cases f2 with
              | Apply f1 s =>
                  cases f1 with
                  | eq =>
                      have hEqBool :
                          RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) :=
                        RuleProofs.eo_has_bool_type_not_arg _ hXBool
                      have hEmpty : __str_is_empty t = Term.Boolean true :=
                        empty_of_prog_string_length_non_empty_not_stuck s t hProg
                      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t hEqBool with
                        ⟨hSTy, hSNonNone⟩
                      have hTTrans : RuleProofs.eo_has_smt_translation t := by
                        unfold RuleProofs.eo_has_smt_translation
                        intro hNone
                        apply hSNonNone
                        rw [hSTy]
                        exact hNone
                      rcases empty_term_smt_info t hEmpty hTTrans with ⟨T, hTTy, _⟩
                      have hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
                        rw [hSTy, hTTy]
                      have hLenTy :
                          __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len s)) = SmtType.Int := by
                        rw [__eo_to_smt.eq_def]
                        change __smtx_typeof_seq_op_1_ret (__smtx_typeof (__eo_to_smt s))
                            SmtType.Int = SmtType.Int
                        rw [hSTySeq]
                        simp [__smtx_typeof_seq_op_1_ret, native_ite, native_Teq]
                      have hNumTy :
                          __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
                        simp [__eo_to_smt.eq_def, __smtx_typeof]
                      have hEqLenBool :
                          RuleProofs.eo_has_bool_type
                            (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s))
                              (Term.Numeral 0)) := by
                        exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                          (Term.Apply Term.str_len s) (Term.Numeral 0)
                          (by rw [hLenTy, hNumTy])
                          (by rw [hLenTy]; simp)
                      simpa [__eo_prog_string_length_non_empty, hEmpty, __eo_requires,
                        native_ite, native_teq, native_not] using
                        RuleProofs.eo_has_bool_type_not_of_bool_arg _ hEqLenBool
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

/-- Shows that the EO program for `string_length_non_empty` is semantically valid. -/
private theorem facts___eo_prog_string_length_non_empty_impl
    (M : SmtModel) (hM : model_total_typed M) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_string_length_non_empty (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_string_length_non_empty (Proof.pf x1)) true := by
  intro hXTrue hProg
  cases x1 with
  | Apply f prem =>
      cases f with
      | not =>
          cases prem with
          | Apply f2 t =>
              cases f2 with
              | Apply f1 s =>
                  cases f1 with
                  | eq =>
                      have hEqFalse :
                          eo_interprets M (Term.Apply (Term.Apply Term.eq s) t) false :=
                        RuleProofs.eo_interprets_not_true_implies_false M _ hXTrue
                      have hEqBool :
                          RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) :=
                        RuleProofs.eo_has_bool_type_of_interprets_false M _ hEqFalse
                      have hEmpty : __str_is_empty t = Term.Boolean true :=
                        empty_of_prog_string_length_non_empty_not_stuck s t hProg
                      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t hEqBool with
                        ⟨hSTy, hSNonNone⟩
                      have hTTrans : RuleProofs.eo_has_smt_translation t := by
                        unfold RuleProofs.eo_has_smt_translation
                        intro hNone
                        apply hSNonNone
                        rw [hSTy]
                        exact hNone
                      rcases empty_term_smt_info t hEmpty hTTrans with ⟨T, hTTy, hEvalT⟩
                      have hSTySeq : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
                        rw [hSTy, hTTy]
                      have hEvalSTy :
                          __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
                            SmtType.Seq T :=
                        smt_model_eval_preserves_type M hM (__eo_to_smt s) (SmtType.Seq T)
                          hSTySeq (type_inhabited_seq T)
                      rcases seq_value_canonical hEvalSTy with ⟨ss, hEvalS⟩
                      cases ss with
                      | empty T0 =>
                          have hSeqTy : SmtType.Seq T0 = SmtType.Seq T := by
                            simpa [__smtx_typeof_value, __smtx_typeof_seq_value, hEvalS] using
                              hEvalSTy
                          have hT0 : T0 = T := by
                            injection hSeqTy
                          have hEvalT' :
                              __smtx_model_eval M (__eo_to_smt t) =
                                SmtValue.Seq (SmtSeq.empty T0) := by
                            rw [hT0]
                            exact hEvalT M
                          have hEqTrue :
                              eo_interprets M (Term.Apply (Term.Apply Term.eq s) t) true := by
                            exact RuleProofs.eo_interprets_eq_of_rel M s t hEqBool <| by
                              rw [hEvalS, hEvalT']
                              exact RuleProofs.smt_value_rel_refl
                                (SmtValue.Seq (SmtSeq.empty T0))
                          have hEqEvalFalse :
                              __smtx_model_eval M
                                  (__eo_to_smt (Term.Apply (Term.Apply Term.eq s) t)) =
                                SmtValue.Boolean false := by
                            rw [RuleProofs.eo_interprets_iff_smt_interprets] at hEqFalse
                            cases hEqFalse with
                            | intro_false _ hEval =>
                                exact hEval
                          have hEqEvalTrue :
                              __smtx_model_eval M
                                  (__eo_to_smt (Term.Apply (Term.Apply Term.eq s) t)) =
                                SmtValue.Boolean true := by
                            rw [RuleProofs.eo_interprets_iff_smt_interprets] at hEqTrue
                            cases hEqTrue with
                            | intro_true _ hEval =>
                                exact hEval
                          rw [hEqEvalTrue] at hEqEvalFalse
                          cases hEqEvalFalse
                      | cons v vs =>
                          have hLenTy :
                              __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len s)) = SmtType.Int := by
                            rw [__eo_to_smt.eq_def]
                            change __smtx_typeof_seq_op_1_ret (__smtx_typeof (__eo_to_smt s))
                                SmtType.Int = SmtType.Int
                            rw [hSTySeq]
                            simp [__smtx_typeof_seq_op_1_ret, native_ite, native_Teq]
                          have hNumTy :
                              __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
                            simp [__eo_to_smt.eq_def, __smtx_typeof]
                          have hEqLenBool :
                              RuleProofs.eo_has_bool_type
                                (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                  (Term.Numeral 0)) := by
                            exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                              (Term.Apply Term.str_len s) (Term.Numeral 0)
                              (by rw [hLenTy, hNumTy])
                              (by rw [hLenTy]; simp)
                          have hEvalLen :
                              __smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_len s)) =
                                SmtValue.Numeral
                                  (native_seq_len (native_unpack_seq (SmtSeq.cons v vs))) := by
                            rw [__eo_to_smt.eq_def]
                            simp [__smtx_model_eval, hEvalS, __smtx_model_eval_str_len]
                          have hEqLenFalse :
                              eo_interprets M
                                (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                  (Term.Numeral 0))
                                false := by
                            apply RuleProofs.eo_interprets_of_bool_eval M _ false hEqLenBool
                            rw [__eo_to_smt.eq_def]
                            change __smtx_model_eval_eq
                                (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_len s)))
                                (__smtx_model_eval M (__eo_to_smt (Term.Numeral 0))) =
                              SmtValue.Boolean false
                            rw [hEvalLen]
                            simp [__eo_to_smt.eq_def, __smtx_model_eval, __smtx_model_eval_eq,
                              native_veq, native_seq_len, native_unpack_seq]
                            intro hZero
                            have hZeroNat : (native_unpack_seq vs).length + 1 = 0 := by
                              exact_mod_cast hZero
                            exact Nat.succ_ne_zero _ hZeroNat
                          simpa [__eo_prog_string_length_non_empty, hEmpty, __eo_requires,
                            native_ite, native_teq, native_not] using
                            RuleProofs.eo_interprets_not_of_false M
                              (Term.Apply (Term.Apply Term.eq (Term.Apply Term.str_len s))
                                (Term.Numeral 0))
                              hEqLenFalse
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

theorem cmd_step_string_length_non_empty_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_length_non_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_length_non_empty args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_length_non_empty args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.string_length_non_empty args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgNonEmpty' :
                  __eo_prog_string_length_non_empty
                    (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck := by
                change __eo_prog_string_length_non_empty
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                exact hProg
              have hProgNonEmpty :
                  __eo_prog_string_length_non_empty (Proof.pf X1) ≠ Term.Stuck := by
                simpa [X1] using hProgNonEmpty'
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_string_length_non_empty (Proof.pf X1)) true
                exact facts___eo_prog_string_length_non_empty_impl M hM X1
                  (hTrue X1 (by simp [X1, premiseTermList])) hProgNonEmpty
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type
                      (__eo_prog_string_length_non_empty (Proof.pf X1))
                    exact typed___eo_prog_string_length_non_empty_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgNonEmpty)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
