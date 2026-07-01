import Cpc.Proofs.RuleSupport.ArithModOverModSupport

open Eo
open SmtEval
open Smtm
open ArithModOverModSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithModOverModMult

private abbrev lhsTerm (c ts r ss : Term) : Term :=
  modTotalTerm
    (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss)) c

private abbrev rhsTerm (c ts r ss : Term) : Term :=
  modTotalTerm
    (__eo_list_singleton_elim multOp
      (__eo_list_concat multOp ts (multTerm r ss))) c

private theorem smtx_typeof_mod_total_int
    (r c : Term)
    (hR : __smtx_typeof (__eo_to_smt r) = SmtType.Int)
    (hC : __smtx_typeof (__eo_to_smt c) = SmtType.Int) :
    __smtx_typeof (__eo_to_smt (modTotalTerm r c)) = SmtType.Int := by
  change __smtx_typeof
      (SmtTerm.mod_total (__eo_to_smt r) (__eo_to_smt c)) = SmtType.Int
  rw [typeof_mod_total_eq]
  simp [native_ite, native_Teq, hR, hC]

private theorem smtx_eval_mod_total_int
    (M : SmtModel) (r c : Term) (nr nc : native_Int)
    (hR : __smtx_model_eval M (__eo_to_smt r) = SmtValue.Numeral nr)
    (hC : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Numeral nc) :
    __smtx_model_eval M (__eo_to_smt (modTotalTerm r c)) =
      SmtValue.Numeral (native_mod_total nr nc) := by
  change __smtx_model_eval M
      (SmtTerm.mod_total (__eo_to_smt r) (__eo_to_smt c)) =
    SmtValue.Numeral (native_mod_total nr nc)
  rw [smtx_eval_mod_total_term_eq, hR, hC]
  simp [__smtx_model_eval_mod_total]

private theorem prog_arith_mod_over_mod_mult_info
    (c ts r ss P : Term)
    (hProg :
      __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) ≠
        Term.Stuck) :
    ∃ c0,
      P = modPremise c0 ∧ c0 = c ∧
      __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
        multConclusion c ts r ss := by
  unfold __eo_prog_arith_mod_over_mod_mult at hProg
  split at hProg <;> try contradiction
  next h1 h2 h3 h4 heq =>
    rename_i c0
    injection heq with hPEq
    have hc0 := RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    have hFinalNe := by
      rw [hc0] at hProg
      simpa [__eo_requires, __eo_eq, native_ite, native_teq,
        native_not, SmtEval.native_not, lhsTerm, rhsTerm, multConclusion,
        modTotalTerm, multTerm, eqTerm] using hProg
    refine ⟨c0, ?_, hc0, ?_⟩
    · simpa [modPremise, eqTerm] using hPEq
    · rw [hPEq, hc0]
      simp [__eo_prog_arith_mod_over_mod_mult, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not, hc0, __eo_eq]
      have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hFinalNe
      have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFinalNe
      have hLhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFunNe
      have hLhsFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hLhsNe
      have hRhsFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hRhsNe
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hFinalNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hLhsFunNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe,
        eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsFunNe]

private theorem mod_total_arg_ne_stuck_of_type_ne_stuck (x c : Term)
    (h : __eo_typeof (modTotalTerm x c) ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  change __eo_typeof_div (__eo_typeof Term.Stuck) (__eo_typeof c) ≠
    Term.Stuck at h
  have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by rfl
  rw [hStuckTy] at h
  simp [__eo_typeof_div] at h

private theorem list_concat_left_is_list_of_ne_stuck {f a b : Term}
    (hConcat : __eo_list_concat f a b ≠ Term.Stuck) :
    __eo_is_list f a = Term.Boolean true := by
  cases hA : __eo_is_list f a <;>
    simp [__eo_list_concat, __eo_requires, hA, native_ite, native_teq,
      native_not, SmtEval.native_not] at hConcat ⊢
  case Boolean b =>
    cases b <;>
      simp [__eo_list_concat, __eo_requires, hA, native_ite, native_teq,
        native_not, SmtEval.native_not] at hConcat ⊢

private theorem list_concat_right_is_list_of_ne_stuck {f a b : Term}
    (hConcat : __eo_list_concat f a b ≠ Term.Stuck) :
    __eo_is_list f b = Term.Boolean true := by
  have hA := list_concat_left_is_list_of_ne_stuck hConcat
  cases hB : __eo_is_list f b <;>
    simp [__eo_list_concat, __eo_requires, hA, hB, native_ite, native_teq,
      native_not, SmtEval.native_not] at hConcat ⊢
  case Boolean b =>
    cases b <;>
      simp [__eo_list_concat, __eo_requires, hA, hB, native_ite, native_teq,
        native_not, SmtEval.native_not] at hConcat ⊢

private theorem mult_lists_of_result_bool
    (c ts r ss P : Term)
    (hProgEq :
      __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
        multConclusion c ts r ss)
    (hResultTy :
      __eo_typeof (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) =
        Term.Bool) :
    __eo_is_list multOp ts = Term.Boolean true ∧
      __eo_is_list multOp ss = Term.Boolean true := by
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq (__eo_typeof (lhsTerm c ts r ss))
      (__eo_typeof (rhsTerm c ts r ss)) = Term.Bool at hResultTy
  have hOperands :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (lhsTerm c ts r ss))
      (__eo_typeof (rhsTerm c ts r ss)) hResultTy
  have hConcatNe :
      __eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss) ≠
        Term.Stuck :=
    mod_total_arg_ne_stuck_of_type_ne_stuck
      (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss)) c
      hOperands.1
  have hTsList := list_concat_left_is_list_of_ne_stuck hConcatNe
  have hTailList := list_concat_right_is_list_of_ne_stuck hConcatNe
  have hSsList :=
    eo_is_list_tail_true_of_cons_self multOp (modTotalTerm r c) ss hTailList
  exact ⟨hTsList, hSsList⟩

private theorem build_mult_lists
    (M : SmtModel) (hM : model_total_typed M) (c ts r ss : Term)
    (hCTrans : RuleProofs.eo_has_smt_translation c)
    (hTsTrans : RuleProofs.eo_has_smt_translation ts)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hSsTrans : RuleProofs.eo_has_smt_translation ss)
    (hCInt : __eo_typeof c = Term.Int)
    (hTsInt : __eo_typeof ts = Term.Int)
    (hRInt : __eo_typeof r = Term.Int)
    (hSsInt : __eo_typeof ss = Term.Int)
    (hTsList : __eo_is_list multOp ts = Term.Boolean true)
    (hSsList : __eo_is_list multOp ss = Term.Boolean true) :
    ∃ nc nts nr nss,
      __smtx_model_eval M (__eo_to_smt c) = SmtValue.Numeral nc ∧
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.Numeral nr ∧
      MulListEval M (__eo_list_concat multOp ts
        (multTerm (modTotalTerm r c) ss))
        (nts * (native_mod_total nr nc * nss)) ∧
      MulListEval M (__eo_list_concat multOp ts (multTerm r ss))
        (nts * (nr * nss)) := by
  have hCSmt : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    smtx_typeof_of_eo_int c hCTrans hCInt
  have hTsSmt : __smtx_typeof (__eo_to_smt ts) = SmtType.Int :=
    smtx_typeof_of_eo_int ts hTsTrans hTsInt
  have hRSmt : __smtx_typeof (__eo_to_smt r) = SmtType.Int :=
    smtx_typeof_of_eo_int r hRTrans hRInt
  have hSsSmt : __smtx_typeof (__eo_to_smt ss) = SmtType.Int :=
    smtx_typeof_of_eo_int ss hSsTrans hSsInt
  rcases smt_eval_int_of_type M hM c hCSmt with ⟨nc, hCEval⟩
  rcases smt_eval_int_of_type M hM r hRSmt with ⟨nr, hREval⟩
  rcases MulListEval.of_type_and_list M hM hTsList hTsSmt with
    ⟨nts, hTsEval⟩
  rcases MulListEval.of_type_and_list M hM hSsList hSsSmt with
    ⟨nss, hSsEval⟩
  have hModTy :
      __smtx_typeof (__eo_to_smt (modTotalTerm r c)) = SmtType.Int :=
    smtx_typeof_mod_total_int r c hRSmt hCSmt
  have hModEval :
      __smtx_model_eval M (__eo_to_smt (modTotalTerm r c)) =
        SmtValue.Numeral (native_mod_total nr nc) :=
    smtx_eval_mod_total_int M r c nr nc hREval hCEval
  refine ⟨nc, nts, nr, nss, hCEval, hREval, ?_, ?_⟩
  · exact MulListEval.concat hTsEval
      (MulListEval.cons hModTy hModEval hSsEval)
  · exact MulListEval.concat hTsEval
      (MulListEval.cons hRSmt hREval hSsEval)

private theorem typed___eo_prog_arith_mod_over_mod_mult_impl
    (M : SmtModel) (hM : model_total_typed M)
    (c ts r ss P : Term) :
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation ts ->
    RuleProofs.eo_has_smt_translation r ->
    RuleProofs.eo_has_smt_translation ss ->
    __eo_typeof c = Term.Int ->
    __eo_typeof ts = Term.Int ->
    __eo_typeof r = Term.Int ->
    __eo_typeof ss = Term.Int ->
    __eo_is_list multOp ts = Term.Boolean true ->
    __eo_is_list multOp ss = Term.Boolean true ->
    __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
      multConclusion c ts r ss ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) := by
  intro hCTrans hTsTrans hRTrans hSsTrans hCInt hTsInt hRInt hSsInt
    hTsList hSsList hProgEq
  rcases build_mult_lists M hM c ts r ss hCTrans hTsTrans hRTrans
      hSsTrans hCInt hTsInt hRInt hSsInt hTsList hSsList with
    ⟨nc, nts, nr, nss, _hCEval, _hREval, hLList, hRList⟩
  have hCSmt : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    smtx_typeof_of_eo_int c hCTrans hCInt
  have hLhsArgTy := MulListEval.type_int hLList
  have hRhsArgInfo := MulListEval.singleton_elim_eval hRList
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhsTerm c ts r ss)) = SmtType.Int :=
    smtx_typeof_mod_total_int
      (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss))
      c hLhsArgTy hCSmt
  have hRhsTy : __smtx_typeof (__eo_to_smt (rhsTerm c ts r ss)) = SmtType.Int :=
    smtx_typeof_mod_total_int
      (__eo_list_singleton_elim multOp
        (__eo_list_concat multOp ts (multTerm r ss)))
      c hRhsArgInfo.1 hCSmt
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (lhsTerm c ts r ss) (rhsTerm c ts r ss)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)

private theorem facts___eo_prog_arith_mod_over_mod_mult_impl
    (M : SmtModel) (hM : model_total_typed M)
    (c ts r ss P : Term) :
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation ts ->
    RuleProofs.eo_has_smt_translation r ->
    RuleProofs.eo_has_smt_translation ss ->
    __eo_typeof c = Term.Int ->
    __eo_typeof ts = Term.Int ->
    __eo_typeof r = Term.Int ->
    __eo_typeof ss = Term.Int ->
    __eo_is_list multOp ts = Term.Boolean true ->
    __eo_is_list multOp ss = Term.Boolean true ->
    __eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P) =
      multConclusion c ts r ss ->
    eo_interprets M
      (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) true := by
  intro hCTrans hTsTrans hRTrans hSsTrans hCInt hTsInt hRInt hSsInt
    hTsList hSsList hProgEq
  have hProgBool :
      RuleProofs.eo_has_bool_type
        (__eo_prog_arith_mod_over_mod_mult c ts r ss (Proof.pf P)) :=
    typed___eo_prog_arith_mod_over_mod_mult_impl M hM c ts r ss P
      hCTrans hTsTrans hRTrans hSsTrans hCInt hTsInt hRInt hSsInt
      hTsList hSsList hProgEq
  have hProgBool' : RuleProofs.eo_has_bool_type (multConclusion c ts r ss) := by
    simpa [hProgEq] using hProgBool
  rcases build_mult_lists M hM c ts r ss hCTrans hTsTrans hRTrans
      hSsTrans hCInt hTsInt hRInt hSsInt hTsList hSsList with
    ⟨nc, nts, nr, nss, hCEval, _hREval, hLList, hRList⟩
  have hLhsArgEval := MulListEval.eval hLList
  have hRhsArgInfo := MulListEval.singleton_elim_eval hRList
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhsTerm c ts r ss)) =
        SmtValue.Numeral
          (native_mod_total (nts * (native_mod_total nr nc * nss)) nc) :=
    smtx_eval_mod_total_int M
      (__eo_list_concat multOp ts (multTerm (modTotalTerm r c) ss))
      c (nts * (native_mod_total nr nc * nss)) nc hLhsArgEval hCEval
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (rhsTerm c ts r ss)) =
        SmtValue.Numeral
          (native_mod_total (nts * (nr * nss)) nc) :=
    smtx_eval_mod_total_int M
      (__eo_list_singleton_elim multOp
        (__eo_list_concat multOp ts (multTerm r ss)))
      c (nts * (nr * nss)) nc hRhsArgInfo.2 hCEval
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (lhsTerm c ts r ss) (rhsTerm c ts r ss) hProgBool' <| by
      rw [hLhsEval, hRhsEval, mod_mul_replace_mod]
      exact RuleProofs.smt_value_rel_refl
        (SmtValue.Numeral (native_mod_total (nts * (nr * nss)) nc))

theorem cmd_step_arith_mod_over_mod_mult_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mod_over_mod_mult args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_mod_over_mod_mult args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mod_over_mod_mult args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_mod_over_mod_mult args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons p1 premises =>
                          cases premises with
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              let C1 := a1
                              let TS1 := a2
                              let R1 := a3
                              let SS1 := a4
                              let P1 := __eo_state_proven_nth s p1
                              have hArgsTrans :
                                  (RuleProofs.eo_has_smt_translation C1 ∧
                                      __eo_typeof C1 = Term.Int) ∧
                                    ((RuleProofs.eo_has_smt_translation TS1 ∧
                                        __eo_typeof TS1 = Term.Int) ∧
                                      ((RuleProofs.eo_has_smt_translation R1 ∧
                                          __eo_typeof R1 = Term.Int) ∧
                                        ((RuleProofs.eo_has_smt_translation SS1 ∧
                                            __eo_typeof SS1 = Term.Int) ∧
                                          True))) := by
                                simpa [cmdTranslationOk, cArgListTranslationOkMask,
                                  argTranslationOkMasked,
                                  RuleProofs.eo_has_smt_translation,
                                  eoHasSmtTranslation] using hCmdTrans
                              have hCTrans :
                                  RuleProofs.eo_has_smt_translation C1 :=
                                hArgsTrans.1.1
                              have hCInt : __eo_typeof C1 = Term.Int :=
                                hArgsTrans.1.2
                              have hTsTrans :
                                  RuleProofs.eo_has_smt_translation TS1 :=
                                hArgsTrans.2.1.1
                              have hTsInt : __eo_typeof TS1 = Term.Int :=
                                hArgsTrans.2.1.2
                              have hRTrans :
                                  RuleProofs.eo_has_smt_translation R1 :=
                                hArgsTrans.2.2.1.1
                              have hRInt : __eo_typeof R1 = Term.Int :=
                                hArgsTrans.2.2.1.2
                              have hSsTrans :
                                  RuleProofs.eo_has_smt_translation SS1 :=
                                hArgsTrans.2.2.2.1.1
                              have hSsInt : __eo_typeof SS1 = Term.Int :=
                                hArgsTrans.2.2.2.1.2
                              change __eo_typeof
                                (__eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                  (Proof.pf P1)) = Term.Bool at hResultTy
                              change __eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                (Proof.pf P1) ≠ Term.Stuck at hProg
                              rcases prog_arith_mod_over_mod_mult_info
                                  C1 TS1 R1 SS1 P1 hProg with
                                ⟨C0, hP1Eq, hC0Eq, hProgEq⟩
                              have hLists :=
                                mult_lists_of_result_bool C1 TS1 R1 SS1 P1
                                  hProgEq hResultTy
                              have hTsList :
                                  __eo_is_list multOp TS1 = Term.Boolean true :=
                                hLists.1
                              have hSsList :
                                  __eo_is_list multOp SS1 = Term.Boolean true :=
                                hLists.2
                              refine ⟨?_, ?_⟩
                              · intro _hPremTrue
                                change eo_interprets M
                                  (__eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                    (Proof.pf P1)) true
                                exact facts___eo_prog_arith_mod_over_mod_mult_impl
                                  M hM C1 TS1 R1 SS1 P1
                                  hCTrans hTsTrans hRTrans hSsTrans hCInt
                                  hTsInt hRInt hSsInt hTsList hSsList hProgEq
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                    (Proof.pf P1))
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                  (__eo_prog_arith_mod_over_mod_mult C1 TS1 R1 SS1
                                    (Proof.pf P1))
                                  (typed___eo_prog_arith_mod_over_mod_mult_impl
                                    M hM C1 TS1 R1 SS1 P1
                                    hCTrans hTsTrans hRTrans hSsTrans hCInt
                                    hTsInt hRInt hSsInt hTsList hSsList hProgEq)

end ArithModOverModMult
