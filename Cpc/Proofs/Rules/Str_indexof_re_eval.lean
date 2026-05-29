import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

private theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq] at h'
  rcases h' with ⟨hxy, hxOk, _hz⟩
  subst y
  simp [__eo_requires, native_ite, native_teq, hxOk]

private theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq] at h'
  rcases h' with ⟨_hxy, hxOk, _hz⟩
  intro hx
  subst x
  simp [hx, native_not] at hxOk

private theorem native_unpack_seq_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | x :: xs => by
      simp [native_pack_seq, native_unpack_seq, native_unpack_seq_pack_seq T xs]

private theorem map_native_ssm_char_of_value_char :
    ∀ s : native_String,
      List.map (native_ssm_char_of_value ∘ SmtValue.Char) s = s
  | [] => rfl
  | c :: cs => by
      simpa [Function.comp_def, native_ssm_char_of_value] using
        map_native_ssm_char_of_value_char cs

private theorem native_unpack_string_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp [native_unpack_string, native_pack_string, native_unpack_seq_pack_seq,
    map_native_ssm_char_of_value_char]

private theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

private theorem eq_operands_have_smt_translation_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    RuleProofs.eo_has_smt_translation x ∧
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation] using hNonNone
  · simpa [RuleProofs.eo_has_smt_translation, hTy] using hNonNone

private theorem str_indexof_re_args_smt_types_of_has_translation
    (s r n : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) r) n) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  intro hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.str_indexof_re (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt n)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) r) n)) ≠
      SmtType.None
    exact hTrans
  exact str_indexof_re_args_of_non_none hNN

private theorem str_indexof_re_eval_concrete_side_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (str : native_String) (r : Term) (ni : native_Int) (rv : native_RegLan)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSideNe :
      (let lenTerm := __eo_len (Term.String str)
       let tail := __eo_extract (Term.String str) (Term.Numeral ni) lenTerm
       let matchTerm :=
        __eo_requires (__eo_is_str tail) (Term.Boolean true)
          (__str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
              (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
                (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
            (Term.Numeral 0))
       let idxTerm := __pair_first matchTerm
       __eo_ite (__eo_or (__eo_gt (Term.Numeral ni) lenTerm)
           (__eo_is_neg (Term.Numeral ni)))
         (Term.Numeral (-1 : native_Int))
         (__eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
           (Term.Numeral (-1 : native_Int))
           (__eo_add (Term.Numeral ni) idxTerm))) ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (let lenTerm := __eo_len (Term.String str)
           let tail := __eo_extract (Term.String str) (Term.Numeral ni) lenTerm
           let matchTerm :=
            __eo_requires (__eo_is_str tail) (Term.Boolean true)
              (__str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
                    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
                (Term.Numeral 0))
           let idxTerm := __pair_first matchTerm
           __eo_ite (__eo_or (__eo_gt (Term.Numeral ni) lenTerm)
               (__eo_is_neg (Term.Numeral ni)))
             (Term.Numeral (-1 : native_Int))
             (__eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
               (Term.Numeral (-1 : native_Int))
               (__eo_add (Term.Numeral ni) idxTerm)))) =
      SmtValue.Numeral (native_str_indexof_re str rv ni) := by
  by_cases hNeg : ni < 0
  · have hNegBool : native_zlt ni 0 = true := by
      simp [native_zlt, hNeg]
    simp [__eo_len, __eo_extract, __eo_gt, __eo_is_neg, __eo_or, __eo_ite,
      native_ite, native_teq, native_or, hNegBool, native_str_indexof_re,
      hNeg]
    change __smtx_model_eval M (SmtTerm.Numeral (-1)) = SmtValue.Numeral (-1)
    rw [__smtx_model_eval.eq_2]
  · by_cases hPastEnd : Int.ofNat str.length < ni
    · have hGtBool : native_zlt (native_str_len str) ni = true := by
        simpa [native_str_len, native_zlt] using hPastEnd
      have hNegBool : native_zlt ni 0 = false := by
        simp [native_zlt, hNeg]
      have hStartNotLe : ¬ Int.toNat ni <= str.length := by
        intro hStartLe
        have hNiNonneg : 0 <= ni := Int.not_lt.mp hNeg
        have hNiEq : Int.ofNat (Int.toNat ni) = ni :=
          Int.toNat_of_nonneg hNiNonneg
        have hLe : (Int.toNat ni : Int) <= (str.length : Int) := by
          exact_mod_cast hStartLe
        change Int.ofNat (Int.toNat ni) <= Int.ofNat str.length at hLe
        rw [hNiEq] at hLe
        omega
      simp [__eo_len, __eo_extract, __eo_gt, __eo_is_neg, __eo_or, __eo_ite,
        native_ite, native_teq, native_or, hGtBool, hNegBool,
        native_str_indexof_re, hNeg, hStartNotLe]
      change __smtx_model_eval M (SmtTerm.Numeral (-1)) = SmtValue.Numeral (-1)
      rw [__smtx_model_eval.eq_2]
    · sorry

private theorem str_indexof_re_eval_side_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (s r n m : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m))
    (hProgNe :
      __eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m) ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)) =
      __smtx_model_eval M (__eo_to_smt m) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n
  let body := Term.Apply (Term.Apply Term.eq lhs) m
  let lenTerm := __eo_len s
  let tail := __eo_extract s n lenTerm
  let matchTerm :=
    __eo_requires (__eo_is_str tail) (Term.Boolean true)
      (__str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (Term.Numeral 0))
  let idxTerm := __pair_first matchTerm
  let side :=
    __eo_ite (__eo_or (__eo_gt n lenTerm) (__eo_is_neg n))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
        (Term.Numeral (-1 : native_Int))
        (__eo_add n idxTerm))
  change __eo_requires side m body ≠ Term.Stuck at hProgNe
  have hSideEq : side = m :=
    eo_requires_eq_of_ne_stuck side m body hProgNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side m body hProgNe
  have hEqOperands :=
    eq_operands_have_smt_translation_of_eq_has_smt_translation lhs m hEqTrans
  have hArgTypes :=
    str_indexof_re_args_smt_types_of_has_translation s r n hEqOperands.1
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := hArgTypes.2.1
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  cases s <;> first
  | case Binary w bv =>
      have hBad := hArgTypes.1
      change __smtx_typeof (SmtTerm.Binary w bv) = SmtType.Seq SmtType.Char at hBad
      cases hCond :
          native_and (native_zleq 0 w)
            (native_zeq bv (native_mod_total bv (native_int_pow2 w))) <;>
        simp [__smtx_typeof, native_ite, hCond] at hBad
  | case String str =>
      cases n <;> first
      | case Numeral ni =>
      have hConcreteSideNe :
          (let lenTerm := __eo_len (Term.String str)
           let tail := __eo_extract (Term.String str) (Term.Numeral ni) lenTerm
           let matchTerm :=
            __eo_requires (__eo_is_str tail) (Term.Boolean true)
              (__str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
                (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
                    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
                (Term.Numeral 0))
           let idxTerm := __pair_first matchTerm
           __eo_ite (__eo_or (__eo_gt (Term.Numeral ni) lenTerm)
               (__eo_is_neg (Term.Numeral ni)))
             (Term.Numeral (-1 : native_Int))
             (__eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
               (Term.Numeral (-1 : native_Int))
               (__eo_add (Term.Numeral ni) idxTerm))) ≠ Term.Stuck := by
        simpa [side, lenTerm, tail, matchTerm, idxTerm] using hSideNe
      have hSideEval :=
        str_indexof_re_eval_concrete_side_model_eval M hM str r ni rv hRTy
          hREval hConcreteSideNe
      have hLhsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.Apply Term.str_indexof_re (Term.String str)) r)
                  (Term.Numeral ni))) =
            SmtValue.Numeral (native_str_indexof_re str rv ni) := by
        change __smtx_model_eval M
            (SmtTerm.str_indexof_re (SmtTerm.String str) (__eo_to_smt r)
              (SmtTerm.Numeral ni)) =
          SmtValue.Numeral (native_str_indexof_re str rv ni)
        simp [__smtx_model_eval, hREval, __smtx_model_eval_str_indexof_re,
          native_unpack_string_pack_string]
      rw [← hSideEq, hLhsEval]
      simpa [side, lenTerm, tail, matchTerm, idxTerm] using hSideEval.symm
      | (change side ≠ Term.Stuck at hSideNe
         simp [lenTerm, tail, matchTerm, idxTerm, side, __eo_len, __eo_extract,
           __eo_gt, __eo_is_neg, __eo_or, __eo_ite, __eo_requires, native_ite,
           native_teq, native_not, SmtEval.native_not] at hSideNe)
  | (change side ≠ Term.Stuck at hSideNe
     simp [lenTerm, tail, matchTerm, idxTerm, side, __eo_len, __eo_extract,
       __eo_gt, __eo_is_neg, __eo_or, __eo_ite, __eo_requires, native_ite,
       native_teq, native_not, SmtEval.native_not] at hSideNe)

private theorem str_indexof_re_eval_valid_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s r n m : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m))
    (hProgNe :
      __eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m) ≠ Term.Stuck)
    (hProgTy :
      __eo_typeof
        (__eo_prog_str_indexof_re_eval
          (Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
            m)) =
        Term.Bool) :
    StepRuleProperties M []
      (__eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m)) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n
  let body := Term.Apply (Term.Apply Term.eq lhs) m
  let lenTerm := __eo_len s
  let tail := __eo_extract s n lenTerm
  let matchTerm :=
    __eo_requires (__eo_is_str tail) (Term.Boolean true)
      (__str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (Term.Numeral 0))
  let idxTerm := __pair_first matchTerm
  let side :=
    __eo_ite (__eo_or (__eo_gt n lenTerm) (__eo_is_neg n))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
        (Term.Numeral (-1 : native_Int))
        (__eo_add n idxTerm))
  have hReqEq : __eo_requires side m body = body := by
    change __eo_requires side m body ≠ Term.Stuck at hProgNe
    exact eo_requires_result_eq_of_ne_stuck side m body hProgNe
  have hBodyTy : __eo_typeof body = Term.Bool := by
    change __eo_typeof (__eo_requires side m body) = Term.Bool at hProgTy
    rw [hReqEq] at hProgTy
    exact hProgTy
  change StepRuleProperties M [] (__eo_requires side m body)
  rw [hReqEq]
  have hBool : RuleProofs.eo_has_bool_type body :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type body hArgTrans hBodyTy
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type body hBool⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M lhs m hBool <| by
    have hEval :=
      str_indexof_re_eval_side_model_eval M hM s r n m hArgTrans hProgNe
    rw [hEval]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt m))

end RuleProofs

theorem cmd_step_str_indexof_re_eval_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_re_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_re_eval args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_re_eval args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_indexof_re_eval args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp m =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply idxApp n =>
                                  cases idxApp with
                                  | Apply idxApp2 r =>
                                      cases idxApp2 with
                                      | Apply idxOp sArg =>
                                          cases idxOp with
                                          | UOp idxOpName =>
                                              cases idxOpName with
                                              | str_indexof_re =>
                                                  have hProps :=
                                                    RuleProofs.str_indexof_re_eval_valid_properties
                                                      M hM sArg r n m (by
                                                        simpa using hA1Trans) (by
                                                        change
                                                          __eo_prog_str_indexof_re_eval
                                                            (Term.Apply
                                                              (Term.Apply Term.eq
                                                                (Term.Apply
                                                                  (Term.Apply
                                                                    (Term.Apply Term.str_indexof_re
                                                                      sArg) r) n))
                                                              m) ≠
                                                            Term.Stuck at hProg
                                                        exact hProg) (by
                                                        change
                                                          __eo_typeof
                                                            (__eo_prog_str_indexof_re_eval
                                                              (Term.Apply
                                                                (Term.Apply Term.eq
                                                                  (Term.Apply
                                                                    (Term.Apply
                                                                      (Term.Apply Term.str_indexof_re
                                                                        sArg) r) n))
                                                                m)) =
                                                            Term.Bool at hResultTy
                                                        exact hResultTy)
                                                  change StepRuleProperties M []
                                                    (__eo_prog_str_indexof_re_eval
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply
                                                            (Term.Apply
                                                              (Term.Apply Term.str_indexof_re
                                                                sArg) r) n))
                                                        m))
                                                  simpa [premiseTermList] using hProps
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
