import Cpc.Proofs.Rules.Bv_umulo_elim

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

private theorem bv_smulo_elim_shape_of_ne_stuck (A : Term) :
    __eo_prog_bv_smulo_elim A ≠ Term.Stuck ->
    ∃ a b c,
      A =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) c := by
  intro h
  by_cases hShape :
      ∃ a b c,
        A =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b)) c
  · exact hShape
  · have hStuck : __eo_prog_bv_smulo_elim A = Term.Stuck := by
      rw [__eo_prog_bv_smulo_elim.eq_2]
      intro a b c hEq
      exact hShape ⟨a, b, c, hEq⟩
    exact False.elim (h hStuck)

private def bvSmuloExpanded (a b : Term) : Term :=
  let wTerm := __bv_bitwidth (__eo_typeof a)
  let nm2 := __eo_add wTerm (Term.Numeral (-2 : native_Int))
  let len :=
    __eo_add
      (__eo_add (Term.Numeral 1)
        (__eo_add (Term.Numeral (-1 : native_Int)) nm2))
      (Term.Numeral (-1 : native_Int))
  let topIdx := __eo_add wTerm (Term.Numeral (-1 : native_Int))
  let topExtract := Term.UOp2 UserOp2.extract topIdx topIdx
  let signExtendTop := Term.UOp1 UserOp1.sign_extend topIdx
  let xb :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) b)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvxor)
          (__eo_mk_apply signExtendTop (__eo_mk_apply topExtract b)))
        (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof b)))
  let xbBit1 := __eo_mk_apply
    (Term.UOp2 UserOp2.extract (Term.Numeral 1) (Term.Numeral 1)) xb
  let xa :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvxor) a)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvxor)
          (__eo_mk_apply signExtendTop (__eo_mk_apply topExtract a)))
        (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof a)))
  let xaTop := __eo_mk_apply (Term.UOp2 UserOp2.extract nm2 nm2) xa
  let scan :=
    __bv_smulo_elim_rec xa xb xaTop
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvand) xbBit1)
        (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.bvand) xaTop)
          (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof xbBit1))))
      (__eo_requires (__eo_is_neg len) (Term.Boolean false)
        (__iota_rec
          (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral 0) len)
          (Term.Numeral 1)))
      nm2
  let signExtendOne := Term.UOp1 UserOp1.sign_extend (Term.Numeral 1)
  let aExt := Term.Apply signExtendOne a
  let product :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt)
      (__eo_mk_apply
        (Term.Apply (Term.UOp UserOp.bvmul)
          (Term.Apply signExtendOne b))
        (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)))
  let prodBitW := __eo_mk_apply (Term.UOp2 UserOp2.extract wTerm wTerm) product
  let prodTopDiff :=
    __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.bvxor) prodBitW)
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.bvxor)
          (__eo_mk_apply topExtract product))
        (__eo_nil (Term.UOp UserOp.bvxor) (__eo_typeof prodBitW)))
  __eo_ite (__eo_eq wTerm (Term.Numeral 1))
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) a)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) b)
            (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof a)))))
      (Term.Binary 1 1))
    (__eo_ite (__eo_eq wTerm (Term.Numeral 2))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq) prodTopDiff)
        (Term.Binary 1 1))
      (__eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp.eq)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.bvor) scan)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.bvor) prodTopDiff)
              (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof scan)))))
        (Term.Binary 1 1)))

private def inc (b : Bool) : Nat :=
  if b then 1 else 0

private def signedOverflowMag (W X Y : Nat) (sx sy : Bool) : Bool :=
  let P := (X + inc sx) * (Y + inc sy)
  if sx = sy then decide (2 ^ W ≤ P) else decide (2 ^ W < P)

private def topDiffMag (W X Y : Nat) (sx sy : Bool) : Bool :=
  let P := (X + inc sx) * (Y + inc sy)
  if sx = sy then
    P.testBit (W + 1) ^^ P.testBit W
  else
    let R := if P = 0 then 0 else 2 ^ (W + 2) - P
    R.testBit (W + 1) ^^ R.testBit W

private theorem testBit_false_of_lt_two_pow {n k : Nat} (h : n < 2 ^ k) :
    n.testBit k = false := by
  by_cases hb : n.testBit k = true
  · have hle := Nat.ge_two_pow_of_testBit hb
    exact False.elim (Nat.not_le_of_gt h hle)
  · exact Bool.eq_false_iff.2 hb

private theorem pos_topDiff_eq (W P : Nat) (hP : P ≤ 2 ^ (W + 1)) :
    (P.testBit (W + 1) ^^ P.testBit W) = decide (2 ^ W ≤ P) := by
  by_cases hlt : P < 2 ^ W
  · have hWfalse : P.testBit W = false := testBit_false_of_lt_two_pow hlt
    have hW1false : P.testBit (W + 1) = false := by
      apply testBit_false_of_lt_two_pow
      exact Nat.lt_trans hlt
        (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : W < W + 1))
    have hnot : ¬ 2 ^ W ≤ P := Nat.not_le_of_gt hlt
    simp [hWfalse, hW1false, hnot]
  · have hge : 2 ^ W ≤ P := Nat.le_of_not_gt hlt
    by_cases heq : P = 2 ^ (W + 1)
    · subst P
      have hge' : 2 ^ W ≤ 2 ^ (W + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      have hb1 : (2 ^ (W + 1)).testBit (W + 1) = true := by
        rw [Nat.testBit_two_pow]
        simp
      have hb0 : (2 ^ (W + 1)).testBit W = false := by
        rw [Nat.testBit_two_pow]
        simp
      simp [hb1, hb0, hge']
    · have hltTop : P < 2 ^ (W + 1) := Nat.lt_of_le_of_ne hP heq
      have hbW : P.testBit W = true := bit_w_of_range hge hltTop
      have hbW1 : P.testBit (W + 1) = false :=
        testBit_false_of_lt_two_pow hltTop
      simp [hbW, hbW1, hge]

private theorem neg_topDiff_eq (W P : Nat) (hP : P ≤ 2 ^ (W + 1)) :
    (let R := if P = 0 then 0 else 2 ^ (W + 2) - P
     R.testBit (W + 1) ^^ R.testBit W) = decide (2 ^ W < P) := by
  by_cases hP0 : P = 0
  · subst P
    simp
  · have hPpos : 0 < P := Nat.pos_of_ne_zero hP0
    let R := 2 ^ (W + 2) - P
    let low := 2 ^ (W + 1) - P
    have hIf : (if P = 0 then 0 else 2 ^ (W + 2) - P) = R := by
      simp [hP0, R]
    rw [hIf]
    have hPow : 2 ^ (W + 2) = 2 ^ (W + 1) + 2 ^ (W + 1) := by
      have h : 2 ^ (W + 2) = 2 ^ (W + 1) * 2 := by
        simpa using (pow_two_mul (W + 1) 1)
      rw [h]
      omega
    have hR_eq : R = 2 ^ (W + 1) + low := by
      dsimp [R, low]
      rw [hPow]
      omega
    have hRlt : R < 2 ^ (W + 2) := by
      dsimp [R]
      exact Nat.sub_lt (Nat.two_pow_pos _) hPpos
    have hRge : 2 ^ (W + 1) ≤ R := by
      dsimp [R]
      omega
    have hbHigh : R.testBit (W + 1) = true := bit_w_of_range hRge hRlt
    have hLowLt : low < 2 ^ (W + 1) := by
      dsimp [low]
      exact Nat.sub_lt (Nat.two_pow_pos _) hPpos
    have hRmod : R % 2 ^ (W + 1) = low := by
      rw [hR_eq]
      have hmod :
          (2 ^ (W + 1) + low) % 2 ^ (W + 1) =
            low % 2 ^ (W + 1) := by
        simpa [Nat.add_comm, Nat.mul_comm] using
          (Nat.add_mul_mod_self_left low (2 ^ (W + 1)) 1)
      rw [hmod, Nat.mod_eq_of_lt hLowLt]
    have hbLowEq : R.testBit W = low.testBit W := by
      have htb := Nat.testBit_mod_two_pow R (W + 1) W
      rw [hRmod] at htb
      have hdec : decide (W < W + 1) = true := by simp
      rw [hdec] at htb
      simpa using htb.symm
    by_cases hle : P ≤ 2 ^ W
    · have hnot : ¬ 2 ^ W < P := Nat.not_lt_of_ge hle
      have hLowGe : 2 ^ W ≤ low := by
        dsimp [low]
        omega
      have hbLow : low.testBit W = true := bit_w_of_range hLowGe hLowLt
      change (R.testBit (W + 1) ^^ R.testBit W) = decide (2 ^ W < P)
      rw [hbHigh, hbLowEq, hbLow]
      simp [hnot]
    · have hgt : 2 ^ W < P := Nat.lt_of_not_ge hle
      have hLowLtW : low < 2 ^ W := by
        dsimp [low]
        omega
      have hbLow : low.testBit W = false :=
        testBit_false_of_lt_two_pow hLowLtW
      change (R.testBit (W + 1) ^^ R.testBit W) = decide (2 ^ W < P)
      rw [hbHigh, hbLowEq, hbLow]
      simp [hgt]

private theorem no_highPair_succ_product_bound {W X Y : Nat}
    (hX : X < 2 ^ W) (hY : Y < 2 ^ W)
    (hNo : ¬ highPair W X Y) :
    (X + 1) * (Y + 1) ≤ 2 ^ (W + 1) := by
  by_cases hY0 : Y = 0
  · subst Y
    have hx1 : X + 1 ≤ 2 ^ W := Nat.succ_le_of_lt hX
    exact Nat.le_trans (by simpa using hx1)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : W ≤ W + 1))
  · let i := Y.log2
    have hlog := (Nat.log2_eq_iff (n := Y) (k := i) hY0).mp rfl
    have hiW : i < W := by
      have hlogLt : Y.log2 < W := (Nat.log2_lt hY0).mpr hY
      simpa [i] using hlogLt
    by_cases hi0 : i = 0
    · have hYlt2 : Y < 2 := by
        simpa [i, hi0] using hlog.2
      have hYeq1 : Y = 1 := by
        have hpos : 0 < Y := Nat.pos_of_ne_zero hY0
        omega
      subst Y
      have hx1 : X + 1 ≤ 2 ^ W := Nat.succ_le_of_lt hX
      calc
        (X + 1) * (1 + 1) = (X + 1) * 2 := by omega
        _ ≤ 2 ^ W * 2 := Nat.mul_le_mul_right 2 hx1
        _ = 2 ^ (W + 1) := by simpa using (pow_two_mul W 1)
    · have hi1 : 1 ≤ i := by omega
      have hbit : Y.testBit i = true := Nat.testBit_log2 hY0
      have hXlt : X < 2 ^ (W - i) := by
        apply Nat.lt_of_not_le
        intro hle
        exact hNo ⟨i, hi1, hiW, hbit, hle⟩
      have hx1 : X + 1 ≤ 2 ^ (W - i) := Nat.succ_le_of_lt hXlt
      have hy1 : Y + 1 ≤ 2 ^ (i + 1) := Nat.succ_le_of_lt hlog.2
      have hmul := Nat.mul_le_mul hx1 hy1
      have hsum : W - i + (i + 1) = W + 1 := by omega
      calc
        (X + 1) * (Y + 1) ≤ 2 ^ (W - i) * 2 ^ (i + 1) := hmul
        _ = 2 ^ (W + 1) := by rw [pow_two_mul, hsum]

private theorem signed_formula_value {W X Y : Nat} {sx sy scan : Bool}
    (hX : X < 2 ^ W) (hY : Y < 2 ^ W)
    (hscan : scan = true ↔ highPair W X Y) :
    (scan || topDiffMag W X Y sx sy) =
      signedOverflowMag W X Y sx sy := by
  let P := (X + inc sx) * (Y + inc sy)
  have hPleMax : P ≤ (X + 1) * (Y + 1) := by
    dsimp [P, inc]
    cases sx <;> cases sy <;> simp
    · exact Nat.mul_le_mul (Nat.le_succ X) (Nat.le_succ Y)
    · exact Nat.mul_le_mul_right (Y + 1) (Nat.le_succ X)
    · exact Nat.mul_le_mul_left (X + 1) (Nat.le_succ Y)
  by_cases hp : highPair W X Y
  · have hscanTrue : scan = true := hscan.2 hp
    have hXYov : 2 ^ W ≤ X * Y := highPair_overflow hp
    have hOverflow : signedOverflowMag W X Y sx sy = true := by
      change
        (if sx = sy then decide (2 ^ W ≤ P) else decide (2 ^ W < P)) =
          true
      by_cases hsame : sx = sy
      · rw [if_pos hsame]
        have hPge : 2 ^ W ≤ P := by
          dsimp [P, inc]
          cases sx <;> cases sy <;> simp [inc] at hsame ⊢
          · exact hXYov
          · exact Nat.le_trans hXYov
              (Nat.mul_le_mul (Nat.le_succ X) (Nat.le_succ Y))
        simp [hPge]
      · rw [if_neg hsame]
        have hYpos : 0 < Y := by
          rcases hp with ⟨_i, _hi1, _hiW, hbit, _⟩
          exact Nat.pos_of_ne_zero (by intro hy0; subst Y; simp at hbit)
        have hXpos : 0 < X := by
          rcases hp with ⟨_i, _hi1, _hiW, _hbit, hle⟩
          exact Nat.pos_of_ne_zero (by intro hx0; subst X; simp at hle)
        have hPgt : 2 ^ W < P := by
          dsimp [P, inc]
          cases sx <;> cases sy <;> simp [inc] at hsame ⊢
          · rw [Nat.mul_add, Nat.mul_one]
            exact Nat.lt_of_le_of_lt hXYov
              (Nat.lt_add_of_pos_right hXpos)
          · rw [Nat.add_mul, Nat.one_mul]
            exact Nat.lt_of_le_of_lt hXYov
              (Nat.lt_add_of_pos_right hYpos)
        simp [hPgt]
    rw [hscanTrue, hOverflow]
    simp
  · have hscanFalse : scan = false :=
      Bool.eq_false_iff.2 (fun hs => hp (hscan.1 hs))
    have hBound : P ≤ 2 ^ (W + 1) :=
      Nat.le_trans hPleMax (no_highPair_succ_product_bound hX hY hp)
    have hTop :
        topDiffMag W X Y sx sy = signedOverflowMag W X Y sx sy := by
      change
        (if sx = sy then P.testBit (W + 1) ^^ P.testBit W
          else
            (let R := if P = 0 then 0 else 2 ^ (W + 2) - P
             R.testBit (W + 1) ^^ R.testBit W)) =
        (if sx = sy then decide (2 ^ W ≤ P) else decide (2 ^ W < P))
      by_cases hsame : sx = sy
      · rw [if_pos hsame, if_pos hsame]
        exact pos_topDiff_eq W P hBound
      · rw [if_neg hsame, if_neg hsame]
        exact neg_topDiff_eq W P hBound
    rw [hscanFalse, hTop]
    simp

/--
Semantic core of `bv_smulo_elim`.

The generated rule expands `(bvsmulo a b)` to `bvSmuloExpanded a b`.  This
lemma isolates the bit-level signed-overflow argument from the command wrapper.
Its proof follows the same value-level shape as `bv_umulo_elim`, with the
additional signed-product top-bit test used by the CPC rule.
-/
private axiom eval_bv_smulo_expanded
    (M : SmtModel) (hM : model_total_typed M) (a b : Term)
    (hNN : term_has_non_none_type
      (SmtTerm.bvsmulo (__eo_to_smt a) (__eo_to_smt b)))
    (hExpandedNe : bvSmuloExpanded a b ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (bvSmuloExpanded a b)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b))

theorem cmd_step_bv_smulo_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_smulo_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_smulo_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_smulo_elim args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.bv_smulo_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                  cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_bv_smulo_elim A)
              change __eo_typeof (__eo_prog_bv_smulo_elim A) = Term.Bool
                at hResultTy
              have hProgNe' : __eo_prog_bv_smulo_elim A ≠ Term.Stuck := by
                simpa using hProgNe
              rcases bv_smulo_elim_shape_of_ne_stuck A hProgNe' with
                ⟨a, b, rhs, hShape⟩
              subst A
              let lhs := Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) a) b
              let expanded := bvSmuloExpanded a b
              let orig := Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
              have hReqNe :
                  __eo_requires expanded rhs orig ≠ Term.Stuck := by
                simpa [__eo_prog_bv_smulo_elim, expanded, orig, lhs,
                  bvSmuloExpanded] using hProgNe'
              have hExpandedEq : expanded = rhs :=
                support_eo_requires_cond_eq_of_non_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                eo_requires_left_ne_stuck_of_ne_stuck hReqNe
              have hRhsNe : rhs ≠ Term.Stuck := by
                rw [← hExpandedEq]
                exact hExpandedNe
              have hProgEq :
                  __eo_prog_bv_smulo_elim
                      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) =
                    orig := by
                rw [__eo_prog_bv_smulo_elim.eq_1]
                change __eo_requires expanded rhs orig = orig
                simp [__eo_requires, hExpandedEq, hRhsNe, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hOrigTy : __eo_typeof orig = Term.Bool := by
                simpa [hProgEq, orig, lhs] using hResultTy
              have hOrigBool : RuleProofs.eo_has_bool_type orig :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  orig hATrans hOrigTy
              rcases
                  RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    lhs rhs hOrigBool with
                ⟨_hSameTy, hLhsNN⟩
              have hBvsmuloNN :
                  term_has_non_none_type
                    (SmtTerm.bvsmulo (__eo_to_smt a) (__eo_to_smt b)) := by
                unfold term_has_non_none_type
                simpa [lhs] using hLhsNN
              have hExpandedEval :
                  __smtx_model_eval M (__eo_to_smt expanded) =
                    __smtx_model_eval M (__eo_to_smt lhs) := by
                simpa [expanded, lhs] using
                  eval_bv_smulo_expanded M hM a b hBvsmuloNN hExpandedNe
              have hRelExpanded :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt expanded))
                    (__smtx_model_eval M (__eo_to_smt lhs)) := by
                rw [hExpandedEval]
                exact RuleProofs.smt_value_rel_refl _
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt lhs))
                    (__smtx_model_eval M (__eo_to_smt rhs)) := by
                rw [← hExpandedEq]
                exact RuleProofs.smt_value_rel_symm _ _ hRelExpanded
              have hFact :
                  eo_interprets M (__eo_prog_bv_smulo_elim orig) true := by
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel
                  M lhs rhs hOrigBool hRel
              exact
                { facts_of_true := by
                    intro _premisesTrue
                    simpa [orig] using hFact
                  has_smt_translation := by
                    rw [hProgEq]
                    exact
                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                        orig hOrigBool }
