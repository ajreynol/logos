import Cpc.Proofs.RuleSupport.ReConcatStarSupport
import Cpc.Proofs.RuleSupport.ReUnfoldNegSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-! ## `__eo_requires` / `__eo_eq` extraction (shared with the wrappers) -/

theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not, SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

theorem eo_eq_eq_true {t s : Term} (h : __eo_eq t s = Term.Boolean true) : s = t := by
  unfold __eo_eq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Term.Boolean.injEq, native_teq] at h
    exact of_decide_eq_true h

/-! ## Small reductions -/

theorem mk_apply_ne_stuck_eq {a w : Term} (ha : a ≠ Term.Stuck) (hw : w ≠ Term.Stuck) :
    __eo_mk_apply a w = Term.Apply a w := by
  cases a <;> cases w <;> simp_all [__eo_mk_apply]

theorem list_concat_rec_cons (f x y z : Term) (hz : z ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f x) y) z =
      __eo_mk_apply (Term.Apply f x) (__eo_list_concat_rec y z) := by
  cases z <;> first | (exact absurd rfl hz) | rfl

/-- `RegLan` semantic equality, read as extensional membership over valid strings. -/
theorem reglan_rel_valid_eq {r s : native_RegLan} {str : native_String}
    (hRel : RuleProofs.smt_value_rel (SmtValue.RegLan r) (SmtValue.RegLan s))
    (hValid : native_string_valid str = true) :
    native_str_in_re str r = native_str_in_re str s := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
  change SmtValue.Boolean (native_re_ext_eq r s) = SmtValue.Boolean true at hRel
  simp at hRel
  exact hRel str hValid

/-! ## `re_concat` right-congruence (valid strings) -/

theorem native_re_concat_right_congr_valid (w v v' : native_RegLan)
    (h : ∀ s : native_String, native_string_valid s = true ->
        native_str_in_re s v = native_str_in_re s v')
    (s : native_String) (hs : native_string_valid s = true) :
    native_str_in_re s (native_re_mk_concat w v) =
      native_str_in_re s (native_re_mk_concat w v') := by
  rw [native_str_in_re_eq_nativeListInRe s _ hs,
    native_str_in_re_eq_nativeListInRe s _ hs]
  have hsValid : s.all native_char_valid = true := by
    simpa [native_string_valid] using hs
  have hsuffixValid : ∀ a b : List native_Char, a ++ b = s ->
      native_string_valid b = true := by
    intro a b hab
    have : b.all native_char_valid = true := by
      have := hsValid
      rw [← hab, List.all_append] at this
      simp only [Bool.and_eq_true] at this
      exact this.2
    simpa [native_string_valid] using this
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hm
    rcases (nativeListInRe_mk_concat_true_iff_exists_append s w v).1 hm with
      ⟨a, b, hab, ha, hb⟩
    have hbValid := hsuffixValid a b hab
    have hb' : nativeListInRe b v' = true := by
      rw [← native_str_in_re_eq_nativeListInRe b _ hbValid, ← h b hbValid,
        native_str_in_re_eq_nativeListInRe b _ hbValid]
      exact hb
    exact (nativeListInRe_mk_concat_true_iff_exists_append s w v').2
      ⟨a, b, hab, ha, hb'⟩
  · intro hm
    rcases (nativeListInRe_mk_concat_true_iff_exists_append s w v').1 hm with
      ⟨a, b, hab, ha, hb⟩
    have hbValid := hsuffixValid a b hab
    have hb' : nativeListInRe b v = true := by
      rw [← native_str_in_re_eq_nativeListInRe b _ hbValid, h b hbValid,
        native_str_in_re_eq_nativeListInRe b _ hbValid]
      exact hb
    exact (nativeListInRe_mk_concat_true_iff_exists_append s w v).2
      ⟨a, b, hab, ha, hb'⟩

/-- `re.concat` evaluation preserves `smt_value_rel` in its right argument. -/
theorem smtx_re_concat_rel_right (w v v' : SmtValue)
    (h : RuleProofs.smt_value_rel v v') :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_re_concat w v) (__smtx_model_eval_re_concat w v') := by
  by_cases hReg : ∃ vr vr', v = SmtValue.RegLan vr ∧ v' = SmtValue.RegLan vr'
  · rcases hReg with ⟨vr, vr', rfl, rfl⟩
    cases w with
    | RegLan wr =>
        apply smt_value_rel_reglan_of_valid_eq
        intro s hs
        exact native_re_concat_right_congr_valid wr vr vr'
          (fun t ht => reglan_rel_valid_eq h ht) s hs
    | _ => exact RuleProofs.smt_value_rel_refl _
  · have hEq : v = v' := (RuleProofs.smt_value_rel_iff_eq v v' hReg).1 h
    subst hEq
    exact RuleProofs.smt_value_rel_refl _

/-! ## Non-stuckness and congruence of `__eo_list_concat_rec` over `re_concat` -/

theorem list_concat_rec_ne_stuck :
    ∀ (a X : Term),
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true ->
      X ≠ Term.Stuck ->
      __eo_list_concat_rec a X ≠ Term.Stuck := by
  intro a X
  induction a, X using __eo_list_concat_rec.induct with
  | case1 z => intro hList _; simp [__eo_is_list] at hList
  | case2 t ht => intro _ hX; exact absurd rfl hX
  | case3 f x y z hz ih =>
      intro hList hX
      have hf := eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) f x y hList
      subst hf
      have hTailList :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y hList
      have hTail := ih hTailList hX
      rw [list_concat_rec_cons (Term.UOp UserOp.re_concat) x y z hX,
        mk_apply_ne_stuck_eq (by simp) hTail]
      simp
  | case4 nil z hns hzs hncons =>
      intro hList hX
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec; split <;> simp_all
      rw [hEq]; exact hX

theorem list_concat_rec_rel_right (M : SmtModel) :
    ∀ (a X : Term),
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true ->
      X ≠ Term.Stuck ->
      ∀ X' : Term, X' ≠ Term.Stuck ->
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt X)) (__smtx_model_eval M (__eo_to_smt X')) ->
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a X)))
          (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a X'))) := by
  intro a X
  induction a, X using __eo_list_concat_rec.induct with
  | case1 z => intro hList _; simp [__eo_is_list] at hList
  | case2 t ht => intro _ hX; exact absurd rfl hX
  | case3 f x y z hz ih =>
      intro hList hX X' hX' hXX
      have hf := eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) f x y hList
      subst hf
      have hTailList :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y hList
      have hLY := list_concat_rec_ne_stuck y z hTailList hX
      have hLY' := list_concat_rec_ne_stuck y X' hTailList hX'
      have ihApplied := ih hTailList hX X' hX' hXX
      rw [list_concat_rec_cons (Term.UOp UserOp.re_concat) x y z hX,
        mk_apply_ne_stuck_eq (by simp) hLY,
        list_concat_rec_cons (Term.UOp UserOp.re_concat) x y X' hX',
        mk_apply_ne_stuck_eq (by simp) hLY']
      have hev : ∀ Z : Term,
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) Z)) =
            __smtx_model_eval_re_concat (__smtx_model_eval M (__eo_to_smt x))
              (__smtx_model_eval M (__eo_to_smt Z)) := by
        intro Z
        change __smtx_model_eval M
          (SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt Z)) = _
        simp only [__smtx_model_eval]
      rw [hev (__eo_list_concat_rec y z), hev (__eo_list_concat_rec y X')]
      exact smtx_re_concat_rel_right _ _ _ ihApplied
  | case4 nil z hns hzs hncons =>
      intro hList hX X' hX' hXX
      have hEqz : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec; split <;> simp_all
      have hEqz' : __eo_list_concat_rec nil X' = X' := by
        unfold __eo_list_concat_rec; split <;> simp_all
      rw [hEqz, hEqz']; exact hXX

/-- `__eo_list_concat` reduces to `__eo_list_concat_rec` for two proper lists. -/
theorem list_concat_reduce (f a b : Term)
    (ha : __eo_is_list f a = Term.Boolean true)
    (hb : __eo_is_list f b = Term.Boolean true) :
    __eo_list_concat f a b = __eo_list_concat_rec a b := by
  change __eo_requires (__eo_is_list f a) (Term.Boolean true)
      (__eo_requires (__eo_is_list f b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) = __eo_list_concat_rec a b
  rw [ha, hb]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

/-- `__eo_list_concat_rec` of two proper `re_concat` lists is again a proper list. -/
theorem list_concat_rec_is_list :
    ∀ (a z : Term),
      __eo_is_list (Term.UOp UserOp.re_concat) a = Term.Boolean true ->
      __eo_is_list (Term.UOp UserOp.re_concat) z = Term.Boolean true ->
      __eo_is_list (Term.UOp UserOp.re_concat) (__eo_list_concat_rec a z) =
        Term.Boolean true := by
  intro a z
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z => intro hList _; simp [__eo_is_list] at hList
  | case2 t ht => intro _ hz; simp [__eo_is_list] at hz
  | case3 f x y z hz ih =>
      intro hList hz2
      have hf := eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.re_concat) f x y hList
      subst hf
      have hTailList :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.re_concat) x y hList
      have hLY := list_concat_rec_ne_stuck y z hTailList hz
      rw [list_concat_rec_cons (Term.UOp UserOp.re_concat) x y z hz,
        mk_apply_ne_stuck_eq (by simp) hLY]
      exact eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.re_concat) x
        (__eo_list_concat_rec y z) (by simp) (ih hTailList hz2)
  | case4 nil z hns hzs hncons =>
      intro hList hz2
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec; split <;> simp_all
      rw [hEq]; exact hz2

/-! ## Evaluation of `re_concat` / `re_mult re_allchar` terms -/

theorem eval_re_concat_term (M : SmtModel) (p q : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) p) q)) =
      __smtx_model_eval_re_concat (__smtx_model_eval M (__eo_to_smt p))
        (__smtx_model_eval M (__eo_to_smt q)) := by
  change __smtx_model_eval M (SmtTerm.re_concat (__eo_to_smt p) (__eo_to_smt q)) = _
  simp only [__smtx_model_eval]

theorem eval_sigma_star (M : SmtModel) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) (Term.UOp UserOp.re_allchar))) =
      SmtValue.RegLan native_re_all := by
  change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt (Term.UOp UserOp.re_allchar))) = _
  simp [__smtx_model_eval, __smtx_model_eval_re_mult, native_re_mult,
    native_re_mk_star, native_re_all, native_re_allchar]

/-! ## Eval-level soundness of the two nullable conclusions -/

/-- Σ* as a term. -/
abbrev tSigma : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) (Term.UOp UserOp.re_allchar)

abbrev tReConcat (p q : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) p) q

/-- The semantic equality underlying `re_concat_star_nullable1`. -/
theorem nullable1_eval_rel (M : SmtModel)
    (xs1 r1 ys1 : Term) (r1v ys1v : native_RegLan)
    (hXsList : __eo_is_list (Term.UOp UserOp.re_concat) xs1 = Term.Boolean true)
    (hYsList : __eo_is_list (Term.UOp UserOp.re_concat) ys1 = Term.Boolean true)
    (hR1 : __smtx_model_eval M (__eo_to_smt r1) = SmtValue.RegLan r1v)
    (hYs1 : __smtx_model_eval M (__eo_to_smt ys1) = SmtValue.RegLan ys1v)
    (hNull : native_re_nullable r1v = true)
    (hLhsEval : ∃ rr, __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.re_concat) xs1
          (tReConcat tSigma (tReConcat r1 ys1)))) = SmtValue.RegLan rr) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.re_concat) xs1
          (tReConcat tSigma (tReConcat r1 ys1)))))
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__eo_list_concat (Term.UOp UserOp.re_concat) xs1
            (tReConcat tSigma ys1))))) := by
  -- list-ness of the two tails `A` and `B`
  have hConsR1 : __eo_is_list (Term.UOp UserOp.re_concat) (tReConcat r1 ys1) =
      Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.re_concat) r1 ys1
      (by simp) hYsList
  have hAList : __eo_is_list (Term.UOp UserOp.re_concat)
      (tReConcat tSigma (tReConcat r1 ys1)) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.re_concat) tSigma _
      (by simp) hConsR1
  have hBList : __eo_is_list (Term.UOp UserOp.re_concat) (tReConcat tSigma ys1) =
      Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.re_concat) tSigma ys1
      (by simp) hYsList
  have hANe : (tReConcat tSigma (tReConcat r1 ys1)) ≠ Term.Stuck := by simp [tReConcat]
  have hBNe : (tReConcat tSigma ys1) ≠ Term.Stuck := by simp [tReConcat]
  -- evaluate the two tails
  have hEvalA : __smtx_model_eval M (__eo_to_smt (tReConcat tSigma (tReConcat r1 ys1))) =
      SmtValue.RegLan (native_re_mk_concat native_re_all
        (native_re_mk_concat r1v ys1v)) := by
    rw [tReConcat, eval_re_concat_term, eval_sigma_star, eval_re_concat_term, hR1, hYs1]
    rfl
  have hEvalB : __smtx_model_eval M (__eo_to_smt (tReConcat tSigma ys1)) =
      SmtValue.RegLan (native_re_mk_concat native_re_all ys1v) := by
    rw [tReConcat, eval_re_concat_term, eval_sigma_star, hYs1]
    rfl
  -- absorption relates `eval A` and `eval B`
  have hAbsorb : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (tReConcat tSigma (tReConcat r1 ys1))))
      (__smtx_model_eval M (__eo_to_smt (tReConcat tSigma ys1))) := by
    rw [hEvalA, hEvalB]
    apply smt_value_rel_reglan_of_valid_eq
    intro s hs
    exact native_str_in_re_all_concat_nullable_absorb r1v ys1v hNull s hs
  -- reduce the two `list_concat`s and apply congruence
  rw [list_concat_reduce (Term.UOp UserOp.re_concat) xs1 _ hXsList hAList]
  rw [list_concat_reduce (Term.UOp UserOp.re_concat) xs1 _ hXsList hBList]
  rw [list_concat_reduce (Term.UOp UserOp.re_concat) xs1 _ hXsList hAList] at hLhsEval
  have hCong : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_list_concat_rec xs1 (tReConcat tSigma (tReConcat r1 ys1)))))
      (__smtx_model_eval M (__eo_to_smt
        (__eo_list_concat_rec xs1 (tReConcat tSigma ys1)))) :=
    list_concat_rec_rel_right M xs1 _ hXsList hANe _ hBNe hAbsorb
  -- the right list is a proper `re_concat` list and evaluates to a `RegLan`
  have hCList : __eo_is_list (Term.UOp UserOp.re_concat)
      (__eo_list_concat_rec xs1 (tReConcat tSigma ys1)) = Term.Boolean true :=
    list_concat_rec_is_list xs1 _ hXsList hBList
  have hCRegLan : ReUnfoldNegSupport.RegLanEval M
      (__eo_list_concat_rec xs1 (tReConcat tSigma ys1)) := by
    rcases hLhsEval with ⟨rr, hrr⟩
    have hRR := hCong
    rw [hrr] at hRR
    -- `smt_value_rel (RegLan rr) X` forces `X` to be a `RegLan`
    cases hX : __smtx_model_eval M (__eo_to_smt
        (__eo_list_concat_rec xs1 (tReConcat tSigma ys1))) with
    | RegLan r => exact ⟨r, hX⟩
    | _ =>
        rw [hX] at hRR
        simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq] at hRR
  -- singleton_elim relates the RHS to the inner list eval
  have hSingleton := ReUnfoldNegSupport.reConcat_singleton_elim_rel_eval M
    (__eo_list_concat_rec xs1 (tReConcat tSigma ys1)) hCList hCRegLan
  exact RuleProofs.smt_value_rel_trans _ _ _ hCong
    (RuleProofs.smt_value_rel_symm _ _ hSingleton)

/-- The semantic equality underlying `re_concat_star_nullable2`. -/
theorem nullable2_eval_rel (M : SmtModel)
    (xs1 r1 ys1 : Term) (r1v ys1v : native_RegLan)
    (hXsList : __eo_is_list (Term.UOp UserOp.re_concat) xs1 = Term.Boolean true)
    (hYsList : __eo_is_list (Term.UOp UserOp.re_concat) ys1 = Term.Boolean true)
    (hR1 : __smtx_model_eval M (__eo_to_smt r1) = SmtValue.RegLan r1v)
    (hYs1 : __smtx_model_eval M (__eo_to_smt ys1) = SmtValue.RegLan ys1v)
    (hNull : native_re_nullable r1v = true)
    (hLhsEval : ∃ rr, __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.re_concat) xs1
          (tReConcat r1 (tReConcat tSigma ys1)))) = SmtValue.RegLan rr) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.re_concat) xs1
          (tReConcat r1 (tReConcat tSigma ys1)))))
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.re_concat)
          (__eo_list_concat (Term.UOp UserOp.re_concat) xs1
            (tReConcat tSigma ys1))))) := by
  have hBList : __eo_is_list (Term.UOp UserOp.re_concat) (tReConcat tSigma ys1) =
      Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.re_concat) tSigma ys1
      (by simp) hYsList
  have hAList : __eo_is_list (Term.UOp UserOp.re_concat)
      (tReConcat r1 (tReConcat tSigma ys1)) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list (Term.UOp UserOp.re_concat) r1 _
      (by simp) hBList
  have hANe : (tReConcat r1 (tReConcat tSigma ys1)) ≠ Term.Stuck := by simp [tReConcat]
  have hBNe : (tReConcat tSigma ys1) ≠ Term.Stuck := by simp [tReConcat]
  have hEvalA : __smtx_model_eval M (__eo_to_smt (tReConcat r1 (tReConcat tSigma ys1))) =
      SmtValue.RegLan (native_re_mk_concat r1v
        (native_re_mk_concat native_re_all ys1v)) := by
    rw [tReConcat, eval_re_concat_term, hR1, eval_re_concat_term, eval_sigma_star, hYs1]
    rfl
  have hEvalB : __smtx_model_eval M (__eo_to_smt (tReConcat tSigma ys1)) =
      SmtValue.RegLan (native_re_mk_concat native_re_all ys1v) := by
    rw [tReConcat, eval_re_concat_term, eval_sigma_star, hYs1]
    rfl
  have hAbsorb : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (tReConcat r1 (tReConcat tSigma ys1))))
      (__smtx_model_eval M (__eo_to_smt (tReConcat tSigma ys1))) := by
    rw [hEvalA, hEvalB]
    apply smt_value_rel_reglan_of_valid_eq
    intro s hs
    exact native_str_in_re_nullable_concat_all_absorb r1v ys1v hNull s hs
  rw [list_concat_reduce (Term.UOp UserOp.re_concat) xs1 _ hXsList hAList]
  rw [list_concat_reduce (Term.UOp UserOp.re_concat) xs1 _ hXsList hBList]
  rw [list_concat_reduce (Term.UOp UserOp.re_concat) xs1 _ hXsList hAList] at hLhsEval
  have hCong : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_list_concat_rec xs1 (tReConcat r1 (tReConcat tSigma ys1)))))
      (__smtx_model_eval M (__eo_to_smt
        (__eo_list_concat_rec xs1 (tReConcat tSigma ys1)))) :=
    list_concat_rec_rel_right M xs1 _ hXsList hANe _ hBNe hAbsorb
  have hCList : __eo_is_list (Term.UOp UserOp.re_concat)
      (__eo_list_concat_rec xs1 (tReConcat tSigma ys1)) = Term.Boolean true :=
    list_concat_rec_is_list xs1 _ hXsList hBList
  have hCRegLan : ReUnfoldNegSupport.RegLanEval M
      (__eo_list_concat_rec xs1 (tReConcat tSigma ys1)) := by
    rcases hLhsEval with ⟨rr, hrr⟩
    have hRR := hCong
    rw [hrr] at hRR
    cases hX : __smtx_model_eval M (__eo_to_smt
        (__eo_list_concat_rec xs1 (tReConcat tSigma ys1))) with
    | RegLan r => exact ⟨r, hX⟩
    | _ =>
        rw [hX] at hRR
        simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq] at hRR
  have hSingleton := ReUnfoldNegSupport.reConcat_singleton_elim_rel_eval M
    (__eo_list_concat_rec xs1 (tReConcat tSigma ys1)) hCList hCRegLan
  exact RuleProofs.smt_value_rel_trans _ _ _ hCong
    (RuleProofs.smt_value_rel_symm _ _ hSingleton)

end RuleProofs
