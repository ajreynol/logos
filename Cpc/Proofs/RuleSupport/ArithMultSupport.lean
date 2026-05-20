import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithMultSupport

abbrev arithZero (m : Term) : Term :=
  __arith_mk_zero (__eo_typeof m)

abbrev arithOne (m : Term) : Term :=
  __eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)

abbrev scale (m x : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.mult) m)
    (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) (arithOne m))

abbrev relTerm (r x y : Term) : Term :=
  Term.Apply (Term.Apply r x) y

abbrev posAntecedent (m F : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m)))
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (Term.Boolean true))

abbrev negAntecedent (m F : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m)))
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (Term.Boolean true))

abbrev posConclusion (r m a b : Term) : Term :=
  relTerm r (scale m a) (scale m b)

abbrev negConclusion (r m a b : Term) : Term :=
  __arith_rel_inv r (scale m a) (scale m b)

private theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem eo_mk_apply_fun_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  intro hf
  subst f
  simp [__eo_mk_apply] at h

private theorem eo_mk_apply_arg_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem scale_mk_eq_of_ne_stuck (m x : Term)
    (h :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) x) (arithOne m)) ≠
        Term.Stuck) :
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) x) (arithOne m)) =
      scale m x := by
  have hInner :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) x) (arithOne m) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hInner]

private theorem arith_rel_inv_left_ne_stuck_of_ne_stuck (r x y : Term)
    (h : __arith_rel_inv r x y ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases r <;> cases y <;> simp [__arith_rel_inv] at h

private theorem arith_rel_inv_right_ne_stuck_of_ne_stuck (r x y : Term)
    (h : __arith_rel_inv r x y ≠ Term.Stuck) :
    y ≠ Term.Stuck := by
  intro hy
  subst y
  cases r <;> cases x <;> simp [__arith_rel_inv] at h

private theorem mk_arith_mult_pos_eq_of_ne_stuck
    (m r a b : Term)
    (h :
      __mk_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck) :
    __mk_arith_mult_pos m (Term.Apply (Term.Apply r a) b) =
      posConclusion r m a b := by
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__mk_arith_mult_pos] at h
  simp [__mk_arith_mult_pos, hM, posConclusion, relTerm] at h ⊢
  let one := arithOne m
  let lhsMk :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a) one)
  let rhsMk :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b) one)
  have hFun :
      __eo_mk_apply r lhsMk ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
  have hLhs : lhsMk ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hFun
  have hRhs : rhsMk ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hFun]
  change Term.Apply (Term.Apply r lhsMk) rhsMk =
    Term.Apply (Term.Apply r (scale m a)) (scale m b)
  rw [show lhsMk = scale m a by
    simpa [lhsMk, one, arithOne] using scale_mk_eq_of_ne_stuck m a hLhs]
  rw [show rhsMk = scale m b by
    simpa [rhsMk, one, arithOne] using scale_mk_eq_of_ne_stuck m b hRhs]

private theorem mk_arith_mult_neg_eq_of_ne_stuck
    (m r a b : Term)
    (h :
      __mk_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck) :
    __mk_arith_mult_neg m (Term.Apply (Term.Apply r a) b) =
      negConclusion r m a b := by
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__mk_arith_mult_neg] at h
  simp [__mk_arith_mult_neg, hM, negConclusion] at h ⊢
  let one := arithOne m
  let lhsMk :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a) one)
  let rhsMk :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b) one)
  have hLhs : lhsMk ≠ Term.Stuck := by
    simpa [lhsMk, one, arithOne] using
      arith_rel_inv_left_ne_stuck_of_ne_stuck r
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a)
            (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)))
        )
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b)
            (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)))
        )
        h
  have hRhs : rhsMk ≠ Term.Stuck := by
    simpa [rhsMk, one, arithOne] using
      arith_rel_inv_right_ne_stuck_of_ne_stuck r
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a)
            (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)))
        )
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b)
            (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)))
        )
        h
  rw [show
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) a)
          (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m))) =
        scale m a by
    simpa [arithOne] using scale_mk_eq_of_ne_stuck m a hLhs]
  rw [show
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) m)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.mult) b)
          (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m))) =
        scale m b by
    simpa [arithOne] using scale_mk_eq_of_ne_stuck m b hRhs]

private theorem prog_arith_mult_pos_eq_of_ne_stuck
    (m r a b : Term)
    (h :
      __eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠
        Term.Stuck) :
    __eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b) =
      Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (posAntecedent m (Term.Apply (Term.Apply r a) b)))
        (posConclusion r m a b) := by
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__eo_prog_arith_mult_pos] at h
  simp [__eo_prog_arith_mult_pos, hM] at h ⊢
  have hConcl :
      __mk_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  have hImp :
      __eo_mk_apply (Term.UOp UserOp.imp)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.and)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply r a) b)) (Term.Boolean true))) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
  have hAnte :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply r a) b)) (Term.Boolean true)) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hImp
  have hAnd :
      __eo_mk_apply (Term.UOp UserOp.and)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m)) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hAnte
  have hSign :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.gt) m) (arithZero m) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hAnd
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hImp]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hAnte]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hAnd]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSign]
  rw [mk_arith_mult_pos_eq_of_ne_stuck m r a b hConcl]

private theorem prog_arith_mult_neg_eq_of_ne_stuck
    (m r a b : Term)
    (h :
      __eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠
        Term.Stuck) :
    __eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b) =
      Term.Apply (Term.Apply (Term.UOp UserOp.imp)
        (negAntecedent m (Term.Apply (Term.Apply r a) b)))
        (negConclusion r m a b) := by
  have hM : m ≠ Term.Stuck := by
    intro hm
    subst m
    simp [__eo_prog_arith_mult_neg] at h
  simp [__eo_prog_arith_mult_neg, hM] at h ⊢
  have hConcl :
      __mk_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ h
  have hImp :
      __eo_mk_apply (Term.UOp UserOp.imp)
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.and)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m)))
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.Apply r a) b)) (Term.Boolean true))) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ h
  have hAnte :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.and)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply r a) b)) (Term.Boolean true)) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hImp
  have hAnd :
      __eo_mk_apply (Term.UOp UserOp.and)
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m)) ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hAnte
  have hSign :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.lt) m) (arithZero m) ≠
        Term.Stuck :=
    eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hAnd
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ h]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hImp]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hAnte]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hAnd]
  rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSign]
  rw [mk_arith_mult_neg_eq_of_ne_stuck m r a b hConcl]

theorem native_to_real_lt_eq (a b : native_Int) :
    native_qlt (native_to_real a) (native_to_real b) = native_zlt a b := by
  rw [← native_qsub_lt_zero_eq (native_to_real a) (native_to_real b)]
  exact native_to_real_sub_lt_zero_eq a b

theorem native_to_real_leq_eq (a b : native_Int) :
    native_qleq (native_to_real a) (native_to_real b) = native_zleq a b := by
  rw [← native_qsub_leq_zero_eq (native_to_real a) (native_to_real b)]
  exact native_to_real_sub_leq_zero_eq a b

theorem native_to_real_qeq_eq (a b : native_Int) :
    native_qeq (native_to_real a) (native_to_real b) = native_zeq a b := by
  rw [← native_qsub_eq_zero_eq (native_to_real a) (native_to_real b)]
  exact native_to_real_sub_eq_zero_eq a b

private theorem rat_mul_lt_of_pos_left {c a b : Rat}
    (hc : 0 < c) (hab : a < b) :
    c * a < c * b := by
  rw [Rat.lt_iff_sub_pos]
  have hdiff : 0 < b - a := (Rat.lt_iff_sub_pos a b).mp hab
  have hmul : 0 < c * (b - a) :=
    (Rat.mul_pos_iff_of_pos_left hc).mpr hdiff
  simpa [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.add_comm] using hmul

private theorem rat_mul_le_of_pos_left {c a b : Rat}
    (hc : 0 < c) (hab : a ≤ b) :
    c * a ≤ c * b := by
  rcases (Rat.le_iff_lt_or_eq.mp hab) with hlt | heq
  · exact Rat.le_iff_lt_or_eq.mpr (Or.inl (rat_mul_lt_of_pos_left hc hlt))
  · subst b
    exact Rat.le_iff_lt_or_eq.mpr (Or.inr rfl)

private theorem rat_mul_lt_of_neg_left {c a b : Rat}
    (hc : c < 0) (hab : a < b) :
    c * b < c * a := by
  have hpos : 0 < -c :=
    (Rat.lt_neg_iff (a := 0) (b := c)).mpr (by simpa using hc)
  have hltneg : (-c) * a < (-c) * b :=
    rat_mul_lt_of_pos_left hpos hab
  have h := Rat.neg_lt_neg hltneg
  simpa [Rat.neg_mul, Rat.neg_neg] using h

private theorem rat_mul_le_of_neg_left {c a b : Rat}
    (hc : c < 0) (hab : a ≤ b) :
    c * b ≤ c * a := by
  have hpos : 0 < -c :=
    (Rat.lt_neg_iff (a := 0) (b := c)).mpr (by simpa using hc)
  have hleNeg : (-c) * a ≤ (-c) * b :=
    rat_mul_le_of_pos_left hpos hab
  have h := Rat.neg_le_neg hleNeg
  simpa [Rat.neg_mul, Rat.neg_neg] using h

theorem native_qlt_mul_of_pos_left {c a b : native_Rat} :
    native_qlt (native_mk_rational 0 1) c = true ->
    native_qlt a b = true ->
    native_qlt (native_qmult c a) (native_qmult c b) = true := by
  intro hc hab
  have hc' : (0 : Rat) < c := by
    simpa [native_qlt, native_mk_rational_zero] using hc
  have hab' : a < b := by
    simpa [native_qlt] using hab
  have hres : c * a < c * b := rat_mul_lt_of_pos_left hc' hab'
  simpa [native_qlt, native_qmult] using hres

theorem native_qleq_mul_of_pos_left {c a b : native_Rat} :
    native_qlt (native_mk_rational 0 1) c = true ->
    native_qleq a b = true ->
    native_qleq (native_qmult c a) (native_qmult c b) = true := by
  intro hc hab
  have hc' : (0 : Rat) < c := by
    simpa [native_qlt, native_mk_rational_zero] using hc
  have hab' : a ≤ b := by
    simpa [native_qleq] using hab
  have hres : c * a ≤ c * b := rat_mul_le_of_pos_left hc' hab'
  simpa [native_qleq, native_qmult] using hres

theorem native_qlt_mul_of_neg_left {c a b : native_Rat} :
    native_qlt c (native_mk_rational 0 1) = true ->
    native_qlt a b = true ->
    native_qlt (native_qmult c b) (native_qmult c a) = true := by
  intro hc hab
  have hc' : c < (0 : Rat) := by
    simpa [native_qlt, native_mk_rational_zero] using hc
  have hab' : a < b := by
    simpa [native_qlt] using hab
  have hres : c * b < c * a := rat_mul_lt_of_neg_left hc' hab'
  simpa [native_qlt, native_qmult] using hres

theorem native_qleq_mul_of_neg_left {c a b : native_Rat} :
    native_qlt c (native_mk_rational 0 1) = true ->
    native_qleq a b = true ->
    native_qleq (native_qmult c b) (native_qmult c a) = true := by
  intro hc hab
  have hc' : c < (0 : Rat) := by
    simpa [native_qlt, native_mk_rational_zero] using hc
  have hab' : a ≤ b := by
    simpa [native_qleq] using hab
  have hres : c * b ≤ c * a := rat_mul_le_of_neg_left hc' hab'
  simpa [native_qleq, native_qmult] using hres

theorem native_qeq_mul_congr_left {c a b : native_Rat} :
    native_qeq a b = true ->
    native_qeq (native_qmult c a) (native_qmult c b) = true := by
  intro hab
  have hab' : a = b := by
    simpa [native_qeq] using hab
  subst b
  simp [native_qeq]

private theorem native_to_real_zero :
    native_to_real 0 = native_mk_rational 0 1 := by
  native_decide

private theorem native_to_real_one :
    native_to_real 1 = native_mk_rational 1 1 := by
  native_decide

theorem arith_rel_op_has_bool_type_of_translation
    (r a b : Term) :
    arithRelOp r ->
    RuleProofs.eo_has_smt_translation (relTerm r a b) ->
    RuleProofs.eo_has_bool_type (relTerm r a b) := by
  intro hRel hTrans
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp [arithRelOp] at hRel
    · rcases eq_operands_same_smt_type_of_eq_has_smt_translation a b
          (by simpa [relTerm] using hTrans) with ⟨hTy, hNN⟩
      simpa [relTerm] using
        RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b hTy hNN
    · unfold RuleProofs.eo_has_smt_translation at hTrans
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.lt) a b) =
          SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) by rfl]
      have hNN : term_has_non_none_type (SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b)) := by
        unfold term_has_non_none_type
        simpa [relTerm] using hTrans
      rcases arith_binop_ret_bool_args_of_non_none
          (op := SmtTerm.lt) (typeof_lt_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
          with hArgs | hArgs
      · rw [typeof_lt_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
      · rw [typeof_lt_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    · unfold RuleProofs.eo_has_smt_translation at hTrans
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.leq) a b) =
          SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) by rfl]
      have hNN : term_has_non_none_type (SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b)) := by
        unfold term_has_non_none_type
        simpa [relTerm] using hTrans
      rcases arith_binop_ret_bool_args_of_non_none
          (op := SmtTerm.leq) (typeof_leq_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
          with hArgs | hArgs
      · rw [typeof_leq_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
      · rw [typeof_leq_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    · unfold RuleProofs.eo_has_smt_translation at hTrans
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.gt) a b) =
          SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
      have hNN : term_has_non_none_type (SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b)) := by
        unfold term_has_non_none_type
        simpa [relTerm] using hTrans
      rcases arith_binop_ret_bool_args_of_non_none
          (op := SmtTerm.gt) (typeof_gt_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
          with hArgs | hArgs
      · rw [typeof_gt_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
      · rw [typeof_gt_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    · unfold RuleProofs.eo_has_smt_translation at hTrans
      unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.geq) a b) =
          SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
      have hNN : term_has_non_none_type (SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b)) := by
        unfold term_has_non_none_type
        simpa [relTerm] using hTrans
      rcases arith_binop_ret_bool_args_of_non_none
          (op := SmtTerm.geq) (typeof_geq_eq (__eo_to_smt a) (__eo_to_smt b)) hNN
          with hArgs | hArgs
      · rw [typeof_geq_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
      · rw [typeof_geq_eq]
        simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]

theorem arith_rel_args_have_translation
    (r a b : Term) :
    arithRelOp r ->
    RuleProofs.eo_has_smt_translation (relTerm r a b) ->
    RuleProofs.eo_has_smt_translation a ∧
      RuleProofs.eo_has_smt_translation b := by
  intro hRel hTrans
  have hBool := arith_rel_op_has_bool_type_of_translation r a b hRel hTrans
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp [arithRelOp] at hRel
    · simpa [relTerm] using
        CnfSupport.eq_args_have_translation_of_translation a b (by simpa [relTerm] using hTrans)
    · rcases rel_operands_arith_type_of_lt_has_bool_type a b
          (by simpa [relTerm] using hBool) with hArgs | hArgs
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
    · rcases rel_operands_arith_type_of_leq_has_bool_type a b
          (by simpa [relTerm] using hBool) with hArgs | hArgs
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
    · rcases rel_operands_arith_type_of_gt_has_bool_type a b
          (by simpa [relTerm] using hBool) with hArgs | hArgs
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
    · rcases rel_operands_arith_type_of_geq_has_bool_type a b
          (by simpa [relTerm] using hBool) with hArgs | hArgs
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone
      · constructor <;> unfold RuleProofs.eo_has_smt_translation <;>
          intro hNone <;> simp [hArgs.1, hArgs.2] at hNone

theorem arith_atom_denote_real_of_smt_arith_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) ->
    ∃ q : native_Rat, arith_atom_denote_real M t = SmtValue.Rational q := by
  intro hTy
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM t hTy with ⟨n, hEval⟩
    refine ⟨native_to_real n, ?_⟩
    unfold arith_atom_denote_real
    rw [hEval]
    simp [__smtx_model_eval_to_real]
  · rcases smt_eval_real_of_type M hM t hTy with ⟨q, hEval⟩
    refine ⟨q, ?_⟩
    unfold arith_atom_denote_real
    rw [hEval]
    simp [__smtx_model_eval_to_real]

private theorem smt_type_of_eo_arith
    (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    (__eo_typeof t = Term.UOp UserOp.Int ∨ __eo_typeof t = Term.UOp UserOp.Real) ->
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) := by
  intro hTrans hTy
  have hPres :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (__eo_typeof t) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (__eo_typeof t) (__eo_to_smt t) rfl hTrans rfl
  rcases hTy with hTy | hTy
  · left
    simpa [hTy] using hPres
  · right
    simpa [hTy] using hPres

private theorem smt_type_of_eo_int
    (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof t = Term.UOp UserOp.Int ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
  intro hTrans hTy
  have hPres :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (__eo_typeof t) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (__eo_typeof t) (__eo_to_smt t) rfl hTrans rfl
  simpa [hTy] using hPres

private theorem smt_type_of_eo_real
    (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __eo_typeof t = Term.UOp UserOp.Real ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
  intro hTrans hTy
  have hPres :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (__eo_typeof t) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t (__eo_typeof t) (__eo_to_smt t) rfl hTrans rfl
  simpa [hTy] using hPres

private theorem arith_one_denote
    (M : SmtModel) (m : Term) :
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    arith_atom_denote_real M (arithOne m) =
      SmtValue.Rational (native_mk_rational 1 1) := by
  intro hTy
  rcases hTy with hTy | hTy
  · have hToQ :
        __eo_to_q (arithOne m) = Term.Rational (native_mk_rational 1 1) := by
      simp [arithOne, __eo_nil, __eo_nil_mult, __arith_mk_one, hTy,
        __eo_to_q, native_to_real_one]
    exact arith_atom_denote_real_of_to_q M (arithOne m)
      (native_mk_rational 1 1) hToQ
  · have hToQ :
        __eo_to_q (arithOne m) = Term.Rational (native_mk_rational 1 1) := by
      simp [arithOne, __eo_nil, __eo_nil_mult, __arith_mk_one, hTy, __eo_to_q]
    exact arith_atom_denote_real_of_to_q M (arithOne m)
      (native_mk_rational 1 1) hToQ

private theorem arith_zero_denote
    (M : SmtModel) (m : Term) :
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    arith_atom_denote_real M (arithZero m) =
      SmtValue.Rational (native_mk_rational 0 1) := by
  intro hTy
  rcases hTy with hTy | hTy
  · have hToQ :
        __eo_to_q (arithZero m) = Term.Rational (native_mk_rational 0 1) := by
      simp [arithZero, __arith_mk_zero, hTy, __eo_to_q, native_to_real_zero]
    exact arith_atom_denote_real_of_to_q M (arithZero m)
      (native_mk_rational 0 1) hToQ
  · have hToQ :
        __eo_to_q (arithZero m) = Term.Rational (native_mk_rational 0 1) := by
      simp [arithZero, __arith_mk_zero, hTy, __eo_to_q]
    exact arith_atom_denote_real_of_to_q M (arithZero m)
      (native_mk_rational 0 1) hToQ

private theorem typeof_plus_int_int :
    __eo_typeof_plus (Term.UOp UserOp.Int) (Term.UOp UserOp.Int) =
      Term.UOp UserOp.Int := by
  simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type, native_teq,
    native_ite, native_not, SmtEval.native_not]

private theorem typeof_plus_real_real :
    __eo_typeof_plus (Term.UOp UserOp.Real) (Term.UOp UserOp.Real) =
      Term.UOp UserOp.Real := by
  simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type, native_teq,
    native_ite, native_not, SmtEval.native_not]

private theorem typeof_plus_arg_int_of_nonstuck (T : Term) :
    __eo_typeof_plus T (Term.UOp UserOp.Int) ≠ Term.Stuck ->
    T = Term.UOp UserOp.Int := by
  intro h
  cases T <;> simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
    native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
      native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢

private theorem typeof_plus_arg_real_of_nonstuck (T : Term) :
    __eo_typeof_plus T (Term.UOp UserOp.Real) ≠ Term.Stuck ->
    T = Term.UOp UserOp.Real := by
  intro h
  cases T <;> simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
    native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
      native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢

private theorem typeof_plus_left_arith_of_nonstuck (T U : Term) :
    __eo_typeof_plus T U ≠ Term.Stuck ->
    T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real := by
  intro h
  cases T <;> cases U <;>
    simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
      native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢
  case UOp.UOp opT opU =>
    cases opT <;> cases opU <;>
      simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
        native_teq, native_ite, native_not, SmtEval.native_not] at h ⊢

private theorem scale_m_eo_arith_of_scale_not_stuck
    (m x : Term) :
    __eo_typeof (scale m x) ≠ Term.Stuck ->
    __eo_typeof m = Term.UOp UserOp.Int ∨
      __eo_typeof m = Term.UOp UserOp.Real := by
  intro hScale
  change __eo_typeof_plus (__eo_typeof m)
      (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) ≠
    Term.Stuck at hScale
  exact typeof_plus_left_arith_of_nonstuck (__eo_typeof m)
    (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) hScale

private theorem scale_arg_eo_type_of_scale_not_stuck
    (m x : Term) :
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof (scale m x) ≠ Term.Stuck ->
    __eo_typeof x = __eo_typeof m ∧
      __eo_typeof (scale m x) = __eo_typeof m := by
  intro hM hScale
  rcases hM with hM | hM
  · have hOneTy : __eo_typeof (arithOne m) = Term.UOp UserOp.Int := by
      change __eo_typeof (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)) =
        Term.UOp UserOp.Int
      rw [hM]
      rfl
    have hScale' :
        __eo_typeof_plus (Term.UOp UserOp.Int)
            (__eo_typeof_plus (__eo_typeof x) (Term.UOp UserOp.Int)) ≠
          Term.Stuck := by
      change __eo_typeof_plus (__eo_typeof m)
          (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) ≠
        Term.Stuck at hScale
      rw [hM, hOneTy] at hScale
      exact hScale
    have hInner :
        __eo_typeof_plus (__eo_typeof x) (Term.UOp UserOp.Int) ≠ Term.Stuck := by
      intro hInner
      exact hScale' (by rw [hInner]; rfl)
    have hxTy : __eo_typeof x = Term.UOp UserOp.Int :=
      typeof_plus_arg_int_of_nonstuck (__eo_typeof x) hInner
    constructor
    · rw [hxTy, hM]
    · rw [hM]
      change
        __eo_typeof_plus (__eo_typeof m)
          (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) =
        Term.UOp UserOp.Int
      rw [hM, hxTy, hOneTy, typeof_plus_int_int, typeof_plus_int_int]
  · have hOneTy : __eo_typeof (arithOne m) = Term.UOp UserOp.Real := by
      change __eo_typeof (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)) =
        Term.UOp UserOp.Real
      rw [hM]
      rfl
    have hScale' :
        __eo_typeof_plus (Term.UOp UserOp.Real)
            (__eo_typeof_plus (__eo_typeof x) (Term.UOp UserOp.Real)) ≠
          Term.Stuck := by
      change __eo_typeof_plus (__eo_typeof m)
          (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) ≠
        Term.Stuck at hScale
      rw [hM, hOneTy] at hScale
      exact hScale
    have hInner :
        __eo_typeof_plus (__eo_typeof x) (Term.UOp UserOp.Real) ≠ Term.Stuck := by
      intro hInner
      exact hScale' (by rw [hInner]; rfl)
    have hxTy : __eo_typeof x = Term.UOp UserOp.Real :=
      typeof_plus_arg_real_of_nonstuck (__eo_typeof x) hInner
    constructor
    · rw [hxTy, hM]
    · rw [hM]
      change
        __eo_typeof_plus (__eo_typeof m)
          (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) =
        Term.UOp UserOp.Real
      rw [hM, hxTy, hOneTy, typeof_plus_real_real, typeof_plus_real_real]

private theorem scale_smt_type_of_eo_type
    (m x : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation x ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof x = __eo_typeof m ->
    (__smtx_typeof (__eo_to_smt (scale m x)) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (scale m x)) = SmtType.Real) := by
  intro hmTrans hxTrans hM hxTy
  have hmSmt := smt_type_of_eo_arith m hmTrans hM
  have hxSmt : __smtx_typeof (__eo_to_smt x) =
      __smtx_typeof (__eo_to_smt m) := by
    have hmPres :
        __smtx_typeof (__eo_to_smt m) =
          __eo_to_smt_type (__eo_typeof m) :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        m (__eo_typeof m) (__eo_to_smt m) rfl hmTrans rfl
    have hxPres :
        __smtx_typeof (__eo_to_smt x) =
          __eo_to_smt_type (__eo_typeof x) :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        x (__eo_typeof x) (__eo_to_smt x) rfl hxTrans rfl
    rw [hxPres, hmPres, hxTy]
  rcases hM with hM | hM
  · have hmSmtInt : __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
      rcases hmSmt with hmSmt | hmSmt
      · exact hmSmt
      · simpa [hM] using
          (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
            m (__eo_typeof m) (__eo_to_smt m) rfl hmTrans rfl)
    left
    rw [show __eo_to_smt (scale m x) =
        SmtTerm.mult (__eo_to_smt m)
          (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt (arithOne m))) by rfl]
    rw [typeof_mult_eq]
    have hOne : __smtx_typeof (__eo_to_smt (arithOne m)) = SmtType.Int := by
      rw [show arithOne m = Term.Numeral 1 by
        simp [arithOne, __eo_nil, __eo_nil_mult, __arith_mk_one, hM]]
      rw [eo_to_smt_numeral_eq, __smtx_typeof.eq_2]
    have hxSmtInt : __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
      rw [hxSmt, hmSmtInt]
    have hInner :
        __smtx_typeof (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt (arithOne m))) =
          SmtType.Int := by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hxSmtInt, hOne]
    simp [__smtx_typeof_arith_overload_op_2, hmSmtInt, hInner]
  · have hmSmtReal : __smtx_typeof (__eo_to_smt m) = SmtType.Real := by
      rcases hmSmt with hmSmt | hmSmt
      · simpa [hM] using
          (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
            m (__eo_typeof m) (__eo_to_smt m) rfl hmTrans rfl)
      · exact hmSmt
    right
    rw [show __eo_to_smt (scale m x) =
        SmtTerm.mult (__eo_to_smt m)
          (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt (arithOne m))) by rfl]
    rw [typeof_mult_eq]
    have hOne : __smtx_typeof (__eo_to_smt (arithOne m)) = SmtType.Real := by
      rw [show arithOne m = Term.Rational (native_mk_rational 1 1) by
        simp [arithOne, __eo_nil, __eo_nil_mult, __arith_mk_one, hM]]
      rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3]
    have hxSmtReal : __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
      rw [hxSmt, hmSmtReal]
    have hInner :
        __smtx_typeof (SmtTerm.mult (__eo_to_smt x) (__eo_to_smt (arithOne m))) =
          SmtType.Real := by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hxSmtReal, hOne]
    simp [__smtx_typeof_arith_overload_op_2, hmSmtReal, hInner]

private theorem scale_denote
    (M : SmtModel) (hM : model_total_typed M) (m x : Term)
    (qm qx : native_Rat) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation x ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof x = __eo_typeof m ->
    arith_atom_denote_real M m = SmtValue.Rational qm ->
    arith_atom_denote_real M x = SmtValue.Rational qx ->
    arith_atom_denote_real M (scale m x) =
      SmtValue.Rational (native_qmult qm qx) := by
  intro hmTrans hxTrans hMArith hxTy hmDen hxDen
  have hScaleTy :=
    scale_smt_type_of_eo_type m x hmTrans hxTrans hMArith hxTy
  exact arith_atom_denote_real_of_scaled_factor M hM m x (arithOne m) qm qx
    (by simpa [scale] using hScaleTy) hmDen hxDen (arith_one_denote M m hMArith)

private theorem scale_eo_type_of_eo_type
    (m x : Term) :
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof x = __eo_typeof m ->
    __eo_typeof (scale m x) = __eo_typeof m := by
  intro hM hxTy
  rcases hM with hM | hM
  · have hOneTy : __eo_typeof (arithOne m) = Term.UOp UserOp.Int := by
      change __eo_typeof (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)) =
        Term.UOp UserOp.Int
      rw [hM]
      rfl
    rw [hM]
    change
      __eo_typeof_plus (__eo_typeof m)
        (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) =
      Term.UOp UserOp.Int
    rw [hxTy, hM, hOneTy, typeof_plus_int_int, typeof_plus_int_int]
  · have hOneTy : __eo_typeof (arithOne m) = Term.UOp UserOp.Real := by
      change __eo_typeof (__eo_nil (Term.UOp UserOp.mult) (__eo_typeof m)) =
        Term.UOp UserOp.Real
      rw [hM]
      rfl
    rw [hM]
    change
      __eo_typeof_plus (__eo_typeof m)
        (__eo_typeof_plus (__eo_typeof x) (__eo_typeof (arithOne m))) =
      Term.UOp UserOp.Real
    rw [hxTy, hM, hOneTy, typeof_plus_real_real, typeof_plus_real_real]

private theorem scale_smt_type_eq_m
    (m x : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation x ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof x = __eo_typeof m ->
    __smtx_typeof (__eo_to_smt (scale m x)) =
      __smtx_typeof (__eo_to_smt m) := by
  intro hmTrans hxTrans hMArith hxTy
  have hScaleArith :=
    scale_smt_type_of_eo_type m x hmTrans hxTrans hMArith hxTy
  have hScaleTrans : RuleProofs.eo_has_smt_translation (scale m x) := by
    unfold RuleProofs.eo_has_smt_translation
    rcases hScaleArith with hTy | hTy <;> rw [hTy] <;> simp
  have hScalePres :
      __smtx_typeof (__eo_to_smt (scale m x)) =
        __eo_to_smt_type (__eo_typeof (scale m x)) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (scale m x) (__eo_typeof (scale m x)) (__eo_to_smt (scale m x))
      rfl hScaleTrans rfl
  have hmPres :
      __smtx_typeof (__eo_to_smt m) =
        __eo_to_smt_type (__eo_typeof m) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      m (__eo_typeof m) (__eo_to_smt m) rfl hmTrans rfl
  rw [hScalePres, hmPres, scale_eo_type_of_eo_type m x hMArith hxTy]

private theorem pair_smt_type_of_eo_match
    (m a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    ((__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) := by
  intro _hmTrans haTrans hbTrans hMArith haTy hbTy
  rcases hMArith with hMInt | hMReal
  · left
    exact ⟨smt_type_of_eo_int a haTrans (by rw [haTy, hMInt]),
      smt_type_of_eo_int b hbTrans (by rw [hbTy, hMInt])⟩
  · right
    exact ⟨smt_type_of_eo_real a haTrans (by rw [haTy, hMReal]),
      smt_type_of_eo_real b hbTrans (by rw [hbTy, hMReal])⟩

private theorem scale_pair_smt_type
    (m a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    ((__smtx_typeof (__eo_to_smt (scale m a)) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt (scale m b)) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt (scale m a)) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt (scale m b)) = SmtType.Real)) := by
  intro hmTrans haTrans hbTrans hMArith haTy hbTy
  have hScaleA := scale_smt_type_eq_m m a hmTrans haTrans hMArith haTy
  have hScaleB := scale_smt_type_eq_m m b hmTrans hbTrans hMArith hbTy
  rcases hMArith with hMInt | hMReal
  · have hmInt := smt_type_of_eo_int m hmTrans hMInt
    left
    exact ⟨by rw [hScaleA, hmInt], by rw [hScaleB, hmInt]⟩
  · have hmReal := smt_type_of_eo_real m hmTrans hMReal
    right
    exact ⟨by rw [hScaleA, hmReal], by rw [hScaleB, hmReal]⟩

private theorem bool_of_true_eval
    {M : SmtModel} {t : Term} {b : Bool} :
    eo_interprets M t true ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
    b = true := by
  intro hTrue hEval
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue
  cases hTrue with
  | intro_true _ hEvalTrue =>
      rw [hEval] at hEvalTrue
      cases b <;> simp at hEvalTrue ⊢

private theorem eval_lt_of_denotes
    (M : SmtModel) (hM : model_total_typed M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.lt) a b)) =
      SmtValue.Boolean (native_qlt qa qb) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.lt) a b) =
        SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_15, hEvalA, hEvalB]
    simp [__smtx_model_eval_lt, hqa, hqb, native_to_real_lt_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.lt) a b) =
        SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_15, hEvalA, hEvalB]
    simp [__smtx_model_eval_lt, hqa, hqb]

private theorem eval_leq_of_denotes
    (M : SmtModel) (hM : model_total_typed M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.leq) a b)) =
      SmtValue.Boolean (native_qleq qa qb) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.leq) a b) =
        SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_16, hEvalA, hEvalB]
    simp [__smtx_model_eval_leq, hqa, hqb, native_to_real_leq_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.leq) a b) =
        SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_16, hEvalA, hEvalB]
    simp [__smtx_model_eval_leq, hqa, hqb]

private theorem eval_eq_of_denotes
    (M : SmtModel) (hM : model_total_typed M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.eq) a b)) =
      SmtValue.Boolean (native_qeq qa qb) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.eq) a b) =
        SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_134, hEvalA, hEvalB]
    simp [__smtx_model_eval_eq, native_veq, native_zeq, hqa, hqb,
      native_to_real_qeq_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.eq) a b) =
        SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_134, hEvalA, hEvalB]
    simp [__smtx_model_eval_eq, native_veq, native_qeq, hqa, hqb]

private theorem eval_gt_of_denotes
    (M : SmtModel) (hM : model_total_typed M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.gt) a b)) =
      SmtValue.Boolean (native_qlt qb qa) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.gt) a b) =
        SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_17, hEvalA, hEvalB]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, hqa, hqb,
      native_to_real_lt_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.gt) a b) =
        SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_17, hEvalA, hEvalB]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, hqa, hqb]

private theorem eval_geq_of_denotes
    (M : SmtModel) (hM : model_total_typed M) (a b : Term)
    (qa qb : native_Rat)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real))
    (ha : arith_atom_denote_real M a = SmtValue.Rational qa)
    (hb : arith_atom_denote_real M b = SmtValue.Rational qb) :
    __smtx_model_eval M (__eo_to_smt (relTerm (Term.UOp UserOp.geq) a b)) =
      SmtValue.Boolean (native_qleq qb qa) := by
  rcases hTy with hTy | hTy
  · rcases smt_eval_int_of_type M hM a hTy.1 with ⟨na, hEvalA⟩
    rcases smt_eval_int_of_type M hM b hTy.2 with ⟨nb, hEvalB⟩
    have hqa : qa = native_to_real na := by
      have h : SmtValue.Rational qa = SmtValue.Rational (native_to_real na) := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = native_to_real nb := by
      have h : SmtValue.Rational qb = SmtValue.Rational (native_to_real nb) := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.geq) a b) =
        SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_18, hEvalA, hEvalB]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hqa, hqb,
      native_to_real_leq_eq]
  · rcases smt_eval_real_of_type M hM a hTy.1 with ⟨ra, hEvalA⟩
    rcases smt_eval_real_of_type M hM b hTy.2 with ⟨rb, hEvalB⟩
    have hqa : qa = ra := by
      have h : SmtValue.Rational qa = SmtValue.Rational ra := by
        rw [← ha]
        unfold arith_atom_denote_real
        rw [hEvalA]
        simp [__smtx_model_eval_to_real]
      injection h
    have hqb : qb = rb := by
      have h : SmtValue.Rational qb = SmtValue.Rational rb := by
        rw [← hb]
        unfold arith_atom_denote_real
        rw [hEvalB]
        simp [__smtx_model_eval_to_real]
      injection h
    rw [show __eo_to_smt (relTerm (Term.UOp UserOp.geq) a b) =
        SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
    rw [__smtx_model_eval.eq_18, hEvalA, hEvalB]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hqa, hqb]

private theorem rel_bool_of_pair_type
    (r a b : Term) :
    arithRelOp r ->
    ((__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) ->
    RuleProofs.eo_has_bool_type (relTerm r a b) := by
  intro hRel hTy
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp [arithRelOp] at hRel
    · rcases hTy with hTy | hTy
      · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
          (by rw [hTy.1, hTy.2])
          (by rw [hTy.1]; simp)
      · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
          (by rw [hTy.1, hTy.2])
          (by rw [hTy.1]; simp)
    · unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.lt) a b) =
          SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) by rfl]
      rcases hTy with hTy | hTy <;>
        rw [typeof_lt_eq] <;>
        simp [__smtx_typeof_arith_overload_op_2_ret, hTy.1, hTy.2]
    · unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.leq) a b) =
          SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) by rfl]
      rcases hTy with hTy | hTy <;>
        rw [typeof_leq_eq] <;>
        simp [__smtx_typeof_arith_overload_op_2_ret, hTy.1, hTy.2]
    · unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.gt) a b) =
          SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
      rcases hTy with hTy | hTy <;>
        rw [typeof_gt_eq] <;>
        simp [__smtx_typeof_arith_overload_op_2_ret, hTy.1, hTy.2]
    · unfold RuleProofs.eo_has_bool_type
      rw [show __eo_to_smt (relTerm (Term.UOp UserOp.geq) a b) =
          SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
      rcases hTy with hTy | hTy <;>
        rw [typeof_geq_eq] <;>
        simp [__smtx_typeof_arith_overload_op_2_ret, hTy.1, hTy.2]

private theorem sign_pair_smt_type
    (m : Term) :
    RuleProofs.eo_has_smt_translation m ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    ((__smtx_typeof (__eo_to_smt m) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt (arithZero m)) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt m) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt (arithZero m)) = SmtType.Real)) := by
  intro hmTrans hMArith
  rcases hMArith with hMInt | hMReal
  · left
    constructor
    · exact smt_type_of_eo_int m hmTrans hMInt
    · rw [show arithZero m = Term.Numeral 0 by
        simp [arithZero, __arith_mk_zero, hMInt]]
      rw [eo_to_smt_numeral_eq, __smtx_typeof.eq_2]
  · right
    constructor
    · exact smt_type_of_eo_real m hmTrans hMReal
    · rw [show arithZero m = Term.Rational (native_mk_rational 0 1) by
        simp [arithZero, __arith_mk_zero, hMReal]]
      rw [eo_to_smt_rational_eq, __smtx_typeof.eq_3]

private theorem neg_conclusion_bool_of_pair_type
    (r m a b : Term) :
    arithRelOp r ->
    ((__smtx_typeof (__eo_to_smt (scale m a)) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt (scale m b)) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt (scale m a)) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt (scale m b)) = SmtType.Real)) ->
    RuleProofs.eo_has_bool_type (negConclusion r m a b) := by
  intro hRel hTy
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp [arithRelOp] at hRel
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.eq) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.gt) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.geq) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.lt) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy
    · simpa [negConclusion, __arith_rel_inv, relTerm, scale] using
        rel_bool_of_pair_type (Term.UOp UserOp.leq) (scale m a) (scale m b)
          (by simp [arithRelOp]) hTy

private theorem pos_conclusion_true
    (M : SmtModel) (hM : model_total_typed M)
    (m r a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    arithRelOp r ->
    eo_interprets M (relTerm (Term.UOp UserOp.gt) m (arithZero m)) true ->
    eo_interprets M (relTerm r a b) true ->
    eo_interprets M (posConclusion r m a b) true := by
  intro hmTrans haTrans hbTrans hMArith haTy hbTy hRel hSignTrue hFTrue
  have hPair := pair_smt_type_of_eo_match m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hScalePair := scale_pair_smt_type m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hConclBool : RuleProofs.eo_has_bool_type (posConclusion r m a b) := by
    simpa [posConclusion] using
      rel_bool_of_pair_type r (scale m a) (scale m b) hRel hScalePair
  have hmSmtArith := smt_type_of_eo_arith m hmTrans hMArith
  have haSmtArith : __smtx_typeof (__eo_to_smt a) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt a) = SmtType.Real := by
    rcases hPair with hPair | hPair
    · exact Or.inl hPair.1
    · exact Or.inr hPair.1
  have hbSmtArith : __smtx_typeof (__eo_to_smt b) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt b) = SmtType.Real := by
    rcases hPair with hPair | hPair
    · exact Or.inl hPair.2
    · exact Or.inr hPair.2
  rcases arith_atom_denote_real_of_smt_arith_type M hM m hmSmtArith with ⟨qm, hmDen⟩
  rcases arith_atom_denote_real_of_smt_arith_type M hM a haSmtArith with ⟨qa, haDen⟩
  rcases arith_atom_denote_real_of_smt_arith_type M hM b hbSmtArith with ⟨qb, hbDen⟩
  have hScaleADen := scale_denote M hM m a qm qa hmTrans haTrans
    hMArith haTy hmDen haDen
  have hScaleBDen := scale_denote M hM m b qm qb hmTrans hbTrans
    hMArith hbTy hmDen hbDen
  have hSignEval := eval_gt_of_denotes M hM m (arithZero m) qm
    (native_mk_rational 0 1) (sign_pair_smt_type m hmTrans hMArith)
    hmDen (arith_zero_denote M m hMArith)
  have hPos : native_qlt (native_mk_rational 0 1) qm = true :=
    bool_of_true_eval hSignTrue hSignEval
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp [arithRelOp] at hRel
    · have hFEval := eval_eq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qeq qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_eq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by
          simpa [posConclusion, relTerm] using
            (by rw [hEval, native_qeq_mul_congr_left hOrig] : __smtx_model_eval M
              (__eo_to_smt (relTerm (Term.UOp UserOp.eq) (scale m a) (scale m b))) =
                SmtValue.Boolean true))
    · have hFEval := eval_lt_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qlt qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_lt_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qlt_mul_of_pos_left hPos hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by simpa [posConclusion, relTerm, hScaled] using hEval)
    · have hFEval := eval_leq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qleq qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_leq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qleq_mul_of_pos_left hPos hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by simpa [posConclusion, relTerm, hScaled] using hEval)
    · have hFEval := eval_gt_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qlt qb qa = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_gt_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qlt_mul_of_pos_left hPos hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by simpa [posConclusion, relTerm, hScaled] using hEval)
    · have hFEval := eval_geq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qleq qb qa = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_geq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qleq_mul_of_pos_left hPos hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [posConclusion, relTerm] using hConclBool)
        (by simpa [posConclusion, relTerm, hScaled] using hEval)

private theorem neg_conclusion_true
    (M : SmtModel) (hM : model_total_typed M)
    (m r a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    arithRelOp r ->
    eo_interprets M (relTerm (Term.UOp UserOp.lt) m (arithZero m)) true ->
    eo_interprets M (relTerm r a b) true ->
    eo_interprets M (negConclusion r m a b) true := by
  intro hmTrans haTrans hbTrans hMArith haTy hbTy hRel hSignTrue hFTrue
  have hPair := pair_smt_type_of_eo_match m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hScalePair := scale_pair_smt_type m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hConclBool : RuleProofs.eo_has_bool_type (negConclusion r m a b) :=
    neg_conclusion_bool_of_pair_type r m a b hRel hScalePair
  have hmSmtArith := smt_type_of_eo_arith m hmTrans hMArith
  have haSmtArith : __smtx_typeof (__eo_to_smt a) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt a) = SmtType.Real := by
    rcases hPair with hPair | hPair
    · exact Or.inl hPair.1
    · exact Or.inr hPair.1
  have hbSmtArith : __smtx_typeof (__eo_to_smt b) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt b) = SmtType.Real := by
    rcases hPair with hPair | hPair
    · exact Or.inl hPair.2
    · exact Or.inr hPair.2
  rcases arith_atom_denote_real_of_smt_arith_type M hM m hmSmtArith with ⟨qm, hmDen⟩
  rcases arith_atom_denote_real_of_smt_arith_type M hM a haSmtArith with ⟨qa, haDen⟩
  rcases arith_atom_denote_real_of_smt_arith_type M hM b hbSmtArith with ⟨qb, hbDen⟩
  have hScaleADen := scale_denote M hM m a qm qa hmTrans haTrans
    hMArith haTy hmDen haDen
  have hScaleBDen := scale_denote M hM m b qm qb hmTrans hbTrans
    hMArith hbTy hmDen hbDen
  have hSignEval := eval_lt_of_denotes M hM m (arithZero m) qm
    (native_mk_rational 0 1) (sign_pair_smt_type m hmTrans hMArith)
    hmDen (arith_zero_denote M m hMArith)
  have hNeg : native_qlt qm (native_mk_rational 0 1) = true :=
    bool_of_true_eval hSignTrue hSignEval
  cases r <;> simp [arithRelOp] at hRel
  case UOp op =>
    cases op <;> simp [arithRelOp] at hRel
    · have hFEval := eval_eq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qeq qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_eq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hEvalTrue :
          __smtx_model_eval M
            (__eo_to_smt (relTerm (Term.UOp UserOp.eq) (scale m a) (scale m b))) =
              SmtValue.Boolean true := by
        rw [hEval, native_qeq_mul_congr_left hOrig]
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hEvalTrue)
    · have hFEval := eval_lt_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qlt qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_gt_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qlt_mul_of_neg_left hNeg hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale, hScaled] using hEval)
    · have hFEval := eval_leq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qleq qa qb = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_geq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled := native_qleq_mul_of_neg_left hNeg hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale, hScaled] using hEval)
    · have hFEval := eval_gt_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qlt qb qa = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_lt_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled :
          native_qlt (native_qmult qm qa) (native_qmult qm qb) = true :=
        native_qlt_mul_of_neg_left (c := qm) (a := qb) (b := qa) hNeg hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale, hScaled] using hEval)
    · have hFEval := eval_geq_of_denotes M hM a b qa qb hPair haDen hbDen
      have hOrig : native_qleq qb qa = true := bool_of_true_eval hFTrue hFEval
      have hEval := eval_leq_of_denotes M hM (scale m a) (scale m b)
        (native_qmult qm qa) (native_qmult qm qb) hScalePair hScaleADen hScaleBDen
      have hScaled :
          native_qleq (native_qmult qm qa) (native_qmult qm qb) = true :=
        native_qleq_mul_of_neg_left (c := qm) (a := qb) (b := qa) hNeg hOrig
      exact RuleProofs.eo_interprets_of_bool_eval M _ true
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale] using hConclBool)
        (by simpa [negConclusion, __arith_rel_inv, relTerm, scale, hScaled] using hEval)

private theorem and_true_bool
    (F : Term) :
    RuleProofs.eo_has_bool_type F ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (Term.Boolean true)) := by
  intro hF
  exact RuleProofs.eo_has_bool_type_and_of_bool_args F (Term.Boolean true)
    hF RuleProofs.eo_has_bool_type_true

theorem facts_arith_mult_pos
    (M : SmtModel) (hM : model_total_typed M)
    (m r a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation (relTerm r a b) ->
    arithRelOp r ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    __eo_typeof (__eo_prog_arith_mult_pos m (relTerm r a b)) = Term.Bool ->
    eo_interprets M (__eo_prog_arith_mult_pos m (relTerm r a b)) true := by
  intro hmTrans hFTrans hRel hMArith haTy hbTy hResultTy
  have hProgNe :
      __eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck :=
    by simpa [relTerm] using term_ne_stuck_of_typeof_bool hResultTy
  have hProgEq := prog_arith_mult_pos_eq_of_ne_stuck m r a b hProgNe
  have hArgs := arith_rel_args_have_translation r a b hRel hFTrans
  have haTrans := hArgs.1
  have hbTrans := hArgs.2
  have hPair := pair_smt_type_of_eo_match m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hScalePair := scale_pair_smt_type m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hSignBool :
      RuleProofs.eo_has_bool_type
        (relTerm (Term.UOp UserOp.gt) m (arithZero m)) :=
    rel_bool_of_pair_type (Term.UOp UserOp.gt) m (arithZero m)
      (by simp [arithRelOp]) (sign_pair_smt_type m hmTrans hMArith)
  have hFBool : RuleProofs.eo_has_bool_type (relTerm r a b) :=
    rel_bool_of_pair_type r a b hRel hPair
  have hConclBool : RuleProofs.eo_has_bool_type (posConclusion r m a b) := by
    simpa [posConclusion] using
      rel_bool_of_pair_type r (scale m a) (scale m b) hRel hScalePair
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true)) :=
    and_true_bool (relTerm r a b) hFBool
  have hAnteBool :
      RuleProofs.eo_has_bool_type
        (posAntecedent m (relTerm r a b)) := by
    simpa [posAntecedent, relTerm] using
      RuleProofs.eo_has_bool_type_and_of_bool_args
        (relTerm (Term.UOp UserOp.gt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        hSignBool hTailBool
  change eo_interprets M
    (__eo_prog_arith_mult_pos m (Term.Apply (Term.Apply r a) b)) true
  rw [hProgEq]
  rcases CnfSupport.eo_interprets_bool_cases M hM
      (posAntecedent m (relTerm r a b)) hAnteBool with hAnteTrue | hAnteFalse
  · have hSignTrue :
        eo_interprets M (relTerm (Term.UOp UserOp.gt) m (arithZero m)) true :=
      RuleProofs.eo_interprets_and_left M
        (relTerm (Term.UOp UserOp.gt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        (by simpa [posAntecedent, relTerm] using hAnteTrue)
    have hTailTrue :
        eo_interprets M
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
            (Term.Boolean true)) true :=
      RuleProofs.eo_interprets_and_right M
        (relTerm (Term.UOp UserOp.gt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        (by simpa [posAntecedent, relTerm] using hAnteTrue)
    have hFTrue : eo_interprets M (relTerm r a b) true :=
      RuleProofs.eo_interprets_and_left M (relTerm r a b) (Term.Boolean true)
        hTailTrue
    exact CnfSupport.eo_interprets_imp_true_of_right_true M hM
      (posAntecedent m (relTerm r a b)) (posConclusion r m a b)
      hAnteBool
      (pos_conclusion_true M hM m r a b hmTrans haTrans hbTrans
        hMArith haTy hbTy hRel hSignTrue hFTrue)
  · exact CnfSupport.eo_interprets_imp_true_of_left_false M hM
      (posAntecedent m (relTerm r a b)) (posConclusion r m a b)
      hAnteFalse hConclBool

theorem facts_arith_mult_neg
    (M : SmtModel) (hM : model_total_typed M)
    (m r a b : Term) :
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation (relTerm r a b) ->
    arithRelOp r ->
    (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ->
    __eo_typeof a = __eo_typeof m ->
    __eo_typeof b = __eo_typeof m ->
    __eo_typeof (__eo_prog_arith_mult_neg m (relTerm r a b)) = Term.Bool ->
    eo_interprets M (__eo_prog_arith_mult_neg m (relTerm r a b)) true := by
  intro hmTrans hFTrans hRel hMArith haTy hbTy hResultTy
  have hProgNe :
      __eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b) ≠ Term.Stuck :=
    by simpa [relTerm] using term_ne_stuck_of_typeof_bool hResultTy
  have hProgEq := prog_arith_mult_neg_eq_of_ne_stuck m r a b hProgNe
  have hArgs := arith_rel_args_have_translation r a b hRel hFTrans
  have haTrans := hArgs.1
  have hbTrans := hArgs.2
  have hPair := pair_smt_type_of_eo_match m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hScalePair := scale_pair_smt_type m a b hmTrans haTrans hbTrans
    hMArith haTy hbTy
  have hSignBool :
      RuleProofs.eo_has_bool_type
        (relTerm (Term.UOp UserOp.lt) m (arithZero m)) :=
    rel_bool_of_pair_type (Term.UOp UserOp.lt) m (arithZero m)
      (by simp [arithRelOp]) (sign_pair_smt_type m hmTrans hMArith)
  have hFBool : RuleProofs.eo_has_bool_type (relTerm r a b) :=
    rel_bool_of_pair_type r a b hRel hPair
  have hConclBool : RuleProofs.eo_has_bool_type (negConclusion r m a b) :=
    neg_conclusion_bool_of_pair_type r m a b hRel hScalePair
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true)) :=
    and_true_bool (relTerm r a b) hFBool
  have hAnteBool :
      RuleProofs.eo_has_bool_type
        (negAntecedent m (relTerm r a b)) := by
    simpa [negAntecedent, relTerm] using
      RuleProofs.eo_has_bool_type_and_of_bool_args
        (relTerm (Term.UOp UserOp.lt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        hSignBool hTailBool
  change eo_interprets M
    (__eo_prog_arith_mult_neg m (Term.Apply (Term.Apply r a) b)) true
  rw [hProgEq]
  rcases CnfSupport.eo_interprets_bool_cases M hM
      (negAntecedent m (relTerm r a b)) hAnteBool with hAnteTrue | hAnteFalse
  · have hSignTrue :
        eo_interprets M (relTerm (Term.UOp UserOp.lt) m (arithZero m)) true :=
      RuleProofs.eo_interprets_and_left M
        (relTerm (Term.UOp UserOp.lt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        (by simpa [negAntecedent, relTerm] using hAnteTrue)
    have hTailTrue :
        eo_interprets M
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
            (Term.Boolean true)) true :=
      RuleProofs.eo_interprets_and_right M
        (relTerm (Term.UOp UserOp.lt) m (arithZero m))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (relTerm r a b))
          (Term.Boolean true))
        (by simpa [negAntecedent, relTerm] using hAnteTrue)
    have hFTrue : eo_interprets M (relTerm r a b) true :=
      RuleProofs.eo_interprets_and_left M (relTerm r a b) (Term.Boolean true)
        hTailTrue
    exact CnfSupport.eo_interprets_imp_true_of_right_true M hM
      (negAntecedent m (relTerm r a b)) (negConclusion r m a b)
      hAnteBool
      (neg_conclusion_true M hM m r a b hmTrans haTrans hbTrans
        hMArith haTy hbTy hRel hSignTrue hFTrue)
  · exact CnfSupport.eo_interprets_imp_true_of_left_false M hM
      (negAntecedent m (relTerm r a b)) (negConclusion r m a b)
      hAnteFalse hConclBool

theorem arithMultArgTranslationOk_two
    (m F : Term) :
    arithMultArgTranslationOk (CArgList.cons m (CArgList.cons F CArgList.nil)) ->
    ∃ r a b,
      F = relTerm r a b ∧
        eoHasSmtTranslation m ∧
        eoHasSmtTranslation (relTerm r a b) ∧
        arithRelOp r ∧
        (__eo_typeof m = Term.UOp UserOp.Int ∨ __eo_typeof m = Term.UOp UserOp.Real) ∧
        __eo_typeof a = __eo_typeof m ∧
        __eo_typeof b = __eo_typeof m := by
  intro hArgOk
  cases F <;> simp [arithMultArgTranslationOk] at hArgOk
  case Apply f b =>
    cases f <;> simp [arithMultArgTranslationOk] at hArgOk
    case Apply r a =>
      rcases hArgOk with ⟨hmTrans, hFTrans, hRel, hMArith, haTy, hbTy⟩
      exact ⟨r, a, b, rfl, hmTrans, by simpa [relTerm] using hFTrans,
        hRel, hMArith, haTy, hbTy⟩

end ArithMultSupport
