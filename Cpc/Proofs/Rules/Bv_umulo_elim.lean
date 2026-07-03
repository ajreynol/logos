import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

private theorem typeof_extract_bit_of_bv
    (b : Term) (w start : Nat)
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hstart : start < w) :
    __eo_typeof
        (Term.Apply
          (Term.UOp2 UserOp2.extract
            (Term.Numeral (native_nat_to_int start))
            (Term.Numeral (native_nat_to_int start))) b) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  change
    __eo_typeof_extract (Term.UOp UserOp.Int)
      (Term.Numeral (native_nat_to_int start))
      (Term.UOp UserOp.Int)
      (Term.Numeral (native_nat_to_int start))
      (__eo_typeof b) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  rw [hbTy]
  change
    __eo_mk_apply (Term.UOp UserOp.BitVec)
      (__eo_requires
        (__eo_gt (Term.Numeral (native_nat_to_int start))
          (Term.Numeral (-1 : native_Int)))
        (Term.Boolean true)
        (__eo_requires
          (__eo_gt (Term.Numeral (native_nat_to_int w))
            (Term.Numeral (native_nat_to_int start)))
          (Term.Boolean true)
          (__eo_requires
            (__eo_gt
              (__eo_add
                (__eo_add (Term.Numeral (native_nat_to_int start))
                  (__eo_neg (Term.Numeral (native_nat_to_int start))))
                (Term.Numeral 1))
              (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true)
            (__eo_add
              (__eo_add (Term.Numeral (native_nat_to_int start))
                (__eo_neg (Term.Numeral (native_nat_to_int start))))
              (Term.Numeral 1))))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  have hStartNonneg :
      native_zlt (native_nat_to_int start) (-1 : native_Int) = false := by
    simp [native_zlt, native_nat_to_int]
  have hStartGtNeg :
      __eo_gt (Term.Numeral (native_nat_to_int start))
        (Term.Numeral (-1 : native_Int)) = Term.Boolean true := by
    have hs0 : (0 : Int) ≤ (start : Int) := Int.natCast_nonneg start
    have hlt : (-1 : Int) < (start : Int) := by omega
    simp [__eo_gt, native_zlt, native_nat_to_int, hlt]
  have hWStart :
      __eo_gt (Term.Numeral (native_nat_to_int w))
        (Term.Numeral (native_nat_to_int start)) = Term.Boolean true := by
    have hlt : (start : Int) < (w : Int) := by exact_mod_cast hstart
    simp [__eo_gt, native_zlt, native_nat_to_int, hlt]
  have hWidth :
      __eo_add
        (__eo_add (Term.Numeral (native_nat_to_int start))
          (__eo_neg (Term.Numeral (native_nat_to_int start))))
        (Term.Numeral 1) = Term.Numeral 1 := by
    have hEq : (↑start + -↑start + 1 : Int) = 1 := by omega
    simp [__eo_add, __eo_neg, native_zplus, native_zneg, native_nat_to_int, hEq]
  rw [hStartGtNeg, hWStart, hWidth]
  native_decide

private theorem nil_bvand_bit :
    __eo_nil (Term.UOp UserOp.bvand)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) =
      Term.Binary 1 1 := by
  native_decide

private theorem nil_bvor_bit :
    __eo_nil (Term.UOp UserOp.bvor)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) =
      Term.Binary 1 0 := by
  native_decide

private def bv1 (b : Bool) : SmtValue :=
  SmtValue.Binary 1 (if b then (1 : Int) else 0)

private theorem native_int_pow2_nat (k : Nat) :
    native_int_pow2 (native_nat_to_int k) = (2 ^ k : Int) := by
  have hnot : ¬ ((k : Int) < 0) :=
    Int.not_lt_of_ge (Int.natCast_nonneg k)
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, hnot]

private theorem extract_bit_binary_eval
    (w pa : Int) (i : Nat) (hpa0 : 0 <= pa) :
    __smtx_model_eval_extract (SmtValue.Numeral (native_nat_to_int i))
        (SmtValue.Numeral (native_nat_to_int i)) (SmtValue.Binary w pa) =
      bv1 ((Int.toNat pa).testBit i) := by
  simp [__smtx_model_eval_extract, native_binary_extract, native_zplus,
    native_zneg, native_nat_to_int]
  have hWidth : (↑i + 1 + -↑i : Int) = 1 := by omega
  rw [hWidth]
  change SmtValue.Binary 1 (native_mod_total (pa / native_int_pow2 (↑i)) (native_int_pow2 1)) =
    bv1 (pa.toNat.testBit i)
  have hpowi : native_int_pow2 (↑i) = (2 ^ i : Int) := by
    simpa [native_nat_to_int] using native_int_pow2_nat i
  have hpow1 : native_int_pow2 1 = (2 : Int) := by
    native_decide
  rw [hpowi, hpow1]
  have hpa : ((Int.toNat pa : Nat) : Int) = pa := by
    simpa using (Int.toNat_of_nonneg hpa0)
  have hdiv : pa / (2 ^ i : Int) = ((Int.toNat pa / 2 ^ i : Nat) : Int) := by
    rw [← hpa]
    exact (Int.natCast_ediv (Int.toNat pa) (2 ^ i)).symm
  have hmod : native_mod_total (pa / (2 ^ i : Int)) 2 =
      ((Int.toNat pa / 2 ^ i % 2 : Nat) : Int) := by
    unfold native_mod_total
    rw [hdiv]
    exact (Int.natCast_emod (Int.toNat pa / 2 ^ i) 2).symm
  rw [hmod]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hbit : (Int.toNat pa / 2 ^ i % 2 = 1)
  · simp [bv1, hbit]
  · have hzero : Int.toNat pa / 2 ^ i % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (Int.toNat pa / 2 ^ i) with h0 | h1
      · exact h0
      · exact False.elim (hbit h1)
    simp [bv1, hbit, hzero]

private theorem bv1_and (x y : Bool) :
    __smtx_model_eval_bvand (bv1 x) (bv1 y) = bv1 (x && y) := by
  cases x <;> cases y <;> native_decide

private theorem bv1_or (x y : Bool) :
    __smtx_model_eval_bvor (bv1 x) (bv1 y) = bv1 (x || y) := by
  cases x <;> cases y <;> native_decide

private theorem bv1_eq_one (x : Bool) :
    __smtx_model_eval_eq (bv1 x) (SmtValue.Binary 1 1) = SmtValue.Boolean x := by
  cases x <;> simp [bv1, __smtx_model_eval_eq, native_veq]

private theorem smtx_eval_bvand_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvand x y) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvor x y) =
      __smtx_model_eval_bvor
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.concat x y) =
      __smtx_model_eval_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvmul_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvmul x y) =
      __smtx_model_eval_bvmul
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvumulo_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvumulo x y) =
      __smtx_model_eval_bvumulo
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem native_mod_nat_of_lt {n m : Nat} (_hm : 0 < m) (h : n < m) :
    native_mod_total (n : Int) (m : Int) = (n : Int) := by
  unfold native_mod_total
  exact Int.emod_eq_of_lt (Int.natCast_nonneg n) (by exact_mod_cast h)

private theorem concat_zero_right_value
    (w A : Nat) (haBound : A < 2 ^ w) :
    __smtx_model_eval_concat
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      (SmtValue.Binary 0 0) =
    SmtValue.Binary (native_nat_to_int w) (A : Int) := by
  change
    SmtValue.Binary (native_zplus (native_nat_to_int w) 0)
      (native_mod_total
        (native_binary_concat (native_nat_to_int w) (A : Int) 0 0)
        (native_int_pow2 (native_zplus (native_nat_to_int w) 0))) =
    SmtValue.Binary (native_nat_to_int w) (A : Int)
  have hWidth : native_zplus (native_nat_to_int w) 0 = native_nat_to_int w := by
    simp [native_zplus, native_nat_to_int]
  rw [hWidth]
  unfold native_binary_concat
  simp [native_zplus, native_zmult]
  have hpow0 : native_int_pow2 0 = (1 : Int) := by native_decide
  rw [hpow0]
  simp
  have hmod :
      native_mod_total (A : Int) (native_int_pow2 (native_nat_to_int w)) =
        (A : Int) := by
    rw [native_int_pow2_nat w]
    exact native_mod_nat_of_lt (Nat.two_pow_pos w) haBound
  rw [hmod]

private theorem concat_zero_left_value
    (w A : Nat) (haBound : A < 2 ^ w) :
    __smtx_model_eval_concat
      (SmtValue.Binary 1 0)
      (SmtValue.Binary (native_nat_to_int w) (A : Int)) =
    SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) := by
  change
    SmtValue.Binary (native_zplus 1 (native_nat_to_int w))
      (native_mod_total
        (native_binary_concat 1 0 (native_nat_to_int w) (A : Int))
        (native_int_pow2 (native_zplus 1 (native_nat_to_int w)))) =
    SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int)
  have hWidth : native_zplus 1 (native_nat_to_int w) = native_nat_to_int (w + 1) := by
    have hEq : (1 : Int) + (w : Int) = ((w + 1 : Nat) : Int) := by omega
    simpa [native_zplus, native_nat_to_int] using hEq
  rw [hWidth]
  unfold native_binary_concat
  simp [native_zplus, native_zmult]
  have hAHi : A < 2 ^ (w + 1) := by
    have hle : 2 ^ w ≤ 2 ^ (w + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact Nat.lt_of_lt_of_le haBound hle
  have hmod :
      native_mod_total (A : Int) (native_int_pow2 (native_nat_to_int (w + 1))) =
        (A : Int) := by
    rw [native_int_pow2_nat (w + 1)]
    exact native_mod_nat_of_lt (Nat.two_pow_pos (w + 1)) hAHi
  rw [hmod]

private theorem eval_extract_bit_term
    (M : SmtModel) (t : Term) (w payload : Int) (i : Nat)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary w payload)
    (hPayload0 : 0 ≤ payload) :
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.UOp2 UserOp2.extract
            (Term.Numeral (native_nat_to_int i))
            (Term.Numeral (native_nat_to_int i))) t)) =
      bv1 (payload.toNat.testBit i) := by
  show __smtx_model_eval M
      (SmtTerm.extract (SmtTerm.Numeral (native_nat_to_int i))
        (SmtTerm.Numeral (native_nat_to_int i)) (__eo_to_smt t)) =
      bv1 (payload.toNat.testBit i)
  rw [smtx_eval_extract_term_eq, hEval]
  simp [__smtx_model_eval]
  exact extract_bit_binary_eval w payload i hPayload0

private theorem eval_bvand_term
    (M : SmtModel) (x y : Term) (bx byv : Bool)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bv1 bx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = bv1 byv) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y)) =
      bv1 (bx && byv) := by
  show __smtx_model_eval M (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y)) =
      bv1 (bx && byv)
  rw [smtx_eval_bvand_term_eq]
  rw [hx, hy]
  exact bv1_and bx byv

private theorem eval_bvor_term
    (M : SmtModel) (x y : Term) (bx byv : Bool)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bv1 bx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = bv1 byv) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x) y)) =
      bv1 (bx || byv) := by
  show __smtx_model_eval M (SmtTerm.bvor (__eo_to_smt x) (__eo_to_smt y)) =
      bv1 (bx || byv)
  rw [smtx_eval_bvor_term_eq]
  rw [hx, hy]
  exact bv1_or bx byv

private theorem eval_concat_term
    (M : SmtModel) (x y : Term) (vx vy : SmtValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = vx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = vy) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y)) =
      __smtx_model_eval_concat vx vy := by
  show __smtx_model_eval M (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_concat vx vy
  rw [smtx_eval_concat_term_eq]
  rw [hx, hy]

private theorem eval_bvmul_term
    (M : SmtModel) (x y : Term) (vx vy : SmtValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = vx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = vy) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) y)) =
      __smtx_model_eval_bvmul vx vy := by
  show __smtx_model_eval M (SmtTerm.bvmul (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_bvmul vx vy
  rw [smtx_eval_bvmul_term_eq]
  rw [hx, hy]

private theorem eval_bvumulo_term
    (M : SmtModel) (x y : Term) (vx vy : SmtValue)
    (hx : __smtx_model_eval M (__eo_to_smt x) = vx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = vy) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) x) y)) =
      __smtx_model_eval_bvumulo vx vy := by
  show __smtx_model_eval M (SmtTerm.bvumulo (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_bvumulo vx vy
  rw [smtx_eval_bvumulo_term_eq]
  rw [hx, hy]

private theorem eval_zero_extend_one_term
    (M : SmtModel) (a : Term) (w A : Nat)
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (haBound : A < 2 ^ w) :
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.concat) (Term.Binary 1 0))
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a)
            (Term.Binary 0 0)))) =
      SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) := by
  have hZero0 : __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
      SmtValue.Binary 0 0 := by
    change __smtx_model_eval M (SmtTerm.Binary 0 0) = SmtValue.Binary 0 0
    simp only [__smtx_model_eval]
  have hInner :=
    eval_concat_term M a (Term.Binary 0 0)
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      (SmtValue.Binary 0 0) haEval hZero0
  have hInner' :
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a)
            (Term.Binary 0 0))) =
        SmtValue.Binary (native_nat_to_int w) (A : Int) := by
    rw [hInner]
    exact concat_zero_right_value w A haBound
  have hZero1 : __smtx_model_eval M (__eo_to_smt (Term.Binary 1 0)) =
      SmtValue.Binary 1 0 := by
    change __smtx_model_eval M (SmtTerm.Binary 1 0) = SmtValue.Binary 1 0
    simp only [__smtx_model_eval]
  have hOuter :=
    eval_concat_term M (Term.Binary 1 0)
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a)
        (Term.Binary 0 0))
      (SmtValue.Binary 1 0)
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      hZero1 hInner'
  rw [hOuter]
  exact concat_zero_left_value w A haBound

private def zeroExtendOneTerm (a : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat) (Term.Binary 1 0))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) (Term.Binary 0 0))

private theorem typeof_zero_extend_one_term
    (a : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    __eo_typeof (zeroExtendOneTerm a) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1))) := by
  dsimp [zeroExtendOneTerm]
  change
    __eo_typeof_concat (__eo_typeof (Term.Binary 1 0))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a)
          (Term.Binary 0 0))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  change
    __eo_typeof_concat
      (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_len (Term.Binary 1 0)))
      (__eo_typeof_concat (__eo_typeof a) (__eo_typeof (Term.Binary 0 0))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  rw [haTy]
  change
    __eo_typeof_concat
      (__eo_mk_apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
      (__eo_typeof_concat
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)))
        (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_len (Term.Binary 0 0)))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  change
    __eo_typeof_concat
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
      (__eo_typeof_concat
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)))
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  change
    __eo_mk_apply (Term.UOp UserOp.BitVec)
      (__eo_add (Term.Numeral 1)
        (__eo_add (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int (w + 1)))
  have hAddInner :
      __eo_add (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Numeral (native_nat_to_int w) := by
    simp [__eo_add, native_zplus, native_nat_to_int]
  have hAddOuter :
      __eo_add (Term.Numeral 1) (Term.Numeral (native_nat_to_int w)) =
        Term.Numeral (native_nat_to_int (w + 1)) := by
    have hEq : (1 : Int) + (w : Int) = ((w + 1 : Nat) : Int) := by omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  rw [hAddInner, hAddOuter]
  rfl

private theorem typeof_bvmul_same_bitvec
    (x y : Term) (w : Nat)
    (hxTy : __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hyTy : __eo_typeof y =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) x) y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  change __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  rw [hxTy, hyTy]
  change
    __eo_requires
      (__eo_eq (Term.Numeral (native_nat_to_int w))
        (Term.Numeral (native_nat_to_int w)))
      (Term.Boolean true)
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
  simp [__eo_eq, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem typeof_binary_bitvec_nat
    (w : Nat) (n : Int) :
    __eo_typeof (Term.Binary (native_nat_to_int w) n) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  change __eo_mk_apply (Term.UOp UserOp.BitVec)
      (__eo_len (Term.Binary (native_nat_to_int w) n)) =
    Term.Apply (Term.UOp UserOp.BitVec)
      (Term.Numeral (native_nat_to_int w))
  rfl

private theorem eval_eq_bv1_one_term
    (M : SmtModel) (x : Term) (bx : Bool)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bv1 bx) :
    __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
        (Term.Binary 1 1))) =
      SmtValue.Boolean bx := by
  show __smtx_model_eval M
      (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1)) =
      SmtValue.Boolean bx
  rw [smtx_eval_eq_term_eq, hx]
  simp [__smtx_model_eval]
  exact bv1_eq_one bx

private theorem bvmul_high_bit_value (w A B : Nat) :
    __smtx_model_eval_extract
      (SmtValue.Numeral (native_nat_to_int w))
      (SmtValue.Numeral (native_nat_to_int w))
      (__smtx_model_eval_bvmul
        (SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int))
        (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))) =
    bv1 ((A * B).testBit w) := by
  have hpow : native_int_pow2 (native_nat_to_int (w + 1)) =
      (2 ^ (w + 1) : Int) := native_int_pow2_nat (w + 1)
  have hmulPayload :
      native_mod_total (native_zmult (A : Int) (B : Int))
          (native_int_pow2 (native_nat_to_int (w + 1))) =
        ((A * B) % 2 ^ (w + 1) : Nat) := by
    unfold native_mod_total native_zmult
    change ((A : Int) * (B : Int)) %
        native_int_pow2 (native_nat_to_int (w + 1)) =
      ((A * B) % 2 ^ (w + 1) : Nat)
    rw [hpow]
    have hcastMul : ((A : Int) * (B : Int)) = ((A * B : Nat) : Int) := by
      norm_cast
    rw [hcastMul]
    exact (Int.natCast_emod (A * B) (2 ^ (w + 1))).symm
  change
    __smtx_model_eval_extract (SmtValue.Numeral (native_nat_to_int w))
      (SmtValue.Numeral (native_nat_to_int w))
      (SmtValue.Binary (native_nat_to_int (w + 1))
        (native_mod_total (native_zmult (A : Int) (B : Int))
          (native_int_pow2 (native_nat_to_int (w + 1))))) =
    bv1 ((A * B).testBit w)
  rw [hmulPayload]
  rw [extract_bit_binary_eval (native_nat_to_int (w + 1))
    (((A * B) % 2 ^ (w + 1) : Nat) : Int) w (Int.natCast_nonneg _)]
  congr 1
  rw [Int.toNat_natCast]
  have htb := Nat.testBit_mod_two_pow (A * B) (w + 1) w
  simpa using htb

private theorem bvmul_one_right_value
    (w B : Nat) (hbBound : B < 2 ^ w) :
    __smtx_model_eval_bvmul
      (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))
      (SmtValue.Binary (native_nat_to_int (w + 1)) 1) =
    SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int) := by
  change
    SmtValue.Binary (native_nat_to_int (w + 1))
      (native_mod_total (native_zmult (B : Int) 1)
        (native_int_pow2 (native_nat_to_int (w + 1)))) =
    SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int)
  simp [native_zmult]
  have hbHi : B < 2 ^ (w + 1) := by
    have hle : 2 ^ w ≤ 2 ^ (w + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    exact Nat.lt_of_lt_of_le hbBound hle
  have hmod :
      native_mod_total (B : Int) (native_int_pow2 (native_nat_to_int (w + 1))) =
        (B : Int) := by
    rw [native_int_pow2_nat (w + 1)]
    exact native_mod_nat_of_lt (Nat.two_pow_pos (w + 1)) hbHi
  rw [hmod]

private theorem bvumulo_value (w A B : Nat) :
    __smtx_model_eval_bvumulo
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      (SmtValue.Binary (native_nat_to_int w) (B : Int)) =
    SmtValue.Boolean (decide (2 ^ w ≤ A * B)) := by
  change
    SmtValue.Boolean
      (native_zleq (native_int_pow2 (native_nat_to_int w))
        (native_zmult (A : Int) (B : Int))) =
    SmtValue.Boolean (decide (2 ^ w ≤ A * B))
  congr 1
  rw [native_int_pow2_nat w]
  change decide ((2 ^ w : Int) ≤ (A : Int) * (B : Int)) =
    decide (2 ^ w ≤ A * B)
  have hMul : (A : Int) * (B : Int) = ((A * B : Nat) : Int) := by
    norm_cast
  rw [hMul]
  have hiff :
      ((2 ^ w : Int) ≤ ((A * B : Nat) : Int)) ↔ 2 ^ w ≤ A * B := by
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  by_cases h : 2 ^ w ≤ A * B
  · have hI : (2 ^ w : Int) ≤ ((A * B : Nat) : Int) := hiff.2 h
    rw [decide_eq_true hI, decide_eq_true h]
  · have hI : ¬ (2 ^ w : Int) ≤ ((A * B : Nat) : Int) := by
      intro hi
      exact h (hiff.1 hi)
    rw [decide_eq_false hI, decide_eq_false h]

private theorem nil_bvmul_bitvec_succ_of_ne_stuck
    (w : Nat)
    (hNe :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int (w + 1)))) ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvmul)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1)))) =
      Term.Binary (native_nat_to_int (w + 1)) 1 := by
  change __eo_to_bin (Term.Numeral (native_nat_to_int (w + 1))) (Term.Numeral 1) =
      Term.Binary (native_nat_to_int (w + 1)) 1
  change
    (native_ite (native_zleq (native_nat_to_int (w + 1)) 4294967296)
        (__eo_mk_binary (native_nat_to_int (w + 1)) 1) Term.Stuck) =
      Term.Binary (native_nat_to_int (w + 1)) 1
  cases hBound : native_zleq (native_nat_to_int (w + 1)) 4294967296
  · exfalso
    apply hNe
    change
      native_ite (native_zleq (native_nat_to_int (w + 1)) 4294967296)
          (__eo_mk_binary (native_nat_to_int (w + 1)) 1) Term.Stuck =
        Term.Stuck
    rw [hBound]
    rfl
  · simp [native_ite, hBound]
    have hNonneg : native_zleq 0 (native_nat_to_int (w + 1)) = true := by
      have h : (0 : Int) ≤ ((w + 1 : Nat) : Int) :=
        Int.natCast_nonneg (w + 1)
      simpa [native_zleq, native_nat_to_int] using h
    simp [__eo_mk_binary, native_ite, hNonneg]
    have hmod : native_mod_total (1 : native_Int)
        (native_int_pow2 (native_nat_to_int (w + 1))) = 1 := by
      unfold native_mod_total
      have hpowGt1 : (1 : Int) < native_int_pow2 (native_nat_to_int (w + 1)) := by
        rw [native_int_pow2_nat (w + 1)]
        have hle : 2 ^ 1 ≤ 2 ^ (w + 1) :=
          Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        exact_mod_cast hle
      exact Int.emod_eq_of_lt (by decide) hpowGt1
    rw [hmod]

private theorem term_apply_ne_stuck0 (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

private theorem eo_mk_apply_of_ne_stuck0
    {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private def intRangeList : Nat -> Nat -> Term
  | _start, 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int)
  | start, Nat.succ len =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral (native_nat_to_int start)))
        (intRangeList (start + 1) len)

private def intZeroList : Nat -> Term
  | 0 =>
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int)
  | Nat.succ k =>
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0))
        (intZeroList k)

private theorem intZeroList_ne_stuck :
    ∀ k : Nat, intZeroList k ≠ Term.Stuck := by
  intro k
  induction k with
  | zero =>
      intro h
      cases h
  | succ k ih =>
      intro h
      cases h

private theorem intRangeList_ne_stuck :
    ∀ start len : Nat, intRangeList start len ≠ Term.Stuck := by
  intro start len
  induction len generalizing start with
  | zero =>
      intro h
      cases h
  | succ len ih =>
      intro h
      cases h

private theorem intZeroList_repeat_rec_eq :
    ∀ k : Nat,
      __eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0) k =
        intZeroList k := by
  intro k
  induction k with
  | zero =>
      change
        __eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
            (__eo_typeof (Term.Numeral 0)) =
          intZeroList 0
      rfl
  | succ k ih =>
      change
        __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0))
            (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0) k) =
          intZeroList (Nat.succ k)
      rw [ih]
      exact eo_mk_apply_of_ne_stuck0 (term_apply_ne_stuck0 _ _)
        (intZeroList_ne_stuck k)

private theorem iota_rec_range_eq :
    ∀ len start : Nat,
      __iota_rec (intZeroList len) (Term.Numeral (native_nat_to_int start)) =
        intRangeList start len := by
  intro len
  induction len with
  | zero =>
      intro start
      rfl
  | succ len ih =>
      intro start
      change
        __eo_mk_apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
            (Term.Numeral (native_nat_to_int start)))
          (__iota_rec (intZeroList len)
            (__eo_add (Term.Numeral (native_nat_to_int start))
              (Term.Numeral 1))) =
        intRangeList start (Nat.succ len)
      have hAdd :
          __eo_add (Term.Numeral (native_nat_to_int start)) (Term.Numeral 1) =
            Term.Numeral (native_nat_to_int (start + 1)) := by
        simp [__eo_add, native_zplus, native_nat_to_int]
      rw [hAdd, ih (start + 1)]
      exact eo_mk_apply_of_ne_stuck0 (term_apply_ne_stuck0 _ _)
        (intRangeList_ne_stuck (start + 1) len)

private def scanRec (w a b : Nat) : Nat -> Nat -> Bool -> Bool -> Bool
  | _start, 0, _uppc, res => res
  | start, len + 1, uppc, res =>
      (b.testBit start && uppc) ||
        scanRec w a b (start + 1) len
          (a.testBit (w - 1 - start) || uppc) res

private def highPair (w a b : Nat) : Prop :=
  ∃ i : Nat, 1 ≤ i ∧ i < w ∧ b.testBit i = true ∧ 2 ^ (w - i) ≤ a

private theorem pow_two_mul (a b : Nat) : 2 ^ a * 2 ^ b = 2 ^ (a + b) := by
  rw [← Nat.pow_add]

private theorem highPair_overflow {w a b : Nat}
    (h : highPair w a b) : 2 ^ w ≤ a * b := by
  rcases h with ⟨i, h1, hiw, hbit, ha⟩
  have hb : 2 ^ i ≤ b := Nat.ge_two_pow_of_testBit hbit
  have hmul : 2 ^ (w - i) * 2 ^ i ≤ a * b := Nat.mul_le_mul ha hb
  have hsum : w - i + i = w := by omega
  have hp : 2 ^ (w - i) * 2 ^ i = 2 ^ w := by
    rw [pow_two_mul, hsum]
  simpa [hp] using hmul

private theorem bit_w_of_range {w n : Nat}
    (hlo : 2 ^ w ≤ n) (hhi : n < 2 ^ (w + 1)) : n.testBit w = true := by
  exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hlo hhi

private theorem large_product_highPair {w a b : Nat}
    (haBound : a < 2 ^ w) (hbBound : b < 2 ^ w)
    (hLarge : 2 ^ (w + 1) ≤ a * b) : highPair w a b := by
  have hbNe : b ≠ 0 := by
    intro hb0
    subst b
    simp at hLarge
  let i := b.log2
  have hbLog := (Nat.log2_eq_iff (n := b) (k := i) hbNe).mp rfl
  have hbLow : 2 ^ i ≤ b := hbLog.1
  have hbHigh : b < 2 ^ (i + 1) := hbLog.2
  have hiw : i < w := by
    have hlogLt : b.log2 < w := (Nat.log2_lt hbNe).mpr hbBound
    simpa [i] using hlogLt
  have hi1 : 1 ≤ i := by
    apply Decidable.by_contra
    intro hnot
    have hi0 : i = 0 := by omega
    have hbLt2 : b < 2 := by
      simpa [hi0] using hbHigh
    have hbPos : 0 < b := Nat.pos_of_ne_zero hbNe
    have hbEq1 : b = 1 := by omega
    have hprod : a * b = a := by simp [hbEq1]
    have h2w_le : 2 ^ w ≤ 2 ^ (w + 1) := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hlt : a * b < 2 ^ (w + 1) := by
      rw [hprod]
      exact Nat.lt_of_lt_of_le haBound h2w_le
    exact Nat.not_le_of_gt hlt hLarge
  have haNeed : 2 ^ (w - i) ≤ a := by
    apply Decidable.by_contra
    intro hnot
    have haLt : a < 2 ^ (w - i) := Nat.lt_of_not_le hnot
    have hbPos : 0 < b := Nat.pos_of_ne_zero hbNe
    have hpowPos : 0 < 2 ^ (w - i) := Nat.two_pow_pos _
    have h1 : a * b < 2 ^ (w - i) * b :=
      Nat.mul_lt_mul_of_pos_right haLt hbPos
    have h2 : 2 ^ (w - i) * b < 2 ^ (w - i) * 2 ^ (i + 1) :=
      Nat.mul_lt_mul_of_pos_left hbHigh hpowPos
    have hltMul : a * b < 2 ^ (w - i) * 2 ^ (i + 1) := Nat.lt_trans h1 h2
    have hsum : w - i + (i + 1) = w + 1 := by omega
    have hp : 2 ^ (w - i) * 2 ^ (i + 1) = 2 ^ (w + 1) := by
      rw [pow_two_mul, hsum]
    rw [hp] at hltMul
    exact Nat.not_le_of_gt hltMul hLarge
  exact ⟨i, hi1, hiw, Nat.testBit_log2 hbNe, haNeed⟩

private theorem bit_or_highPair_of_overflow {w a b : Nat}
    (haBound : a < 2 ^ w) (hbBound : b < 2 ^ w)
    (hov : 2 ^ w ≤ a * b) :
    (a * b).testBit w = true ∨ highPair w a b := by
  by_cases hbit : (a * b).testBit w = true
  · exact Or.inl hbit
  · right
    have hLarge : 2 ^ (w + 1) ≤ a * b := by
      apply Decidable.by_contra
      intro hnot
      have hlt : a * b < 2 ^ (w + 1) := Nat.lt_of_not_le hnot
      have htrue : (a * b).testBit w = true := bit_w_of_range hov hlt
      exact hbit htrue
    exact large_product_highPair haBound hbBound hLarge

private theorem bit_or_highPair_iff_overflow {w a b : Nat}
    (haBound : a < 2 ^ w) (hbBound : b < 2 ^ w) :
    ((a * b).testBit w = true ∨ highPair w a b) ↔ 2 ^ w ≤ a * b := by
  constructor
  · intro h
    cases h with
    | inl hbit => exact Nat.ge_two_pow_of_testBit hbit
    | inr hp => exact highPair_overflow hp
  · exact bit_or_highPair_of_overflow haBound hbBound

private def scanPair (w a b : Nat) : Nat -> Nat -> Bool -> Bool
  | _start, 0, _uppc => false
  | start, len + 1, uppc =>
      (b.testBit start && uppc) ||
        scanPair w a b (start + 1) len (a.testBit (w - 1 - start) || uppc)

private theorem uppc_step (a k : Nat) :
    (a.testBit k || decide (2 ^ (k + 1) ≤ a)) = decide (2 ^ k ≤ a) := by
  by_cases hlow : 2 ^ k ≤ a
  · have hr : decide (2 ^ k ≤ a) = true := by simp [hlow]
    by_cases hbit : a.testBit k = true
    · simp [hbit, hr]
    · have hhi : 2 ^ (k + 1) ≤ a := by
        apply Decidable.by_contra
        intro hnot
        have hlt : a < 2 ^ (k + 1) := Nat.lt_of_not_le hnot
        have htrue : a.testBit k = true :=
          Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hlow hlt
        exact hbit htrue
      simp [hbit, hhi, hr]
  · have hr : decide (2 ^ k ≤ a) = false := by simp [hlow]
    have hbit : a.testBit k = false := by
      by_cases h : a.testBit k = true
      · have hle := Nat.ge_two_pow_of_testBit h
        exact False.elim (hlow hle)
      · exact Bool.eq_false_iff.2 h
    have hhiNot : ¬ 2 ^ (k + 1) ≤ a := by
      intro hhi
      have hlePow : 2 ^ k ≤ 2 ^ (k + 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      exact hlow (Nat.le_trans hlePow hhi)
    simp [hbit, hhiNot, hr]

private theorem scanPair_iff_highPair_aux (w a b : Nat) :
    ∀ start len : Nat,
      start + len = w ->
      (scanPair w a b start len (decide (2 ^ (w - start) ≤ a)) = true ↔
        ∃ i : Nat, start ≤ i ∧ i < w ∧ b.testBit i = true ∧ 2 ^ (w - i) ≤ a) := by
  intro start len
  induction len generalizing start with
  | zero =>
      intro hsum
      constructor
      · intro h
        simp [scanPair] at h
      · intro h
        rcases h with ⟨i, hsi, hiw, _⟩
        omega
  | succ len ih =>
      intro hsum
      simp [scanPair]
      have hws : w - start = w - 1 - start + 1 := by omega
      rw [hws]
      rw [uppc_step a (w - 1 - start)]
      have hpowIdx : w - (start + 1) = w - 1 - start := by omega
      rw [← hpowIdx]
      have htail := ih (start + 1) (by omega)
      rw [htail]
      constructor
      · intro h
        cases h with
        | inl hhead =>
            exact ⟨start, by omega, by omega, hhead.1, by
              simpa [hws, hpowIdx] using hhead.2⟩
        | inr htailEx =>
            rcases htailEx with ⟨i, hsi, hiw, hbi, hai⟩
            exact ⟨i, by omega, hiw, hbi, hai⟩
      · intro h
        rcases h with ⟨i, hsi, hiw, hbi, hai⟩
        by_cases his : i = start
        · subst i
          left
          exact ⟨hbi, by simpa [hws, hpowIdx] using hai⟩
        · right
          exact ⟨i, by omega, hiw, hbi, hai⟩

private theorem scanPair_iff_highPair {w a b : Nat}
    (hw : 1 ≤ w) (haBound : a < 2 ^ w) :
    scanPair w a b 1 (w - 1) (a.testBit (w - 1)) = true ↔ highPair w a b := by
  have hinit : a.testBit (w - 1) = decide (2 ^ (w - 1) ≤ a) := by
    have hk : w - 1 + 1 = w := Nat.sub_add_cancel hw
    rw [← uppc_step a (w - 1)]
    have htooHigh : ¬ 2 ^ ((w - 1) + 1) ≤ a := by
      intro h
      rw [hk] at h
      exact Nat.not_le_of_gt haBound h
    simp [htooHigh]
  rw [hinit]
  have hsum : 1 + (w - 1) = w := by omega
  have haux := scanPair_iff_highPair_aux w a b 1 (w - 1) hsum
  simpa [highPair] using haux

private theorem scanRec_eq_or_scanPair (w a b start len : Nat)
    (up rs : Bool) :
    scanRec w a b start len up rs = (rs || scanPair w a b start len up) := by
  induction len generalizing start up with
  | zero =>
      simp [scanRec, scanPair]
  | succ len ih =>
      simp [scanRec, scanPair, ih]
      let tail :=
        scanPair w a b (start + 1) len
          (a.testBit (w - 1 - start) || up)
      cases b.testBit start <;> cases up <;> cases rs <;> cases tail <;> rfl

private theorem scanRec_iff_overflow {w a b : Nat}
    (hw : 1 ≤ w) (haBound : a < 2 ^ w) (hbBound : b < 2 ^ w) :
    scanRec w a b 1 (w - 1) (a.testBit (w - 1)) ((a * b).testBit w) = true ↔
      2 ^ w ≤ a * b := by
  rw [scanRec_eq_or_scanPair]
  constructor
  · intro h
    have hor : (a * b).testBit w = true ∨
        scanPair w a b 1 (w - 1) (a.testBit (w - 1)) = true := by
      simpa using h
    exact (bit_or_highPair_iff_overflow haBound hbBound).1 <|
      hor.imp id (fun hscan => (scanPair_iff_highPair hw haBound).1 hscan)
  · intro hov
    have hor := (bit_or_highPair_iff_overflow haBound hbBound).2 hov
    cases hor with
    | inl hbit =>
        simp [hbit]
    | inr hp =>
        have hscan := (scanPair_iff_highPair hw haBound).2 hp
        simp [hscan]

private theorem term_apply_ne_stuck (f x : Term) :
    Term.Apply f x ≠ Term.Stuck := by
  intro h
  cases h

private theorem term_uop_ne_stuck (op : UserOp) :
    Term.UOp op ≠ Term.Stuck := by
  intro h
  cases h

private theorem term_binary_ne_stuck (w n : Int) :
    Term.Binary w n ≠ Term.Stuck := by
  intro h
  cases h

private theorem term_numeral_ne_stuck (n : Int) :
    Term.Numeral n ≠ Term.Stuck := by
  intro h
  cases h

private theorem eo_to_smt_stuck :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rfl

private theorem eval_stuck (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt Term.Stuck) = SmtValue.NotValue := by
  rw [eo_to_smt_stuck]
  change __smtx_model_eval M SmtTerm.None = SmtValue.NotValue
  simp only [__smtx_model_eval]

private theorem term_ne_stuck_of_eval_bv1
    (M : SmtModel) (t : Term) (b : Bool)
    (h : __smtx_model_eval M (__eo_to_smt t) = bv1 b) :
    t ≠ Term.Stuck := by
  intro ht
  subst t
  rw [eval_stuck] at h
  cases b <;> cases h

private theorem term_ne_stuck_of_eval_binary
    (M : SmtModel) (t : Term) (w n : Int)
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary w n) :
    t ≠ Term.Stuck := by
  intro ht
  subst t
  rw [eval_stuck] at h
  cases h

private theorem eval_binary (M : SmtModel) (w n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Binary w n)) =
      SmtValue.Binary w n := by
  change __smtx_model_eval M (SmtTerm.Binary w n) = SmtValue.Binary w n
  simp only [__smtx_model_eval]

private theorem eo_mk_apply_of_ne_stuck
    {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem index_term_eq (w start : Nat) (hstart : start < w) :
    __eo_add
        (__eo_add (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (-1 : native_Int)))
        (__eo_neg (Term.Numeral (native_nat_to_int start))) =
      Term.Numeral (native_nat_to_int (w - 1 - start)) := by
  have hEq : ((w : Int) + -1 + -(start : Int) :
      Int) = (w - 1 - start : Nat) := by
    omega
  simp [__eo_add, __eo_neg, native_zplus, native_zneg, native_nat_to_int, hEq]

private theorem umulo_indices_eq
    (w : Nat) (hw : 1 ≤ w) :
    __eo_requires
      (__eo_is_neg
        (__eo_add
          (__eo_add (Term.Numeral 1)
            (__eo_add (Term.Numeral (native_nat_to_int w))
              (Term.Numeral (-1 : native_Int))))
          (Term.Numeral (-1 : native_Int))))
      (Term.Boolean false)
      (__iota_rec
        (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (__eo_add
            (__eo_add (Term.Numeral 1)
              (__eo_add (Term.Numeral (native_nat_to_int w))
                (Term.Numeral (-1 : native_Int))))
            (Term.Numeral (-1 : native_Int))))
        (Term.Numeral 1)) =
      intRangeList 1 (w - 1) := by
  have hSub :
      __eo_add (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (w - 1)) := by
    have hEq : ((w : Int) + (-1 : Int) : Int) = ((w - 1 : Nat) : Int) := by
      omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  have hLen :
      __eo_add
          (__eo_add (Term.Numeral 1)
            (Term.Numeral (native_nat_to_int (w - 1))))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (w - 1)) := by
    have hEq : ((1 : Int) + (w - 1 : Nat) + (-1 : Int) : Int) =
        ((w - 1 : Nat) : Int) := by omega
    simp [__eo_add, native_zplus, native_nat_to_int, hEq]
  rw [hSub, hLen]
  have hNotNeg :
      __eo_is_neg (Term.Numeral (native_nat_to_int (w - 1))) =
        Term.Boolean false := by
    have hNonneg : ¬ (((w - 1 : Nat) : Int) < 0) :=
      Int.not_lt_of_ge (Int.natCast_nonneg (w - 1))
    simp [__eo_is_neg, native_zlt, native_nat_to_int, hNonneg]
  have hRepeat :
      __eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (Term.Numeral (native_nat_to_int (w - 1))) =
        intZeroList (w - 1) := by
    change
      native_ite
        (native_zlt (native_nat_to_int (w - 1)) (0 : native_Int))
        Term.Stuck
        (__eo_list_repeat_rec (Term.UOp UserOp._at__at_TypedList_cons)
          (Term.Numeral 0)
          (native_int_to_nat (native_nat_to_int (w - 1)))) =
        intZeroList (w - 1)
    have hNegFalse :
        native_zlt (native_nat_to_int (w - 1)) (0 : native_Int) = false := by
      simp [native_zlt, native_nat_to_int]
    have hToNat :
        native_int_to_nat (native_nat_to_int (w - 1)) = w - 1 := by
      simp [native_int_to_nat, native_nat_to_int]
    rw [hNegFalse, hToNat]
    simp [native_ite]
    exact intZeroList_repeat_rec_eq (w - 1)
  have hIota :
      __iota_rec (intZeroList (w - 1)) (Term.Numeral 1) =
        intRangeList 1 (w - 1) := by
    simpa [native_nat_to_int] using iota_rec_range_eq (w - 1) 1
  rw [hNotNeg, hRepeat, hIota]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]

private def mulHighBitTerm (a b : Term) : Term :=
  let wTerm := __bv_bitwidth (__eo_typeof a)
  let aExt := zeroExtendOneTerm a
  let bExt := zeroExtendOneTerm b
  __eo_mk_apply (Term.UOp2 UserOp2.extract wTerm wTerm)
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) bExt)
        (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt))))

private theorem eval_mul_high_bit_term
    (M : SmtModel) (a b : Term) (w A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (haBound : A < 2 ^ w) (hbBound : B < 2 ^ w)
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (mulHighBitTerm a b)) =
      bv1 ((A * B).testBit w) := by
  let aExt := zeroExtendOneTerm a
  let bExt := zeroExtendOneTerm b
  have haExtEval :
      __smtx_model_eval M (__eo_to_smt aExt) =
        SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int) := by
    simpa [aExt, zeroExtendOneTerm] using
      eval_zero_extend_one_term M a w A haEval haBound
  have hbExtEval :
      __smtx_model_eval M (__eo_to_smt bExt) =
        SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int) := by
    simpa [bExt, zeroExtendOneTerm] using
      eval_zero_extend_one_term M b w B hbEval hbBound
  have haExtTy :
      __eo_typeof aExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    simpa [aExt] using typeof_zero_extend_one_term a w haTy
  let nilMul := __eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)
  have hNilNe' : nilMul ≠ Term.Stuck := by
    simpa [nilMul, aExt] using hNilNe
  have hNilEq :
      nilMul = Term.Binary (native_nat_to_int (w + 1)) 1 := by
    dsimp [nilMul]
    rw [haExtTy]
    exact nil_bvmul_bitvec_succ_of_ne_stuck w (by
      simpa [nilMul, haExtTy] using hNilNe')
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt nilMul) =
        SmtValue.Binary (native_nat_to_int (w + 1)) 1 := by
    rw [hNilEq]
    change __smtx_model_eval M
      (SmtTerm.Binary (native_nat_to_int (w + 1)) 1) =
      SmtValue.Binary (native_nat_to_int (w + 1)) 1
    simp only [__smtx_model_eval]
  let bTimesOne := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul
  have hbTimesOneEq :
      bTimesOne = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul := by
    dsimp [bTimesOne]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by rw [hNilEq]; exact term_binary_ne_stuck _ _)
  have hbTimesOneEval :
      __smtx_model_eval M (__eo_to_smt bTimesOne) =
        SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int) := by
    rw [hbTimesOneEq]
    have hMul :=
      eval_bvmul_term M bExt nilMul
        (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))
        (SmtValue.Binary (native_nat_to_int (w + 1)) 1)
        hbExtEval hNilEval
    rw [hMul]
    exact bvmul_one_right_value w B hbBound
  have hbTimesOneNe : bTimesOne ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M bTimesOne (native_nat_to_int (w + 1))
      (B : Int) hbTimesOneEval
  let product := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne
  have hProductEq :
      product = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne := by
    dsimp [product]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) hbTimesOneNe
  have hProductEval :
      __smtx_model_eval M (__eo_to_smt product) =
        __smtx_model_eval_bvmul
          (SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int))
          (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int)) := by
    rw [hProductEq]
    exact eval_bvmul_term M aExt bTimesOne
      (SmtValue.Binary (native_nat_to_int (w + 1)) (A : Int))
      (SmtValue.Binary (native_nat_to_int (w + 1)) (B : Int))
      haExtEval hbTimesOneEval
  have hProductNe : product ≠ Term.Stuck := by
    rw [hProductEq]
    exact term_apply_ne_stuck _ _
  have hExtractEq :
      __eo_mk_apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product =
      Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product := by
    exact eo_mk_apply_of_ne_stuck (by intro h; cases h) hProductNe
  have hEvalExtract :
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
              (Term.Numeral (native_nat_to_int w))) product)) =
        bv1 ((A * B).testBit w) := by
    show __smtx_model_eval M
        (SmtTerm.extract (SmtTerm.Numeral (native_nat_to_int w))
          (SmtTerm.Numeral (native_nat_to_int w)) (__eo_to_smt product)) =
        bv1 ((A * B).testBit w)
    rw [smtx_eval_extract_term_eq, hProductEval]
    simp [__smtx_model_eval]
    exact bvmul_high_bit_value w A B
  have hWidth :
      __bv_bitwidth (__eo_typeof a) = Term.Numeral (native_nat_to_int w) := by
    rw [haTy]
    rfl
  dsimp [mulHighBitTerm, zeroExtendOneTerm]
  rw [hWidth]
  change
    __smtx_model_eval M
      (__eo_to_smt
        (__eo_mk_apply
          (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
            (Term.Numeral (native_nat_to_int w))) product)) =
      bv1 ((A * B).testBit w)
  rw [hExtractEq]
  exact hEvalExtract

private theorem typeof_mul_high_bit_term
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck) :
    __eo_typeof (mulHighBitTerm a b) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
  let aExt := zeroExtendOneTerm a
  let bExt := zeroExtendOneTerm b
  have haExtTy :
      __eo_typeof aExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    simpa [aExt] using typeof_zero_extend_one_term a w haTy
  have hbExtTy :
      __eo_typeof bExt =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    simpa [bExt] using typeof_zero_extend_one_term b w hbTy
  let nilMul := __eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof aExt)
  have hNilNe' : nilMul ≠ Term.Stuck := by
    simpa [nilMul, aExt] using hNilNe
  have hNilEq :
      nilMul = Term.Binary (native_nat_to_int (w + 1)) 1 := by
    dsimp [nilMul]
    rw [haExtTy]
    exact nil_bvmul_bitvec_succ_of_ne_stuck w (by
      simpa [nilMul, haExtTy] using hNilNe')
  have hNilTy :
      __eo_typeof nilMul =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    rw [hNilEq]
    exact typeof_binary_bitvec_nat (w + 1) 1
  let bTimesOne := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul
  have hbTimesOneEq :
      bTimesOne = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) bExt) nilMul := by
    dsimp [bTimesOne]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by rw [hNilEq]; exact term_binary_ne_stuck _ _)
  have hbTimesOneTy :
      __eo_typeof bTimesOne =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    rw [hbTimesOneEq]
    exact typeof_bvmul_same_bitvec bExt nilMul (w + 1) hbExtTy hNilTy
  let product := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne
  have hProductEq :
      product = Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) aExt) bTimesOne := by
    dsimp [product]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by
        intro h
        have hTyStuck : __eo_typeof bTimesOne = __eo_typeof Term.Stuck := by
          rw [h]
        rw [hbTimesOneTy] at hTyStuck
        change Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) = Term.Stuck at hTyStuck
        cases hTyStuck)
  have hProductTy :
      __eo_typeof product =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int (w + 1))) := by
    rw [hProductEq]
    exact typeof_bvmul_same_bitvec aExt bTimesOne (w + 1) haExtTy hbTimesOneTy
  have hWidth :
      __bv_bitwidth (__eo_typeof a) = Term.Numeral (native_nat_to_int w) := by
    rw [haTy]
    rfl
  dsimp [mulHighBitTerm, zeroExtendOneTerm]
  rw [hWidth]
  change
    __eo_typeof
      (__eo_mk_apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  have hExtractEq :
      __eo_mk_apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product =
      Term.Apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (native_nat_to_int w))) product := by
    exact eo_mk_apply_of_ne_stuck (by intro h; cases h)
      (by rw [hProductEq]; exact term_apply_ne_stuck _ _)
  rw [hExtractEq]
  exact typeof_extract_bit_of_bv product (w + 1) w hProductTy (by omega)

private def mulHighOrTerm (a b : Term) : Term :=
  let hi := mulHighBitTerm a b
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.bvor) hi)
    (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof hi))

private theorem mulHighBitTerm_stuck_of_nil_bvmul_stuck
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNil :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) = Term.Stuck) :
    mulHighBitTerm a b = Term.Stuck := by
  dsimp [mulHighBitTerm]
  rw [haTy]
  simp [__bv_bitwidth, hNil, __eo_mk_apply]

private theorem mulHighOrTerm_stuck_of_high_stuck
    (a b : Term) (hHi : mulHighBitTerm a b = Term.Stuck) :
    mulHighOrTerm a b = Term.Stuck := by
  dsimp [mulHighOrTerm]
  rw [hHi]
  simp [__eo_mk_apply]

private theorem eval_mul_high_or_term
    (M : SmtModel) (a b : Term) (w A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (haBound : A < 2 ^ w) (hbBound : B < 2 ^ w)
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (mulHighOrTerm a b)) =
      bv1 ((A * B).testBit w) := by
  let hi := mulHighBitTerm a b
  have hHiEval :
      __smtx_model_eval M (__eo_to_smt hi) =
        bv1 ((A * B).testBit w) := by
    simpa [hi] using
      eval_mul_high_bit_term M a b w A B haTy haEval hbEval
        haBound hbBound hNilNe
  have hHiTy :
      __eo_typeof hi =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
    simpa [hi] using typeof_mul_high_bit_term a b w haTy hbTy hNilNe
  let nilOr := __eo_nil (Term.UOp UserOp.bvor) (__eo_typeof hi)
  have hNilOrEq : nilOr = Term.Binary 1 0 := by
    dsimp [nilOr]
    rw [hHiTy, nil_bvor_bit]
  have hNilOrEval :
      __smtx_model_eval M (__eo_to_smt nilOr) = bv1 false := by
    rw [hNilOrEq]
    simpa [bv1] using eval_binary M 1 0
  let bvorHi := __eo_mk_apply (Term.UOp UserOp.bvor) hi
  have hBvorHiEq :
      bvorHi = Term.Apply (Term.UOp UserOp.bvor) hi := by
    dsimp [bvorHi]
    exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
      (term_ne_stuck_of_eval_bv1 M hi _ hHiEval)
  have hTermEq :
      __eo_mk_apply bvorHi nilOr =
        Term.Apply (Term.Apply (Term.UOp UserOp.bvor) hi) nilOr := by
    rw [hBvorHiEq]
    exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
      (by rw [hNilOrEq]; exact term_binary_ne_stuck _ _)
  dsimp [mulHighOrTerm]
  change
    __smtx_model_eval M
      (__eo_to_smt (__eo_mk_apply bvorHi nilOr)) =
      bv1 ((A * B).testBit w)
  rw [hTermEq]
  have hEval := eval_bvor_term M hi nilOr ((A * B).testBit w) false
    hHiEval hNilOrEval
  simpa using hEval

private def bvUmuloExpanded (a b : Term) : Term :=
  let wTerm := __bv_bitwidth (__eo_typeof a)
  let topIdx := __eo_add wTerm (Term.Numeral (-1 : native_Int))
  let len :=
    __eo_add (__eo_add (Term.Numeral 1) topIdx)
      (Term.Numeral (-1 : native_Int))
  __eo_ite (__eo_eq wTerm (Term.Numeral 1)) (Term.Boolean false)
    (__eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp.eq)
        (__bv_umulo_elim_rec a b
          (__eo_mk_apply (Term.UOp2 UserOp2.extract topIdx topIdx) a)
          (mulHighOrTerm a b)
          (__eo_requires (__eo_is_neg len) (Term.Boolean false)
            (__iota_rec
              (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.Numeral 0) len)
              (Term.Numeral 1)))
          wTerm))
      (Term.Binary 1 1))


private theorem umulo_rec_nil_eq
    {a b uppc res n : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck)
    (hu : uppc ≠ Term.Stuck) (hr : res ≠ Term.Stuck)
    (hn : n ≠ Term.Stuck) :
    __bv_umulo_elim_rec a b uppc res
      (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
        (Term.UOp UserOp.Int)) n = res := by
  simp [__bv_umulo_elim_rec, ha, hb, hu, hr, hn]

private theorem umulo_rec_cons_eq
    {a b uppc res i ns n : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck)
    (hu : uppc ≠ Term.Stuck) (hr : res ≠ Term.Stuck)
    (hn : n ≠ Term.Stuck) :
    __bv_umulo_elim_rec a b uppc res
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) i) ns) n =
      (let _v0 := (__eo_add (__eo_add n (Term.Numeral (-1 : native_Int)))
          (__eo_neg i))
       let _v1 := (__eo_mk_apply (Term.UOp2 UserOp2.extract _v0 _v0) a)
       let _v2 := (Term.Apply (Term.UOp2 UserOp2.extract i i) b)
       (__eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.bvor)
            (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) _v2)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) uppc)
                (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof _v2)))))
          (__bv_umulo_elim_rec a b
            (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.bvor) _v1)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) uppc)
                (__eo_nil (Term.UOp UserOp.bvor) (__eo_typeof _v1))))
            res ns n))) := by
  simp [__bv_umulo_elim_rec, ha, hb, hu, hr, hn]

private theorem umulo_rec_list_stuck_eq
    (a b uppc res n : Term) :
    __bv_umulo_elim_rec a b uppc res Term.Stuck n = Term.Stuck := by
  by_cases ha : a = Term.Stuck
  · subst a
    exact __bv_umulo_elim_rec.eq_1 b uppc res Term.Stuck n
  by_cases hb : b = Term.Stuck
  · subst b
    exact __bv_umulo_elim_rec.eq_2 a uppc res Term.Stuck n ha
  by_cases hu : uppc = Term.Stuck
  · subst uppc
    exact __bv_umulo_elim_rec.eq_3 a b res Term.Stuck n ha hb
  by_cases hr : res = Term.Stuck
  · subst res
    exact __bv_umulo_elim_rec.eq_4 a b uppc Term.Stuck n ha hb hu
  by_cases hn : n = Term.Stuck
  · subst n
    exact __bv_umulo_elim_rec.eq_5 a b uppc res Term.Stuck ha hb hu hr
  exact __bv_umulo_elim_rec.eq_8 a b uppc res Term.Stuck n ha hb hu hr
    (by intro h; cases h)
    (by intro i ns h; cases h)
    hn

private theorem umulo_rec_res_stuck_eq
    (a b uppc ns n : Term) :
    __bv_umulo_elim_rec a b uppc Term.Stuck ns n = Term.Stuck := by
  by_cases ha : a = Term.Stuck
  · subst a
    exact __bv_umulo_elim_rec.eq_1 b uppc Term.Stuck ns n
  by_cases hb : b = Term.Stuck
  · subst b
    exact __bv_umulo_elim_rec.eq_2 a uppc Term.Stuck ns n ha
  by_cases hu : uppc = Term.Stuck
  · subst uppc
    exact __bv_umulo_elim_rec.eq_3 a b Term.Stuck ns n ha hb
  exact __bv_umulo_elim_rec.eq_4 a b uppc ns n ha hb hu

private theorem umulo_rec_eval
    (M : SmtModel) (a b uppc res : Term)
    (w A B start len : Nat) (up rs : Bool)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (hupEval : __smtx_model_eval M (__eo_to_smt uppc) = bv1 up)
    (hrsEval : __smtx_model_eval M (__eo_to_smt res) = bv1 rs)
    (hbound : start + len ≤ w) :
    __smtx_model_eval M
      (__eo_to_smt
        (__bv_umulo_elim_rec a b uppc res (intRangeList start len)
          (Term.Numeral (native_nat_to_int w)))) =
      bv1 (scanRec w A B start len up rs) := by
  have haNe : a ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M a (native_nat_to_int w) (A : Int) haEval
  have hbNe : b ≠ Term.Stuck :=
    term_ne_stuck_of_eval_binary M b (native_nat_to_int w) (B : Int) hbEval
  have hrNe : res ≠ Term.Stuck :=
    term_ne_stuck_of_eval_bv1 M res rs hrsEval
  induction len generalizing start uppc up with
  | zero =>
      have huNe : uppc ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M uppc up hupEval
      change
        __smtx_model_eval M
          (__eo_to_smt
            (__bv_umulo_elim_rec a b uppc res
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
                (Term.UOp UserOp.Int))
              (Term.Numeral (native_nat_to_int w)))) =
          bv1 (scanRec w A B start 0 up rs)
      rw [umulo_rec_nil_eq haNe hbNe huNe hrNe (term_numeral_ne_stuck _)]
      simpa [intRangeList, scanRec] using hrsEval
  | succ len ih =>
      have huNe : uppc ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M uppc up hupEval
      have hstartLt : start < w := by omega
      have htailBound : start + 1 + len ≤ w := by omega
      have hIdx := index_term_eq w start hstartLt
      change
        __smtx_model_eval M
          (__eo_to_smt
            (__bv_umulo_elim_rec a b uppc res
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                  (Term.Numeral (native_nat_to_int start)))
                (intRangeList (start + 1) len))
              (Term.Numeral (native_nat_to_int w)))) =
          bv1 (scanRec w A B start (Nat.succ len) up rs)
      rw [umulo_rec_cons_eq haNe hbNe huNe hrNe (term_numeral_ne_stuck _)]
      rw [hIdx]
      let hiTerm := Term.Numeral (native_nat_to_int (w - 1 - start))
      let iTerm := Term.Numeral (native_nat_to_int start)
      let v1 := Term.Apply (Term.UOp2 UserOp2.extract hiTerm hiTerm) a
      let v2 := Term.Apply (Term.UOp2 UserOp2.extract iTerm iTerm) b
      have hv1MkEq :
          __eo_mk_apply (Term.UOp2 UserOp2.extract hiTerm hiTerm) a = v1 := by
        dsimp [v1]
        exact eo_mk_apply_of_ne_stuck (by intro h; cases h) haNe
      have hv1Eval :
          __smtx_model_eval M (__eo_to_smt v1) =
            bv1 (A.testBit (w - 1 - start)) := by
        simpa [v1, hiTerm] using
          eval_extract_bit_term M a (native_nat_to_int w) (A : Int)
            (w - 1 - start) haEval (Int.natCast_nonneg A)
      have hv2Eval :
          __smtx_model_eval M (__eo_to_smt v2) =
            bv1 (B.testBit start) := by
        simpa [v2, iTerm] using
          eval_extract_bit_term M b (native_nat_to_int w) (B : Int)
            start hbEval (Int.natCast_nonneg B)
      have hv1Ty :
          __eo_typeof v1 =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        simpa [v1, hiTerm] using
          typeof_extract_bit_of_bv a w (w - 1 - start) haTy (by omega)
      have hv2Ty :
          __eo_typeof v2 =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) := by
        simpa [v2, iTerm] using
          typeof_extract_bit_of_bv b w start hbTy hstartLt
      let nilAnd := __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof v2)
      have hnilAndEq : nilAnd = Term.Binary 1 1 := by
        dsimp [nilAnd]
        rw [hv2Ty, nil_bvand_bit]
      have hnilAndEval :
          __smtx_model_eval M (__eo_to_smt nilAnd) = bv1 true := by
        rw [hnilAndEq]
        simpa [bv1] using eval_binary M 1 1
      let upAnd := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) uppc) nilAnd
      have hupAndEq :
          upAnd = Term.Apply (Term.Apply (Term.UOp UserOp.bvand) uppc) nilAnd := by
        dsimp [upAnd]
        exact eo_mk_apply_of_ne_stuck
          (term_apply_ne_stuck _ _)
          (by rw [hnilAndEq]; exact term_binary_ne_stuck 1 1)
      have hupAndEval :
          __smtx_model_eval M (__eo_to_smt upAnd) = bv1 up := by
        rw [hupAndEq]
        have h := eval_bvand_term M uppc nilAnd up true hupEval hnilAndEval
        simpa using h
      let headAnd := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) v2) upAnd
      have hheadAndEq :
          headAnd = Term.Apply (Term.Apply (Term.UOp UserOp.bvand) v2) upAnd := by
        dsimp [headAnd]
        exact eo_mk_apply_of_ne_stuck
          (term_apply_ne_stuck _ _)
          (term_ne_stuck_of_eval_bv1 M upAnd up hupAndEval)
      have hheadAndEval :
          __smtx_model_eval M (__eo_to_smt headAnd) =
            bv1 (B.testBit start && up) := by
        rw [hheadAndEq]
        exact eval_bvand_term M v2 upAnd (B.testBit start) up
          hv2Eval hupAndEval
      let nilOr := __eo_nil (Term.UOp UserOp.bvor) (__eo_typeof v1)
      have hnilOrEq : nilOr = Term.Binary 1 0 := by
        dsimp [nilOr]
        rw [hv1Ty, nil_bvor_bit]
      have hnilOrEval :
          __smtx_model_eval M (__eo_to_smt nilOr) = bv1 false := by
        rw [hnilOrEq]
        simpa [bv1] using eval_binary M 1 0
      let upOrTail := __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) uppc) nilOr
      have hupOrTailEq :
          upOrTail = Term.Apply (Term.Apply (Term.UOp UserOp.bvor) uppc) nilOr := by
        dsimp [upOrTail]
        exact eo_mk_apply_of_ne_stuck
          (term_apply_ne_stuck _ _)
          (by rw [hnilOrEq]; exact term_binary_ne_stuck 1 0)
      have hupOrTailEval :
          __smtx_model_eval M (__eo_to_smt upOrTail) = bv1 up := by
        rw [hupOrTailEq]
        have h := eval_bvor_term M uppc nilOr up false hupEval hnilOrEval
        simpa using h
      let newUppc := __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.bvor) v1) upOrTail
      have hBvorV1Eq :
          __eo_mk_apply (Term.UOp UserOp.bvor) v1 =
            Term.Apply (Term.UOp UserOp.bvor) v1 := by
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
          (term_apply_ne_stuck _ _)
      have hnewUppcEq :
          newUppc =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) v1) upOrTail := by
        dsimp [newUppc]
        rw [hBvorV1Eq]
        exact eo_mk_apply_of_ne_stuck
          (term_apply_ne_stuck _ _)
          (term_ne_stuck_of_eval_bv1 M upOrTail up hupOrTailEval)
      have hnewUppcEval :
          __smtx_model_eval M (__eo_to_smt newUppc) =
            bv1 (A.testBit (w - 1 - start) || up) := by
        rw [hnewUppcEq]
        exact eval_bvor_term M v1 upOrTail
          (A.testBit (w - 1 - start)) up hv1Eval hupOrTailEval
      have htailEval :=
        ih newUppc (start + 1)
          (A.testBit (w - 1 - start) || up)
          hnewUppcEval htailBound
      let tail :=
        __bv_umulo_elim_rec a b newUppc res
          (intRangeList (start + 1) len)
          (Term.Numeral (native_nat_to_int w))
      have htailEval' :
          __smtx_model_eval M (__eo_to_smt tail) =
            bv1
              (scanRec w A B (start + 1) len
                (A.testBit (w - 1 - start) || up) rs) := by
        simpa [tail] using htailEval
      have htailNe : tail ≠ Term.Stuck :=
        term_ne_stuck_of_eval_bv1 M tail _ htailEval'
      let headOr := __eo_mk_apply (Term.UOp UserOp.bvor) headAnd
      have hheadOrEq :
          headOr = Term.Apply (Term.UOp UserOp.bvor) headAnd := by
        dsimp [headOr]
        exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.bvor)
          (term_ne_stuck_of_eval_bv1 M headAnd _ hheadAndEval)
      have hresultEq :
          __eo_mk_apply headOr tail =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) headAnd) tail := by
        rw [hheadOrEq]
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) htailNe
      have hresultEqDirect :
          __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvor) headAnd) tail =
            Term.Apply (Term.Apply (Term.UOp UserOp.bvor) headAnd) tail := by
        exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _) htailNe
      have hFinal := eval_bvor_term M headAnd tail
        (B.testBit start && up)
        (scanRec w A B (start + 1) len
          (A.testBit (w - 1 - start) || up) rs)
        hheadAndEval htailEval'
      simpa [scanRec, hiTerm, iTerm, v1, v2, nilAnd, upAnd, headAnd,
        nilOr, upOrTail, newUppc, tail, headOr, hv1MkEq, hheadOrEq,
        hresultEq, hresultEqDirect] using hFinal

private theorem eval_bv_umulo_expanded
    (M : SmtModel) (a b : Term) (w A B : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hbTy : __eo_typeof b =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (haEval : __smtx_model_eval M (__eo_to_smt a) =
      SmtValue.Binary (native_nat_to_int w) (A : Int))
    (hbEval : __smtx_model_eval M (__eo_to_smt b) =
      SmtValue.Binary (native_nat_to_int w) (B : Int))
    (haBound : A < 2 ^ w) (hbBound : B < 2 ^ w)
    (hw : 1 ≤ w)
    (hNilNe :
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (bvUmuloExpanded a b)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b)) := by
  have hWidth :
      __bv_bitwidth (__eo_typeof a) = Term.Numeral (native_nat_to_int w) := by
    rw [haTy]
    rfl
  have hOrigEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b)) =
        SmtValue.Boolean (decide (2 ^ w ≤ A * B)) := by
    have h := eval_bvumulo_term M a b
      (SmtValue.Binary (native_nat_to_int w) (A : Int))
      (SmtValue.Binary (native_nat_to_int w) (B : Int))
      haEval hbEval
    rw [h]
    exact bvumulo_value w A B
  by_cases hw1 : w = 1
  · subst w
    have hNoOverflow : ¬ 2 ^ 1 ≤ A * B := by
      intro hov
      have hA : A ≤ 1 := by omega
      have hB : B ≤ 1 := by omega
      have hA01 : A = 0 ∨ A = 1 := by omega
      have hB01 : B = 0 ∨ B = 1 := by omega
      have hProd : A * B ≤ 1 := by
        rcases hA01 with rfl | rfl <;> rcases hB01 with rfl | rfl <;> omega
      change (2 : Nat) ≤ A * B at hov
      omega
    dsimp [bvUmuloExpanded]
    rw [hWidth]
    change
      __smtx_model_eval M
        (__eo_to_smt
          (__eo_ite
            (__eo_eq (Term.Numeral (native_nat_to_int 1)) (Term.Numeral 1))
            (Term.Boolean false)
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp.eq)
                (__bv_umulo_elim_rec a b
                  (__eo_mk_apply
                    (Term.UOp2 UserOp2.extract
                      (__eo_add (Term.Numeral (native_nat_to_int 1))
                        (Term.Numeral (-1 : native_Int)))
                      (__eo_add (Term.Numeral (native_nat_to_int 1))
                        (Term.Numeral (-1 : native_Int)))) a)
                  (mulHighOrTerm a b)
                  (__eo_requires
                    (__eo_is_neg
                      (__eo_add
                        (__eo_add (Term.Numeral 1)
                          (__eo_add (Term.Numeral (native_nat_to_int 1))
                            (Term.Numeral (-1 : native_Int))))
                        (Term.Numeral (-1 : native_Int))))
                    (Term.Boolean false)
                    (__iota_rec
                      (__eo_list_repeat
                        (Term.UOp UserOp._at__at_TypedList_cons)
                        (Term.Numeral 0)
                        (__eo_add
                          (__eo_add (Term.Numeral 1)
                            (__eo_add (Term.Numeral (native_nat_to_int 1))
                              (Term.Numeral (-1 : native_Int))))
                          (Term.Numeral (-1 : native_Int))))
                      (Term.Numeral 1)))
                  (Term.Numeral (native_nat_to_int 1))))
              (Term.Binary 1 1)))) =
        __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b))
    have hCond :
        __eo_eq (Term.Numeral (native_nat_to_int 1)) (Term.Numeral 1) =
          Term.Boolean true := by
      native_decide
    rw [hCond]
    simp [__eo_ite, native_ite, native_teq]
    rw [hOrigEval]
    simp [hNoOverflow, __smtx_model_eval]
  · have hTop :
        __eo_add (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (w - 1)) := by
      have hEq : ((w : Int) + (-1 : Int) : Int) = ((w - 1 : Nat) : Int) := by
        omega
      simp [__eo_add, native_zplus, native_nat_to_int, hEq]
    have hCond :
        __eo_eq (Term.Numeral (native_nat_to_int w)) (Term.Numeral 1) =
          Term.Boolean false := by
      have hne : (w : Int) ≠ 1 := by omega
      have hne' : ¬ (1 : Int) = (w : Int) := by omega
      simp [__eo_eq, native_teq, native_nat_to_int, hne, hne']
    let uppc :=
      __eo_mk_apply
        (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int (w - 1)))
          (Term.Numeral (native_nat_to_int (w - 1)))) a
    have haNe : a ≠ Term.Stuck :=
      term_ne_stuck_of_eval_binary M a (native_nat_to_int w) (A : Int) haEval
    have hUppcEq :
        uppc =
          Term.Apply
            (Term.UOp2 UserOp2.extract (Term.Numeral (native_nat_to_int (w - 1)))
              (Term.Numeral (native_nat_to_int (w - 1)))) a := by
      dsimp [uppc]
      exact eo_mk_apply_of_ne_stuck (by intro h; cases h) haNe
    have hUppcEval :
        __smtx_model_eval M (__eo_to_smt uppc) =
          bv1 (A.testBit (w - 1)) := by
      rw [hUppcEq]
      simpa using
        eval_extract_bit_term M a (native_nat_to_int w) (A : Int)
          (w - 1) haEval (Int.natCast_nonneg A)
    have hResEval :
        __smtx_model_eval M (__eo_to_smt (mulHighOrTerm a b)) =
          bv1 ((A * B).testBit w) := by
      exact eval_mul_high_or_term M a b w A B haTy hbTy haEval hbEval
        haBound hbBound hNilNe
    have hIndices := umulo_indices_eq w hw
    have hIndices' :
        __eo_requires
          (__eo_is_neg
            (__eo_add
              (__eo_add (Term.Numeral 1)
                (Term.Numeral (native_nat_to_int (w - 1))))
              (Term.Numeral (-1 : native_Int))))
          (Term.Boolean false)
          (__iota_rec
            (__eo_list_repeat (Term.UOp UserOp._at__at_TypedList_cons)
              (Term.Numeral 0)
              (__eo_add
                (__eo_add (Term.Numeral 1)
                  (Term.Numeral (native_nat_to_int (w - 1))))
                (Term.Numeral (-1 : native_Int))))
            (Term.Numeral 1)) =
          intRangeList 1 (w - 1) := by
      simpa [hTop] using hIndices
    have hRecEval :
        __smtx_model_eval M
          (__eo_to_smt
            (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
              (intRangeList 1 (w - 1))
              (Term.Numeral (native_nat_to_int w)))) =
          bv1
            (scanRec w A B 1 (w - 1) (A.testBit (w - 1))
              ((A * B).testBit w)) := by
      exact umulo_rec_eval M a b uppc (mulHighOrTerm a b)
        w A B 1 (w - 1) (A.testBit (w - 1)) ((A * B).testBit w)
        haTy hbTy haEval hbEval hUppcEval hResEval (by omega)
    have hEqEval :
        __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
                  (intRangeList 1 (w - 1))
                  (Term.Numeral (native_nat_to_int w))))
              (Term.Binary 1 1))) =
          SmtValue.Boolean
            (scanRec w A B 1 (w - 1) (A.testBit (w - 1))
              ((A * B).testBit w)) := by
      exact eval_eq_bv1_one_term M
        (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
          (intRangeList 1 (w - 1))
          (Term.Numeral (native_nat_to_int w)))
        (scanRec w A B 1 (w - 1) (A.testBit (w - 1))
          ((A * B).testBit w)) hRecEval
    have hScanBool :
        scanRec w A B 1 (w - 1) (A.testBit (w - 1))
            ((A * B).testBit w) =
          decide (2 ^ w ≤ A * B) := by
      have hiff := scanRec_iff_overflow (w := w) (a := A) (b := B)
        hw haBound hbBound
      by_cases hscan :
          scanRec w A B 1 (w - 1) (A.testBit (w - 1))
            ((A * B).testBit w) = true
      · have hov : 2 ^ w ≤ A * B := hiff.1 hscan
        simp [hscan, hov]
      · have hnOv : ¬ 2 ^ w ≤ A * B := by
          intro hov
          exact hscan (hiff.2 hov)
        have hscanFalse :
          scanRec w A B 1 (w - 1) (A.testBit (w - 1))
            ((A * B).testBit w) = false := Bool.eq_false_iff.2 hscan
        simp [hscanFalse, hnOv]
    dsimp [bvUmuloExpanded]
    rw [hWidth, hTop, hCond]
    simp [__eo_ite, native_ite, native_teq]
    rw [hIndices']
    change
      __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.eq)
              (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
                (intRangeList 1 (w - 1))
                (Term.Numeral (native_nat_to_int w))))
            (Term.Binary 1 1))) =
        __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b))
    have hRecNe :
        __bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
          (intRangeList 1 (w - 1))
          (Term.Numeral (native_nat_to_int w)) ≠ Term.Stuck :=
      term_ne_stuck_of_eval_bv1 M _ _ hRecEval
    have hEqHead :
        __eo_mk_apply (Term.UOp UserOp.eq)
          (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
            (intRangeList 1 (w - 1))
            (Term.Numeral (native_nat_to_int w))) =
        Term.Apply (Term.UOp UserOp.eq)
          (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
            (intRangeList 1 (w - 1))
            (Term.Numeral (native_nat_to_int w))) := by
      exact eo_mk_apply_of_ne_stuck (term_uop_ne_stuck UserOp.eq) hRecNe
    rw [hEqHead]
    have hEqTerm :
        __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
              (intRangeList 1 (w - 1))
              (Term.Numeral (native_nat_to_int w))))
          (Term.Binary 1 1) =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (__bv_umulo_elim_rec a b uppc (mulHighOrTerm a b)
              (intRangeList 1 (w - 1))
              (Term.Numeral (native_nat_to_int w))))
          (Term.Binary 1 1) := by
      exact eo_mk_apply_of_ne_stuck (term_apply_ne_stuck _ _)
        (term_binary_ne_stuck 1 1)
    rw [hEqTerm, hEqEval, hOrigEval, hScanBool]

private theorem bvUmuloExpanded_width_pos
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNe : bvUmuloExpanded a b ≠ Term.Stuck) :
    1 ≤ w := by
  by_cases hw0 : w = 0
  · subst w
    exfalso
    apply hNe
    dsimp [bvUmuloExpanded]
    rw [haTy]
    simp [__bv_bitwidth, __eo_eq, __eo_add, __eo_is_neg, __eo_requires,
      __eo_ite, __eo_mk_apply, __bv_umulo_elim_rec, native_ite,
      native_teq, native_not, SmtEval.native_not, native_zplus,
      native_zlt, native_nat_to_int, umulo_rec_list_stuck_eq]
  · omega

private theorem nil_bvmul_ne_of_bvUmuloExpanded_ne
    (a b : Term) (w : Nat)
    (haTy : __eo_typeof a =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
    (hNe : bvUmuloExpanded a b ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvmul)
      (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck := by
  have hw : 1 ≤ w := bvUmuloExpanded_width_pos a b w haTy hNe
  by_cases hw1 : w = 1
  · subst w
    intro hNil
    have hTy :
        __eo_typeof (zeroExtendOneTerm a) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int 2)) := by
      simpa [native_nat_to_int] using typeof_zero_extend_one_term a 1 haTy
    rw [hTy] at hNil
    have hNilOk :
        __eo_nil (Term.UOp UserOp.bvmul)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int 2))) =
          Term.Binary (native_nat_to_int 2) 1 := by
      native_decide
    rw [hNilOk] at hNil
    cases hNil
  · intro hNil
    apply hNe
    have hHiStuck : mulHighBitTerm a b = Term.Stuck :=
      mulHighBitTerm_stuck_of_nil_bvmul_stuck a b w haTy hNil
    have hResStuck : mulHighOrTerm a b = Term.Stuck :=
      mulHighOrTerm_stuck_of_high_stuck a b hHiStuck
    have hWidth :
        __bv_bitwidth (__eo_typeof a) = Term.Numeral (native_nat_to_int w) := by
      rw [haTy]
      rfl
    have hTop :
        __eo_add (Term.Numeral (native_nat_to_int w))
          (Term.Numeral (-1 : native_Int)) =
        Term.Numeral (native_nat_to_int (w - 1)) := by
      have hEq : ((w : Int) + (-1 : Int) : Int) = ((w - 1 : Nat) : Int) := by
        omega
      simp [__eo_add, native_zplus, native_nat_to_int, hEq]
    have hCond :
        __eo_eq (Term.Numeral (native_nat_to_int w)) (Term.Numeral 1) =
          Term.Boolean false := by
      have hne : (w : Int) ≠ 1 := by omega
      have hne' : ¬ (1 : Int) = (w : Int) := by omega
      simp [__eo_eq, native_teq, native_nat_to_int, hne, hne']
    dsimp [bvUmuloExpanded]
    rw [hWidth, hTop, hCond, hResStuck]
    simp [__eo_ite, __eo_mk_apply, native_ite, native_teq,
      umulo_rec_res_stuck_eq]


private theorem eo_requires_left_ne_stuck_of_ne_stuck
    {x y z : Term} (h : __eo_requires x y z ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h

private theorem bv_umulo_elim_shape_of_ne_stuck (A : Term) :
    __eo_prog_bv_umulo_elim A ≠ Term.Stuck ->
    ∃ a b c,
      A =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b)) c := by
  intro h
  by_cases hShape :
      ∃ a b c,
        A =
          Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b)) c
  · exact hShape
  · have hStuck : __eo_prog_bv_umulo_elim A = Term.Stuck := by
      rw [__eo_prog_bv_umulo_elim.eq_2]
      intro a b c hEq
      exact hShape ⟨a, b, c, hEq⟩
    exact False.elim (h hStuck)

private theorem bvumulo_typeof_args_of_non_none
    {a b : Term}
    (hNN : term_has_non_none_type
      (SmtTerm.bvumulo (__eo_to_smt a) (__eo_to_smt b))) :
    ∃ w,
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w := by
  apply bv_binop_ret_args_of_non_none
    (op := SmtTerm.bvumulo) (ret := SmtType.Bool)
  · rw [__smtx_typeof.eq_def] <;> simp only
  · exact hNN

private theorem eo_bitvec_type_of_smt_type
    (t : Term) (w : Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    __eo_typeof t =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)) := by
  have hTrans : RuleProofs.eo_has_smt_translation t := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTy]
    intro h
    cases h
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans
  have hEoTy : __eo_to_smt_type (__eo_typeof t) = SmtType.BitVec w := by
    rw [← hMatch, hTy]
  exact TranslationProofs.eo_to_smt_type_eq_bitvec hEoTy

private theorem bitvec_eval_nat_payload
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (w : Nat)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    ∃ n : Nat,
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) (n : Int) ∧
      n < 2 ^ w := by
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  have hEvalTy := type_preservation M hM (__eo_to_smt t) hNN
  rw [hTy] at hEvalTy
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEval⟩
  have hWidth : native_zleq 0 (native_nat_to_int w) = true :=
    bitvec_width_nonneg (by simpa [hEval] using hEvalTy)
  have hCanon :
      native_zeq payload
        (native_mod_total payload (native_int_pow2 (native_nat_to_int w))) =
        true :=
    bitvec_payload_canonical (by simpa [hEval] using hEvalTy)
  have hRange := bitvec_payload_range_of_canonical hWidth hCanon
  let n : Nat := Int.toNat payload
  have hPayloadNat : ((n : Nat) : Int) = payload := by
    simpa [n] using Int.toNat_of_nonneg hRange.1
  have hEvalNat :
      __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) (n : Int) := by
    rw [hEval, hPayloadNat]
  have hBound : n < 2 ^ w := by
    have hLt : (n : Int) < (2 ^ w : Int) := by
      rw [hPayloadNat]
      simpa [native_int_pow2_nat w] using hRange.2
    exact_mod_cast hLt
  exact ⟨n, hEvalNat, hBound⟩

theorem cmd_step_bv_umulo_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_umulo_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_umulo_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_umulo_elim args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.bv_umulo_elim args premises ≠ Term.Stuck :=
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
              change StepRuleProperties M [] (__eo_prog_bv_umulo_elim A)
              change __eo_typeof (__eo_prog_bv_umulo_elim A) = Term.Bool
                at hResultTy
              have hProgNe' : __eo_prog_bv_umulo_elim A ≠ Term.Stuck := by
                simpa using hProgNe
              rcases bv_umulo_elim_shape_of_ne_stuck A hProgNe' with
                ⟨a, b, rhs, hShape⟩
              subst A
              let lhs := Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) a) b
              let expanded := bvUmuloExpanded a b
              let orig := Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
              have hReqNe :
                  __eo_requires expanded rhs orig ≠ Term.Stuck := by
                simpa [__eo_prog_bv_umulo_elim, expanded, orig, lhs,
                  bvUmuloExpanded, mulHighOrTerm, mulHighBitTerm,
                  zeroExtendOneTerm] using hProgNe'
              have hExpandedEq : expanded = rhs :=
                support_eo_requires_cond_eq_of_non_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                eo_requires_left_ne_stuck_of_ne_stuck hReqNe
              have hRhsNe : rhs ≠ Term.Stuck := by
                rw [← hExpandedEq]
                exact hExpandedNe
              have hProgEq :
                  __eo_prog_bv_umulo_elim
                      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) =
                    orig := by
                rw [__eo_prog_bv_umulo_elim.eq_1]
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
              have hBvumuloNN :
                  term_has_non_none_type
                    (SmtTerm.bvumulo (__eo_to_smt a) (__eo_to_smt b)) := by
                unfold term_has_non_none_type
                simpa [lhs] using hLhsNN
              rcases bvumulo_typeof_args_of_non_none hBvumuloNN with
                ⟨w, haSmtTy, hbSmtTy⟩
              have haEoTy := eo_bitvec_type_of_smt_type a w haSmtTy
              have hbEoTy := eo_bitvec_type_of_smt_type b w hbSmtTy
              rcases bitvec_eval_nat_payload M hM a w haSmtTy with
                ⟨av, haEval, haBound⟩
              rcases bitvec_eval_nat_payload M hM b w hbSmtTy with
                ⟨bv, hbEval, hbBound⟩
              have hw : 1 ≤ w :=
                bvUmuloExpanded_width_pos a b w haEoTy hExpandedNe
              have hNilNe :
                  __eo_nil (Term.UOp UserOp.bvmul)
                    (__eo_typeof (zeroExtendOneTerm a)) ≠ Term.Stuck :=
                nil_bvmul_ne_of_bvUmuloExpanded_ne a b w haEoTy hExpandedNe
              have hExpandedEval :
                  __smtx_model_eval M (__eo_to_smt expanded) =
                    __smtx_model_eval M (__eo_to_smt lhs) := by
                simpa [expanded, lhs] using
                  eval_bv_umulo_expanded M a b w av bv haEoTy hbEoTy
                    haEval hbEval haBound hbBound hw hNilNe
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
                  eo_interprets M (__eo_prog_bv_umulo_elim orig) true := by
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
