module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport
public import Cpc.Proofs.Rules.Evaluate
import all Cpc.Proofs.Rules.Evaluate

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

/-! Shared support for the two multiplication/comparison rewrites. -/

private theorem mul_lt_mul_characterization (x y a : Int) :
    y * a < x * a ↔
      y ≠ x ∧ a ≠ 0 ∧ ((y < x) ↔ (a > 0)) := by
  constructor
  · intro h
    rcases Int.lt_trichotomy a 0 with haNeg | haZero | haPos
    · have hxy : x < y := (Int.mul_lt_mul_right_of_neg haNeg).mp h
      exact ⟨by omega, by omega, by simp [show ¬y < x by omega,
        show ¬a > 0 by omega]⟩
    · subst a
      simp at h
    · have hyx : y < x := (Int.mul_lt_mul_right haPos).mp h
      exact ⟨by omega, by omega, by simp [hyx, haPos]⟩
  · rintro ⟨hyx, ha, hSigns⟩
    by_cases hy : y < x
    · have haPos : a > 0 := by
        simpa [hy] using hSigns.symm
      exact (Int.mul_lt_mul_right haPos).mpr hy
    · have hxy : x < y := by omega
      have haNotPos : ¬a > 0 := by
        simpa [hy] using hSigns.symm
      have haNeg : a < 0 := by omega
      exact (Int.mul_lt_mul_right_of_neg haNeg).mpr hxy

private theorem int_mul_bounds_of_natAbs
    {x y : Int} {s t : Nat} (hx : x.natAbs ≤ s) (hy : y.natAbs ≤ t) :
    -((s * t : Nat) : Int) ≤ x * y ∧ x * y ≤ ((s * t : Nat) : Int) := by
  have hUpper := Int.mul_le_mul_of_natAbs_le hx hy
  have hLower := Int.mul_le_mul_of_natAbs_le
    (x := -x) (y := y) (s := s) (t := t) (by simpa) hy
  have hLower' : -(x * y) ≤ ((s * t : Nat) : Int) := by
    simpa [Int.neg_mul] using hLower
  exact ⟨by omega, hUpper⟩

private theorem signed_product_fits
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x : BitVec T) (a : BitVec U) :
    -(2 : Int) ^ (W - 1) ≤ x.toInt * a.toInt ∧
      x.toInt * a.toInt < (2 : Int) ^ (W - 1) := by
  rcases T with _ | t
  · simp only [BitVec.of_length_zero, BitVec.toInt_zero, Int.zero_mul]
    exact ⟨Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide)),
      Int.pow_pos (by decide)⟩
  rcases U with _ | u
  · simp only [BitVec.of_length_zero, BitVec.toInt_zero, Int.mul_zero]
    exact ⟨Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide)),
      Int.pow_pos (by decide)⟩
  have hxLo := BitVec.le_two_mul_toInt (x := x)
  have hxHi := BitVec.two_mul_toInt_lt (x := x)
  have haLo := BitVec.le_two_mul_toInt (x := a)
  have haHi := BitVec.two_mul_toInt_lt (x := a)
  have hPowT : (2 : Int) ^ (t + 1) = 2 * (2 : Int) ^ t := by
    rw [Int.pow_succ]
    omega
  have hPowU : (2 : Int) ^ (u + 1) = 2 * (2 : Int) ^ u := by
    rw [Int.pow_succ]
    omega
  rw [hPowT] at hxLo hxHi
  rw [hPowU] at haLo haHi
  have hPowCastT : ((2 ^ t : Nat) : Int) = (2 : Int) ^ t := by norm_cast
  have hPowCastU : ((2 ^ u : Nat) : Int) = (2 : Int) ^ u := by norm_cast
  have hxAbs : x.toInt.natAbs ≤ 2 ^ t := by
    apply Int.ofNat_le.1
    rw [hPowCastT]
    by_cases hx : 0 ≤ x.toInt
    · rw [Int.natAbs_of_nonneg hx]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  have haAbs : a.toInt.natAbs ≤ 2 ^ u := by
    apply Int.ofNat_le.1
    rw [hPowCastU]
    by_cases ha : 0 ≤ a.toInt
    · rw [Int.natAbs_of_nonneg ha]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  have hMulBounds := int_mul_bounds_of_natAbs hxAbs haAbs
  have hPowMul : (2 ^ t * 2 ^ u : Nat) = 2 ^ (t + u) := by
    rw [← Nat.pow_add]
  rw [hPowMul] at hMulBounds
  have hAbsMul : -(2 : Int) ^ (t + u) ≤ x.toInt * a.toInt ∧
      x.toInt * a.toInt ≤ (2 : Int) ^ (t + u) := by
    exact_mod_cast hMulBounds
  have hPowLt : (2 : Int) ^ (t + u) < (2 : Int) ^ (W - 1) := by
    have hPowLtNat : (2 : Nat) ^ (t + u) < 2 ^ (W - 1) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    exact_mod_cast hPowLtNat
  exact ⟨Int.le_trans (Int.neg_le_neg (Int.le_of_lt hPowLt)) hAbsMul.1,
    Int.lt_of_le_of_lt hAbsMul.2 hPowLt⟩

private theorem unsigned_signed_product_fits
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x : BitVec T) (a : BitVec U) :
    -(2 : Int) ^ (W - 1) ≤ (x.toNat : Int) * a.toInt ∧
      (x.toNat : Int) * a.toInt < (2 : Int) ^ (W - 1) := by
  rcases T with _ | t
  · simp [BitVec.of_length_zero]
    have hNonneg : 0 ≤ (2 : Int) ^ (W - 1) := Int.pow_nonneg (by decide)
    have hPos : 0 < (2 : Int) ^ (W - 1) := Int.pow_pos (by decide)
    exact ⟨hNonneg, hPos⟩
  rcases U with _ | u
  · simp [BitVec.of_length_zero]
    have hNonneg : 0 ≤ (2 : Int) ^ (W - 1) := Int.pow_nonneg (by decide)
    have hPos : 0 < (2 : Int) ^ (W - 1) := Int.pow_pos (by decide)
    exact ⟨hNonneg, hPos⟩
  have hx0 : (0 : Int) ≤ x.toNat := Int.natCast_nonneg _
  have hxHiNat := x.isLt
  have hxHi : (x.toNat : Int) < (2 : Int) ^ (t + 1) := by exact_mod_cast hxHiNat
  have haLo := BitVec.le_two_mul_toInt (x := a)
  have haHi := BitVec.two_mul_toInt_lt (x := a)
  have hPowU : (2 : Int) ^ (u + 1) = 2 * (2 : Int) ^ u := by
    rw [Int.pow_succ]
    omega
  rw [hPowU] at haLo haHi
  have hPowCastU : ((2 ^ u : Nat) : Int) = (2 : Int) ^ u := by norm_cast
  have haAbs : a.toInt.natAbs ≤ 2 ^ u := by
    apply Int.ofNat_le.1
    rw [hPowCastU]
    by_cases ha : 0 ≤ a.toInt
    · rw [Int.natAbs_of_nonneg ha]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  have hxAbs : ((x.toNat : Int).natAbs) < 2 ^ (t + 1) := by
    simpa using hxHiNat
  have hMulAbs : ((x.toNat : Int) * a.toInt).natAbs <
      2 ^ (t + u + 1) := by
    rw [Int.natAbs_mul]
    by_cases ha0 : a.toInt.natAbs = 0
    · simp [ha0, Nat.two_pow_pos]
    · have h1 := Nat.mul_lt_mul_of_pos_right hxAbs (Nat.pos_of_ne_zero ha0)
      have h2 := Nat.mul_le_mul_left (2 ^ (t + 1)) haAbs
      have hPow : 2 ^ (t + 1) * 2 ^ u = 2 ^ (t + u + 1) := by
        rw [← Nat.pow_add]
        rw [show t + 1 + u = t + u + 1 by omega]
      rw [hPow] at h2
      exact Nat.lt_of_lt_of_le h1 h2
  have hTargetNat : 2 ^ (t + u + 1) ≤ 2 ^ (W - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hMulAbsTarget : ((x.toNat : Int) * a.toInt).natAbs < 2 ^ (W - 1) :=
    Nat.lt_of_lt_of_le hMulAbs hTargetNat
  have hAbsCast :
      (((((x.toNat : Int) * a.toInt).natAbs) : Nat) : Int) <
        (2 : Int) ^ (W - 1) := by
    exact_mod_cast hMulAbsTarget
  have hNatAbsBounds := Int.natAbs_eq ((x.toNat : Int) * a.toInt)
  rcases hNatAbsBounds with hPos | hNeg
  · rw [hPos]
    constructor <;> omega
  · rw [hNeg]
    constructor <;> omega

private theorem bitvec_sub_ne_zero_iff {W : Nat} (x y : BitVec W) :
    y - x ≠ 0#W ↔ y ≠ x := by
  constructor
  · intro hSub hEq
    subst y
    exact hSub (by simp)
  · intro hNe hSub
    have hEq : y = x := by
      have h := (BitVec.sub_eq_iff_eq_add).mp hSub
      simpa using h
    exact hNe hEq

private theorem bitvec_toInt_ne_iff {W : Nat} (x y : BitVec W) :
    x.toInt ≠ y.toInt ↔ x ≠ y :=
  not_congr BitVec.toInt_inj

private theorem bitvec_toInt_ne_zero_iff {W : Nat} (x : BitVec W) :
    x.toInt ≠ 0 ↔ x ≠ 0#W := by
  simpa only [BitVec.toInt_zero] using bitvec_toInt_ne_iff x 0#W

private theorem bitvec_natcast_ne_iff {W : Nat} (x y : BitVec W) :
    (x.toNat : Int) ≠ (y.toNat : Int) ↔ x ≠ y := by
  constructor
  · intro hxy hEq
    subst y
    exact hxy rfl
  · intro hxy hNat
    apply hxy
    apply BitVec.eq_of_toNat_eq
    exact_mod_cast hNat

private theorem signed_bitvec_mult_slt_iff
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    (y.signExtend W * a.signExtend W).slt
        (x.signExtend W * a.signExtend W) ↔
      y ≠ x ∧ a ≠ 0#U ∧
        ((y.slt x) = ((0#U).slt a)) := by
  have hyFit := signed_product_fits hWPos hWidth y a
  have hxFit := signed_product_fits hWPos hWidth x a
  have hyProd :
      (y.signExtend W * a.signExtend W).toInt = y.toInt * a.toInt := by
    change (BitVec.ofInt W y.toInt * BitVec.ofInt W a.toInt).toInt = _
    rw [← BitVec.ofInt_mul]
    exact BitVec.toInt_ofInt_eq_self hWPos hyFit.1 hyFit.2
  have hxProd :
      (x.signExtend W * a.signExtend W).toInt = x.toInt * a.toInt := by
    change (BitVec.ofInt W x.toInt * BitVec.ofInt W a.toInt).toInt = _
    rw [← BitVec.ofInt_mul]
    exact BitVec.toInt_ofInt_eq_self hWPos hxFit.1 hxFit.2
  rw [BitVec.slt_iff_toInt_lt, hyProd, hxProd,
    mul_lt_mul_characterization]
  simp only [BitVec.slt_eq_decide, BitVec.toInt_zero, decide_eq_decide,
    bitvec_toInt_ne_iff, bitvec_toInt_ne_zero_iff]

private theorem unsigned_bitvec_mult_slt_iff
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    (y.zeroExtend W * a.signExtend W).slt
        (x.zeroExtend W * a.signExtend W) ↔
      y ≠ x ∧ a ≠ 0#U ∧
        ((y.ult x) = ((0#U).slt a)) := by
  have hyFit := unsigned_signed_product_fits hWPos hWidth y a
  have hxFit := unsigned_signed_product_fits hWPos hWidth x a
  have hyProd :
      (y.zeroExtend W * a.signExtend W).toInt = (y.toNat : Int) * a.toInt := by
    have hyZero : y.zeroExtend W = BitVec.ofInt W (y.toNat : Int) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.zeroExtend_eq_setWidth,
        BitVec.toNat_setWidth_of_le (b := y) (w' := W) (by omega)]
      have hPow : (2 : Nat) ^ T ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      rw [ofInt_toNat_canonical W (y.toNat : Int)
        (Int.natCast_nonneg _)
        (by exact_mod_cast Nat.lt_of_lt_of_le y.isLt hPow)]
      simp
    rw [hyZero]
    change (BitVec.ofInt W (y.toNat : Int) * BitVec.ofInt W a.toInt).toInt = _
    rw [← BitVec.ofInt_mul]
    exact BitVec.toInt_ofInt_eq_self hWPos hyFit.1 hyFit.2
  have hxProd :
      (x.zeroExtend W * a.signExtend W).toInt = (x.toNat : Int) * a.toInt := by
    have hxZero : x.zeroExtend W = BitVec.ofInt W (x.toNat : Int) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.zeroExtend_eq_setWidth,
        BitVec.toNat_setWidth_of_le (b := x) (w' := W) (by omega)]
      have hPow : (2 : Nat) ^ T ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      rw [ofInt_toNat_canonical W (x.toNat : Int)
        (Int.natCast_nonneg _)
        (by exact_mod_cast Nat.lt_of_lt_of_le x.isLt hPow)]
      simp
    rw [hxZero]
    change (BitVec.ofInt W (x.toNat : Int) * BitVec.ofInt W a.toInt).toInt = _
    rw [← BitVec.ofInt_mul]
    exact BitVec.toInt_ofInt_eq_self hWPos hxFit.1 hxFit.2
  rw [BitVec.slt_iff_toInt_lt, hyProd, hxProd,
    mul_lt_mul_characterization]
  simp only [BitVec.ult_eq_decide, BitVec.slt_eq_decide,
    BitVec.toInt_zero, decide_eq_decide]
  have hCastLt : ((y.toNat : Int) < x.toNat) = (y.toNat < x.toNat) := by
    exact propext Int.ofNat_lt
  rw [hCastLt]
  simp only [bitvec_natcast_ne_iff, bitvec_toInt_ne_zero_iff]

private theorem bvslt_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvslt
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (x.slt y) := by
  have hW0 : native_zleq 0 (W : Int) = true := by
    simpa [SmtEval.native_zleq] using Int.natCast_nonneg W
  have hWCast : (W : Int) = native_nat_to_int W := by
    simp [native_nat_to_int, SmtEval.native_nat_to_int]
  have hXCanon : native_zeq (x.toNat : Int)
      (native_mod_total (x.toNat : Int) (native_int_pow2 (W : Int))) = true := by
    rw [hWCast]
    rw [native_int_pow2_nat W]
    have hMod : (x.toNat : Int) % (2 ^ W : Nat) = x.toNat := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast x.isLt)
    simpa [SmtEval.native_zeq, SmtEval.native_mod_total] using hMod.symm
  have hYCanon : native_zeq (y.toNat : Int)
      (native_mod_total (y.toNat : Int) (native_int_pow2 (W : Int))) = true := by
    rw [hWCast]
    rw [native_int_pow2_nat W]
    have hMod : (y.toNat : Int) % (2 ^ W : Nat) = y.toNat := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast y.isLt)
    simpa [SmtEval.native_zeq, SmtEval.native_mod_total] using hMod.symm
  unfold __smtx_model_eval_bvslt
  rw [smtx_model_eval_bvsgt_binary_eq_uts_public hW0 hYCanon hXCanon]
  rw [native_binary_uts_eq_bitvec_toInt W (x.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt),
    native_binary_uts_eq_bitvec_toInt W (y.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast y.isLt)]
  rw [bitvec_ofInt_natCast_toNat, bitvec_ofInt_natCast_toNat]
  rfl

private theorem bvult_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvult
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (x.ult y) := by
  change SmtValue.Boolean (decide ((x.toNat : Int) < y.toNat)) = _
  congr 2
  exact propext Int.ofNat_lt

private theorem bvsub_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvsub
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Binary (W : Int) ((x - y).toNat : Int) := by
  change SmtValue.Binary (W : Int)
      (native_mod_total
        (native_zplus (x.toNat : Int)
          (native_mod_total (native_zneg (y.toNat : Int))
            (native_int_pow2 (W : Int))))
        (native_int_pow2 (W : Int))) = _
  congr 2
  have hWCast : (W : Int) = native_nat_to_int W := by
    simp [native_nat_to_int, SmtEval.native_nat_to_int]
  rw [hWCast]
  rw [native_int_pow2_nat W]
  simp only [SmtEval.native_zplus, SmtEval.native_zneg,
    SmtEval.native_mod_total]
  rw [Int.add_emod_emod]
  have hSub : x - y =
      BitVec.ofInt W ((x.toNat : Int) - (y.toNat : Int)) := by
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
      bitvec_ofInt_natCast_toNat, bitvec_ofInt_natCast_toNat,
      BitVec.sub_eq_add_neg]
  rw [hSub, BitVec.toNat_ofInt]
  have hPowPos : (0 : Int) < (2 ^ W : Nat) := by
    exact_mod_cast Nat.two_pow_pos W
  have hNonneg : 0 ≤ ((x.toNat : Int) + -(y.toNat : Int)) % (2 ^ W : Nat) :=
    Int.emod_nonneg _ (Int.ne_of_gt hPowPos)
  rw [Int.sub_eq_add_neg]
  rw [Int.toNat_of_nonneg hNonneg]
  norm_cast

private theorem zero_extend_val_bitvec_local
    (W K : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_model_eval_zero_extend (SmtValue.Numeral (K : Int))
        (SmtValue.Binary (W : Int) p) =
      SmtValue.Binary ((K + W : Nat) : Int)
        ((BitVec.ofInt W p).zeroExtend (K + W) |>.toNat : Int) := by
  have hWidth : (K : Int) + W = ((K + W : Nat) : Int) := by norm_cast
  have hPayload : (BitVec.ofInt W p).toNat = p.toNat :=
    ofInt_toNat_canonical W p hp0 hp1
  simp only [__smtx_model_eval_zero_extend, SmtEval.native_zplus,
    SmtEval.native_mod_total]
  rw [hWidth]
  congr 2
  rw [BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth_of_le (by omega), hPayload]
  exact (Int.toNat_of_nonneg hp0).symm

private theorem bvsgt_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvsgt
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (y.slt x) := by
  simpa [__smtx_model_eval_bvslt] using bvslt_bitvec_values y x

private theorem bvmul_bitvec_values_local {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvmul
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Binary (W : Int) ((x * y).toNat : Int) := by
  change SmtValue.Binary (W : Int)
      (native_mod_total
        (native_zmult (x.toNat : Int) (y.toNat : Int))
        (native_int_pow2 (W : Int))) = _
  congr 2

private theorem signed_mult_smt_values
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    __smtx_model_eval_eq
        (__smtx_model_eval_bvslt
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((y.signExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int))))
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((x.signExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int)))))
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval_eq
              (__smtx_model_eval_bvsub
                (SmtValue.Binary (T : Int) (y.toNat : Int))
                (SmtValue.Binary (T : Int) (x.toNat : Int)))
              (SmtValue.Binary (T : Int) ((0#T).toNat : Int))))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval_eq
                (SmtValue.Binary (U : Int) (a.toNat : Int))
                (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
            (__smtx_model_eval_and
              (__smtx_model_eval_eq
                (__smtx_model_eval_bvslt
                  (SmtValue.Binary (T : Int) (y.toNat : Int))
                  (SmtValue.Binary (T : Int) (x.toNat : Int)))
                (__smtx_model_eval_bvsgt
                  (SmtValue.Binary (U : Int) (a.toNat : Int))
                  (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
              (SmtValue.Boolean true)))) =
      SmtValue.Boolean true := by
  rw [bvmul_bitvec_values_local (a.signExtend W) 1#W]
  simp only [BitVec.mul_one]
  rw [bvmul_bitvec_values_local (y.signExtend W) (a.signExtend W)]
  rw [bvmul_bitvec_values_local (x.signExtend W) (a.signExtend W),
    bvslt_bitvec_values]
  rw [bvsub_bitvec_values, bvslt_bitvec_values, bvsgt_bitvec_values]
  simp [-BitVec.toNat_sub, __smtx_model_eval_eq, native_veq, __smtx_model_eval_not,
    __smtx_model_eval_and, native_and, native_not,
    bitvec_sub_ne_zero_iff,
    signed_bitvec_mult_slt_iff hWPos hWidth x y a]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq]
  have hSubNat : (y - x).toNat ≠ 0 ↔ y - x ≠ 0#T := by
    exact not_congr (by simpa using
      (BitVec.toNat_inj (x := y - x) (y := 0#T)))
  have hANat : a.toNat ≠ 0 ↔ a ≠ 0#U := by
    exact not_congr (by simpa using
      (BitVec.toNat_inj (x := a) (y := 0#U)))
  change
    (y.signExtend W * a.signExtend W).slt
        (x.signExtend W * a.signExtend W) = true ↔
      (y - x).toNat ≠ 0 ∧ a.toNat ≠ 0 ∧
        y.slt x = (0#U).slt a
  rw [hSubNat, hANat, bitvec_sub_ne_zero_iff]
  exact signed_bitvec_mult_slt_iff hWPos hWidth x y a

private theorem unsigned_mult_smt_values
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    __smtx_model_eval_eq
        (__smtx_model_eval_bvslt
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((y.zeroExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int))))
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((x.zeroExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int)))))
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval_eq
              (__smtx_model_eval_bvsub
                (SmtValue.Binary (T : Int) (y.toNat : Int))
                (SmtValue.Binary (T : Int) (x.toNat : Int)))
              (SmtValue.Binary (T : Int) ((0#T).toNat : Int))))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval_eq
                (SmtValue.Binary (U : Int) (a.toNat : Int))
                (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
            (__smtx_model_eval_and
              (__smtx_model_eval_eq
                (__smtx_model_eval_bvult
                  (SmtValue.Binary (T : Int) (y.toNat : Int))
                  (SmtValue.Binary (T : Int) (x.toNat : Int)))
                (__smtx_model_eval_bvsgt
                  (SmtValue.Binary (U : Int) (a.toNat : Int))
                  (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
              (SmtValue.Boolean true)))) =
      SmtValue.Boolean true := by
  rw [bvmul_bitvec_values_local (a.signExtend W) 1#W]
  simp only [BitVec.mul_one]
  rw [bvmul_bitvec_values_local (y.zeroExtend W) (a.signExtend W)]
  rw [bvmul_bitvec_values_local (x.zeroExtend W) (a.signExtend W),
    bvslt_bitvec_values]
  rw [bvsub_bitvec_values, bvult_bitvec_values, bvsgt_bitvec_values]
  simp [-BitVec.toNat_sub, __smtx_model_eval_eq, native_veq,
    __smtx_model_eval_not, __smtx_model_eval_and, native_and, native_not,
    bitvec_sub_ne_zero_iff,
    unsigned_bitvec_mult_slt_iff hWPos hWidth x y a]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq]
  have hSubNat : (y - x).toNat ≠ 0 ↔ y - x ≠ 0#T := by
    exact not_congr (by simpa using
      (BitVec.toNat_inj (x := y - x) (y := 0#T)))
  have hANat : a.toNat ≠ 0 ↔ a ≠ 0#U := by
    exact not_congr (by simpa using
      (BitVec.toNat_inj (x := a) (y := 0#U)))
  change
    (y.zeroExtend W * a.signExtend W).slt
        (x.zeroExtend W * a.signExtend W) = true ↔
      (y - x).toNat ≠ 0 ∧ a.toNat ≠ 0 ∧
        y.ult x = (0#U).slt a
  rw [hSubNat, hANat, bitvec_sub_ne_zero_iff]
  exact unsigned_bitvec_mult_slt_iff hWPos hWidth x y a

def bvMultSltSizePrem (size source : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) size)
    (Term.Apply (Term.UOp UserOp._at_bvsize) source)

def bvMultSltGePrem (amount size : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) amount) size))
    (Term.Boolean true)

def bvMultSltExt (unsigned : Bool) (amount x : Term) : Term :=
  Term.Apply
    (Term.UOp1 (if unsigned then UserOp1.zero_extend else UserOp1.sign_extend)
      amount) x

def bvMultSltRawTerm
    (unsigned : Bool) (x y a n m tn an : Term) : Term :=
  let zeroA := Term.Apply (Term.UOp1 UserOp1.int_to_bv an) (Term.Numeral 0)
  let xExt := bvMultSltExt unsigned n x
  let yExt := bvMultSltExt unsigned n y
  let aExt := Term.Apply (Term.UOp1 UserOp1.sign_extend m) a
  let aTimesOneX := __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.bvmul) aExt)
    (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof xExt))
  let aTimesOneY := __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.bvmul) aExt)
    (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof yExt))
  let lhs := __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.bvslt)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) yExt) aTimesOneY))
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) xExt) aTimesOneX)
  let order := if unsigned then UserOp.bvult else UserOp.bvslt
  let rhs :=
    Term.Apply (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x))
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv tn) (Term.Numeral 0)))))
      (Term.Apply (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) zeroA)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp order) y) x))
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) a) zeroA)))
          (Term.Boolean true)))))
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) lhs) rhs

def bvMultSltProgram
    (unsigned : Bool) (x y a n m tn an P1 P2 P3 P4 : Term) : Term :=
  if unsigned then
    __eo_prog_bv_mult_slt_mult_2 x y a n m tn an
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
  else
    __eo_prog_bv_mult_slt_mult_1 x y a n m tn an
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)

private theorem bv_mult_slt_program_canonical
    (unsigned : Bool) (x y a n m tn an : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> a ≠ Term.Stuck ->
    n ≠ Term.Stuck -> m ≠ Term.Stuck -> tn ≠ Term.Stuck -> an ≠ Term.Stuck ->
    bvMultSltProgram unsigned x y a n m tn an
        (bvMultSltSizePrem tn x) (bvMultSltSizePrem an a)
        (bvMultSltGePrem n tn) (bvMultSltGePrem m an) =
      bvMultSltRawTerm unsigned x y a n m tn an := by
  intro hX hY hA hN hM hTn hAn
  cases unsigned with
  | false =>
      unfold bvMultSltProgram bvMultSltSizePrem bvMultSltGePrem
      rw [__eo_prog_bv_mult_slt_mult_1.eq_8 x y a n m tn an
        tn x an a n tn m an hX hY hA hN hM hTn hAn]
      simp [bvMultSltRawTerm, bvMultSltExt, __eo_requires, __eo_and,
        __eo_eq, native_ite, native_teq, native_not, native_and,
        hX, hY, hA, hN, hM, hTn, hAn]
  | true =>
      unfold bvMultSltProgram bvMultSltSizePrem bvMultSltGePrem
      rw [__eo_prog_bv_mult_slt_mult_2.eq_8 x y a n m tn an
        tn x an a n tn m an hX hY hA hN hM hTn hAn]
      simp [bvMultSltRawTerm, bvMultSltExt, __eo_requires, __eo_and,
        __eo_eq, native_ite, native_teq, native_not, native_and,
        hX, hY, hA, hN, hM, hTn, hAn]
