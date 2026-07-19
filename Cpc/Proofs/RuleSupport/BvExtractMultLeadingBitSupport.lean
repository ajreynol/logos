module

public import Cpc.Proofs.RuleSupport.BvExtractConcatSupport
import all Cpc.Proofs.RuleSupport.BvExtractConcatSupport
public import Cpc.Proofs.RuleSupport.BvMultSltMultSupport
import all Cpc.Proofs.RuleSupport.BvMultSltMultSupport

open Eo
open SmtEval
open Smtm

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

def bvExtractMultLeadingZeros (i n : Nat) : Nat :=
  if i = 0 then n else n - (i.log2 + 1)

private theorem prefix_payload_bound
    {i n tail z : Nat} (hi : i < 2 ^ n) (hz : z < 2 ^ tail) :
    i * 2 ^ tail + z <
      2 ^ (n + tail - bvExtractMultLeadingZeros i n) := by
  unfold bvExtractMultLeadingZeros
  by_cases hi0 : i = 0
  · subst i
    simp
    have hSub : n + tail - n = tail := by omega
    simpa [hSub] using hz
  · rw [if_neg hi0]
    have hLogLt : i.log2 < n := (Nat.log2_lt hi0).2 hi
    have hiPow : i < 2 ^ (i.log2 + 1) := Nat.lt_log2_self
    have hSum : i * 2 ^ tail + z <
        2 ^ (i.log2 + 1) * 2 ^ tail := by
      calc
        i * 2 ^ tail + z < i * 2 ^ tail + 2 ^ tail :=
          Nat.add_lt_add_left hz _
        _ = (i + 1) * 2 ^ tail := by
          rw [Nat.add_mul]
          simp
        _ ≤ 2 ^ (i.log2 + 1) * 2 ^ tail :=
          Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hiPow)
    have hExp : n + tail - (n - (i.log2 + 1)) = i.log2 + 1 + tail := by
      omega
    rw [hExp, Nat.pow_add]
    exact hSum

theorem extract_mult_leading_bit_core
    {W WX WY xi yi xv yv low len : Nat}
    (hWX : WX ≤ W) (hWY : WY ≤ W)
    (hXi : xi < 2 ^ (W - WX)) (hYi : yi < 2 ^ (W - WY))
    (hXv : xv < 2 ^ WX) (hYv : yv < 2 ^ WY)
    (hLow :
      (2 * W -
        (bvExtractMultLeadingZeros xi (W - WX) +
          bvExtractMultLeadingZeros yi (W - WY))) ≤ low) :
    (((BitVec.ofNat W
        ((xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv))).extractLsb'
      low len).toNat) = 0 := by
  let zx := bvExtractMultLeadingZeros xi (W - WX)
  let zy := bvExtractMultLeadingZeros yi (W - WY)
  have hX : xi * 2 ^ WX + xv < 2 ^ (W - zx) := by
    have := prefix_payload_bound hXi hXv
    simpa [zx, Nat.sub_add_cancel hWX] using this
  have hY : yi * 2 ^ WY + yv < 2 ^ (W - zy) := by
    have := prefix_payload_bound hYi hYv
    simpa [zy, Nat.sub_add_cancel hWY] using this
  have hZx : zx ≤ W := by
    have : zx ≤ W - WX := by
      unfold zx bvExtractMultLeadingZeros
      split <;> omega
    exact Nat.le_trans this (Nat.sub_le W WX)
  have hZy : zy ≤ W := by
    have : zy ≤ W - WY := by
      unfold zy bvExtractMultLeadingZeros
      split <;> omega
    exact Nat.le_trans this (Nat.sub_le W WY)
  have hProd :
      (xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv) <
        2 ^ (2 * W - (zx + zy)) := by
    have hMul :
        (xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv) <
          2 ^ (W - zx) * 2 ^ (W - zy) := by
      by_cases hy0 : yi * 2 ^ WY + yv = 0
      · rw [hy0, Nat.mul_zero]
        exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      · exact Nat.lt_trans
          (Nat.mul_lt_mul_of_pos_right hX (Nat.pos_of_ne_zero hy0))
          (Nat.mul_lt_mul_of_pos_left hY (Nat.two_pow_pos _))
    have hExp : (W - zx) + (W - zy) = 2 * W - (zx + zy) := by omega
    rw [← Nat.pow_add, hExp] at hMul
    exact hMul
  have hProdLow :
      (xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv) < 2 ^ low := by
    exact Nat.lt_of_lt_of_le hProd (Nat.pow_le_pow_right (by decide) (by
      simpa [zx, zy] using hLow))
  have hModLow :
      (BitVec.ofNat W
        ((xi * 2 ^ WX + xv) * (yi * 2 ^ WY + yv))).toNat < 2 ^ low := by
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hProdLow
  simp only [BitVec.extractLsb'_toNat]
  rw [Nat.shiftRight_eq_zero _ _ hModLow]
  simp

private def extractLeadApp1 (op x : Term) : Term := Term.Apply op x
private def extractLeadApp2 (op x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y
private def extractLeadApp3 (op x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply op x) y) z

def bvExtractMultLeadingWidthPrem (xin x : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.gt)
      (extractLeadApp2 (Term.UOp UserOp.plus) xin
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (extractLeadApp1 (Term.UOp UserOp._at_bvsize) x)
          (Term.Numeral 0)))
      (Term.Numeral 64))
    (Term.Boolean true)

def bvExtractMultLeadingNonnegPrem (i : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.geq) i (Term.Numeral 0))
    (Term.Boolean true)

def bvExtractMultLeadingRangePrem (i n : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.lt) i
      (extractLeadApp1 (Term.UOp UserOp.int_pow2) n))
    (Term.Boolean true)

def bvExtractMultLeadingZerosTerm (i n : Term) : Term :=
  extractLeadApp3 (Term.UOp UserOp.ite)
    (extractLeadApp2 (Term.UOp UserOp.eq) i (Term.Numeral 0)) n
    (extractLeadApp2 (Term.UOp UserOp.neg) n
      (extractLeadApp2 (Term.UOp UserOp.plus) (Term.Numeral 1)
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (extractLeadApp1 (Term.UOp UserOp.int_log2) i)
          (Term.Numeral 0))))

def bvExtractMultLeadingLowPrem
    (low xi xin x yi yin : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.leq)
      (extractLeadApp2 (Term.UOp UserOp.neg)
        (extractLeadApp2 (Term.UOp UserOp.mult) (Term.Numeral 2)
          (extractLeadApp2 (Term.UOp UserOp.mult)
            (extractLeadApp2 (Term.UOp UserOp.plus) xin
              (extractLeadApp2 (Term.UOp UserOp.plus)
                (extractLeadApp1 (Term.UOp UserOp._at_bvsize) x)
                (Term.Numeral 0)))
            (Term.Numeral 1)))
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (bvExtractMultLeadingZerosTerm xi xin)
          (extractLeadApp2 (Term.UOp UserOp.plus)
            (bvExtractMultLeadingZerosTerm yi yin) (Term.Numeral 0))))
      low)
    (Term.Boolean true)

private def bvExtractMultLeadingZerosRefs
    (iCond nThen nSub iLog : Term) : Term :=
  extractLeadApp3 (Term.UOp UserOp.ite)
    (extractLeadApp2 (Term.UOp UserOp.eq) iCond (Term.Numeral 0)) nThen
    (extractLeadApp2 (Term.UOp UserOp.neg) nSub
      (extractLeadApp2 (Term.UOp UserOp.plus) (Term.Numeral 1)
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (extractLeadApp1 (Term.UOp UserOp.int_log2) iLog)
          (Term.Numeral 0))))

private def bvExtractMultLeadingLowPremRefs
    (low xin x xiCond xinThen xinSub xiLog yiCond yinThen yinSub yiLog : Term) :
    Term :=
  extractLeadApp2 (Term.UOp UserOp.eq)
    (extractLeadApp2 (Term.UOp UserOp.leq)
      (extractLeadApp2 (Term.UOp UserOp.neg)
        (extractLeadApp2 (Term.UOp UserOp.mult) (Term.Numeral 2)
          (extractLeadApp2 (Term.UOp UserOp.mult)
            (extractLeadApp2 (Term.UOp UserOp.plus) xin
              (extractLeadApp2 (Term.UOp UserOp.plus)
                (extractLeadApp1 (Term.UOp UserOp._at_bvsize) x)
                (Term.Numeral 0)))
            (Term.Numeral 1)))
        (extractLeadApp2 (Term.UOp UserOp.plus)
          (bvExtractMultLeadingZerosRefs xiCond xinThen xinSub xiLog)
          (extractLeadApp2 (Term.UOp UserOp.plus)
            (bvExtractMultLeadingZerosRefs yiCond yinThen yinSub yiLog)
            (Term.Numeral 0))))
      low)
    (Term.Boolean true)

def bvExtractMultLeadingResultWidthPrem (w high low : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.eq) w
    (extractLeadApp2 (Term.UOp UserOp.plus) (Term.Numeral 1)
      (extractLeadApp2 (Term.UOp UserOp.plus)
        (extractLeadApp2 (Term.UOp UserOp.neg) high low)
        (Term.Numeral 0)))

def bvExtractMultLeadingOperand (i n tail : Term) : Term :=
  extractLeadApp2 (Term.UOp UserOp.concat)
    (extractLeadApp1 (Term.UOp1 UserOp1.int_to_bv n) i)
    (extractLeadApp2 (Term.UOp UserOp.concat) tail (Term.Binary 0 0))

def bvExtractMultLeadingRaw
    (high low xi xin x yi yin y w : Term) : Term :=
  let xFull := bvExtractMultLeadingOperand xi xin x
  let yFull := bvExtractMultLeadingOperand yi yin y
  let product := extractLeadApp2 (Term.UOp UserOp.bvmul) xFull
    (extractLeadApp2 (Term.UOp UserOp.bvmul) yFull
      (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof xFull)))
  extractLeadApp2 (Term.UOp UserOp.eq)
    (Term.Apply (Term.UOp2 UserOp2.extract high low) product)
    (extractLeadApp1 (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0))

def bvExtractMultLeadingProgram
    (high low xi xin x yi yin y w P1 P2 P3 P4 P5 P6 P7 : Term) : Term :=
  __eo_prog_bv_extract_mult_leading_bit high low xi xin x yi yin y w
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
    (Proof.pf P5) (Proof.pf P6) (Proof.pf P7)
