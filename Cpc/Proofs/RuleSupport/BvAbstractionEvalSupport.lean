module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Eo SmtEval Smtm

namespace BvAbstraction

def bvValue {w : Nat} (x : BitVec w) : SmtValue :=
  SmtValue.Binary (native_nat_to_int w) x.toNat

theorem native_mod_pow2_eq_toNat_ofInt (w : Nat) (n : Int) :
    native_mod_total n (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n).toNat : Int) := by
  rw [native_int_pow2_nat]
  change n % (2 ^ w : Int) = ((BitVec.ofInt w n).toNat : Int)
  rw [BitVec.toNat_ofInt]
  have hp : 0 < (2 ^ w : Int) := by exact_mod_cast Nat.two_pow_pos w
  exact (Int.toNat_of_nonneg (Int.emod_nonneg n (Int.ne_of_gt hp))).symm

theorem ofInt_natCast_toNat {w : Nat} (x : BitVec w) :
    BitVec.ofInt w (x.toNat : Int) = x := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp

theorem eval_bvmul_bvValue {w : Nat} (x y : BitVec w) :
    __smtx_model_eval_bvmul (bvValue x) (bvValue y) = bvValue (x * y) := by
  simp only [bvValue, __smtx_model_eval_bvmul]
  rw [native_mod_pow2_eq_toNat_ofInt]
  simp [native_zmult, BitVec.ofInt_mul, ofInt_natCast_toNat]

theorem eval_bvadd_bvValue {w : Nat} (x y : BitVec w) :
    __smtx_model_eval_bvadd (bvValue x) (bvValue y) = bvValue (x + y) := by
  simp only [bvValue, __smtx_model_eval_bvadd]
  rw [native_mod_pow2_eq_toNat_ofInt]
  simp [native_zplus, BitVec.ofInt_add, ofInt_natCast_toNat]

theorem eval_bvneg_bvValue {w : Nat} (x : BitVec w) :
    __smtx_model_eval_bvneg (bvValue x) = bvValue (-x) := by
  simp only [bvValue, __smtx_model_eval_bvneg]
  rw [native_mod_pow2_eq_toNat_ofInt]
  simp [native_zneg, BitVec.ofInt_neg, ofInt_natCast_toNat]

theorem eval_bvnot_bvValue {w : Nat} (x : BitVec w) :
    __smtx_model_eval_bvnot (bvValue x) = bvValue (~~~x) := by
  have hp0 : (0 : Int) ≤ x.toNat := Int.natCast_nonneg _
  have hp1 : (x.toNat : Int) < (2 : Int) ^ w := by exact_mod_cast x.isLt
  have hraw0 : 0 ≤ (2 : Int) ^ w - ((x.toNat : Int) + 1) := by omega
  have hraw1 : (2 : Int) ^ w - ((x.toNat : Int) + 1) < (2 : Int) ^ w := by omega
  simp only [bvValue, __smtx_model_eval_bvnot, native_mod_total,
    native_binary_not, native_zplus, native_zneg]
  rw [native_int_pow2_nat]
  rw [show (2 : Int) ^ w + -((x.toNat : Int) + 1) =
      (2 : Int) ^ w - ((x.toNat : Int) + 1) by omega]
  rw [Int.emod_eq_of_lt hraw0 hraw1]
  congr 2
  simp only [BitVec.toNat_not]
  have hle : x.toNat + 1 ≤ 2 ^ w := by omega
  have hpCast : (↑(2 ^ w : Nat) : Int) = (2 : Int) ^ w := by norm_cast
  calc
    (2 : Int) ^ w - ((x.toNat : Int) + 1) =
        (↑(2 ^ w : Nat) : Int) - ↑(x.toNat + 1) := by rw [hpCast]; norm_cast
    _ = ↑(2 ^ w - (x.toNat + 1) : Nat) := (Int.ofNat_sub hle).symm
    _ = ↑(2 ^ w - 1 - x.toNat : Nat) := by
      rw [Nat.sub_sub, Nat.add_comm]

theorem eval_bvand_bvValue {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    __smtx_model_eval_bvand (bvValue x) (bvValue y) = bvValue (x &&& y) := by
  simp only [bvValue, __smtx_model_eval_bvand]
  congr 1
  rw [native_mod_pow2_eq_toNat_ofInt]
  norm_cast
  apply congrArg BitVec.toNat
  have hraw : native_binary_and (native_nat_to_int w) x.toNat y.toNat =
      (x &&& y).toInt := by
    rw [native_binary_and]
    simp only [native_nat_to_int]
    simp only [native_zeq]
    simp [native_ite, native_piand]
    rw [if_neg (Nat.ne_of_gt hw), BitVec.toInt_eq_toNat_bmod]
    congr 2
  rw [hraw, BitVec.ofInt_toInt]

theorem eval_bvor_bvValue {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    __smtx_model_eval_bvor (bvValue x) (bvValue y) = bvValue (x ||| y) := by
  simp only [bvValue, __smtx_model_eval_bvor]
  congr 1
  rw [native_mod_pow2_eq_toNat_ofInt]
  norm_cast
  apply congrArg BitVec.toNat
  have hraw : native_binary_or (native_nat_to_int w) x.toNat y.toNat =
      (x ||| y).toInt := by
    rw [native_binary_or]
    simp only [native_nat_to_int]
    simp only [native_zeq]
    simp [native_ite, native_pior]
    rw [if_neg (Nat.ne_of_gt hw), BitVec.toInt_eq_toNat_bmod]
    congr 2
  rw [hraw, BitVec.ofInt_toInt]

theorem eval_bvxor_bvValue {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    __smtx_model_eval_bvxor (bvValue x) (bvValue y) = bvValue (x ^^^ y) := by
  simp only [bvValue, __smtx_model_eval_bvxor]
  congr 1
  rw [native_mod_pow2_eq_toNat_ofInt]
  norm_cast
  apply congrArg BitVec.toNat
  have hraw : native_binary_xor (native_nat_to_int w) x.toNat y.toNat =
      (x ^^^ y).toInt := by
    rw [native_binary_xor]
    simp only [native_nat_to_int]
    simp only [native_zeq]
    simp [native_ite, native_pixor]
    rw [if_neg (Nat.ne_of_gt hw), BitVec.toInt_eq_toNat_bmod]
    congr 2
  rw [hraw, BitVec.ofInt_toInt]

theorem eval_bvudiv_bvValue {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    __smtx_model_eval_bvudiv (bvValue x) (bvValue y) =
      bvValue (x.smtUDiv y) := by
  simp only [bvValue, __smtx_model_eval_bvudiv]
  rw [native_mod_pow2_eq_toNat_ofInt]
  by_cases hy : y = 0#w
  · subst y
    simp [BitVec.smtUDiv, native_ite, native_zeq, native_binary_max,
      native_int_pow2_nat]
    have hp : (0 : Int) < 2 ^ w := by exact_mod_cast Nat.two_pow_pos w
    rw [show native_zplus ((2 : Int) ^ w) (native_zneg 1) =
        (2 : Int) ^ w - 1 by rfl]
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.max_eq_left (by omega)]
    norm_cast
    exact (Int.ofNat_sub (Nat.two_pow_pos w)).symm
  · have hyn : y.toNat ≠ 0 := BitVec.toNat_ne_iff_ne.mpr hy
    simp [BitVec.smtUDiv, hy, native_ite, native_zeq, hyn, native_div_total,
      BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.toNat_udiv]
    rw [← Int.natCast_ediv]
    have hlt : x.toNat / y.toNat < 2 ^ w :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hlt),
      Int.max_eq_left (Int.natCast_nonneg _)]

theorem eval_bvurem_bvValue {w : Nat} (hw : 0 < w) (x y : BitVec w) :
    __smtx_model_eval_bvurem (bvValue x) (bvValue y) = bvValue (x % y) := by
  simp only [bvValue, __smtx_model_eval_bvurem]
  rw [native_mod_pow2_eq_toNat_ofInt]
  by_cases hy : y = 0#w
  · subst y
    simp [native_ite, native_zeq]
  · have hyn : y.toNat ≠ 0 := BitVec.toNat_ne_iff_ne.mpr hy
    simp [native_ite, native_zeq, hyn, native_mod_total,
      BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.toNat_umod]
    rw [← Int.natCast_emod]
    have hrlt : x.toNat % y.toNat < 2 ^ w :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hrlt),
      Int.max_eq_left (Int.natCast_nonneg _)]

theorem eval_as_bvValue (M : SmtModel) (hM : model_total_typed M)
    (a : Term) (w : Nat)
    (hty : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    ∃ x : BitVec w, __smtx_model_eval M (__eo_to_smt a) = bvValue x := by
  have hnn : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [hty]
    simp
  have hpres := type_preservation M hM (__eo_to_smt a) hnn
  rw [hty] at hpres
  obtain ⟨n, hn⟩ := bitvec_value_canonical hpres
  let x : BitVec w := BitVec.ofInt w n
  refine ⟨x, ?_⟩
  rw [hn] at hpres
  rw [hn]
  dsimp [bvValue, x]
  have hcanon := bitvec_payload_canonical hpres
  simp only [native_zeq, decide_eq_true_eq] at hcanon
  congr 1
  exact hcanon.trans (native_mod_pow2_eq_toNat_ofInt w n)

end BvAbstraction
