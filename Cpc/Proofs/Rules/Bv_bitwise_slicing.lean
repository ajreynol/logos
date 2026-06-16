import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

/-!
Foundation lemmas for `bv_bitwise_slicing` soundness.

The rule rewrites a bitwise term `(f c a)` (f ∈ {bvand, bvor, bvxor}, `c` a constant
operand) into a concatenation of per-slice bitwise ops.  The key fact is that a bitwise
op distributes over any contiguous split of the bit range; everything below is the
machinery for that, lifted from `BitVec`/`Int` down to the `Nat` bit level.
-/

-- For a width-`w` bitvector, reducing its signed `toInt` mod `2^w` recovers `toNat`.
private theorem bv_toInt_emod (w : Nat) (x : BitVec w) :
    x.toInt % (2^w : Int) = (x.toNat : Int) := by
  have hc : ((2:Int)^w) = ((2^w : Nat):Int) := by norm_cast
  rw [hc, BitVec.toInt_eq_toNat_bmod, Int.bmod_emod]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast x.isLt)

-- `ofInt` of a canonical (in-range, nonneg) integer keeps the same `toNat`.
private theorem ofInt_toNat_canonical (w : Nat) (c : Int) (h0 : 0 ≤ c) (h1 : c < 2^w) :
    (BitVec.ofInt w c).toNat = c.toNat := by
  rw [BitVec.toNat_ofInt]; congr 1
  exact Int.emod_eq_of_lt h0 (by exact_mod_cast h1)

private theorem natpow2_eq (w : Nat) : native_int_pow2 (↑w : Int) = (2:Int)^w := by
  have hwnn : ¬ ((↑w:Int) < 0) := by omega
  unfold native_int_pow2 native_zexp_total
  rw [if_neg hwnn, Int.toNat_natCast]

-- A bitwise Nat op commutes with division by `2^k` (selecting the high bits).
private theorem op_div2pow {f : Nat → Nat → Nat} {g : Bool → Bool → Bool}
    (hf : ∀ x y i, (f x y).testBit i = g (x.testBit i) (y.testBit i))
    (c a k : Nat) : (f c a) / 2^k = f (c / 2^k) (a / 2^k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, hf, hf, Nat.testBit_div_two_pow,
      Nat.testBit_div_two_pow]

-- A bitwise Nat op commutes with mod `2^k` (selecting the low bits).
private theorem op_mod2pow {f : Nat → Nat → Nat} {g : Bool → Bool → Bool}
    (hf : ∀ x y i, (f x y).testBit i = g (x.testBit i) (y.testBit i))
    (hff : g false false = false)
    (c a k : Nat) : (f c a) % 2^k = f (c % 2^k) (a % 2^k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, hf, hf, Nat.testBit_mod_two_pow,
      Nat.testBit_mod_two_pow]
  cases hd : decide (i < k) <;> simp [hff]

-- The core split identity: a bitwise op over the whole word equals the concat
-- (high * 2^k + low) of the op applied to the high and low parts.
private theorem op_split {f : Nat → Nat → Nat} {g : Bool → Bool → Bool}
    (hf : ∀ x y i, (f x y).testBit i = g (x.testBit i) (y.testBit i))
    (hff : g false false = false)
    (c a k : Nat) :
    f c a = f (c / 2^k) (a / 2^k) * 2^k + f (c % 2^k) (a % 2^k) := by
  rw [← op_div2pow hf, ← op_mod2pow hf hff, Nat.mul_comm (f c a / 2^k) (2^k)]
  exact (Nat.div_add_mod (f c a) (2^k)).symm

-- The model-level bitwise-op payloads, expressed as plain `Nat` bit operations.
private theorem bvand_payload (w : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^w) (ha0 : 0 ≤ an) (ha1 : an < 2^w) :
    native_mod_total (native_binary_and (↑w) cn an) (native_int_pow2 (↑w))
      = ((cn.toNat &&& an.toNat : Nat) : Int) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    rw [show ((2:Int)^0) = 1 from rfl] at hc1 ha1
    have hcn : cn = 0 := by omega
    have han : an = 0 := by omega
    subst cn; subst an; decide
  · have hne : native_zeq (↑w:Int) 0 = false := by simp [native_zeq]; omega
    have hand : native_binary_and (↑w) cn an
        = (BitVec.ofInt w cn &&& BitVec.ofInt w an).toInt := by
      simp only [native_binary_and, native_piand]; rw [hne, Int.toNat_natCast]; rfl
    have e1 : native_mod_total (native_binary_and (↑w) cn an) (native_int_pow2 ↑w)
        = (BitVec.ofInt w cn &&& BitVec.ofInt w an).toInt % (2:Int)^w := by
      rw [hand]; simp only [native_mod_total]; rw [natpow2_eq]
    rw [e1, bv_toInt_emod, BitVec.toNat_and,
        ofInt_toNat_canonical w cn hc0 hc1, ofInt_toNat_canonical w an ha0 ha1]

private theorem bvor_payload (w : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^w) (ha0 : 0 ≤ an) (ha1 : an < 2^w) :
    native_mod_total (native_binary_or (↑w) cn an) (native_int_pow2 (↑w))
      = ((cn.toNat ||| an.toNat : Nat) : Int) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    rw [show ((2:Int)^0) = 1 from rfl] at hc1 ha1
    have hcn : cn = 0 := by omega
    have han : an = 0 := by omega
    subst cn; subst an; decide
  · have hne : native_zeq (↑w:Int) 0 = false := by simp [native_zeq]; omega
    have hand : native_binary_or (↑w) cn an
        = (BitVec.ofInt w cn ||| BitVec.ofInt w an).toInt := by
      simp only [native_binary_or, native_pior]; rw [hne, Int.toNat_natCast]; rfl
    have e1 : native_mod_total (native_binary_or (↑w) cn an) (native_int_pow2 ↑w)
        = (BitVec.ofInt w cn ||| BitVec.ofInt w an).toInt % (2:Int)^w := by
      rw [hand]; simp only [native_mod_total]; rw [natpow2_eq]
    rw [e1, bv_toInt_emod, BitVec.toNat_or,
        ofInt_toNat_canonical w cn hc0 hc1, ofInt_toNat_canonical w an ha0 ha1]

private theorem bvxor_payload (w : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^w) (ha0 : 0 ≤ an) (ha1 : an < 2^w) :
    native_mod_total (native_binary_xor (↑w) cn an) (native_int_pow2 (↑w))
      = ((cn.toNat ^^^ an.toNat : Nat) : Int) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    rw [show ((2:Int)^0) = 1 from rfl] at hc1 ha1
    have hcn : cn = 0 := by omega
    have han : an = 0 := by omega
    subst cn; subst an; decide
  · have hne : native_zeq (↑w:Int) 0 = false := by simp [native_zeq]; omega
    have hand : native_binary_xor (↑w) cn an
        = (BitVec.ofInt w cn ^^^ BitVec.ofInt w an).toInt := by
      simp only [native_binary_xor, native_pixor]; rw [hne, Int.toNat_natCast]; rfl
    have e1 : native_mod_total (native_binary_xor (↑w) cn an) (native_int_pow2 ↑w)
        = (BitVec.ofInt w cn ^^^ BitVec.ofInt w an).toInt % (2:Int)^w := by
      rw [hand]; simp only [native_mod_total]; rw [natpow2_eq]
    rw [e1, bv_toInt_emod, BitVec.toNat_xor,
        ofInt_toNat_canonical w cn hc0 hc1, ofInt_toNat_canonical w an ha0 ha1]

/- ===== Value-level eval lemmas ===== -/

private theorem eval_num (M : SmtModel) (n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) = SmtValue.Numeral n := by
  show __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
  simp only [__smtx_model_eval]

private theorem eval_bin (M : SmtModel) (w n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Binary w n)) = SmtValue.Binary w n := by
  show __smtx_model_eval M (SmtTerm.Binary w n) = SmtValue.Binary w n
  simp only [__smtx_model_eval]

private theorem eval_extract (M : SmtModel) (X : Term) (hi lo w xn : Int)
    (hX : __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w xn) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral hi)
          (Term.Numeral lo)) X))
      = __smtx_model_eval_extract (SmtValue.Numeral hi) (SmtValue.Numeral lo)
          (SmtValue.Binary w xn) := by
  have ht : __eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral hi)
        (Term.Numeral lo)) X)
      = SmtTerm.extract (SmtTerm.Numeral hi) (SmtTerm.Numeral lo) (__eo_to_smt X) := rfl
  rw [ht]; simp only [__smtx_model_eval]; rw [hX]

private theorem eval_concat (M : SmtModel) (X Y : Term) (w1 n1 w2 n2 : Int)
    (hX : __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w1 n1)
    (hY : __smtx_model_eval M (__eo_to_smt Y) = SmtValue.Binary w2 n2) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) X) Y))
      = __smtx_model_eval_concat (SmtValue.Binary w1 n1) (SmtValue.Binary w2 n2) := by
  have ht : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) X) Y)
      = SmtTerm.concat (__eo_to_smt X) (__eo_to_smt Y) := rfl
  rw [ht]; simp only [__smtx_model_eval]; rw [hX, hY]

private theorem eval_bvand (M : SmtModel) (X Y : Term) (w1 n1 w2 n2 : Int)
    (hX : __smtx_model_eval M (__eo_to_smt X) = SmtValue.Binary w1 n1)
    (hY : __smtx_model_eval M (__eo_to_smt Y) = SmtValue.Binary w2 n2) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) X) Y))
      = __smtx_model_eval_bvand (SmtValue.Binary w1 n1) (SmtValue.Binary w2 n2) := by
  have ht : __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) X) Y)
      = SmtTerm.bvand (__eo_to_smt X) (__eo_to_smt Y) := rfl
  rw [ht]; simp only [__smtx_model_eval]; rw [hX, hY]

/- ===== Arithmetic computations on values ===== -/

private theorem nat_split_mod (D k m : Nat) (hkm : k ≤ m) :
    D % 2^m = ((D / 2^k) % 2^(m-k)) * 2^k + D % 2^k := by
  have hpow : (2:Nat)^m = 2^k * 2^(m-k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hpow, Nat.mod_mul, Nat.add_comm, Nat.mul_comm]

-- extract value, payload/width as casts of Nat ops.
private theorem extract_valN (W : Nat) (Xn : Int) (hi lo : Nat)
    (hX0 : 0 ≤ Xn) (hlo : lo ≤ hi + 1) :
    __smtx_model_eval_extract (SmtValue.Numeral ↑hi) (SmtValue.Numeral ↑lo)
        (SmtValue.Binary ↑W Xn)
      = SmtValue.Binary ↑(hi + 1 - lo) ↑((Xn.toNat / 2^lo) % 2^(hi + 1 - lo)) := by
  obtain ⟨N, rfl⟩ : ∃ N : Nat, Xn = (↑N : Int) := ⟨Xn.toNat, (Int.toNat_of_nonneg hX0).symm⟩
  simp only [__smtx_model_eval_extract, native_zplus, native_zneg,
    native_mod_total, native_binary_extract, native_div_total, Int.toNat_natCast]
  have hw : (↑hi + 1 + -↑lo : Int) = ↑(hi + 1 - lo) := by omega
  rw [hw, natpow2_eq lo, natpow2_eq (hi + 1 - lo),
      show ((2:Int)^lo) = ((2^lo:Nat):Int) from by norm_cast,
      show ((2:Int)^(hi+1-lo)) = ((2^(hi+1-lo):Nat):Int) from by norm_cast]
  norm_cast

private theorem bvand_valN (W : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (hc1 : cn < 2^W) (ha0 : 0 ≤ an) (ha1 : an < 2^W) :
    __smtx_model_eval_bvand (SmtValue.Binary ↑W cn) (SmtValue.Binary ↑W an)
      = SmtValue.Binary ↑W ↑(cn.toNat &&& an.toNat) := by
  simp only [__smtx_model_eval_bvand]
  rw [bvand_payload W cn an hc0 hc1 ha0 ha1]

private theorem concat_valN (w1 p1 w2 p2 : Nat) :
    __smtx_model_eval_concat (SmtValue.Binary ↑w1 ↑p1) (SmtValue.Binary ↑w2 ↑p2)
      = SmtValue.Binary ↑(w1 + w2) ↑((p1 * 2^w2 + p2) % 2^(w1 + w2)) := by
  simp only [__smtx_model_eval_concat, native_zplus, native_mod_total,
    native_binary_concat, native_zmult]
  have hw : (↑w1 + ↑w2 : Int) = ↑(w1 + w2) := by norm_cast
  rw [hw, natpow2_eq w2, natpow2_eq (w1 + w2),
      show ((2:Int)^w2) = ((2^w2:Nat):Int) from by norm_cast,
      show ((2:Int)^(w1+w2)) = ((2^(w1+w2):Nat):Int) from by norm_cast]
  norm_cast

private theorem natCast_mod_lt (x m : Nat) : ((x % 2^m : Nat) : Int) < (2:Int)^m := by
  have h : x % 2^m < 2^m := Nat.mod_lt _ (Nat.two_pow_pos m)
  exact_mod_cast h

-- bvand of two equal-range slices, in closed Nat form.
private theorem slice_bvand (W : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an) (hi lo : Nat) (hlo : lo ≤ hi + 1) :
    __smtx_model_eval_bvand
        (__smtx_model_eval_extract (SmtValue.Numeral ↑hi) (SmtValue.Numeral ↑lo)
          (SmtValue.Binary ↑W cn))
        (__smtx_model_eval_extract (SmtValue.Numeral ↑hi) (SmtValue.Numeral ↑lo)
          (SmtValue.Binary ↑W an))
      = SmtValue.Binary ↑(hi + 1 - lo)
          ↑(((cn.toNat &&& an.toNat) / 2^lo) % 2^(hi + 1 - lo)) := by
  rw [extract_valN W cn hi lo hc0 hlo, extract_valN W an hi lo ha0 hlo,
      bvand_valN (hi + 1 - lo) _ _ (Int.natCast_nonneg _) (natCast_mod_lt _ _)
        (Int.natCast_nonneg _) (natCast_mod_lt _ _)]
  congr 2
  rw [Int.toNat_natCast, Int.toNat_natCast,
      ← op_mod2pow Nat.testBit_and (by decide), ← op_div2pow Nat.testBit_and]

-- The value-level split: bvand over [s:0] = concat of bvand over [s:k] and [k-1:0].
private theorem concat_split_bvand (W : Nat) (cn an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an) (s k : Nat) (hk1 : 1 ≤ k) (hks : k ≤ s + 1) :
    __smtx_model_eval_bvand
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s) (SmtValue.Numeral (0:Int))
          (SmtValue.Binary ↑W cn))
        (__smtx_model_eval_extract (SmtValue.Numeral ↑s) (SmtValue.Numeral (0:Int))
          (SmtValue.Binary ↑W an))
      = __smtx_model_eval_concat
          (__smtx_model_eval_bvand
            (__smtx_model_eval_extract (SmtValue.Numeral ↑s) (SmtValue.Numeral ↑k)
              (SmtValue.Binary ↑W cn))
            (__smtx_model_eval_extract (SmtValue.Numeral ↑s) (SmtValue.Numeral ↑k)
              (SmtValue.Binary ↑W an)))
          (__smtx_model_eval_bvand
            (__smtx_model_eval_extract (SmtValue.Numeral ↑(k-1)) (SmtValue.Numeral (0:Int))
              (SmtValue.Binary ↑W cn))
            (__smtx_model_eval_extract (SmtValue.Numeral ↑(k-1)) (SmtValue.Numeral (0:Int))
              (SmtValue.Binary ↑W an))) := by
  have e0 : ((0:Int)) = ((0:Nat):Int) := by norm_cast
  rw [e0, slice_bvand W cn an hc0 ha0 s 0 (by omega),
      slice_bvand W cn an hc0 ha0 s k (by omega),
      slice_bvand W cn an hc0 ha0 (k-1) 0 (by omega)]
  simp only [Nat.sub_zero, Nat.pow_zero, Nat.div_one]
  rw [Nat.sub_add_cancel hk1, concat_valN (s + 1 - k) _ k _, Nat.sub_add_cancel hks]
  congr 1
  norm_cast
  rw [← nat_split_mod (cn.toNat &&& an.toNat) k (s + 1) hks, Nat.mod_mod]

-- AND with the all-ones mask of width m is the identity on m-bit values.
private theorem bvand_nil (m : Nat) (pa : Int) (h0 : 0 ≤ pa) (h1 : pa < 2^m) :
    __smtx_model_eval_bvand (SmtValue.Binary ↑m pa) (SmtValue.Binary ↑m ↑(2^m - 1))
      = SmtValue.Binary ↑m pa := by
  have hpos : (1:Int) ≤ (2:Int)^m := by
    have : (1:Nat) ≤ 2^m := Nat.one_le_two_pow
    exact_mod_cast this
  have h2 : (2:Int)^m = ((2^m : Nat) : Int) := by norm_cast
  rw [bvand_valN m pa _ h0 h1 (by omega) (by omega)]
  congr 1
  have htoNat : ((2:Int)^m - 1).toNat = 2^m - 1 := by rw [h2]; omega
  rw [htoNat]
  have hpaN : pa.toNat < 2^m := by omega
  have hx : pa.toNat &&& (2^m - 1) = pa.toNat := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < m
    · simp [hi]
    · have hge : 2^m ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (by omega : pa.toNat < 2^i)]
      simp
  rw [hx, Int.toNat_of_nonneg h0]


private theorem requires_tt (X : Term) :
    __eo_requires (Term.Boolean true) (Term.Boolean true) X = X := by
  unfold __eo_requires
  simp only [native_teq, native_ite, native_not, decide_true, reduceIte, reduceCtorEq,
    Bool.not_false, decide_false]

-- The nil operand for the `bvand` slice [hi:lo] of the constant `c` (width W) reduces
-- to the all-ones literal of the slice width (needs the slice width ≤ 2^32 so `to_bin`
-- does not get stuck).
private theorem nil_term_bvand (W : Nat) (cn : Int) (hi lo : Nat)
    (hhiW : hi < W) (hlo : lo ≤ hi + 1)
    (hMle : ((hi + 1 - lo : Nat) : Int) ≤ 4294967296) :
    __eo_nil (Term.UOp UserOp.bvand)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))
      = Term.Binary ↑(hi + 1 - lo) ((2:Int)^(hi + 1 - lo) - 1) := by
  have hMeq : (↑hi - ↑lo + 1 : Int) = ↑(hi + 1 - lo) := by omega
  have hg1 : __eo_gt (__eo_add (Term.Numeral ↑lo) (Term.Numeral 1)) (Term.Numeral 0)
      = Term.Boolean true := by
    show Term.Boolean (native_zlt 0 (native_zplus (↑lo) 1)) = Term.Boolean true
    congr 1; show native_zlt 0 (native_zplus (↑lo) 1) = true
    unfold native_zlt; exact decide_eq_true (show (0:Int) < ↑lo + 1 by omega)
  have hg2 : __eo_gt (Term.Numeral ↑W) (Term.Numeral ↑hi) = Term.Boolean true := by
    show Term.Boolean (native_zlt (↑hi) (↑W)) = Term.Boolean true
    congr 1; show native_zlt (↑hi) (↑W) = true
    unfold native_zlt; exact decide_eq_true (by exact_mod_cast hhiW)
  have htype : __eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
        (Term.Numeral ↑lo)) (Term.Binary ↑W cn))
      = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (↑hi - ↑lo + 1)) := by
    show __eo_mk_apply (Term.UOp UserOp.BitVec)
        (__eo_requires (__eo_gt (__eo_add (Term.Numeral ↑lo) (Term.Numeral 1)) (Term.Numeral 0))
          (Term.Boolean true)
          (__eo_requires (__eo_gt (Term.Numeral ↑W) (Term.Numeral ↑hi)) (Term.Boolean true)
            (__eo_add (__eo_add (Term.Numeral ↑hi) (__eo_neg (Term.Numeral ↑lo))) (Term.Numeral 1)))) = _
    rw [hg1, hg2, requires_tt, requires_tt]
    show (Term.UOp UserOp.BitVec).Apply
        (Term.Numeral (native_zplus (native_zplus ↑hi (native_zneg ↑lo)) 1)) = _
    congr 2
  rw [htype]
  show __eo_not (__eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0)) = _
  have htobin : __eo_to_bin (Term.Numeral (↑hi - ↑lo + 1)) (Term.Numeral 0)
      = Term.Binary (↑hi - ↑lo + 1) 0 := by
    show native_ite (native_zleq (↑hi - ↑lo + 1) 4294967296)
        (__eo_mk_binary (↑hi - ↑lo + 1) 0) Term.Stuck = _
    rw [show native_zleq (↑hi - ↑lo + 1) 4294967296 = true from by
      unfold native_zleq; exact decide_eq_true (by rw [hMeq]; exact hMle)]
    show __eo_mk_binary (↑hi - ↑lo + 1) 0 = _
    show native_ite (native_zleq 0 (↑hi - ↑lo + 1))
        (Term.Binary (↑hi - ↑lo + 1) (native_mod_total 0 (native_int_pow2 (↑hi - ↑lo + 1)))) Term.Stuck = _
    rw [show native_zleq 0 (↑hi - ↑lo + 1) = true from by
      unfold native_zleq; exact decide_eq_true (by rw [hMeq]; exact_mod_cast Nat.zero_le _)]
    show Term.Binary (↑hi - ↑lo + 1) (native_mod_total 0 (native_int_pow2 (↑hi - ↑lo + 1)))
        = Term.Binary (↑hi - ↑lo + 1) 0
    congr 1
  rw [htobin]
  show Term.Binary (↑hi - ↑lo + 1)
      (native_mod_total (native_binary_not (↑hi - ↑lo + 1) 0)
        (native_int_pow2 (↑hi - ↑lo + 1))) = _
  rw [hMeq]
  congr 1
  simp only [native_binary_not, native_mod_total, native_zplus, native_zneg]
  rw [natpow2_eq (hi + 1 - lo)]
  have hge : (1:Int) ≤ (2:Int)^(hi+1-lo) := by
    have : (1:Nat) ≤ 2^(hi+1-lo) := Nat.one_le_two_pow
    exact_mod_cast this
  rw [show ((2:Int)^(hi+1-lo) + -(0+1)) = (2:Int)^(hi+1-lo) - 1 from by omega]
  exact Int.emod_eq_of_lt (by omega) (by omega)

-- eval of the full per-slice term: `bvand (extract c) (bvand (extract a) nil)` = the
-- closed-form `bvand` of the [hi:lo] slices of `c` and `a`.
private theorem slice_eval (M : SmtModel) (W : Nat) (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (hi lo : Nat) (hhiW : hi < W) (hlo : lo ≤ hi + 1)
    (hMle : ((hi + 1 - lo : Nat) : Int) ≤ 4294967296) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand)
          (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo))
            (Term.Binary ↑W cn)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand)
            (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo)) a))
            (__eo_nil (Term.UOp UserOp.bvand)
              (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
                (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))))))
      = SmtValue.Binary ↑(hi + 1 - lo)
          ↑(((cn.toNat &&& an.toNat) / 2^lo) % 2^(hi + 1 - lo)) := by
  have hCext : __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo))
        (Term.Binary ↑W cn)))
      = SmtValue.Binary ↑(hi + 1 - lo) ↑((cn.toNat / 2^lo) % 2^(hi + 1 - lo)) := by
    rw [eval_extract M (Term.Binary ↑W cn) ↑hi ↑lo ↑W cn (eval_bin M ↑W cn),
        extract_valN W cn hi lo hc0 hlo]
  have hAext : __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo)) a))
      = SmtValue.Binary ↑(hi + 1 - lo) ↑((an.toNat / 2^lo) % 2^(hi + 1 - lo)) := by
    rw [eval_extract M a ↑hi ↑lo ↑W an ha, extract_valN W an hi lo ha0 hlo]
  have hNil : __smtx_model_eval M (__eo_to_smt (__eo_nil (Term.UOp UserOp.bvand)
        (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
          (Term.Numeral ↑lo)) (Term.Binary ↑W cn)))))
      = SmtValue.Binary ↑(hi + 1 - lo) ((2:Int)^(hi + 1 - lo) - 1) := by
    rw [nil_term_bvand W cn hi lo hhiW hlo hMle]; exact eval_bin M _ _
  have hInner : __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand)
        (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi) (Term.Numeral ↑lo)) a))
        (__eo_nil (Term.UOp UserOp.bvand)
          (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑hi)
            (Term.Numeral ↑lo)) (Term.Binary ↑W cn))))))
      = SmtValue.Binary ↑(hi + 1 - lo) ↑((an.toNat / 2^lo) % 2^(hi + 1 - lo)) := by
    rw [eval_bvand M _ _ _ _ _ _ hAext hNil]
    exact bvand_nil (hi + 1 - lo) _ (Int.natCast_nonneg _) (natCast_mod_lt _ _)
  rw [eval_bvand M _ _ _ _ _ _ hCext hInner,
      bvand_valN (hi + 1 - lo) _ _ (Int.natCast_nonneg _) (natCast_mod_lt _ _)
        (Int.natCast_nonneg _) (natCast_mod_lt _ _)]
  congr 2
  rw [Int.toNat_natCast, Int.toNat_natCast,
      ← op_mod2pow Nat.testBit_and (by decide), ← op_div2pow Nat.testBit_and]

-- Closed-form split used by the induction's emit case.
private theorem closed_split (D s e : Nat) (hes : e ≤ s) :
    SmtValue.Binary ↑(s + 1) ↑(D % 2^(s + 1))
      = __smtx_model_eval_concat
          (SmtValue.Binary ↑(s - e) ↑((D / 2^(e + 1)) % 2^(s - e)))
          (SmtValue.Binary ↑(e + 1) ↑(D % 2^(e + 1))) := by
  rw [concat_valN (s - e) ((D / 2^(e + 1)) % 2^(s - e)) (e + 1) (D % 2^(e + 1))]
  congr 1
  · rw [show s + 1 = (s - e) + (e + 1) from by omega]
  · congr 1
    have hns := nat_split_mod D (e + 1) (s + 1) (by omega)
    rw [show (s + 1) - (e + 1) = s - e from by omega] at hns
    rw [show (s - e) + (e + 1) = s + 1 from by omega, ← hns, Nat.mod_mod]

private theorem concat_rempty (m p : Nat) (h : p < 2^m) :
    __smtx_model_eval_concat (SmtValue.Binary ↑m ↑p) (SmtValue.Binary 0 0)
      = SmtValue.Binary ↑m ↑p := by
  have h0 : native_int_pow2 (0:Int) = 1 := by rfl
  simp only [__smtx_model_eval_concat, native_zplus, native_mod_total,
    native_binary_concat, native_zmult]
  rw [show (↑m + (0:Int)) = ↑m from by omega, natpow2_eq m, h0]
  congr 1
  rw [show (↑p * (1:Int) + 0) = ↑p from by omega]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast h)

private theorem eo_mk_apply_ne {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

-- bs is a `@from_bools` list of length L (ending in `Binary 0 0`).
inductive FB : Term → Nat → Prop
  | nil : FB (Term.Binary 0 0) 0
  | cons (b bs' : Term) (L : Nat) (hb : b ≠ Term.Stuck) : FB bs' L →
      FB (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) b) bs') (L + 1)

private theorem base_eval (M : SmtModel) (W : Nat) (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (s : Nat) (hsW : s < W) (hWB : (↑W : Int) ≤ 4294967296) :
    __smtx_model_eval M (__eo_to_smt
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat)
        (__eo_mk_apply ((Term.UOp UserOp.bvand).Apply
            ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply (Term.Binary ↑W cn)))
          (__eo_mk_apply ((Term.UOp UserOp.bvand).Apply
              ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply a))
            (__eo_nil (Term.UOp UserOp.bvand)
              (__eo_typeof ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral 0)).Apply
                (Term.Binary ↑W cn)))))))
        (Term.Binary 0 0)))
      = SmtValue.Binary ↑(s + 1) ↑((cn.toNat &&& an.toNat) % 2^(s + 1)) := by
  have hMle : ((s + 1 - 0 : Nat) : Int) ≤ 4294967296 := by omega
  rw [show Term.Numeral (0:Int) = Term.Numeral ((0:Nat):Int) from by simp]
  have hNILne : __eo_nil (Term.UOp UserOp.bvand)
      (__eo_typeof ((Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ((0:Nat):Int))).Apply
        (Term.Binary ↑W cn))) ≠ Term.Stuck := by
    rw [nil_term_bvand W cn s 0 hsW (by omega) hMle]; intro h; cases h
  rw [eo_mk_apply_ne (by intro h; cases h) hNILne,
      eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h),
      eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h),
      eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)]
  rw [eval_concat M _ (Term.Binary 0 0) _ _ _ _
        (slice_eval M W cn a an hc0 ha0 ha s 0 hsW (by omega) hMle) (eval_bin M 0 0),
      concat_rempty (s + 1 - 0) (((cn.toNat &&& an.toNat) / 2^0) % 2^(s + 1 - 0))
        (Nat.mod_lt _ (Nat.two_pow_pos _))]
  simp only [Nat.sub_zero, Nat.pow_zero, Nat.div_one]

private theorem ne_stuck_of_eval_bin (M : SmtModel) (t : Term) (w n : Int)
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary w n) : t ≠ Term.Stuck := by
  intro hs; subst hs
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl,
      show __smtx_model_eval M SmtTerm.None = SmtValue.NotValue from by
        simp only [__smtx_model_eval]] at h
  cases h

private theorem emit_eval (M : SmtModel) (W : Nat) (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (hane : a ≠ Term.Stuck)
    (s L' : Nat) (hL's : L' ≤ s) (hsW : s < W) (hWB : (↑W : Int) ≤ 4294967296)
    (rest : Term)
    (hrest : __smtx_model_eval M (__eo_to_smt rest)
      = SmtValue.Binary ↑(L' + 1) ↑((cn.toNat &&& an.toNat) % 2^(L' + 1)))
    (hrestne : rest ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt
      (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.concat)
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.bvand)
            (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
              (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) (Term.Binary ↑W cn)))
          (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.bvand)
              (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) a))
            (__eo_nil (Term.UOp UserOp.bvand)
              (__eo_typeof (__eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s)
                (__eo_add (Term.Numeral ↑L') (Term.Numeral 1))) (Term.Binary ↑W cn)))))))
        rest))
      = SmtValue.Binary ↑(s + 1) ↑((cn.toNat &&& an.toNat) % 2^(s + 1)) := by
  have hMle : ((s + 1 - (L' + 1) : Nat) : Int) ≤ 4294967296 := by omega
  have hbr : (↑L' : Int) + 1 = ↑(L' + 1) := by omega
  rw [show __eo_add (Term.Numeral ↑L') (Term.Numeral 1) = Term.Numeral ↑(L' + 1) from by
        show Term.Numeral ((↑L' : Int) + 1) = Term.Numeral ↑(L' + 1)
        rw [hbr]]
  have eA : __eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)
      = Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  have eB : __eo_mk_apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a = Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a :=
    eo_mk_apply_ne (by intro h; cases h) hane
  simp only [eA, eB]
  have hNILne : __eo_nil (Term.UOp UserOp.bvand)
      (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))) ≠ Term.Stuck := by
    rw [nil_term_bvand W cn s (L' + 1) hsW (by omega) hMle]; intro h; cases h
  have eC : __eo_mk_apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))
      = Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  have eD : __eo_mk_apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a)
      = Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  simp only [eC, eD]
  have eE : __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
        (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))))
      = Term.Apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
        (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))) :=
    eo_mk_apply_ne (by intro h; cases h) hNILne
  simp only [eE]
  have eF : __eo_mk_apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
          (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))))
      = Term.Apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
          (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))))) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  simp only [eF]
  have eG : __eo_mk_apply (Term.UOp UserOp.concat)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
            (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn))))))
      = Term.Apply (Term.UOp UserOp.concat)
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) a))
            (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract (Term.Numeral ↑s) (Term.Numeral ↑(L' + 1))) (Term.Binary ↑W cn)))))) :=
    eo_mk_apply_ne (by intro h; cases h) (by intro h; cases h)
  rw [eG, eo_mk_apply_ne (by intro h; cases h) hrestne]
  rw [eval_concat M _ rest _ _ _ _
        (slice_eval M W cn a an hc0 ha0 ha s (L' + 1) hsW (by omega) hMle) hrest]
  rw [show s + 1 - (L' + 1) = s - L' from by omega]
  exact (closed_split (cn.toNat &&& an.toNat) s L' hL's).symm

private theorem eo_ite_true (X Y : Term) : __eo_ite (Term.Boolean true) X Y = X := by
  simp [__eo_ite, native_teq, native_ite]
private theorem eo_ite_false (X Y : Term) : __eo_ite (Term.Boolean false) X Y = Y := by
  simp [__eo_ite, native_teq, native_ite]
private theorem eo_eq_ne {b bn : Term} (hb : b ≠ Term.Stuck) (hbn : bn ≠ Term.Stuck) :
    __eo_eq b bn = Term.Boolean (native_teq bn b) := by
  cases b <;> cases bn <;> simp [__eo_eq] at hb hbn ⊢

-- The recursion reconstructs `bvand(extract[s:0] c, extract[s:0] a)` regardless of the
-- (well-formed) bitlist `bs`; only `start = s` matters.
private theorem rec_inv (M : SmtModel) (W : Nat) (cn : Int) (a : Term) (an : Int)
    (hc0 : 0 ≤ cn) (ha0 : 0 ≤ an)
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Binary ↑W an)
    (hane : a ≠ Term.Stuck) (hWB : (↑W : Int) ≤ 4294967296) :
    ∀ (L : Nat) (bs : Term), FB bs L → ∀ (bn : Term), bn ≠ Term.Stuck →
    ∀ (s : Nat), L ≤ s + 1 → s < W →
      __smtx_model_eval M (__eo_to_smt (__bv_mk_bitwise_slicing_rec (Term.UOp UserOp.bvand)
        (Term.Binary ↑W cn) a bs bn (Term.Numeral ↑s) (Term.Numeral ((↑L : Int) - 1))))
        = SmtValue.Binary ↑(s + 1) ↑((cn.toNat &&& an.toNat) % 2^(s + 1)) := by
  intro L bs hFB
  induction hFB with
  | nil =>
    intro bn hbn s hLs hsW
    rw [show ((↑(0:Nat) : Int) - 1) = (-1:Int) from by omega]
    rw [__bv_mk_bitwise_slicing_rec.eq_8 (Term.UOp UserOp.bvand) (Term.Binary ↑W cn) a
        (Term.Binary 0 0) bn (Term.Numeral ↑s)
        (by intro h; cases h) (by intro h; cases h) hane (by intro h; cases h) hbn
        (by intro h; cases h)]
    exact base_eval M W cn a an hc0 ha0 ha s hsW hWB
  | cons b bs' L' hb hFB' ih =>
    intro bn hbn s hLs hsW
    rw [show ((↑(L' + 1) : Int) - 1) = ↑L' from by push_cast; omega]
    rw [__bv_mk_bitwise_slicing_rec.eq_9 (Term.UOp UserOp.bvand) (Term.Binary ↑W cn) a bn
        (Term.Numeral ↑s) (Term.Numeral ↑L') b bs'
        (by intro h; cases h) (by intro h; cases h) hane hbn (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)]
    rw [show __eo_add (Term.Numeral ↑L') (Term.Numeral (-1)) = Term.Numeral ((↑L' : Int) - 1)
          from rfl, eo_eq_ne hb hbn]
    have hMs := ih b hb s (by omega) hsW
    have hrest := ih b hb L' (by omega) (by omega)
    cases hbb : native_teq bn b
    · rw [eo_ite_false]
      exact emit_eval M W cn a an hc0 ha0 ha hane s L' (by omega) hsW hWB _ hrest
        (ne_stuck_of_eval_bin M _ _ _ hrest)
    · rw [eo_ite_true]
      exact hMs

theorem cmd_step_bv_bitwise_slicing_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_bitwise_slicing args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_bitwise_slicing args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_bitwise_slicing args premises) :=
by
  sorry
