import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

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
