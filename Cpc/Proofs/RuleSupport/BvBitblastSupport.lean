module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

namespace BvBitblast

private theorem term_ne_stuck_of_eval_boolean
    {M : SmtModel} {t : Term} {b : Bool}
    (h : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b) :
    t ≠ Term.Stuck := by
  intro ht
  subst t
  cases h

private theorem mk_apply_eq
    {f x : Term} (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem mk_apply_arg_ne_stuck
    {f x : Term} (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem mk_apply_fun_ne_stuck
    {f x : Term} (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  cases f <;> cases x <;> simp_all [__eo_mk_apply]

private theorem pair_second_arg_ne_stuck
    {p : Term} (h : __pair_second p ≠ Term.Stuck) :
    p ≠ Term.Stuck := by
  cases p <;> simp_all [__pair_second]

private theorem singleton_elim_arg_ne_stuck {f c : Term}
    (h : __eo_list_singleton_elim f c ≠ Term.Stuck) :
    c ≠ Term.Stuck := by
  intro hc
  subst c
  cases f <;>
    simp_all [__eo_list_singleton_elim, __eo_is_list, __eo_requires,
      native_ite, native_teq]

private theorem mk_from_bools_eq
    {head tail : Term} (hh : head ≠ Term.Stuck) (ht : tail ≠ Term.Stuck) :
    __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp._at_from_bools) head) tail =
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) head) tail := by
  rw [mk_apply_eq (by intro h; cases h) hh]
  exact mk_apply_eq (by intro h; cases h) ht

private theorem requires_refl (t result : Term) (ht : t ≠ Term.Stuck) :
    __eo_requires t t result = result := by
  simp [__eo_requires, native_teq, native_ite, native_not, ht]

private theorem requires_result_ne_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) :
    z ≠ Term.Stuck := by
  intro hz
  subst z
  cases x <;> cases y <;>
    simp_all [__eo_requires, native_ite, native_teq]

private theorem eval_eq_is_boolean (x y : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq x y = SmtValue.Boolean b := by
  cases x <;> cases y <;> exact ⟨_, rfl⟩

/--
The natural-number value of CPC's little-endian Boolean list. Its head is the
least-significant bit; this is why `@from_bools b tail` translates to
`concat tail (ite b #b1 #b0)`.
-/
def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => 2 * bitsValue bs + b.toNat

def bitsEq : List Bool → List Bool → Bool
  | [], [] => true
  | x :: xs, y :: ys => (x == y) && bitsEq xs ys
  | _, _ => false

inductive BitListSyntax : Term → Prop
  | nil : BitListSyntax (Term.Binary 0 0)
  | cons (bit tail : Term) (ht : BitListSyntax tail) :
      BitListSyntax
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail)

theorem BitListSyntax.ne_stuck {t : Term} (h : BitListSyntax t) :
    t ≠ Term.Stuck := by
  cases h <;> intro hh <;> cases hh

private theorem bitlist_syntax_of_get_nil (f a : Term)
    (hf : f = Term.UOp UserOp._at_from_bools)
    (h : __eo_get_nil_rec f a ≠ Term.Stuck) :
    BitListSyntax a := by
  fun_induction __eo_get_nil_rec f a <;>
    simp_all [__eo_get_nil_rec]
  case case3 f g x y ih =>
    have hfg := support_eo_requires_cond_eq_of_non_stuck h
    subst g
    apply BitListSyntax.cons
    apply ih
    exact requires_result_ne_stuck h
  case case4 f nil hnilNe hnotApp =>
    have hnil := support_eo_requires_cond_eq_of_non_stuck h
    cases nil <;> simp_all [__eo_is_list_nil]
    split at hnil <;> simp_all
    exact BitListSyntax.nil

theorem bitlist_syntax_of_is_list (a : Term)
    (h : __eo_is_list (Term.UOp UserOp._at_from_bools) a =
      Term.Boolean true) :
    BitListSyntax a := by
  have hget :
      __eo_get_nil_rec (Term.UOp UserOp._at_from_bools) a ≠
        Term.Stuck := by
    have haNe : a ≠ Term.Stuck := by
      intro ha
      subst a
      cases h
    have his :
        __eo_is_list (Term.UOp UserOp._at_from_bools) a =
          __eo_is_ok
            (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) a) := by
      cases a <;> simp_all [__eo_is_list]
    rw [his] at h
    intro hg
    rw [hg] at h
    cases h
  exact bitlist_syntax_of_get_nil _ a rfl hget

inductive BitListsSameLength : Term → Term → Prop
  | nil : BitListsSameLength (Term.Binary 0 0) (Term.Binary 0 0)
  | cons (abit atail bbit btail : Term)
      (ht : BitListsSameLength atail btail) :
      BitListsSameLength
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) abit) atail)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) bbit) btail)

theorem bitsEq_eq_true_iff {xs ys : List Bool} :
    bitsEq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp [bitsEq]
  | cons x xs ih =>
      cases ys with
      | nil => simp [bitsEq]
      | cons y ys =>
          simp [bitsEq, ih]

theorem bitsValue_lt : ∀ bs : List Bool, bitsValue bs < 2 ^ bs.length := by
  intro bs
  induction bs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
      simp only [bitsValue, List.length_cons, Nat.pow_succ]
      have hb : b.toNat ≤ 1 := Bool.toNat_le b
      omega

theorem bitsValue_inj_of_length {xs ys : List Bool}
    (hlen : xs.length = ys.length)
    (hval : bitsValue xs = bitsValue ys) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          cases x <;> cases y <;> simp [bitsValue] at hval ⊢
          all_goals try omega
          all_goals
            congr 1
            apply ih htail
            omega

theorem ofBoolListLE_toNat (bs : List Bool) :
    (BitVec.ofBoolListLE bs).toNat = bitsValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [BitVec.ofBoolListLE, bitsValue, ih, BitVec.toNat_concat,
        Nat.add_comm, Nat.mul_comm]

theorem ofInt_bitsValue (bs : List Bool) :
    BitVec.ofInt bs.length (bitsValue bs : Int) =
      BitVec.ofBoolListLE bs := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, ofBoolListLE_toNat]
  norm_cast
  exact Nat.mod_eq_of_lt (bitsValue_lt bs)

private theorem native_int_pow2_nat (n : Nat) :
    native_int_pow2 (n : Int) = ((2 ^ n : Nat) : Int) := by
  have hn : ¬ ((n : Int) < 0) := by omega
  simp [native_int_pow2, native_zexp_total, hn]

private theorem bv_toInt_emod (w : Nat) (x : BitVec w) :
    x.toInt % (2 ^ w : Int) = (x.toNat : Int) := by
  have hc : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by
    norm_cast
  rw [hc, BitVec.toInt_eq_toNat_bmod, Int.bmod_emod]
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by
    exact_mod_cast x.isLt)

theorem ofBoolListLE_zipWith_and :
    ∀ (xs ys : List Bool) (hlen : xs.length = ys.length),
      BitVec.cast (by simp [List.length_zipWith, hlen])
          (BitVec.ofBoolListLE (List.zipWith (· && ·) xs ys)) =
        BitVec.ofBoolListLE xs &&&
          BitVec.cast hlen.symm (BitVec.ofBoolListLE ys) := by
  intro xs ys hlen
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    BitVec.getLsbD_and]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_zipWith, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem ofBoolListLE_zipWith_or :
    ∀ (xs ys : List Bool) (hlen : xs.length = ys.length),
      BitVec.cast (by simp [List.length_zipWith, hlen])
          (BitVec.ofBoolListLE (List.zipWith (· || ·) xs ys)) =
        BitVec.ofBoolListLE xs |||
          BitVec.cast hlen.symm (BitVec.ofBoolListLE ys) := by
  intro xs ys hlen
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    BitVec.getLsbD_or]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_zipWith, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem ofBoolListLE_zipWith_xor :
    ∀ (xs ys : List Bool) (hlen : xs.length = ys.length),
      BitVec.cast (by simp [List.length_zipWith, hlen])
          (BitVec.ofBoolListLE (List.zipWith (· != ·) xs ys)) =
        BitVec.ofBoolListLE xs ^^^
          BitVec.cast hlen.symm (BitVec.ofBoolListLE ys) := by
  intro xs ys hlen
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    BitVec.getLsbD_xor]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_zipWith, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by omega)]
  simp

theorem bitsValue_zipWith_and (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    bitsValue (List.zipWith (· && ·) xs ys) =
      bitsValue xs &&& bitsValue ys := by
  have h := congrArg BitVec.toNat
    (ofBoolListLE_zipWith_and xs ys hlen)
  simpa [ofBoolListLE_toNat] using h

theorem bitsValue_zipWith_or (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    bitsValue (List.zipWith (· || ·) xs ys) =
      bitsValue xs ||| bitsValue ys := by
  have h := congrArg BitVec.toNat
    (ofBoolListLE_zipWith_or xs ys hlen)
  simpa [ofBoolListLE_toNat] using h

theorem bitsValue_zipWith_xor (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    bitsValue (List.zipWith (· != ·) xs ys) =
      bitsValue xs ^^^ bitsValue ys := by
  have h := congrArg BitVec.toNat
    (ofBoolListLE_zipWith_xor xs ys hlen)
  simpa [ofBoolListLE_toNat] using h

private theorem ofInt_bitsValue_width (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    BitVec.ofInt xs.length (bitsValue ys : Int) =
      BitVec.cast hlen.symm (BitVec.ofBoolListLE ys) := by
  apply BitVec.eq_of_toNat_eq
  simp [ofBoolListLE_toNat]
  exact Nat.mod_eq_of_lt (by simpa [hlen] using bitsValue_lt ys)

private theorem native_and_bits (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    native_mod_total
        (native_binary_and (xs.length : Int)
          (bitsValue xs : Int) (bitsValue ys : Int))
        (native_int_pow2 (xs.length : Int)) =
      (bitsValue (List.zipWith (· && ·) xs ys) : Int) := by
  by_cases hw : xs.length = 0
  · have hx : xs = [] := List.eq_nil_of_length_eq_zero hw
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    subst ys
    rfl
  · rw [native_int_pow2_nat]
    simp only [native_binary_and, native_zeq, native_ite, decide_eq_true_eq]
    rw [if_neg (by exact_mod_cast hw)]
    change
      ((BitVec.ofInt xs.length (bitsValue xs : Int) &&&
          BitVec.ofInt xs.length (bitsValue ys : Int)).toInt %
        ((2 ^ xs.length : Nat) : Int)) =
          (bitsValue (List.zipWith (· && ·) xs ys) : Int)
    rw [show ((2 ^ xs.length : Nat) : Int) =
      (2 : Int) ^ xs.length by norm_cast]
    rw [bv_toInt_emod, ofInt_bitsValue,
      ofInt_bitsValue_width xs ys hlen, BitVec.toNat_and,
      BitVec.toNat_cast, ofBoolListLE_toNat, ofBoolListLE_toNat,
      bitsValue_zipWith_and xs ys hlen]

private theorem native_or_bits (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    native_mod_total
        (native_binary_or (xs.length : Int)
          (bitsValue xs : Int) (bitsValue ys : Int))
        (native_int_pow2 (xs.length : Int)) =
      (bitsValue (List.zipWith (· || ·) xs ys) : Int) := by
  by_cases hw : xs.length = 0
  · have hx : xs = [] := List.eq_nil_of_length_eq_zero hw
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    subst ys
    rfl
  · rw [native_int_pow2_nat]
    simp only [native_binary_or, native_zeq, native_ite, decide_eq_true_eq]
    rw [if_neg (by exact_mod_cast hw)]
    change
      ((BitVec.ofInt xs.length (bitsValue xs : Int) |||
          BitVec.ofInt xs.length (bitsValue ys : Int)).toInt %
        ((2 ^ xs.length : Nat) : Int)) =
          (bitsValue (List.zipWith (· || ·) xs ys) : Int)
    rw [show ((2 ^ xs.length : Nat) : Int) =
      (2 : Int) ^ xs.length by norm_cast]
    rw [bv_toInt_emod, ofInt_bitsValue,
      ofInt_bitsValue_width xs ys hlen, BitVec.toNat_or,
      BitVec.toNat_cast, ofBoolListLE_toNat, ofBoolListLE_toNat,
      bitsValue_zipWith_or xs ys hlen]

private theorem native_xor_bits (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    native_mod_total
        (native_binary_xor (xs.length : Int)
          (bitsValue xs : Int) (bitsValue ys : Int))
        (native_int_pow2 (xs.length : Int)) =
      (bitsValue (List.zipWith (· != ·) xs ys) : Int) := by
  by_cases hw : xs.length = 0
  · have hx : xs = [] := List.eq_nil_of_length_eq_zero hw
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs
    subst ys
    rfl
  · rw [native_int_pow2_nat]
    simp only [native_binary_xor, native_zeq, native_ite,
      decide_eq_true_eq]
    rw [if_neg (by exact_mod_cast hw)]
    change
      ((BitVec.ofInt xs.length (bitsValue xs : Int) ^^^
          BitVec.ofInt xs.length (bitsValue ys : Int)).toInt %
        ((2 ^ xs.length : Nat) : Int)) =
          (bitsValue (List.zipWith (· != ·) xs ys) : Int)
    rw [show ((2 ^ xs.length : Nat) : Int) =
      (2 : Int) ^ xs.length by norm_cast]
    rw [bv_toInt_emod, ofInt_bitsValue,
      ofInt_bitsValue_width xs ys hlen, BitVec.toNat_xor,
      BitVec.toNat_cast, ofBoolListLE_toNat, ofBoolListLE_toNat,
      bitsValue_zipWith_xor xs ys hlen]

/--
`BitListEval M t bs` says that `t` is a CPC `@from_bools` spine ending in the
empty bit-vector and that its Boolean heads evaluate, least-significant first,
to `bs`.
-/
inductive BitListEval (M : SmtModel) : Term → List Bool → Prop
  | nil : BitListEval M (Term.Binary 0 0) []
  | cons (b tail : Term) (v : Bool) (vs : List Bool)
      (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean v)
      (ht : BitListEval M tail vs) :
      BitListEval M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) b) tail)
        (v :: vs)

theorem BitListEval.ne_stuck {M : SmtModel} {t : Term} {bs : List Bool}
    (h : BitListEval M t bs) : t ≠ Term.Stuck := by
  cases h <;> intro ht <;> cases ht

theorem BitListEval.eval {M : SmtModel} {t : Term} {bs : List Bool}
    (h : BitListEval M t bs) :
    __smtx_model_eval M (__eo_to_smt t) =
      SmtValue.Binary (bs.length : Int) (bitsValue bs : Int) := by
  induction h with
  | nil => rfl
  | cons b tail v vs hb ht ih =>
      change
        __smtx_model_eval_concat
            (__smtx_model_eval M (__eo_to_smt tail))
            (__smtx_model_eval_ite
              (__smtx_model_eval M (__eo_to_smt b))
              (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)) =
          SmtValue.Binary ((v :: vs).length : Int)
            (bitsValue (v :: vs) : Int)
      rw [hb, ih]
      have hpowOne : native_int_pow2 1 = 2 := by rfl
      have hpowSucc :
          native_int_pow2 ((vs.length : Int) + 1) =
            ((2 ^ (vs.length + 1) : Nat) : Int) := by
        rw [show (vs.length : Int) + 1 = ((vs.length + 1 : Nat) : Int) by omega]
        exact native_int_pow2_nat (vs.length + 1)
      have hlt := bitsValue_lt vs
      cases v <;>
        simp [__smtx_model_eval_ite, __smtx_model_eval_concat,
          bitsValue, native_zplus, native_mod_total, native_binary_concat,
          native_zmult]
      · rw [hpowOne, hpowSucc, Int.emod_eq_of_lt]
        · rw [Int.mul_comm]
        · exact Int.mul_nonneg (Int.natCast_nonneg _) (by decide)
        · exact_mod_cast (show bitsValue vs * 2 < 2 ^ (vs.length + 1) by
            rw [Nat.pow_succ]
            omega)
      · rw [hpowOne, hpowSucc, Int.emod_eq_of_lt]
        · rw [Int.mul_comm]
        · have hn := Int.natCast_nonneg (bitsValue vs)
          omega
        · exact_mod_cast (show bitsValue vs * 2 + 1 < 2 ^ (vs.length + 1) by
            rw [Nat.pow_succ]
            omega)

private theorem wrap_bool_eval {M : SmtModel} {c : Term} {b : Bool}
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean b) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at_from_bools) c)
            (Term.Binary 0 0))) =
      SmtValue.Binary 1 (if b then 1 else 0) := by
  have hcNe : c ≠ Term.Stuck := by
    intro h
    subst c
    cases hc
  rw [mk_apply_eq (by intro h; cases h) hcNe]
  rw [mk_apply_eq (by intro h; cases h)
    (by intro h; cases h)]
  have hout :=
    BitListEval.cons c (Term.Binary 0 0) b [] hc
      (BitListEval.nil (M := M))
  rw [hout.eval]
  cases b <;> rfl

theorem BitListSyntax.eval {M : SmtModel} (hM : model_total_typed M)
    {t : Term} (hs : BitListSyntax t)
    (hnn : term_has_non_none_type (__eo_to_smt t)) :
    ∃ bs : List Bool, BitListEval M t bs := by
  induction hs with
  | nil =>
      exact ⟨[], BitListEval.nil⟩
  | cons bit tail htail ih =>
      let bitSmt :=
        SmtTerm.ite (__eo_to_smt bit)
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)
      have hconcat :
          __eo_to_smt
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_from_bools) bit) tail) =
            SmtTerm.concat (__eo_to_smt tail) bitSmt := by
        rfl
      have hconcatNN :
          term_has_non_none_type
            (SmtTerm.concat (__eo_to_smt tail) bitSmt) := by
        simpa [hconcat] using hnn
      rcases bv_concat_args_of_non_none hconcatNN with
        ⟨wtail, wbit, htailTy, hbitTy⟩
      have htailNN :
          term_has_non_none_type (__eo_to_smt tail) := by
        unfold term_has_non_none_type
        rw [htailTy]
        simp
      have hbitNN : term_has_non_none_type bitSmt := by
        unfold term_has_non_none_type
        rw [hbitTy]
        simp
      rcases ite_args_of_non_none hbitNN with
        ⟨T, hcondTy, _hthenTy, _helseTy, _hT⟩
      have hcondNN :
          term_has_non_none_type (__eo_to_smt bit) := by
        unfold term_has_non_none_type
        rw [hcondTy]
        simp
      have hpres :=
        type_preservation M hM (__eo_to_smt bit) hcondNN
      rw [hcondTy] at hpres
      rcases bool_value_canonical hpres with ⟨b, hb⟩
      rcases ih htailNN with ⟨bs, hbs⟩
      exact ⟨b :: bs, BitListEval.cons bit tail b bs hb hbs⟩

theorem BitListsSameLength.syntax_left {a b : Term}
    (h : BitListsSameLength a b) : BitListSyntax a := by
  induction h with
  | nil => exact BitListSyntax.nil
  | cons abit atail bbit btail ht ih =>
      exact BitListSyntax.cons abit atail ih

theorem BitListsSameLength.syntax_right {a b : Term}
    (h : BitListsSameLength a b) : BitListSyntax b := by
  induction h with
  | nil => exact BitListSyntax.nil
  | cons abit atail bbit btail ht ih =>
      exact BitListSyntax.cons bbit btail ih

theorem BitListsSameLength.eval_length {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (hs : BitListsSameLength a b)
    (ha : BitListEval M a xs) (hb : BitListEval M b ys) :
    xs.length = ys.length := by
  induction hs generalizing xs ys with
  | nil =>
      cases ha
      cases hb
      rfl
  | cons abit atail bbit btail ht ih =>
      cases ha with
      | cons _ _ _ xs _ hat =>
          cases hb with
          | cons _ _ _ ys _ hbt =>
              simpa using congrArg Nat.succ (ih hat hbt)

theorem bitblast_apply_unary_syntax (f a : Term)
    (h : __bv_bitblast_apply_unary f a ≠ Term.Stuck) :
    BitListSyntax a := by
  fun_induction __bv_bitblast_apply_unary f a <;> simp_all
  · exact BitListSyntax.nil
  · apply BitListSyntax.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h

theorem bitblast_apply_binary_same_length (f a b : Term)
    (h : __bv_bitblast_apply_binary f a b ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_bitblast_apply_binary f a b <;> simp_all
  · exact BitListsSameLength.nil
  · apply BitListsSameLength.cons
    apply_assumption
    exact mk_apply_arg_ne_stuck h

theorem bitblast_ult_rec_same_length (a b previous : Term)
    (h : __bv_bitblast_ult_rec a b previous ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_bitblast_ult_rec a b previous <;> simp_all
  · exact BitListsSameLength.nil
  · exact BitListsSameLength.cons _ _ _ _ (by apply_assumption)

theorem bitblast_ult_shape (a b orEqual : Term)
    (h : __bv_bitblast_ult a b orEqual ≠ Term.Stuck) :
    ∃ x xtail y ytail,
      a =
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail ∧
      b =
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail ∧
      BitListsSameLength xtail ytail := by
  unfold __bv_bitblast_ult at h
  split at h <;> simp_all
  refine ⟨_, _, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, ?_⟩
  exact bitblast_ult_rec_same_length _ _ _ h

private theorem bitlist_rev_is_list (a : Term)
    (h : __eo_list_rev (Term.UOp UserOp._at_from_bools) a ≠
      Term.Stuck) :
    __eo_is_list (Term.UOp UserOp._at_from_bools) a =
      Term.Boolean true := by
  have hReq :
      __eo_requires
          (__eo_is_list (Term.UOp UserOp._at_from_bools) a)
          (Term.Boolean true)
          (__eo_list_rev_rec a
            (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) a)) ≠
        Term.Stuck := by
    simpa [__eo_list_rev] using h
  exact support_eo_requires_cond_eq_of_non_stuck hReq

theorem bitlist_rev_syntax (a : Term)
    (h : __eo_list_rev (Term.UOp UserOp._at_from_bools) a ≠
      Term.Stuck) :
    BitListSyntax a :=
  bitlist_syntax_of_is_list a (bitlist_rev_is_list a h)

theorem bitblast_slt_args_ne_stuck (a b orEqual : Term)
    (h : __bv_bitblast_slt_impl a b orEqual ≠ Term.Stuck) :
    a ≠ Term.Stuck ∧ b ≠ Term.Stuck := by
  unfold __bv_bitblast_slt_impl at h
  split at h <;> simp_all [__eo_mk_apply]

theorem ripple_carry_same_length (a b carry res : Term)
    (h : __bv_ripple_carry_adder_2 a b carry res ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_ripple_carry_adder_2 a b carry res <;> simp_all
  · apply BitListsSameLength.cons
    apply_assumption
  · exact BitListsSameLength.nil

private theorem bitblast_step_ite_shape (c a b : Term)
    (h : __bv_mk_bitblast_step_ite c a b ≠ Term.Stuck) :
    ∃ bit : Term,
      c = Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) bit)
          (Term.Binary 0 0) ∧
      BitListsSameLength a b := by
  fun_induction __bv_mk_bitblast_step_ite c a b <;>
    simp_all [__eo_mk_apply]
  · apply BitListsSameLength.cons
    apply_assumption
    intro hrec
    simp [hrec] at h
  · exact BitListsSameLength.nil

theorem BitListEval.apply_not {M : SmtModel} {t : Term} {bs : List Bool}
    (h : BitListEval M t bs) :
    BitListEval M
      (__bv_bitblast_apply_unary (Term.UOp UserOp.not) t)
      (bs.map (!·)) := by
  induction h with
  | nil =>
      exact BitListEval.nil
  | cons b tail v vs hb ht ih =>
      have hh :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) b)) =
            SmtValue.Boolean (!v) := by
        change
          __smtx_model_eval_not (__smtx_model_eval M (__eo_to_smt b)) =
            SmtValue.Boolean (!v)
        rw [hb]
        cases v <;> rfl
      simp only [__bv_bitblast_apply_unary]
      rw [mk_apply_eq (by intro h; cases h) (BitListEval.ne_stuck ih)]
      exact
        BitListEval.cons (Term.Apply (Term.UOp UserOp.not) b)
          (__bv_bitblast_apply_unary (Term.UOp UserOp.not) tail)
          (!v) (vs.map (!·)) hh ih

private theorem binary_app_and_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __bv_bitblast_binary_app (Term.UOp UserOp.and) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.and) a)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) b)
          (Term.Boolean true)) := by
  cases a <;> cases b <;> simp_all [__bv_bitblast_binary_app]

private theorem binary_app_or_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __bv_bitblast_binary_app (Term.UOp UserOp.or) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.or) a)
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) b)
          (Term.Boolean false)) := by
  cases a <;> cases b <;> simp_all [__bv_bitblast_binary_app]

private theorem binary_app_xor_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __bv_bitblast_binary_app (Term.UOp UserOp.xor) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b := by
  cases a <;> cases b <;> simp_all [__bv_bitblast_binary_app]

private theorem binary_app_eq_eq {a b : Term}
    (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __bv_bitblast_binary_app (Term.UOp UserOp.eq) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b := by
  cases a <;> cases b <;> simp_all [__bv_bitblast_binary_app]

private theorem eval_binary_and {M : SmtModel} {a b : Term} {x y : Bool}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean x)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean y) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_binary_app (Term.UOp UserOp.and) a b)) =
      SmtValue.Boolean (x && y) := by
  rw [binary_app_and_eq
    (term_ne_stuck_of_eval_boolean ha)
    (term_ne_stuck_of_eval_boolean hb)]
  change
    __smtx_model_eval_and
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean true)) =
      SmtValue.Boolean (x && y)
  rw [ha, hb]
  cases x <;> cases y <;> rfl

private theorem eval_binary_or {M : SmtModel} {a b : Term} {x y : Bool}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean x)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean y) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_binary_app (Term.UOp UserOp.or) a b)) =
      SmtValue.Boolean (x || y) := by
  rw [binary_app_or_eq
    (term_ne_stuck_of_eval_boolean ha)
    (term_ne_stuck_of_eval_boolean hb)]
  change
    __smtx_model_eval_or
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval_or
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean false)) =
      SmtValue.Boolean (x || y)
  rw [ha, hb]
  cases x <;> cases y <;> rfl

private theorem eval_binary_xor {M : SmtModel} {a b : Term} {x y : Bool}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean x)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean y) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_binary_app (Term.UOp UserOp.xor) a b)) =
      SmtValue.Boolean (x != y) := by
  rw [binary_app_xor_eq
    (term_ne_stuck_of_eval_boolean ha)
    (term_ne_stuck_of_eval_boolean hb)]
  change
    __smtx_model_eval_xor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean (x != y)
  rw [ha, hb]
  cases x <;> cases y <;> rfl

private theorem eval_binary_eq {M : SmtModel} {a b : Term} {x y : Bool}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean x)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean y) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_binary_app (Term.UOp UserOp.eq) a b)) =
      SmtValue.Boolean (x == y) := by
  rw [binary_app_eq_eq
    (term_ne_stuck_of_eval_boolean ha)
    (term_ne_stuck_of_eval_boolean hb)]
  change
    __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean (x == y)
  rw [ha, hb]
  cases x <;> cases y <;> rfl

theorem BitListEval.apply_and {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_binary (Term.UOp UserOp.and) a b)
      (List.zipWith (· && ·) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb <;> simp_all [__bv_bitblast_apply_binary]
      exact BitListEval.nil
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_bitblast_apply_binary.eq_3 _ _ _ _ _
            (by intro h; cases h)]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean (eval_binary_and hax hby))]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (__bv_bitblast_binary_app (Term.UOp UserOp.and) a b)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.and) atail btail)
              (x && y) (List.zipWith (· && ·) xs ys)
              (eval_binary_and hax hby) (ih hbt htail)

theorem BitListEval.apply_or {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_binary (Term.UOp UserOp.or) a b)
      (List.zipWith (· || ·) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb <;> simp_all [__bv_bitblast_apply_binary]
      exact BitListEval.nil
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_bitblast_apply_binary.eq_3 _ _ _ _ _
            (by intro h; cases h)]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean (eval_binary_or hax hby))]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (__bv_bitblast_binary_app (Term.UOp UserOp.or) a b)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.or) atail btail)
              (x || y) (List.zipWith (· || ·) xs ys)
              (eval_binary_or hax hby) (ih hbt htail)

theorem BitListEval.apply_xor {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b)
      (List.zipWith (· != ·) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb <;> simp_all [__bv_bitblast_apply_binary]
      exact BitListEval.nil
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_bitblast_apply_binary.eq_3 _ _ _ _ _
            (by intro h; cases h)]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean (eval_binary_xor hax hby))]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (__bv_bitblast_binary_app (Term.UOp UserOp.xor) a b)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) atail btail)
              (x != y) (List.zipWith (· != ·) xs ys)
              (eval_binary_xor hax hby) (ih hbt htail)

theorem BitListEval.apply_eq {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b)
      (List.zipWith (· == ·) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb <;> simp_all [__bv_bitblast_apply_binary]
      exact BitListEval.nil
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_bitblast_apply_binary.eq_3 _ _ _ _ _
            (by intro h; cases h)]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean (eval_binary_eq hax hby))]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (__bv_bitblast_binary_app (Term.UOp UserOp.eq) a b)
              (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) atail btail)
              (x == y) (List.zipWith (· == ·) xs ys)
              (eval_binary_eq hax hby) (ih hbt htail)

theorem BitListEval.eval_bvand {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and) a b)) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) := by
  have hout := (ha.apply_and hb hlen).eval
  rw [hout, ha.eval, hb.eval]
  simp only [__smtx_model_eval_bvand]
  rw [native_and_bits xs ys hlen]
  simp [List.length_zipWith, hlen]

theorem BitListEval.eval_bvor {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.or) a b)) =
      __smtx_model_eval_bvor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) := by
  have hout := (ha.apply_or hb hlen).eval
  rw [hout, ha.eval, hb.eval]
  simp only [__smtx_model_eval_bvor]
  rw [native_or_bits xs ys hlen]
  simp [List.length_zipWith, hlen]

theorem BitListEval.eval_bvxor {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b)) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) := by
  have hout := (ha.apply_xor hb hlen).eval
  rw [hout, ha.eval, hb.eval]
  simp only [__smtx_model_eval_bvxor]
  rw [native_xor_bits xs ys hlen]
  simp [List.length_zipWith, hlen]

private theorem zipWith_eq_eq_map_not_xor :
    ∀ (xs ys : List Bool),
      List.zipWith (· == ·) xs ys =
        (List.zipWith (· != ·) xs ys).map (!·) := by
  intro xs
  induction xs with
  | nil => intro ys; rfl
  | cons x xs ih =>
      intro ys
      cases ys with
      | nil => rfl
      | cons y ys =>
          cases x <;> cases y <;>
            simp [ih ys]

theorem BitListEval.apply_ite {M : SmtModel}
    {c a b : Term} {cv : Bool} {xs ys : List Bool}
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean cv)
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_bitblast_apply_ite c a b)
      (List.zipWith (fun x y => if cv then x else y) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb with
      | nil =>
          rw [__bv_bitblast_apply_ite.eq_2 c
            (term_ne_stuck_of_eval_boolean hc)]
          exact BitListEval.nil
      | cons =>
          simp at hlen
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil =>
          simp at hlen
      | cons b btail y ys hby hbt =>
          have hhead :
              __smtx_model_eval_ite
                  (__smtx_model_eval M (__eo_to_smt c))
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)) =
                SmtValue.Boolean (if cv then x else y) := by
            rw [hc, hax, hby]
            cases cv <;> rfl
          have htail : xs.length = ys.length := by simpa using hlen
          have hheadNe :
              Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b ≠
                Term.Stuck := by intro h; cases h
          rw [__bv_bitblast_apply_ite.eq_3 _ _ _ _ _
            (term_ne_stuck_of_eval_boolean hc)]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hbt htail))]
          exact
            BitListEval.cons
              (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b)
              (__bv_bitblast_apply_ite c atail btail)
              (if cv then x else y)
              (List.zipWith (fun x y => if cv then x else y) xs ys)
              hhead (ih hbt htail)

private theorem eval_ite_bit {M : SmtModel}
    {c x y : Term} {cb xb yb : Bool}
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean cb)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.or)
                  (Term.Apply (Term.UOp UserOp.not) c))
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.or) x)
                  (Term.Boolean false))))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.or) c)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.or) y)
                    (Term.Boolean false))))
              (Term.Boolean true)))) =
      SmtValue.Boolean (if cb then xb else yb) := by
  change
    __smtx_model_eval_and
      (__smtx_model_eval_or
        (__smtx_model_eval_not
          (__smtx_model_eval M (__eo_to_smt c)))
        (__smtx_model_eval_or
          (__smtx_model_eval M (__eo_to_smt x))
          (SmtValue.Boolean false)))
      (__smtx_model_eval_and
        (__smtx_model_eval_or
          (__smtx_model_eval M (__eo_to_smt c))
          (__smtx_model_eval_or
            (__smtx_model_eval M (__eo_to_smt y))
            (SmtValue.Boolean false)))
        (SmtValue.Boolean true)) =
      SmtValue.Boolean (if cb then xb else yb)
  rw [hc, hx, hy]
  cases cb <;> cases xb <;> cases yb <;> rfl

private theorem bitblast_step_ite_eval {M : SmtModel}
    {cbit a b : Term} {cb : Bool} {xs ys : List Bool}
    (hc : __smtx_model_eval M (__eo_to_smt cbit) =
      SmtValue.Boolean cb)
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    BitListEval M
      (__bv_mk_bitblast_step_ite
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) cbit)
          (Term.Binary 0 0))
        a b)
      (List.zipWith (fun x y => if cb then x else y) xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb with
      | nil => exact BitListEval.nil
      | cons => simp at hlen
  | cons x xtail xb xs hx hxt ih =>
      cases hb with
      | nil => simp at hlen
      | cons y ytail yb ys hy hyt =>
          have htail : xs.length = ys.length := by simpa using hlen
          rw [__bv_mk_bitblast_step_ite.eq_1]
          rw [mk_apply_eq (by intro h; cases h)
            (BitListEval.ne_stuck (ih hyt htail))]
          exact BitListEval.cons _ _ _ _
            (eval_ite_bit hc hx hy) (ih hyt htail)

private theorem zipWith_left_of_length {α β : Type}
    (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    List.zipWith (fun x _ => x) xs ys = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zipWith_cons_cons, List.cons.injEq, true_and]
          apply ih
          simpa using h

private theorem zipWith_right_of_length {α β : Type}
    (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    List.zipWith (fun _ y => y) xs ys = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zipWith_cons_cons, List.cons.injEq, true_and]
          apply ih
          simpa using h

theorem BitListEval.concat {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys) :
    BitListEval M (__bv_bitblast_concat a b) (xs ++ ys) := by
  induction ha with
  | nil =>
      rw [__bv_bitblast_concat.eq_3 b (BitListEval.ne_stuck hb)]
      exact hb
  | cons head tail x xs hhead htail ih =>
      rw [__bv_bitblast_concat.eq_2 b head tail
        (BitListEval.ne_stuck hb)]
      rw [mk_apply_eq (by intro h; cases h) (BitListEval.ne_stuck ih)]
      simpa using BitListEval.cons head (__bv_bitblast_concat tail b)
        x (xs ++ ys) hhead ih

private theorem list_rev_rec_nil (acc : Term) (hacc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (Term.Binary 0 0) acc = acc := by
  cases acc <;> simp_all [__eo_list_rev_rec]

private theorem list_rev_rec_cons
    (head tail acc : Term) (hacc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) head) tail)
        acc =
      __eo_list_rev_rec tail
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) head) acc) := by
  cases acc <;> simp_all [__eo_list_rev_rec]

private theorem BitListEval.rev_rec {M : SmtModel}
    {t acc : Term} {xs ys : List Bool}
    (ht : BitListEval M t xs) (ha : BitListEval M acc ys) :
    BitListEval M (__eo_list_rev_rec t acc) (xs.reverse ++ ys) := by
  induction ht generalizing acc ys with
  | nil =>
      rw [list_rev_rec_nil acc (BitListEval.ne_stuck ha)]
      simpa using ha
  | cons head tail x xs hhead htail ih =>
      rw [list_rev_rec_cons head tail acc (BitListEval.ne_stuck ha)]
      have hcons := BitListEval.cons head acc x ys hhead ha
      have hrec := ih hcons
      simpa [List.reverse_cons, List.append_assoc] using hrec

private theorem BitListEval.get_nil {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) :
    __eo_get_nil_rec (Term.UOp UserOp._at_from_bools) t =
      Term.Binary 0 0 := by
  induction h with
  | nil =>
      exact requires_refl _ _ (by intro hh; cases hh)
  | cons head tail x xs hhead htail ih =>
      show
        __eo_requires (Term.UOp UserOp._at_from_bools)
            (Term.UOp UserOp._at_from_bools)
            (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) tail) =
          Term.Binary 0 0
      rw [requires_refl _ _ (by intro hh; cases hh)]
      exact ih

private theorem BitListEval.is_list {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) :
    __eo_is_list (Term.UOp UserOp._at_from_bools) t =
      Term.Boolean true := by
  have hnil := h.get_nil
  have hne := h.ne_stuck
  cases t <;>
    simp_all [__eo_is_list, __eo_is_ok, native_not, native_teq,
      reduceCtorEq]

theorem BitListEval.rev {M : SmtModel}
    {t : Term} {xs : List Bool} (h : BitListEval M t xs) :
    BitListEval M
      (__eo_list_rev (Term.UOp UserOp._at_from_bools) t)
      xs.reverse := by
  change
    BitListEval M
      (__eo_requires
        (__eo_is_list (Term.UOp UserOp._at_from_bools) t)
        (Term.Boolean true)
        (__eo_list_rev_rec t
          (__eo_get_nil_rec (Term.UOp UserOp._at_from_bools) t)))
      xs.reverse
  rw [h.is_list, h.get_nil,
    requires_refl _ _ (by intro hh; cases hh)]
  simpa using h.rev_rec (BitListEval.nil (M := M))

theorem BitListEval.eq_rec_eval {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_eq_rec a b)) =
      SmtValue.Boolean (bitsEq xs ys) := by
  induction ha generalizing b ys with
  | nil =>
      cases hb with
      | nil => rfl
      | cons => simp at hlen
  | cons a atail x xs hax hat ih =>
      cases hb with
      | nil => simp at hlen
      | cons b btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hrec := ih hbt htail
          rw [__bv_mk_bitblast_step_eq_rec.eq_2]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean hrec)]
          change
            __smtx_model_eval_and
                (__smtx_model_eval_eq
                  (__smtx_model_eval M (__eo_to_smt a))
                  (__smtx_model_eval M (__eo_to_smt b)))
                (__smtx_model_eval M
                  (__eo_to_smt (__bv_mk_bitblast_step_eq_rec atail btail))) =
              SmtValue.Boolean (bitsEq (x :: xs) (y :: ys))
          rw [hax, hby, hrec]
          cases x <;> cases y <;>
            simp [bitsEq, __smtx_model_eval_eq, native_veq,
              __smtx_model_eval_and, SmtEval.native_and]

private theorem eq_rec_same_length (a b : Term)
    (h : __bv_mk_bitblast_step_eq_rec a b ≠ Term.Stuck) :
    BitListsSameLength a b := by
  fun_induction __bv_mk_bitblast_step_eq_rec a b <;>
    simp_all [__eo_mk_apply]
  · exact BitListsSameLength.nil
  · apply BitListsSameLength.cons
    apply_assumption
    intro hrec
    simp [hrec] at h

private theorem BitListEval.eq_rec_get_nil {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __eo_get_nil_rec (Term.UOp UserOp.and)
        (__bv_mk_bitblast_step_eq_rec a b) =
      Term.Boolean true := by
  induction ha generalizing b ys with
  | nil =>
      cases hb with
      | nil => rfl
      | cons => simp at hlen
  | cons abit atail x xs hax hat ih =>
      cases hb with
      | nil => simp at hlen
      | cons bbit btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hrec := hat.eq_rec_eval hbt htail
          rw [__bv_mk_bitblast_step_eq_rec.eq_2]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean hrec)]
          change
            __eo_requires (Term.UOp UserOp.and) (Term.UOp UserOp.and)
                (__eo_get_nil_rec (Term.UOp UserOp.and)
                  (__bv_mk_bitblast_step_eq_rec atail btail)) =
              Term.Boolean true
          rw [requires_refl _ _ (by intro h; cases h)]
          exact ih hbt htail

private theorem BitListEval.eq_rec_is_list {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __eo_is_list (Term.UOp UserOp.and)
        (__bv_mk_bitblast_step_eq_rec a b) =
      Term.Boolean true := by
  have hnil := ha.eq_rec_get_nil hb hlen
  have hne :=
    term_ne_stuck_of_eval_boolean (ha.eq_rec_eval hb hlen)
  generalize hc :
      __bv_mk_bitblast_step_eq_rec a b = c at hnil hne ⊢
  cases c <;>
    simp_all [__eo_is_list, __eo_is_ok, native_not, native_teq,
      reduceCtorEq]

theorem BitListEval.eq_step_eval {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.and)
            (__bv_mk_bitblast_step_eq_rec a b))) =
      SmtValue.Boolean (bitsEq xs ys) := by
  rw [__eo_list_singleton_elim, ha.eq_rec_is_list hb hlen,
    requires_refl _ _ (by intro h; cases h)]
  cases ha with
  | nil =>
      cases hb with
      | nil => rfl
      | cons => simp at hlen
  | cons abit atail x xs hax hat =>
      cases hb with
      | nil => simp at hlen
      | cons bbit btail y ys hby hbt =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hrec := hat.eq_rec_eval hbt htail
          rw [__bv_mk_bitblast_step_eq_rec.eq_2]
          rw [mk_apply_eq (by intro h; cases h)
            (term_ne_stuck_of_eval_boolean hrec)]
          cases hat with
          | nil =>
              cases hbt with
              | nil =>
                  change
                    __smtx_model_eval M
                        (__eo_to_smt
                          (__eo_ite (Term.Boolean true)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.eq) abit) bbit)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.and)
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.eq) abit)
                                  bbit))
                              (Term.Boolean true)))) =
                      SmtValue.Boolean (bitsEq [x] [y])
                  rw [show
                    __eo_ite (Term.Boolean true)
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.eq) abit) bbit)
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.and)
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.eq) abit)
                              bbit))
                          (Term.Boolean true)) =
                      Term.Apply
                        (Term.Apply (Term.UOp UserOp.eq) abit) bbit by
                    rfl]
                  have heq := eval_binary_eq hax hby
                  rw [binary_app_eq_eq
                    (term_ne_stuck_of_eval_boolean hax)
                    (term_ne_stuck_of_eval_boolean hby)] at heq
                  simpa [bitsEq] using heq
              | cons => simp at htail
          | cons tailHead tailTail xv xvs hth htt =>
              cases hbt with
              | nil => simp at htail
              | cons otherHead otherTail yv yvs hoh hot =>
                  have htailtail : xvs.length = yvs.length := by
                    simpa using htail
                  have htailEval := htt.eq_rec_eval hot htailtail
                  have htailNotNil :
                      __eo_is_list_nil (Term.UOp UserOp.and)
                          (__bv_mk_bitblast_step_eq_rec
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp._at_from_bools)
                                tailHead) tailTail)
                            (Term.Apply
                              (Term.Apply
                                (Term.UOp UserOp._at_from_bools)
                                otherHead) otherTail)) =
                        Term.Boolean false := by
                    rw [__bv_mk_bitblast_step_eq_rec.eq_2]
                    rw [mk_apply_eq (by intro h; cases h)
                      (term_ne_stuck_of_eval_boolean htailEval)]
                    rfl
                  have hfull :=
                    (BitListEval.cons abit
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp._at_from_bools)
                          tailHead) tailTail)
                      x (xv :: xvs) hax
                      (BitListEval.cons tailHead tailTail xv xvs hth htt)).eq_rec_eval
                      (BitListEval.cons bbit
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp._at_from_bools)
                            otherHead) otherTail)
                        y (yv :: yvs) hby
                        (BitListEval.cons otherHead otherTail yv yvs hoh hot))
                      hlen
                  rw [__bv_mk_bitblast_step_eq_rec.eq_2,
                    mk_apply_eq (by intro h; cases h)
                      (term_ne_stuck_of_eval_boolean hrec)] at hfull
                  rw [__eo_list_singleton_elim_2, htailNotNil]
                  simp [__eo_ite, native_ite, native_teq]
                  exact hfull

def fullSum (x y carry : Bool) : Bool :=
  (x != y) != carry

def fullCarry (x y carry : Bool) : Bool :=
  (x && y) || ((x != y) && carry)

def addBits : List Bool → List Bool → Bool → List Bool
  | [], [], _ => []
  | x :: xs, y :: ys, carry =>
      fullSum x y carry :: addBits xs ys (fullCarry x y carry)
  | _, _, _ => []

def addCarry : List Bool → List Bool → Bool → Bool
  | [], [], carry => carry
  | x :: xs, y :: ys, carry =>
      addCarry xs ys (fullCarry x y carry)
  | _, _, carry => carry

private def sumTerm (x y carry : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.xor)
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y))
    carry

private def carryTerm (x y carry : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.or)
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
          (Term.Boolean true))))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) carry)
            (Term.Boolean true))))
      (Term.Boolean false))

private theorem eval_sumTerm {M : SmtModel}
    {x y carry : Term} {xb yb cb : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb)
    (hc : __smtx_model_eval M (__eo_to_smt carry) = SmtValue.Boolean cb) :
    __smtx_model_eval M (__eo_to_smt (sumTerm x y carry)) =
      SmtValue.Boolean (fullSum xb yb cb) := by
  change
    __smtx_model_eval_xor
      (__smtx_model_eval_xor
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)))
      (__smtx_model_eval M (__eo_to_smt carry)) =
      SmtValue.Boolean (fullSum xb yb cb)
  rw [hx, hy, hc]
  cases xb <;> cases yb <;> cases cb <;> rfl

private theorem eval_carryTerm {M : SmtModel}
    {x y carry : Term} {xb yb cb : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb)
    (hc : __smtx_model_eval M (__eo_to_smt carry) = SmtValue.Boolean cb) :
    __smtx_model_eval M (__eo_to_smt (carryTerm x y carry)) =
      SmtValue.Boolean (fullCarry xb yb cb) := by
  change
    __smtx_model_eval_or
      (__smtx_model_eval_and
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt y))
          (SmtValue.Boolean true)))
      (__smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval_xor
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt y)))
          (__smtx_model_eval_and
            (__smtx_model_eval M (__eo_to_smt carry))
            (SmtValue.Boolean true)))
        (SmtValue.Boolean false)) =
      SmtValue.Boolean (fullCarry xb yb cb)
  rw [hx, hy, hc]
  cases xb <;> cases yb <;> cases cb <;> rfl

inductive BitPairEval (M : SmtModel) : Term → Bool → List Bool → Prop
  | intro (carryTerm bitsTerm : Term) (carry : Bool) (bits : List Bool)
      (carry_eval :
        __smtx_model_eval M (__eo_to_smt carryTerm) =
          SmtValue.Boolean carry)
      (bits_eval : BitListEval M bitsTerm bits) :
      BitPairEval M
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_pair) carryTerm) bitsTerm)
        carry bits

theorem BitPairEval.first_eval {M : SmtModel} {t : Term}
    {carry : Bool} {bits : List Bool} (h : BitPairEval M t carry bits) :
    __smtx_model_eval M (__eo_to_smt (__pair_first t)) =
      SmtValue.Boolean carry := by
  rcases h with ⟨ct, bt, carry, bits, hc, hb⟩
  exact hc

theorem BitPairEval.second {M : SmtModel} {t : Term}
    {carry : Bool} {bits : List Bool} (h : BitPairEval M t carry bits) :
    BitListEval M (__pair_second t) bits := by
  rcases h with ⟨ct, bt, carry, bits, hc, hb⟩
  exact hb

private theorem ripple_carry_eval_acc {M : SmtModel}
    {a b carry res : Term} {xs ys rs : List Bool} {cb : Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hc :
      __smtx_model_eval M (__eo_to_smt carry) =
        SmtValue.Boolean cb)
    (hr : BitListEval M res rs)
    (hlen : xs.length = ys.length) :
    BitPairEval M
      (__bv_ripple_carry_adder_2 a b carry res)
      (addCarry xs ys cb)
      (rs.reverse ++ addBits xs ys cb) := by
  induction ha generalizing b ys carry res rs cb with
  | nil =>
      cases hb with
      | nil =>
          rw [__bv_ripple_carry_adder_2.eq_4 carry res
            (term_ne_stuck_of_eval_boolean hc) hr.ne_stuck]
          have hrev := hr.rev
          rw [mk_apply_eq (by intro h; cases h) hrev.ne_stuck]
          simpa [addCarry, addBits] using
            BitPairEval.intro carry
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) res)
              cb rs.reverse hc (by simpa using hrev)
      | cons => simp at hlen
  | cons x xtail xb xs hx hxtail ih =>
      cases hb with
      | nil => simp at hlen
      | cons y ytail yb ys hy hytail =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hsum := eval_sumTerm hx hy hc
          have hcarry := eval_carryTerm hx hy hc
          have hnewRes :
              BitListEval M
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_from_bools)
                    (sumTerm x y carry))
                  res)
                (fullSum xb yb cb :: rs) :=
            BitListEval.cons (sumTerm x y carry) res
              (fullSum xb yb cb) rs hsum hr
          rw [__bv_ripple_carry_adder_2.eq_3 carry res x xtail y ytail
            (term_ne_stuck_of_eval_boolean hc) hr.ne_stuck]
          have hrec :=
            ih hytail hcarry hnewRes htail
          simpa [addBits, addCarry, List.reverse_cons,
            List.append_assoc] using hrec

theorem ripple_carry_eval {M : SmtModel}
    {a b carry : Term} {xs ys : List Bool} {cb : Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hc :
      __smtx_model_eval M (__eo_to_smt carry) =
        SmtValue.Boolean cb)
    (hlen : xs.length = ys.length) :
    BitPairEval M
      (__bv_ripple_carry_adder_2 a b carry (Term.Binary 0 0))
      (addCarry xs ys cb)
      (addBits xs ys cb) := by
  simpa using ripple_carry_eval_acc ha hb hc
    (BitListEval.nil (M := M)) hlen

theorem addBits_value :
    ∀ (xs ys : List Bool) (carry : Bool),
      xs.length = ys.length →
      bitsValue (addBits xs ys carry) +
          2 ^ xs.length * (addCarry xs ys carry).toNat =
        bitsValue xs + bitsValue ys + carry.toNat := by
  intro xs
  induction xs with
  | nil =>
      intro ys carry hlen
      cases ys
      · cases carry <;> decide
      · simp at hlen
  | cons x xs ih =>
      intro ys carry hlen
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hrec := ih ys (fullCarry x y carry) htail
          simp only [addBits, addCarry, bitsValue, List.length_cons,
            Nat.pow_succ]
          have hbit :
              (fullSum x y carry).toNat +
                  2 * (fullCarry x y carry).toNat =
                x.toNat + y.toNat + carry.toNat := by
            cases x <;> cases y <;> cases carry <;> decide
          have hmul :
              2 ^ xs.length * 2 *
                    (addCarry xs ys (fullCarry x y carry)).toNat =
                2 * (2 ^ xs.length *
                    (addCarry xs ys (fullCarry x y carry)).toNat) := by
            ac_rfl
          rw [hmul]
          omega

theorem addBits_length {xs ys : List Bool} {carry : Bool}
    (hlen : xs.length = ys.length) :
    (addBits xs ys carry).length = xs.length := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys
      · rfl
      · simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          simp only [addBits, List.length_cons]
          exact congrArg Nat.succ
            (ih (ys := ys) (carry := fullCarry x y carry) htail)

theorem addBits_value_mod {xs ys : List Bool} {carry : Bool}
    (hlen : xs.length = ys.length) :
    bitsValue (addBits xs ys carry) =
      (bitsValue xs + bitsValue ys + carry.toNat) % (2 ^ xs.length) := by
  have hval := addBits_value xs ys carry hlen
  have hlt := bitsValue_lt (addBits xs ys carry)
  rw [addBits_length hlen] at hlt
  rw [← hval]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]

theorem bitsValue_map_not :
    ∀ xs : List Bool,
      bitsValue (xs.map (!·)) = 2 ^ xs.length - 1 - bitsValue xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hlt := bitsValue_lt xs
      cases x <;>
        simp [bitsValue, ih, Nat.pow_succ]
      all_goals omega

private theorem native_mod_nat (a m : Nat) :
    native_mod_total (a : Int) (m : Int) = ((a % m : Nat) : Int) := by
  simp [native_mod_total]

theorem eval_addBits {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval_bvadd
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2 a b (Term.Boolean false)
              (Term.Binary 0 0)))) := by
  have hc :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
        SmtValue.Boolean false := by rfl
  have hadd := ripple_carry_eval ha hb hc hlen
  have hout := hadd.second
  rw [ha.eval, hb.eval, hout.eval]
  simp only [__smtx_model_eval_bvadd]
  rw [show (addBits xs ys false).length = xs.length from
    addBits_length hlen]
  rw [native_int_pow2_nat]
  simp only [native_zplus]
  have hplus :
      (↑(bitsValue xs) : Int) + ↑(bitsValue ys) =
        (↑(bitsValue xs + bitsValue ys) : Int) := by omega
  rw [hplus, native_mod_nat]
  congr 2
  norm_cast
  exact (addBits_value_mod (carry := false) hlen).symm

theorem eval_bitnot {M : SmtModel}
    {a : Term} {xs : List Bool} (ha : BitListEval M a xs) :
    __smtx_model_eval_bvnot
        (__smtx_model_eval M (__eo_to_smt a)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)) := by
  have hout := ha.apply_not
  rw [ha.eval, hout.eval]
  simp only [__smtx_model_eval_bvnot, native_binary_not,
    native_zplus, native_zneg]
  rw [native_int_pow2_nat, bitsValue_map_not]
  have hlt := bitsValue_lt xs
  have hltI :
      (↑(bitsValue xs) : Int) < (↑(2 ^ xs.length) : Int) := by
    exact_mod_cast hlt
  have hnonneg :
      0 ≤ (↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1) := by
    omega
  have hupper :
      (↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1) <
        (↑(2 ^ xs.length) : Int) := by
    have hp := Nat.two_pow_pos xs.length
    omega
  simp only [List.length_map]
  congr 1
  change
    ((↑(2 ^ xs.length) : Int) - (↑(bitsValue xs) + 1)) %
        (↑(2 ^ xs.length) : Int) =
      (↑(2 ^ xs.length - 1 - bitsValue xs) : Int)
  rw [Int.emod_eq_of_lt hnonneg hupper]
  norm_cast
  omega

theorem BitListEval.eval_bvxnor {M : SmtModel}
    {a b : Term} {xs ys : List Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b)) =
      __smtx_model_eval_bvxnor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) := by
  have heq := ha.apply_eq hb hlen
  have hxor := ha.apply_xor hb hlen
  have hnot := hxor.apply_not
  rw [heq.eval, zipWith_eq_eq_map_not_xor]
  rw [← hnot.eval]
  rw [← eval_bitnot hxor]
  rw [ha.eval_bvxor hb hlen]
  rfl

private theorem list_repeat_rec_from_bools {M : SmtModel}
    {bit : Term} {b : Bool}
    (hb :
      __smtx_model_eval M (__eo_to_smt bit) =
        SmtValue.Boolean b)
    (hty : __eo_typeof bit ≠ Term.Stuck) :
    ∀ n : Nat,
      BitListEval M
        (__eo_list_repeat_rec (Term.UOp UserOp._at_from_bools) bit n)
        (List.replicate n b) := by
  intro n
  induction n with
  | zero =>
      rw [__eo_list_repeat_rec.eq_4 _ _ 0
        (by intro h; cases h)
        (term_ne_stuck_of_eval_boolean hb)
        (by intro k hk; cases hk)]
      have hnil :
          __eo_nil (Term.UOp UserOp._at_from_bools) (__eo_typeof bit) =
            Term.Binary 0 0 := by
        cases ht : __eo_typeof bit <;> simp_all [__eo_nil]
      rw [hnil]
      exact BitListEval.nil
  | succ n ih =>
      rw [__eo_list_repeat_rec.eq_3 _ _ n
        (by intro h; cases h)
        (term_ne_stuck_of_eval_boolean hb)]
      rw [mk_apply_eq (by intro h; cases h) ih.ne_stuck]
      simpa [List.replicate_succ] using
        BitListEval.cons bit
          (__eo_list_repeat_rec (Term.UOp UserOp._at_from_bools) bit n)
          b (List.replicate n b) hb ih

theorem list_repeat_from_bools {M : SmtModel}
    {bit : Term} {b : Bool}
    (hb :
      __smtx_model_eval M (__eo_to_smt bit) =
        SmtValue.Boolean b)
    (hty : __eo_typeof bit ≠ Term.Stuck)
    (n : Nat) :
    BitListEval M
      (__eo_list_repeat (Term.UOp UserOp._at_from_bools) bit
        (Term.Numeral (n : Int)))
      (List.replicate n b) := by
  rw [__eo_list_repeat.eq_3 _ _ _ (by intro h; cases h)
    (term_ne_stuck_of_eval_boolean hb)]
  rw [show native_zlt (n : Int) 0 = false by
    simp [native_zlt]]
  simp only [native_ite, Bool.false_eq_true, if_false]
  rw [show native_int_to_nat (n : Int) = n by
    simp [native_int_to_nat]]
  exact list_repeat_rec_from_bools hb hty n

theorem bitsValue_replicate_false (n : Nat) :
    bitsValue (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bitsValue, ih]

theorem bitsValue_replicate_true (n : Nat) :
    bitsValue (List.replicate n true) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, bitsValue, ih, Nat.pow_succ]
      simp only [Bool.toNat_true]
      have hp := Nat.two_pow_pos n
      omega

def ultStep (x y previous : Bool) : Bool :=
  (x == y && previous) || (!x && y)

def ultBits : List Bool → List Bool → Bool → Bool
  | [], [], previous => previous
  | x :: xs, y :: ys, previous =>
      ultBits xs ys (ultStep x y previous)
  | _, _, _ => false

private def ultStepTerm (x y previous : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.or)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) previous)
          (Term.Boolean true))))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.and)
            (Term.Apply (Term.UOp UserOp.not) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
            (Term.Boolean true))))
      (Term.Boolean false))

private theorem eval_ultStepTerm {M : SmtModel}
    {x y previous : Term} {xb yb pb : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb)
    (hp :
      __smtx_model_eval M (__eo_to_smt previous) =
        SmtValue.Boolean pb) :
    __smtx_model_eval M (__eo_to_smt (ultStepTerm x y previous)) =
      SmtValue.Boolean (ultStep xb yb pb) := by
  change
    __smtx_model_eval_or
      (__smtx_model_eval_and
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt previous))
          (SmtValue.Boolean true)))
      (__smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval M (__eo_to_smt x)))
          (__smtx_model_eval_and
            (__smtx_model_eval M (__eo_to_smt y))
            (SmtValue.Boolean true)))
        (SmtValue.Boolean false)) =
      SmtValue.Boolean (ultStep xb yb pb)
  rw [hx, hy, hp]
  cases xb <;> cases yb <;> cases pb <;> rfl

private theorem bitblast_ult_rec_eval {M : SmtModel}
    {a b previous : Term} {xs ys : List Bool} {pb : Bool}
    (ha : BitListEval M a xs) (hb : BitListEval M b ys)
    (hp :
      __smtx_model_eval M (__eo_to_smt previous) =
        SmtValue.Boolean pb)
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_ult_rec a b previous)) =
      SmtValue.Boolean (ultBits xs ys pb) := by
  induction ha generalizing b ys previous pb with
  | nil =>
      cases hb with
      | nil =>
          rw [__bv_bitblast_ult_rec.eq_2 previous
            (term_ne_stuck_of_eval_boolean hp)]
          simpa [ultBits] using hp
      | cons => simp at hlen
  | cons x xtail xb xs hx hxtail ih =>
      cases hb with
      | nil => simp at hlen
      | cons y ytail yb ys hy hytail =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hstep := eval_ultStepTerm hx hy hp
          rw [__bv_bitblast_ult_rec.eq_3 previous x xtail y ytail
            (term_ne_stuck_of_eval_boolean hp)]
          simpa [ultBits] using ih hytail hstep htail

private theorem eval_ult_initial {M : SmtModel}
    {x y : Term} {xb yb orEqual : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean xb)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean yb) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_ite (Term.Boolean orEqual)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.or)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.and)
                    (Term.Apply (Term.UOp UserOp.not) x))
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
                    (Term.Boolean true))))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.or)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
                (Term.Boolean false)))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply (Term.UOp UserOp.not) x))
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) y)
                (Term.Boolean true))))) =
      SmtValue.Boolean (ultStep xb yb orEqual) := by
  cases orEqual with
  | false =>
    simp only [__eo_ite, native_teq, native_ite, Bool.false_eq_true,
      if_false]
    change
      __smtx_model_eval_and
        (__smtx_model_eval_not
          (__smtx_model_eval M (__eo_to_smt x)))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt y))
          (SmtValue.Boolean true)) =
        SmtValue.Boolean (ultStep xb yb false)
    rw [hx, hy]
    cases xb <;> cases yb <;> rfl
  | true =>
    simp only [__eo_ite, native_teq, native_ite, if_true]
    change
      __smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval M (__eo_to_smt x)))
          (__smtx_model_eval_and
            (__smtx_model_eval M (__eo_to_smt y))
            (SmtValue.Boolean true)))
        (__smtx_model_eval_or
          (__smtx_model_eval_eq
            (__smtx_model_eval M (__eo_to_smt x))
            (__smtx_model_eval M (__eo_to_smt y)))
          (SmtValue.Boolean false)) =
        SmtValue.Boolean (ultStep xb yb true)
    rw [hx, hy]
    cases xb <;> cases yb <;> rfl

theorem bitblast_ult_eval {M : SmtModel}
    {a b x y xtail ytail : Term} {xb yb orEqual : Bool}
    {xs ys : List Bool}
    (ha :
      BitListEval M
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)
        (xb :: xs))
    (hb :
      BitListEval M
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail)
        (yb :: ys))
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_ult
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail)
            (Term.Boolean orEqual))) =
      SmtValue.Boolean
        (ultBits (xb :: xs) (yb :: ys) orEqual) := by
  cases ha with
  | cons _ _ _ _ hx hxt =>
      cases hb with
      | cons _ _ _ _ hy hyt =>
          rw [__bv_bitblast_ult.eq_2 _ x xtail y ytail
            (by intro h; cases h)]
          have hinit := eval_ult_initial
            (orEqual := orEqual) hx hy
          simpa [ultBits] using
            bitblast_ult_rec_eval hxt hyt hinit hlen

theorem ultBits_spec :
    ∀ (xs ys : List Bool) (previous : Bool),
      xs.length = ys.length →
      ultBits xs ys previous =
        decide
          (bitsValue xs < bitsValue ys ∨
            (bitsValue xs = bitsValue ys ∧ previous = true)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys previous hlen
      cases ys
      · cases previous <;> decide
      · simp at hlen
  | cons x xs ih =>
      intro ys previous hlen
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := by simpa using hlen
          have hxle : x.toNat ≤ 1 := Bool.toNat_le x
          have hyle : y.toNat ≤ 1 := Bool.toNat_le y
          rw [ultBits, ih ys (ultStep x y previous) htail]
          by_cases hxy : bitsValue xs < bitsValue ys
          · have hall :
                bitsValue (x :: xs) < bitsValue (y :: ys) := by
              simp only [bitsValue]
              omega
            simp [hxy, hall]
          · by_cases hyx : bitsValue ys < bitsValue xs
            · have hnall :
                  ¬ bitsValue (x :: xs) < bitsValue (y :: ys) := by
                simp only [bitsValue]
                omega
              have hne : bitsValue xs ≠ bitsValue ys := by omega
              have hneall :
                  bitsValue (x :: xs) ≠ bitsValue (y :: ys) := by
                simp only [bitsValue]
                omega
              simp [hxy, hne, hnall, hneall]
            · have heq : bitsValue xs = bitsValue ys := by omega
              cases x <;> cases y <;> cases previous <;>
                simp [ultStep, bitsValue, heq]

theorem ultBits_false_lt {xs ys : List Bool}
    (hlen : xs.length = ys.length) :
    ultBits xs ys false = decide (bitsValue xs < bitsValue ys) := by
  rw [ultBits_spec xs ys false hlen]
  simp

theorem ultBits_true_le {xs ys : List Bool}
    (hlen : xs.length = ys.length) :
    ultBits xs ys true = decide (bitsValue xs ≤ bitsValue ys) := by
  rw [ultBits_spec xs ys true hlen]
  by_cases hlt : bitsValue xs < bitsValue ys
  · have hle : bitsValue xs ≤ bitsValue ys := Nat.le_of_lt hlt
    simp [hlt, hle]
  · by_cases heq : bitsValue xs = bitsValue ys
    · have hle : bitsValue xs ≤ bitsValue ys := by omega
      simp [hlt, heq, hle]
    · have hnle : ¬ bitsValue xs ≤ bitsValue ys := by omega
      simp [hlt, heq, hnle]

theorem bitsValue_append_singleton (xs : List Bool) (s : Bool) :
    bitsValue (xs ++ [s]) =
      bitsValue xs + 2 ^ xs.length * s.toNat := by
  induction xs with
  | nil => cases s <;> rfl
  | cons x xs ih =>
      cases x <;> cases s <;>
        simp [bitsValue, ih, Nat.pow_succ] <;> omega

private theorem msb_ofBoolListLE_append_singleton
    (xs : List Bool) (s : Bool) :
    (BitVec.ofBoolListLE (xs ++ [s])).msb = s := by
  cases s with
  | false =>
      apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
      rw [ofBoolListLE_toNat, bitsValue_append_singleton]
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero,
        List.length_append, List.length_singleton, Nat.pow_succ]
      have h := bitsValue_lt xs
      omega
  | true =>
      apply BitVec.msb_eq_true_iff_two_mul_ge.mpr
      rw [ofBoolListLE_toNat, bitsValue_append_singleton]
      simp only [Bool.toNat_true, Nat.mul_one, List.length_append,
        List.length_singleton, Nat.pow_succ]
      omega

private theorem toInt_ofBoolListLE_append_singleton
    (xs : List Bool) (s : Bool) :
    (BitVec.ofBoolListLE (xs ++ [s])).toInt =
      if s then (bitsValue xs : Int) - (2 ^ xs.length : Nat)
      else (bitsValue xs : Int) := by
  rw [BitVec.toInt_eq_msb_cond,
    msb_ofBoolListLE_append_singleton,
    ofBoolListLE_toNat, bitsValue_append_singleton]
  cases s <;>
    simp [Nat.pow_succ]
  omega

private theorem bitvec_toInt_cast {w v : Nat} (h : w = v)
    (x : BitVec w) :
    (BitVec.cast h x).toInt = x.toInt := by
  rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond,
    BitVec.msb_cast, BitVec.toNat_cast]
  subst v
  rfl

theorem ofBoolListLE_slt_append_singleton
    (xs ys : List Bool) (sx sy : Bool)
    (hlen : xs.length = ys.length) :
    (BitVec.ofBoolListLE (xs ++ [sx])).slt
        (BitVec.cast (by simp [hlen])
          (BitVec.ofBoolListLE (ys ++ [sy]))) =
      (((sx == sy) && decide (bitsValue xs < bitsValue ys)) ||
        (sx && !sy)) := by
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.slt_iff_toInt_lt]
  rw [bitvec_toInt_cast, toInt_ofBoolListLE_append_singleton,
    toInt_ofBoolListLE_append_singleton]
  cases sx <;> cases sy <;> simp
  all_goals
    have hx := bitsValue_lt xs
    have hy := bitsValue_lt ys
    have hp : (2 ^ xs.length : Nat) = 2 ^ ys.length :=
      congrArg (2 ^ ·) hlen
    have hxI : (bitsValue xs : Int) < (2 ^ xs.length : Nat) := by
      exact_mod_cast hx
    have hyI : (bitsValue ys : Int) < (2 ^ ys.length : Nat) := by
      exact_mod_cast hy
    have hpI :
        ((2 ^ xs.length : Nat) : Int) =
          ((2 ^ ys.length : Nat) : Int) := by
      exact_mod_cast hp
    have hpowCastX :
        (2 : Int) ^ xs.length = ((2 ^ xs.length : Nat) : Int) := by
      norm_cast
    have hpowCastY :
        (2 : Int) ^ ys.length = ((2 ^ ys.length : Nat) : Int) := by
      norm_cast
    omega

theorem ofBoolListLE_sle_append_singleton
    (xs ys : List Bool) (sx sy : Bool)
    (hlen : xs.length = ys.length) :
    (BitVec.ofBoolListLE (xs ++ [sx])).sle
        (BitVec.cast (by simp [hlen])
          (BitVec.ofBoolListLE (ys ++ [sy]))) =
      (((sx == sy) && decide (bitsValue xs ≤ bitsValue ys)) ||
        (sx && !sy)) := by
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.sle_iff_toInt_le]
  rw [bitvec_toInt_cast, toInt_ofBoolListLE_append_singleton,
    toInt_ofBoolListLE_append_singleton]
  cases sx <;> cases sy <;> simp
  all_goals
    have hx := bitsValue_lt xs
    have hy := bitsValue_lt ys
    have hp : (2 ^ xs.length : Nat) = 2 ^ ys.length :=
      congrArg (2 ^ ·) hlen
    have hxI : (bitsValue xs : Int) < (2 ^ xs.length : Nat) := by
      exact_mod_cast hx
    have hyI : (bitsValue ys : Int) < (2 ^ ys.length : Nat) := by
      exact_mod_cast hy
    have hpI :
        ((2 ^ xs.length : Nat) : Int) =
          ((2 ^ ys.length : Nat) : Int) := by
      exact_mod_cast hp
    have hpowCastX :
        (2 : Int) ^ xs.length = ((2 ^ xs.length : Nat) : Int) := by
      norm_cast
    have hpowCastY :
        (2 : Int) ^ ys.length = ((2 ^ ys.length : Nat) : Int) := by
      norm_cast
    omega

private theorem native_int_pow2_native_nat (n : Nat) :
    native_int_pow2 (native_nat_to_int n) =
      ((2 ^ n : Nat) : Int) := by
  have hn : ¬ ((n : Int) < 0) := by omega
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, hn]

theorem bvslt_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvslt
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (x.slt y) := by
  have hW0 : native_zleq 0 (W : Int) = true := by
    simpa [SmtEval.native_zleq] using Int.natCast_nonneg W
  have hWCast : (W : Int) = native_nat_to_int W := by
    simp [native_nat_to_int, SmtEval.native_nat_to_int]
  have hXCanon : native_zeq (x.toNat : Int)
      (native_mod_total (x.toNat : Int)
        (native_int_pow2 (W : Int))) = true := by
    rw [hWCast]
    rw [native_int_pow2_native_nat W]
    have hMod : (x.toNat : Int) % (2 ^ W : Nat) = x.toNat := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast x.isLt)
    simpa [SmtEval.native_zeq, SmtEval.native_mod_total] using hMod.symm
  have hYCanon : native_zeq (y.toNat : Int)
      (native_mod_total (y.toNat : Int)
        (native_int_pow2 (W : Int))) = true := by
    rw [hWCast]
    rw [native_int_pow2_native_nat W]
    have hMod : (y.toNat : Int) % (2 ^ W : Nat) = y.toNat := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast y.isLt)
    simpa [SmtEval.native_zeq, SmtEval.native_mod_total] using hMod.symm
  unfold __smtx_model_eval_bvslt
  rw [EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_uts
    hW0 hYCanon hXCanon]
  rw [native_binary_uts_eq_bitvec_toInt W (x.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt),
    native_binary_uts_eq_bitvec_toInt W (y.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast y.isLt)]
  rw [bitvec_ofInt_natCast_toNat, bitvec_ofInt_natCast_toNat]
  rfl

private theorem eval_bvsle_not_bvslt_swap_binary
    (w x y : native_Int) :
    __smtx_model_eval_bvsle
        (SmtValue.Binary w x) (SmtValue.Binary w y) =
      __smtx_model_eval_not
        (__smtx_model_eval_bvslt
          (SmtValue.Binary w y) (SmtValue.Binary w x)) := by
  have hWExpr : w + -1 + 1 + -(w + -1) = 1 := by
    grind
  simp [__smtx_model_eval_bvsle, __smtx_model_eval_bvsge,
    __smtx_model_eval_bvslt, __smtx_model_eval_bvsgt,
    __smtx_model_eval_bvugt, __smtx_model_eval_eq,
    __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_or, __smtx_model_eval_extract,
    __smtx_model_eval__, __smtx_bv_sizeof_value,
    native_binary_extract, native_zlt, native_veq, native_not,
    native_and, native_or, native_zplus, native_zneg, hWExpr]
  generalize hsx :
      decide
        (native_mod_total
          (native_div_total x (native_int_pow2 (w + -1)))
          (native_int_pow2 1) = 1) = sx
  generalize hsy :
      decide
        (native_mod_total
          (native_div_total y (native_int_pow2 (w + -1)))
          (native_int_pow2 1) = 1) = sy
  cases sx <;> cases sy <;>
    by_cases hxy : x < y <;>
    by_cases hyx : y < x <;>
    simp [hxy, hyx, Int.ne_of_lt, Int.ne_of_gt] <;> grind

theorem bvsle_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvsle
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (x.sle y) := by
  rw [eval_bvsle_not_bvslt_swap_binary, bvslt_bitvec_values]
  change SmtValue.Boolean (!(y.slt x)) =
    SmtValue.Boolean (x.sle y)
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [BitVec.sle_iff_toInt_le]
  rw [Bool.not_eq_true']
  change y.slt x = false ↔ x.toInt ≤ y.toInt
  simp [BitVec.slt_eq_decide]

theorem bitListEval_cons_shape {M : SmtModel}
    {t : Term} {b : Bool} {bs : List Bool}
    (h : BitListEval M t (b :: bs)) :
    ∃ head tail,
      t =
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) head) tail ∧
      __smtx_model_eval M (__eo_to_smt head) =
        SmtValue.Boolean b ∧
      BitListEval M tail bs := by
  cases h
  exact ⟨_, _, rfl, ‹_›, ‹_›⟩

private theorem eval_signed_sign_bit {M : SmtModel}
    {x y : Term} {sx sy : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Boolean sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Boolean sy) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
              (Term.Apply (Term.UOp UserOp.not) y))
              (Term.Boolean true)))) =
      SmtValue.Boolean (sx && !sy) := by
  change
    __smtx_model_eval_and
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval_and
        (__smtx_model_eval_not
          (__smtx_model_eval M (__eo_to_smt y)))
        (SmtValue.Boolean true)) =
      _
  rw [hx, hy]
  cases sx <;> cases sy <;> rfl

private theorem eval_signed_formula {M : SmtModel}
    {x y mag : Term} {sx sy m : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Boolean sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Boolean sy)
    (hm : __smtx_model_eval M (__eo_to_smt mag) =
      SmtValue.Boolean m) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.or)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.and)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.eq) x) y))
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.and) mag)
                  (Term.Boolean true))))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.or)
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                    (Term.Apply (Term.UOp UserOp.not) y))
                    (Term.Boolean true))))
              (Term.Boolean false)))) =
      SmtValue.Boolean
        (((sx == sy) && m) || (sx && !sy)) := by
  change
    __smtx_model_eval_or
      (__smtx_model_eval_and
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)))
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt mag))
          (SmtValue.Boolean true)))
      (__smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval M (__eo_to_smt y)))
            (SmtValue.Boolean true)))
        (SmtValue.Boolean false)) =
      _
  rw [hx, hy, hm]
  cases sx <;> cases sy <;> cases m <;> rfl

private theorem eval_single_signed_formula {M : SmtModel}
    {x y : Term} {sx sy : Bool}
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Boolean sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Boolean sy) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.or)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.or)
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                    (Term.Apply (Term.UOp UserOp.not) y))
                    (Term.Boolean true))))
              (Term.Boolean false)))) =
      SmtValue.Boolean ((sx == sy) || (sx && !sy)) := by
  change
    __smtx_model_eval_or
      (__smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)))
      (__smtx_model_eval_or
        (__smtx_model_eval_and
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval M (__eo_to_smt y)))
            (SmtValue.Boolean true)))
        (SmtValue.Boolean false)) =
      _
  rw [hx, hy]
  cases sx <;> cases sy <;> rfl

theorem bitblast_slt_impl_eval {M : SmtModel}
    {x xt y yt : Term} {sx sy orEqual : Bool}
    {xs ys : List Bool}
    (ha : BitListEval M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) x) xt)
      (sx :: xs))
    (hb : BitListEval M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) y) yt)
      (sy :: ys))
    (hlen : xs.length = ys.length) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) x) xt)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) y) yt)
            (Term.Boolean orEqual))) =
      SmtValue.Boolean
        (((sx == sy) && ultBits xs.reverse ys.reverse orEqual) ||
          (sx && !sy)) := by
  cases ha with
  | cons _ _ _ _ hx hxt =>
    cases hb with
    | cons _ _ _ _ hy hyt =>
      cases hxt with
      | nil =>
        cases hyt with
        | nil =>
          rw [__bv_bitblast_slt_impl.eq_2
            (Term.Boolean orEqual) x y (by intro h; cases h)]
          cases orEqual <;>
            simp only [__eo_ite, native_ite, native_teq,
              Bool.false_eq_true, if_false, if_true]
          · simpa [ultBits] using eval_signed_sign_bit hx hy
          · simpa [ultBits] using eval_single_signed_formula hx hy
        | cons =>
          simp at hlen
      | cons x2 xt2 sx2 xs2 hx2 hxt2 =>
        cases hyt with
        | nil =>
          simp at hlen
        | cons y2 yt2 sy2 ys2 hy2 hyt2 =>
          have hxtEval :
              BitListEval M
                (Term.Apply
                  (Term.Apply
                    (Term.UOp UserOp._at_from_bools) x2) xt2)
                (sx2 :: xs2) :=
            BitListEval.cons x2 xt2 sx2 xs2 hx2 hxt2
          have hytEval :
              BitListEval M
                (Term.Apply
                  (Term.Apply
                    (Term.UOp UserOp._at_from_bools) y2) yt2)
                (sy2 :: ys2) :=
            BitListEval.cons y2 yt2 sy2 ys2 hy2 hyt2
          have hxr := hxtEval.rev
          have hyr := hytEval.rev
          have hxrNe : (sx2 :: xs2).reverse ≠ [] := by simp
          have hyrNe : (sy2 :: ys2).reverse ≠ [] := by simp
          rcases List.exists_cons_of_ne_nil hxrNe with
            ⟨xrb, xrs, hxrList⟩
          rcases List.exists_cons_of_ne_nil hyrNe with
            ⟨yrb, yrs, hyrList⟩
          rw [hxrList] at hxr
          rw [hyrList] at hyr
          rcases bitListEval_cons_shape hxr with
            ⟨xr, xrt, hxrTerm, hxrHead, hxrTail⟩
          rcases bitListEval_cons_shape hyr with
            ⟨yr, yrt, hyrTerm, hyrHead, hyrTail⟩
          have hult :=
            bitblast_ult_eval
              (a := __eo_list_rev
                (Term.UOp UserOp._at_from_bools)
                (Term.Apply
                  (Term.Apply
                    (Term.UOp UserOp._at_from_bools) x2) xt2))
              (b := __eo_list_rev
                (Term.UOp UserOp._at_from_bools)
                (Term.Apply
                  (Term.Apply
                    (Term.UOp UserOp._at_from_bools) y2) yt2))
              (orEqual := orEqual)
              (BitListEval.cons xr xrt xrb xrs hxrHead hxrTail)
              (BitListEval.cons yr yrt yrb yrs hyrHead hyrTail)
              (by
                have hrlen :
                    (sx2 :: xs2).reverse.length =
                      (sy2 :: ys2).reverse.length := by
                  simpa using hlen
                simpa [hxrList, hyrList] using hrlen)
          rw [← hxrTerm] at hult
          rw [← hyrTerm] at hult
          rw [← hxrList, ← hyrList] at hult
          have hultNe := term_ne_stuck_of_eval_boolean hult
          rw [__bv_bitblast_slt_impl.eq_3
            (Term.Boolean orEqual) x
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_from_bools) x2) xt2)
              y
              (Term.Apply
                (Term.Apply
                  (Term.UOp UserOp._at_from_bools) y2) yt2)
            (by intro h; cases h)
            (by intro h; cases h)]
          simp only [__eo_mk_apply, hultNe]
          exact eval_signed_formula hx hy hult

private def reifyBits (p i : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => p.testBit i :: reifyBits p (i + 1) n

@[simp] private theorem reifyBits_length (p i n : Nat) :
    (reifyBits p i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [reifyBits, ih]

private theorem reifyBits_getD (p i n j : Nat) (hj : j < n) :
    (reifyBits p i n).getD j false = p.testBit (i + j) := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [reifyBits]
    | succ j =>
      simp only [reifyBits, List.getD_cons_succ]
      rw [ih (i := i + 1) (j := j) (by omega)]
      congr 1
      omega

private theorem bitsValue_reifyBits (p W : Nat) (hp : p < 2 ^ W) :
    bitsValue (reifyBits p 0 W) = p := by
  let lhs : BitVec W :=
    BitVec.cast (reifyBits_length p 0 W)
      (BitVec.ofBoolListLE (reifyBits p 0 W))
  let rhs := BitVec.ofNat W p
  have heq : lhs = rhs := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [lhs, rhs, BitVec.getLsbD_cast,
      BitVec.getLsbD_ofBoolListLE, BitVec.getLsbD_ofNat]
    rw [reifyBits_getD p 0 W i hi]
    simp [hi]
  have hnat := congrArg BitVec.toNat heq
  simpa [lhs, rhs, BitVec.toNat_cast, ofBoolListLE_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using hnat

private theorem eval_at_bit
    (M : SmtModel) (a : Term) (W i : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (ha :
      __smtx_model_eval M (__eo_to_smt a) =
        SmtValue.Binary (W : Int) p) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.UOp1 UserOp1._at_bit (Term.Numeral (i : Int))) a)) =
      SmtValue.Boolean ((BitVec.ofInt W p).getLsbD i) := by
  change
    __smtx_model_eval_eq
      (__smtx_model_eval_extract
        (__smtx_model_eval M (SmtTerm.Numeral (i : Int)))
        (__smtx_model_eval M (SmtTerm.Numeral (i : Int)))
        (__smtx_model_eval M (__eo_to_smt a)))
      (SmtValue.Binary 1 1) =
    _
  rw [ha]
  rw [show __smtx_model_eval M (SmtTerm.Numeral (i : Int)) =
      SmtValue.Numeral (i : Int) by
    rw [__smtx_model_eval.eq_def] <;> simp only]
  have hi0 : ¬ ((i : Int) < 0) := by omega
  have hone : (i : Int) + 1 + -(i : Int) = 1 := by omega
  simp [__smtx_model_eval_extract, __smtx_model_eval_eq,
    native_binary_extract, native_int_pow2, native_zexp_total,
    native_div_total, native_mod_total, native_veq,
    native_zplus, native_zneg, BitVec.getLsbD, BitVec.toNat_ofInt,
    hp0, hp1, hi0, hone, Int.emod_eq_of_lt,
    Nat.testBit_eq_decide_div_mod_eq]
  have hpcast : (p.toNat : Int) = p := by omega
  rw [← hpcast]
  norm_cast

private theorem reify_rec_eval
    (M : SmtModel) (a : Term) (W i n : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hin : i + n ≤ W)
    (ha :
      __smtx_model_eval M (__eo_to_smt a) =
        SmtValue.Binary (W : Int) p) :
    BitListEval M (__bv_bitblast_reify_rec a i n)
      (reifyBits p.toNat i n) := by
  induction n generalizing i with
  | zero =>
    exact BitListEval.nil
  | succ n ih =>
    rw [__bv_bitblast_reify_rec]
    exact BitListEval.cons _ _ _ _
      (by
        simpa [BitVec.getLsbD, BitVec.toNat_ofInt,
          Int.emod_eq_of_lt hp0 hp1] using
            eval_at_bit M a W i p hp0 hp1 ha)
      (ih (i := i + 1) (by omega))

private theorem reify_rec_full_eval
    (M : SmtModel) (a : Term) (W : Nat) (p : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (ha :
      __smtx_model_eval M (__eo_to_smt a) =
        SmtValue.Binary (W : Int) p) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_reify_rec a 0 W)) =
      __smtx_model_eval M (__eo_to_smt a) := by
  have hlist := reify_rec_eval M a W 0 W p hp0 hp1 (by omega) ha
  rw [hlist.eval, ha]
  simp only [reifyBits_length]
  rw [bitsValue_reifyBits p.toNat W]
  · have hpcast : (p.toNat : Int) = p := by omega
    rw [hpcast]
  · have hpcast : (p.toNat : Int) = p := by omega
    rw [← hpcast] at hp1
    exact_mod_cast hp1

private theorem reify_shape (a : Term)
    (h : __bv_bitblast_reify a ≠ Term.Stuck) :
    ∃ w : Int,
      __eo_typeof a =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
        0 ≤ w ∧
        __bv_bitblast_reify a =
          __bv_bitblast_reify_rec a 0 w.toNat := by
  unfold __bv_bitblast_reify at h ⊢
  split at *
  all_goals try simp_all
  split at *
  all_goals try simp_all
  rename_i _ _ _ w heo
  rcases h with ⟨hw, hrec⟩
  have hneg : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [hneg]

theorem eval_step_reify
    (M : SmtModel) (hM : model_total_typed M) (a : Term)
    (hExpanded : __bv_bitblast_reify a ≠ Term.Stuck)
    (hnn : term_has_non_none_type (__eo_to_smt a)) :
    __smtx_model_eval M (__eo_to_smt (__bv_bitblast_reify a)) =
      __smtx_model_eval M (__eo_to_smt a) := by
  rcases reify_shape a hExpanded with
    ⟨w, heo, hwNN, hExpandedEq⟩
  rw [hExpandedEq]
  have htrans : RuleProofs.eo_has_smt_translation a := hnn
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width
      a (Term.Numeral w) htrans heo with
    ⟨w', hw', hw0, haTy⟩
  injection hw' with hww
  subst w'
  rcases smt_eval_binary_of_smt_type_bitvec
      M hM (__eo_to_smt a) w.toNat haTy with
    ⟨p, ha, hcan⟩
  have hrange :=
    bitvec_payload_range_of_canonical
      (w := (w.toNat : Int)) (n := p)
        (by
          unfold native_zleq
          exact decide_eq_true (Int.natCast_nonneg _)) hcan
  apply reify_rec_full_eval M a w.toNat p
  · exact hrange.1
  · simpa only [native_int_pow2_nat, Int.natCast_pow] using hrange.2
  · exact ha

theorem eval_step_bvnot (M : SmtModel) (hM : model_total_typed M)
    (a : Term)
    (hExpanded :
      __bv_bitblast_apply_unary (Term.UOp UserOp.not) a ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) a))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) a)) := by
  have hs := bitblast_apply_unary_syntax _ _ hExpanded
  change
    term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt a)) at hnn
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvnot)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  rcases hs.eval hM haNN with ⟨xs, ha⟩
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval M (__eo_to_smt a))
  exact (eval_bitnot ha).symm

theorem eval_step_bvand (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_apply_binary (Term.UOp UserOp.and) a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and) a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b)) := by
  have hs := bitblast_apply_binary_same_length _ _ _ hExpanded
  change
    term_has_non_none_type
      (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvand)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.and) a b)) =
      __smtx_model_eval_bvand
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact ha.eval_bvand hb hlen

theorem eval_step_bvor (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_apply_binary (Term.UOp UserOp.or) a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.or) a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b)) := by
  have hs := bitblast_apply_binary_same_length _ _ _ hExpanded
  change
    term_has_non_none_type
      (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvor)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.or) a b)) =
      __smtx_model_eval_bvor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact ha.eval_bvor hb hlen

theorem eval_step_bvxor (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b)) := by
  have hs := bitblast_apply_binary_same_length _ _ _ hExpanded
  change
    term_has_non_none_type
      (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvxor)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.xor) a b)) =
      __smtx_model_eval_bvxor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact ha.eval_bvxor hb hlen

theorem eval_step_bvxnor (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) a) b)) := by
  have hs := bitblast_apply_binary_same_length _ _ _ hExpanded
  change
    term_has_non_none_type
      (SmtTerm.bvxnor (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvxnor)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_apply_binary (Term.UOp UserOp.eq) a b)) =
      __smtx_model_eval_bvxnor
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact ha.eval_bvxnor hb hlen

theorem eval_ripple_bvadd (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __pair_second
          (__bv_ripple_carry_adder_2 a b (Term.Boolean false)
            (Term.Binary 0 0)) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2 a b (Term.Boolean false)
              (Term.Binary 0 0)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b)) := by
  have hRipple := pair_second_arg_ne_stuck hExpanded
  have hs := ripple_carry_same_length _ _ _ _ hRipple
  change
    term_has_non_none_type
      (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvadd)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  change
    __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2 a b (Term.Boolean false)
              (Term.Binary 0 0)))) =
      __smtx_model_eval_bvadd
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  exact (eval_addBits ha hb hlen).symm

theorem eval_step_bvult (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_ult a b (Term.Boolean false) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_ult a b (Term.Boolean false))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b)) := by
  rcases bitblast_ult_shape a b (Term.Boolean false) hExpanded with
    ⟨x, xtail, y, ytail, rfl, rfl, hs⟩
  change
    term_has_non_none_type
      (SmtTerm.bvult
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail))
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail))) at hnn
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvult) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail)) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  have hsFull := BitListsSameLength.cons x xtail y ytail hs
  rcases hsFull.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hsFull.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  cases ha with
  | cons _ _ xb xbs hx hxt =>
      cases hb with
      | cons _ _ yb ybs hy hyt =>
          have htail := hs.eval_length hxt hyt
          have hout := bitblast_ult_eval
            (a := Term.Stuck) (b := Term.Stuck)
            (orEqual := false)
            (BitListEval.cons x xtail xb xbs hx hxt)
            (BitListEval.cons y ytail yb ybs hy hyt) htail
          rw [hout]
          change
            SmtValue.Boolean (ultBits (xb :: xbs) (yb :: ybs) false) =
              __smtx_model_eval_bvult
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_from_bools) x)
                      xtail)))
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_from_bools) y)
                      ytail)))
          rw [(BitListEval.cons x xtail xb xbs hx hxt).eval,
            (BitListEval.cons y ytail yb ybs hy hyt).eval]
          rw [ultBits_false_lt (by simpa using htail)]
          simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
            native_zlt]

theorem eval_step_bvule (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_ult a b (Term.Boolean true) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_bitblast_ult a b (Term.Boolean true))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) a) b)) := by
  rcases bitblast_ult_shape a b (Term.Boolean true) hExpanded with
    ⟨x, xtail, y, ytail, rfl, rfl, hs⟩
  change
    term_has_non_none_type
      (SmtTerm.bvule
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail))
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail))) at hnn
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvule) (ret := SmtType.Bool)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) x) xtail)) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at_from_bools) y) ytail)) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  have hsFull := BitListsSameLength.cons x xtail y ytail hs
  rcases hsFull.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hsFull.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  cases ha with
  | cons _ _ xb xbs hx hxt =>
      cases hb with
      | cons _ _ yb ybs hy hyt =>
          have htail := hs.eval_length hxt hyt
          have hout := bitblast_ult_eval
            (a := Term.Stuck) (b := Term.Stuck)
            (orEqual := true)
            (BitListEval.cons x xtail xb xbs hx hxt)
            (BitListEval.cons y ytail yb ybs hy hyt) htail
          rw [hout]
          change
            SmtValue.Boolean (ultBits (xb :: xbs) (yb :: ybs) true) =
              __smtx_model_eval_bvule
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_from_bools) x)
                      xtail)))
                (__smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_from_bools) y)
                      ytail)))
          rw [(BitListEval.cons x xtail xb xbs hx hxt).eval,
            (BitListEval.cons y ytail yb ybs hy hyt).eval]
          rw [ultBits_true_le (by simpa using htail)]
          simp [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
            __smtx_model_eval_bvugt, __smtx_model_eval_or,
            __smtx_model_eval_eq, native_zlt, native_veq, native_or]
          by_cases hlt :
              bitsValue (xb :: xbs) < bitsValue (yb :: ybs)
          · have hle :
                bitsValue (xb :: xbs) ≤ bitsValue (yb :: ybs) :=
              Nat.le_of_lt hlt
            simp [hlt, hle]
          · by_cases heq :
                bitsValue (xb :: xbs) = bitsValue (yb :: ybs)
            · simp [hlt, heq, htail]
            · have hnle :
                  ¬ bitsValue (xb :: xbs) ≤ bitsValue (yb :: ybs) := by
                omega
              have hneI :
                  ¬ (bitsValue (yb :: ybs) : Int) =
                    (bitsValue (xb :: xbs) : Int) := by
                intro h
                apply heq
                exact_mod_cast h.symm
              simp [hlt, hnle, htail, hneI]

theorem eval_step_eq (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __eo_list_singleton_elim (Term.UOp UserOp.and)
          (__bv_mk_bitblast_step_eq_rec a b) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.and)
            (__bv_mk_bitblast_step_eq_rec a b))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) := by
  have hrec := singleton_elim_arg_ne_stuck hExpanded
  have hs := eq_rec_same_length a b hrec
  change
    __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a))
        (__smtx_typeof (__eo_to_smt b)) ≠
      SmtType.None at hnn
  simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
    native_Teq] at hnn
  rcases hnn with ⟨haNN, hsame⟩
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [← hsame]
    exact haNN
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  have hlen := hs.eval_length ha hb
  rw [ha.eq_step_eval hb hlen]
  change
    SmtValue.Boolean (bitsEq xs ys) =
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  rw [ha.eval, hb.eval]
  by_cases hxy : xs = ys
  · subst ys
    rw [(bitsEq_eq_true_iff).2 rfl]
    simp [__smtx_model_eval_eq, native_veq]
  · have hbits : bitsEq xs ys = false := by
      apply Bool.eq_false_iff.mpr
      simpa [bitsEq_eq_true_iff]
    have hval : bitsValue xs ≠ bitsValue ys := by
      intro hv
      exact hxy (bitsValue_inj_of_length hlen hv)
    have hvalI :
        (bitsValue xs : Int) ≠ (bitsValue ys : Int) := by
      exact_mod_cast hval
    rw [hbits]
    simp [__smtx_model_eval_eq, native_veq, hlen, hvalI]

theorem eval_step_bvsub (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __pair_second
          (__bv_ripple_carry_adder_2 a
            (__bv_bitblast_apply_unary (Term.UOp UserOp.not) b)
            (Term.Boolean true) (Term.Binary 0 0)) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2 a
              (__bv_bitblast_apply_unary (Term.UOp UserOp.not) b)
              (Term.Boolean true) (Term.Binary 0 0)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b)) := by
  have hRipple := pair_second_arg_ne_stuck hExpanded
  have hs := ripple_carry_same_length _ _ _ _ hRipple
  have hnotNe := hs.syntax_right.ne_stuck
  have hbSyntax := bitblast_apply_unary_syntax _ _ hnotNe
  change
    term_has_non_none_type
      (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvsub)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hbSyntax.eval hM hbNN with ⟨ys, hb⟩
  have hbnot := hb.apply_not
  have hlen := hs.eval_length ha hbnot
  have hout :=
    (ripple_carry_eval
      (carry := Term.Boolean true) (cb := true)
      ha hbnot (by rfl) hlen).second
  rw [hout.eval]
  change
    SmtValue.Binary ((addBits xs (ys.map (!·)) true).length : Int)
        (bitsValue (addBits xs (ys.map (!·)) true) : Int) =
      __smtx_model_eval_bvsub
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  rw [ha.eval, hb.eval]
  rw [addBits_length hlen, addBits_value_mod hlen,
    bitsValue_map_not]
  have hlists : xs.length = ys.length := by simpa using hlen
  rw [show ys.length = xs.length by omega]
  simp only [__smtx_model_eval_bvsub, __smtx_model_eval_bvneg,
    __smtx_model_eval_bvadd, native_zneg, native_zplus]
  rw [native_int_pow2_nat]
  simp [native_mod_total]
  have hylt : bitsValue ys < 2 ^ xs.length := by
    simpa [hlists] using bitsValue_lt ys
  have hyle : bitsValue ys ≤ 2 ^ xs.length - 1 := by omega
  have hOne : 1 ≤ 2 ^ xs.length := by
    have := Nat.two_pow_pos xs.length
    omega
  calc
    (↑(bitsValue xs) + ↑(2 ^ xs.length - 1 - bitsValue ys) + 1) %
        (2 ^ xs.length : Int) =
        ((bitsValue xs : Int) - bitsValue ys +
          (2 ^ xs.length : Nat)) % (2 ^ xs.length : Int) := by
            congr 1
            rw [Int.ofNat_sub hyle, Int.ofNat_sub hOne]
            omega
    _ = ((bitsValue xs : Int) - bitsValue ys) %
          (2 ^ xs.length : Int) := by
            rw [Int.add_emod]
            simp
    _ = ((bitsValue xs : Int) + -(bitsValue ys : Int)) %
          (2 ^ xs.length : Int) := by rfl

theorem eval_step_bvneg (M : SmtModel) (hM : model_total_typed M)
    (a : Term)
    (hExpanded :
      __pair_second
          (__bv_ripple_carry_adder_2
            (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)
            (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
              (Term.Boolean false) (__bv_bitwidth (__eo_typeof a)))
            (Term.Boolean true) (Term.Binary 0 0)) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) a))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__pair_second
            (__bv_ripple_carry_adder_2
              (__bv_bitblast_apply_unary (Term.UOp UserOp.not) a)
              (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
                (Term.Boolean false) (__bv_bitwidth (__eo_typeof a)))
              (Term.Boolean true) (Term.Binary 0 0)))) =
      __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) a)) := by
  have hRipple := pair_second_arg_ne_stuck hExpanded
  have hs := ripple_carry_same_length _ _ _ _ hRipple
  have hnotNe := hs.syntax_left.ne_stuck
  have haSyntax := bitblast_apply_unary_syntax _ _ hnotNe
  change
    term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt a)) at hnn
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvneg)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  rcases haSyntax.eval hM haNN with ⟨xs, ha⟩
  have haTrans : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [haTy]
    intro h
    cases h
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a haTrans
  have hEoSmt :
      __eo_to_smt_type (__eo_typeof a) = SmtType.BitVec w := by
    rw [← hMatch, haTy]
  have hEoTy :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hEoSmt
  have hWidth :
      __bv_bitwidth (__eo_typeof a) =
        Term.Numeral (native_nat_to_int w) := by
    rw [hEoTy]
    rfl
  have hzero :
      BitListEval M
        (__eo_list_repeat (Term.UOp UserOp._at_from_bools)
          (Term.Boolean false) (__bv_bitwidth (__eo_typeof a)))
        (List.replicate w false) := by
    rw [hWidth]
    simpa [native_nat_to_int] using
      (list_repeat_from_bools (M := M) (bit := Term.Boolean false)
        (b := false) (by rfl) (by intro h; cases h) w)
  have hanot := ha.apply_not
  have hlen := hs.eval_length hanot hzero
  have hout :=
    (ripple_carry_eval
      (carry := Term.Boolean true) (cb := true)
      hanot hzero (by rfl) hlen).second
  rw [hout.eval]
  change
    SmtValue.Binary
        ((addBits (xs.map (!·)) (List.replicate w false) true).length : Int)
        (bitsValue
          (addBits (xs.map (!·)) (List.replicate w false) true) : Int) =
      __smtx_model_eval_bvneg
        (__smtx_model_eval M (__eo_to_smt a))
  rw [ha.eval]
  rw [addBits_length hlen, addBits_value_mod hlen,
    bitsValue_map_not, bitsValue_replicate_false]
  have hlists : xs.length = w := by simpa using hlen
  simp only [List.length_map]
  simp only [__smtx_model_eval_bvneg, native_zneg]
  rw [native_int_pow2_nat]
  simp [native_mod_total]
  have hxlt := bitsValue_lt xs
  have hxle : bitsValue xs ≤ 2 ^ xs.length - 1 := by omega
  have hOne : 1 ≤ 2 ^ xs.length := by
    have := Nat.two_pow_pos xs.length
    omega
  calc
    (↑(2 ^ xs.length - 1 - bitsValue xs) + 0 + 1) %
        (2 ^ xs.length : Int) =
        ((-(bitsValue xs : Int)) +
          (2 ^ xs.length : Nat)) % (2 ^ xs.length : Int) := by
            congr 1
            rw [Int.ofNat_sub hxle, Int.ofNat_sub hOne]
            omega
    _ = (-(bitsValue xs : Int)) %
          (2 ^ xs.length : Int) := by
            rw [Int.add_emod]
            simp

theorem eval_step_bvite (M : SmtModel) (hM : model_total_typed M)
    (c a b : Term)
    (hExpanded : __bv_mk_bitblast_step_ite c a b ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt (__bv_mk_bitblast_step_ite c a b)) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) a) b)) := by
  rcases bitblast_step_ite_shape c a b hExpanded with ⟨cbit, rfl, hs⟩
  change
    term_has_non_none_type
      (SmtTerm.ite
        (SmtTerm.eq
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) cbit)
              (Term.Binary 0 0)))
          (SmtTerm.Binary 1 1))
        (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases ite_args_of_non_none hnn with
    ⟨T, hcTy, haTy, hbTy, hT⟩
  change
    __smtx_typeof_eq
        (__smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_from_bools) cbit)
              (Term.Binary 0 0))))
        (SmtType.BitVec 1) =
      SmtType.Bool at hcTy
  rcases (RuleProofs.smtx_typeof_eq_bool_iff _ _).mp hcTy with
    ⟨hcSame, hcNN⟩
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    exact hT
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    exact hT
  have hcSyntax :
      BitListSyntax
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at_from_bools) cbit)
          (Term.Binary 0 0)) :=
    BitListSyntax.cons cbit (Term.Binary 0 0) BitListSyntax.nil
  rcases hcSyntax.eval hM hcNN with ⟨cs, hc⟩
  rcases hs.syntax_left.eval hM haNN with ⟨xs, ha⟩
  rcases hs.syntax_right.eval hM hbNN with ⟨ys, hb⟩
  cases hc with
  | cons _ _ cb cbs hcbit hctail =>
      cases hctail with
      | nil =>
          have hlen := hs.eval_length ha hb
          have hout := bitblast_step_ite_eval hcbit ha hb hlen
          rw [hout.eval]
          change
            SmtValue.Binary
                ((List.zipWith
                  (fun x y => if cb then x else y) xs ys).length : Int)
                (bitsValue
                  (List.zipWith
                    (fun x y => if cb then x else y) xs ys) : Int) =
              __smtx_model_eval_ite
                (__smtx_model_eval_eq
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply
                          (Term.UOp UserOp._at_from_bools) cbit)
                        (Term.Binary 0 0))))
                  (SmtValue.Binary 1 1))
                (__smtx_model_eval M (__eo_to_smt a))
                (__smtx_model_eval M (__eo_to_smt b))
          rw [(BitListEval.cons cbit (Term.Binary 0 0) cb [] hcbit
            (BitListEval.nil (M := M))).eval, ha.eval, hb.eval]
          cases cb
          · simp only [Bool.false_eq_true, if_false]
            rw [zipWith_right_of_length xs ys hlen]
            rfl
          · simp only [if_true]
            rw [zipWith_left_of_length xs ys hlen]
            rfl

theorem eval_step_bvcomp (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
            (__eo_list_singleton_elim (Term.UOp UserOp.and)
              (__bv_mk_bitblast_step_eq_rec a b)))
          (Term.Binary 0 0) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
              (__eo_list_singleton_elim (Term.UOp UserOp.and)
                (__bv_mk_bitblast_step_eq_rec a b)))
            (Term.Binary 0 0))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) a) b)) := by
  let c :=
    __eo_list_singleton_elim (Term.UOp UserOp.and)
      (__bv_mk_bitblast_step_eq_rec a b)
  have hinner :
      __eo_mk_apply (Term.UOp UserOp._at_from_bools) c ≠ Term.Stuck :=
    mk_apply_fun_ne_stuck hExpanded
  have hcNe : c ≠ Term.Stuck :=
    mk_apply_arg_ne_stuck hinner
  change
    term_has_non_none_type
      (SmtTerm.bvcomp (__eo_to_smt a) (__eo_to_smt b)) at hnn
  rcases bv_binop_ret_args_of_non_none
      (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1)
      (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
    ⟨w, haTy, hbTy⟩
  have heqNN :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) := by
    change
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a))
          (__smtx_typeof (__eo_to_smt b)) ≠
        SmtType.None
    rw [haTy, hbTy]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  have hcEq := eval_step_eq M hM a b hcNe heqNN
  change
    __smtx_model_eval M (__eo_to_smt c) =
      __smtx_model_eval_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) at hcEq
  rcases eval_eq_is_boolean
      (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) with ⟨cb, heq⟩
  have hc : __smtx_model_eval M (__eo_to_smt c) =
      SmtValue.Boolean cb := hcEq.trans heq
  rw [wrap_bool_eval hc]
  change
    SmtValue.Binary 1 (if cb then 1 else 0) =
      __smtx_model_eval_bvcomp
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
  unfold __smtx_model_eval_bvcomp
  rw [heq]
  cases cb <;> rfl

private theorem eval_step_bvslt_or_le_aux
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term) (orEqual : Bool) (w : Nat)
    (hExpanded :
      __bv_bitblast_slt_impl
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
        (Term.Boolean orEqual) ≠ Term.Stuck)
    (haTy :
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w)
    (hbTy :
      __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
            (Term.Boolean orEqual))) =
      if orEqual then
        __smtx_model_eval_bvsle
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b))
      else
        __smtx_model_eval_bvslt
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)) := by
  have hargs := bitblast_slt_args_ne_stuck _ _ _ hExpanded
  have hsa := bitlist_rev_syntax a hargs.1
  have hsb := bitlist_rev_syntax b hargs.2
  have haNN : term_has_non_none_type (__eo_to_smt a) := by
    unfold term_has_non_none_type
    rw [haTy]
    simp
  have hbNN : term_has_non_none_type (__eo_to_smt b) := by
    unfold term_has_non_none_type
    rw [hbTy]
    simp
  rcases hsa.eval hM haNN with ⟨as, ha⟩
  rcases hsb.eval hM hbNN with ⟨bs, hb⟩
  have hpresA := type_preservation M hM (__eo_to_smt a) haNN
  have hpresB := type_preservation M hM (__eo_to_smt b) hbNN
  rw [haTy, ha.eval] at hpresA
  rw [hbTy, hb.eval] at hpresB
  have hlen : as.length = bs.length := by
    have hwa := bitvec_width_nonneg hpresA
    have hca := bitvec_payload_canonical hpresA
    have hwb := bitvec_width_nonneg hpresB
    have hcb := bitvec_payload_canonical hpresB
    rw [typeof_value_binary_of_nonneg _ _ hwa hca] at hpresA
    rw [typeof_value_binary_of_nonneg _ _ hwb hcb] at hpresB
    injection hpresA with hla
    injection hpresB with hlb
    simpa using hla.trans hlb.symm
  have hasNe : as ≠ [] := by
    intro has
    subst as
    cases ha
    have hrev :
        __eo_list_rev (Term.UOp UserOp._at_from_bools)
            (Term.Binary 0 0) =
          Term.Binary 0 0 := by native_decide
    rw [hrev] at hExpanded
    simp [__bv_bitblast_slt_impl] at hExpanded
  have hbsNe : bs ≠ [] := by
    intro hbs
    subst bs
    cases hb
    have hrev :
        __eo_list_rev (Term.UOp UserOp._at_from_bools)
            (Term.Binary 0 0) =
          Term.Binary 0 0 := by native_decide
    rw [hrev] at hExpanded
    simp [__bv_bitblast_slt_impl] at hExpanded
  have har := ha.rev
  have hbr := hb.rev
  rcases List.exists_cons_of_ne_nil
      (show as.reverse ≠ [] by simpa using hasNe) with
    ⟨sa, ars, harList⟩
  rcases List.exists_cons_of_ne_nil
      (show bs.reverse ≠ [] by simpa using hbsNe) with
    ⟨sb, brs, hbrList⟩
  rw [harList] at har
  rw [hbrList] at hbr
  rcases bitListEval_cons_shape har with
    ⟨atop, atail, harTerm, hatop, hatail⟩
  rcases bitListEval_cons_shape hbr with
    ⟨btop, btail, hbrTerm, hbtop, hbtail⟩
  have htailLen : ars.length = brs.length := by
    have hrlen : as.reverse.length = bs.reverse.length := by
      simpa using hlen
    simpa [harList, hbrList] using hrlen
  have hcircuit :=
    bitblast_slt_impl_eval
      (orEqual := orEqual)
      (BitListEval.cons atop atail sa ars hatop hatail)
      (BitListEval.cons btop btail sb brs hbtop hbtail)
      htailLen
  rw [← harTerm, ← hbrTerm] at hcircuit
  rw [hcircuit]
  change
    SmtValue.Boolean
        (sa == sb &&
            ultBits ars.reverse brs.reverse orEqual ||
          sa && !sb) =
      _
  rw [ha.eval, hb.eval]
  have haDecomp : as = ars.reverse ++ [sa] := by
    have h := congrArg List.reverse harList
    simpa using h
  have hbDecomp : bs = brs.reverse ++ [sb] := by
    have h := congrArg List.reverse hbrList
    simpa using h
  subst as
  subst bs
  simp only [List.length_append, List.length_reverse,
    List.length_singleton]
  rw [← htailLen]
  let xv := BitVec.ofBoolListLE (ars.reverse ++ [sa])
  let yv : BitVec (ars.reverse ++ [sa]).length :=
    BitVec.cast (by simp [htailLen])
      (BitVec.ofBoolListLE (brs.reverse ++ [sb]))
  have hxnat : xv.toNat =
      bitsValue (ars.reverse ++ [sa]) := by
    simp [xv, ofBoolListLE_toNat]
  have hynat : yv.toNat =
      bitsValue (brs.reverse ++ [sb]) := by
    simp [yv, BitVec.toNat_cast, ofBoolListLE_toNat]
  rw [← hxnat, ← hynat]
  cases orEqual with
  | false =>
    rw [ultBits_false_lt (by simpa using htailLen)]
    have hev :
        __smtx_model_eval_bvslt
            (SmtValue.Binary ((ars.length + 1 : Nat) : Int)
              (xv.toNat : Int))
            (SmtValue.Binary ((ars.length + 1 : Nat) : Int)
              (yv.toNat : Int)) =
          SmtValue.Boolean (xv.slt yv) := by
      simpa only [List.length_append, List.length_reverse,
        List.length_singleton] using bvslt_bitvec_values xv yv
    rw [hev]
    congr 1
    exact (ofBoolListLE_slt_append_singleton
      ars.reverse brs.reverse sa sb
      (by simpa using htailLen)).symm
  | true =>
    rw [ultBits_true_le (by simpa using htailLen)]
    have hev :
        __smtx_model_eval_bvsle
            (SmtValue.Binary ((ars.length + 1 : Nat) : Int)
              (xv.toNat : Int))
            (SmtValue.Binary ((ars.length + 1 : Nat) : Int)
              (yv.toNat : Int)) =
          SmtValue.Boolean (xv.sle yv) := by
      simpa only [List.length_append, List.length_reverse,
        List.length_singleton] using bvsle_bitvec_values xv yv
    rw [hev]
    congr 1
    exact (ofBoolListLE_sle_append_singleton
      ars.reverse brs.reverse sa sb
      (by simpa using htailLen)).symm

theorem eval_step_bvslt_or_le
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term) (orEqual : Bool)
    (hExpanded :
      __bv_bitblast_slt_impl
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
        (Term.Boolean orEqual) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.UOp
                (if orEqual then UserOp.bvsle else UserOp.bvslt)) a)
            b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
            (Term.Boolean orEqual))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.UOp
                (if orEqual then UserOp.bvsle else UserOp.bvslt)) a)
            b)) := by
  cases orEqual with
  | false =>
    change
      term_has_non_none_type
        (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) at hnn
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvslt) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
      ⟨w, haTy, hbTy⟩
    exact eval_step_bvslt_or_le_aux
      M hM a b false w hExpanded haTy hbTy
  | true =>
    change
      term_has_non_none_type
        (SmtTerm.bvsle (__eo_to_smt a) (__eo_to_smt b)) at hnn
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvsle) (ret := SmtType.Bool)
        (by rw [__smtx_typeof.eq_def] <;> simp only) hnn with
      ⟨w, haTy, hbTy⟩
    exact eval_step_bvslt_or_le_aux
      M hM a b true w hExpanded haTy hbTy

theorem eval_step_bvslt (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_slt_impl
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
        (Term.Boolean false) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
            (Term.Boolean false))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) a) b)) :=
  eval_step_bvslt_or_le M hM a b false hExpanded hnn

theorem eval_step_bvsle (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __bv_bitblast_slt_impl
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
        (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
        (Term.Boolean true) ≠ Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__bv_bitblast_slt_impl
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
            (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
            (Term.Boolean true))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) a) b)) :=
  eval_step_bvslt_or_le M hM a b true hExpanded hnn

theorem eval_step_bvultbv (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
            (__bv_bitblast_ult a b (Term.Boolean false)))
          (Term.Binary 0 0) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
              (__bv_bitblast_ult a b (Term.Boolean false)))
            (Term.Binary 0 0))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) a) b)) := by
  let c := __bv_bitblast_ult a b (Term.Boolean false)
  have hinner :
      __eo_mk_apply (Term.UOp UserOp._at_from_bools) c ≠ Term.Stuck :=
    mk_apply_fun_ne_stuck hExpanded
  have hcNe : c ≠ Term.Stuck :=
    mk_apply_arg_ne_stuck hinner
  change
    term_has_non_none_type
      (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b))
        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) at hnn
  rcases ite_args_of_non_none hnn with
    ⟨T, hcTy, hthenTy, helseTy, hT⟩
  have hultNN :
      term_has_non_none_type
        (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hcTy]
    simp
  have hcEq := eval_step_bvult M hM a b hcNe hultNN
  change
    __smtx_model_eval M (__eo_to_smt c) =
      __smtx_model_eval_bvult
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) at hcEq
  rcases smt_model_eval_bool_is_boolean M hM
      (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) hcTy with
    ⟨cb, hpred⟩
  change
    __smtx_model_eval_bvult
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean cb at hpred
  have hc : __smtx_model_eval M (__eo_to_smt c) =
      SmtValue.Boolean cb := hcEq.trans hpred
  rw [wrap_bool_eval hc]
  change
    SmtValue.Binary 1 (if cb then 1 else 0) =
      __smtx_model_eval_ite
        (__smtx_model_eval_bvult
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)))
        (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)
  rw [hpred]
  cases cb <;> rfl

theorem eval_step_bvsltbv (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (hExpanded :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
            (__bv_bitblast_slt_impl
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
              (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
              (Term.Boolean false)))
          (Term.Binary 0 0) ≠
        Term.Stuck)
    (hnn :
      term_has_non_none_type
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) a) b))) :
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at_from_bools)
              (__bv_bitblast_slt_impl
                (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
                (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
                (Term.Boolean false)))
            (Term.Binary 0 0))) =
      __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) a) b)) := by
  let c :=
    __bv_bitblast_slt_impl
      (__eo_list_rev (Term.UOp UserOp._at_from_bools) a)
      (__eo_list_rev (Term.UOp UserOp._at_from_bools) b)
      (Term.Boolean false)
  have hinner :
      __eo_mk_apply (Term.UOp UserOp._at_from_bools) c ≠ Term.Stuck :=
    mk_apply_fun_ne_stuck hExpanded
  have hcNe : c ≠ Term.Stuck :=
    mk_apply_arg_ne_stuck hinner
  change
    term_has_non_none_type
      (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b))
        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) at hnn
  rcases ite_args_of_non_none hnn with
    ⟨T, hcTy, hthenTy, helseTy, hT⟩
  have hsltNN :
      term_has_non_none_type
        (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hcTy]
    simp
  have hcEq := eval_step_bvslt M hM a b hcNe hsltNN
  change
    __smtx_model_eval M (__eo_to_smt c) =
      __smtx_model_eval_bvslt
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) at hcEq
  rcases smt_model_eval_bool_is_boolean M hM
      (SmtTerm.bvslt (__eo_to_smt a) (__eo_to_smt b)) hcTy with
    ⟨cb, hpred⟩
  change
    __smtx_model_eval_bvslt
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean cb at hpred
  have hc : __smtx_model_eval M (__eo_to_smt c) =
      SmtValue.Boolean cb := hcEq.trans hpred
  rw [wrap_bool_eval hc]
  change
    SmtValue.Binary 1 (if cb then 1 else 0) =
      __smtx_model_eval_ite
        (__smtx_model_eval_bvslt
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (__eo_to_smt b)))
        (SmtValue.Binary 1 1) (SmtValue.Binary 1 0)
  rw [hpred]
  cases cb <;> rfl

theorem eval_bv_mk_bitblast_step
    (M : SmtModel) (hM : model_total_typed M) (lhs : Term)
    (hne : __bv_mk_bitblast_step lhs ≠ Term.Stuck)
    (hnn : term_has_non_none_type (__eo_to_smt lhs)) :
    __smtx_model_eval M (__eo_to_smt (__bv_mk_bitblast_step lhs)) =
      __smtx_model_eval M (__eo_to_smt lhs) := by
  unfold __bv_mk_bitblast_step at hne ⊢
  split at * <;> simp_all
  case h_2 => exact eval_step_bvnot M hM _ hne hnn
  case h_3 => exact eval_step_eq M hM _ _ hne hnn
  case h_4 => exact eval_step_bvult M hM _ _ hne hnn
  case h_5 => exact eval_step_bvule M hM _ _ hne hnn
  case h_6 => exact eval_step_bvslt M hM _ _ hne hnn
  case h_7 => exact eval_step_bvsle M hM _ _ hne hnn
  case h_8 => exact eval_step_reify M hM _ hne hnn
  case h_9 => exact eval_step_reify M hM _ hne hnn
  case h_10 => exact eval_step_reify M hM _ hne hnn
  case h_11 => exact eval_step_reify M hM _ hne hnn
  case h_12 => exact eval_step_reify M hM _ hne hnn
  case h_13 => exact eval_step_bvxnor M hM _ _ hne hnn
  case h_14 => exact eval_step_reify M hM _ hne hnn
  case h_15 => exact eval_step_reify M hM _ hne hnn
  case h_16 => exact eval_step_reify M hM _ hne hnn
  case h_17 => exact eval_step_reify M hM _ hne hnn
  case h_18 => exact eval_step_bvsub M hM _ _ hne hnn
  case h_19 => exact eval_step_bvneg M hM _ hne hnn
  case h_20 => exact eval_step_bvite M hM _ _ _ hne hnn
  case h_21 => exact eval_step_reify M hM _ hne hnn
  case h_22 => exact eval_step_reify M hM _ hne hnn
  case h_23 => exact eval_step_reify M hM _ hne hnn
  case h_24 => exact eval_step_bvcomp M hM _ _ hne hnn
  case h_25 => exact eval_step_bvultbv M hM _ _ hne hnn
  case h_26 => exact eval_step_bvsltbv M hM _ _ hne hnn
  case h_27 => exact eval_step_reify M hM _ hne hnn
  case h_28 => exact eval_step_reify M hM _ hne hnn

end BvBitblast
