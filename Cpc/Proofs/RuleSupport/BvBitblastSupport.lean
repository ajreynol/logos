module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

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

private theorem mk_from_bools_eq
    {head tail : Term} (hh : head ≠ Term.Stuck) (ht : tail ≠ Term.Stuck) :
    __eo_mk_apply
        (__eo_mk_apply (Term.UOp UserOp._at_from_bools) head) tail =
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at_from_bools) head) tail := by
  rw [mk_apply_eq (by intro h; cases h) hh]
  exact mk_apply_eq (by intro h; cases h) ht

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

private theorem native_int_pow2_nat (n : Nat) :
    native_int_pow2 (n : Int) = ((2 ^ n : Nat) : Int) := by
  have hn : ¬ ((n : Int) < 0) := by omega
  simp [native_int_pow2, native_zexp_total, hn]

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

end BvBitblast
