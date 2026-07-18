module

public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

public section

/-! Support for bit-vector extract-over-concat rewrites. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvConcatTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y

def bvExtractConcat4Tail (y xs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) xs
    (bvConcatTerm y (Term.Binary 0 0))

def bvExtractConcat4TailElim (y xs : Term) : Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.concat)
    (bvExtractConcat4Tail y xs)

def bvExtractConcat4Lhs (x y xs i j : Term) : Term :=
  bvExtractTerm (bvConcatTerm x (bvExtractConcat4Tail y xs)) j i

def bvExtractConcat4Rhs (y xs i j : Term) : Term :=
  bvExtractTerm (bvExtractConcat4TailElim y xs) j i

def bvExtractConcat4Term (x y xs i j : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractConcat4Lhs x y xs i j)) (bvExtractConcat4Rhs y xs i j)

def bvExtractConcat1Seed (x y : Term) : Term :=
  bvConcatTerm y (bvConcatTerm x (Term.Binary 0 0))

def bvExtractConcat1Whole (x y xs : Term) : Term :=
  __eo_list_concat (Term.UOp UserOp.concat) xs
    (bvExtractConcat1Seed x y)

def bvExtractConcat1Lhs (x y xs i j : Term) : Term :=
  bvExtractTerm (bvExtractConcat1Whole x y xs) j i

def bvExtractConcat1Rhs (x i j : Term) : Term :=
  bvExtractTerm x j i

def bvExtractConcat1Term (x y xs i j : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractConcat1Lhs x y xs i j)) (bvExtractConcat1Rhs x i j)

def bvExtractConcat1PremRaw (j x : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) j)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
    (Term.Boolean true)

def bvExtractConcat1Prem (x j : Term) : Term :=
  bvExtractConcat1PremRaw j x

def bvExtractConcat1Program
    (x xs y i j : Term) (p : Proof) : Term :=
  __eo_prog_bv_extract_concat_1 x xs y i j p

def bvExtractConcat1ProgramBody (x xs y i j : Term) : Term :=
  let ext := Term.UOp2 UserOp2.extract j i
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply ext (bvExtractConcat1Whole x y xs)))
    (Term.Apply ext x)

def bvExtractConcat4PremRaw (j x y xs x' : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt) j)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (Term.Apply (Term.UOp UserOp._at_bvsize) x'))))
    (Term.Boolean true)

def bvExtractConcat4Prem (x y xs j : Term) : Term :=
  bvExtractConcat4PremRaw j x y xs x

def bvExtractConcat4Program
    (x y xs i j : Term) (p : Proof) : Term :=
  __eo_prog_bv_extract_concat_4 x y xs i j p

def bvExtractConcat4ProgramBody (x y xs i j : Term) : Term :=
  let tail := bvExtractConcat4Tail y xs
  let ext := Term.UOp2 UserOp2.extract j i
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply ext
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.concat) x) tail)))
    (__eo_mk_apply ext
      (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail))

private def BvEvalCanonical (M : SmtModel) (t : Term) : Prop :=
  ∃ (w : Nat) (n : Int),
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary ↑w n ∧
      0 ≤ n ∧ n < (2 : Int) ^ w

private def BvConcatListCanonical (M : SmtModel) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) xs =>
      BvEvalCanonical M x ∧ BvConcatListCanonical M xs
  | t => BvEvalCanonical M t

private theorem term_ne_stuck_of_smt_bitvec_type
    {t : Term} {w : native_Nat} :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

private theorem bvEvalCanonical_of_smt_type
    (M : SmtModel) (hM : model_total_typed M)
    (t : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    BvEvalCanonical M t := by
  intro hTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt t) w hTy with
    ⟨p, hEval, hCan⟩
  have hWidth0 : native_zleq 0 (native_nat_to_int w) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int, SmtEval.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCan
  refine ⟨w, p, ?_, hRange.1, ?_⟩
  · simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hEval
  · simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hRange.2

private theorem bvConcat_args_of_bitvec_type
    (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (bvConcatTerm y x)) = SmtType.BitVec w ->
    ∃ wy wx : native_Nat,
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx := by
  intro hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    change __smtx_typeof (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) ≠
      SmtType.None
    rw [show
      __smtx_typeof (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w by
      simpa [bvConcatTerm] using hTy]
    intro h
    cases h
  exact bv_concat_args_of_non_none hNN

private theorem smt_typeof_bv_concat_eq
    (x y : Term) (wx wy : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt (bvConcatTerm x y)) =
      SmtType.BitVec (wx + wy) := by
  intro hXTy hYTy
  change __smtx_typeof
      (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.BitVec (wx + wy)
  rw [typeof_concat_eq, hXTy, hYTy]
  simp only [__smtx_typeof_concat, SmtEval.native_zplus,
    native_nat_to_int, SmtEval.native_nat_to_int,
    native_int_to_nat, SmtEval.native_int_to_nat]
  congr

private theorem smt_typeof_bv_concat_width_inv
    (x y : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt (bvConcatTerm x y)) =
      SmtType.BitVec w ->
    ∃ wx wy,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      w = wx + wy := by
  intro hTy
  rcases bvConcat_args_of_bitvec_type x y w hTy with
    ⟨wx, wy, hXTy, hYTy⟩
  have hConcatTy := smt_typeof_bv_concat_eq x y wx wy hXTy hYTy
  rw [hConcatTy] at hTy
  injection hTy with hW
  exact ⟨wx, wy, hXTy, hYTy, hW.symm⟩

private theorem smt_typeof_concat_empty :
    __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) =
      SmtType.BitVec 0 := by
  change __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0
  simp [__smtx_typeof, SmtEval.native_and, native_ite,
    SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
    native_mod_total, native_int_to_nat, SmtEval.native_int_to_nat]

private theorem bv_concat_empty_is_list_true :
    __eo_is_list (Term.UOp UserOp.concat) (Term.Binary 0 0) =
      Term.Boolean true := by
  simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
    __eo_requires, __eo_is_ok, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem bv_concat_nil_width_zero
    (nil : Term) (w : Nat) :
    (∀ f x y, nil ≠ Term.Apply (Term.Apply f x) y) ->
    __eo_is_list (Term.UOp UserOp.concat) nil = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    w = 0 := by
  intro hNot hList hTy
  cases nil <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_requires, __eo_is_ok, native_ite, native_teq, native_not,
      SmtEval.native_not] at hList hTy ⊢
  case Binary bw bn =>
    split at hList <;> simp_all
    rw [smt_typeof_concat_empty] at hTy
    injection hTy with hW
    exact hW.symm

private theorem bv_concat_nil_width_zero_of_nil_true
    (nil : Term) (w : Nat) :
    __eo_is_list_nil (Term.UOp UserOp.concat) nil = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt nil) = SmtType.BitVec w ->
    w = 0 := by
  intro hNil hTy
  cases nil <;> simp [__eo_is_list_nil] at hNil hTy ⊢
  case Binary bw bn =>
    split at hNil <;> simp_all
    rw [smt_typeof_concat_empty] at hTy
    injection hTy with hW
    exact hW.symm

private theorem bv_concat_is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.concat) t = Term.Boolean b := by
  intro hNe
  cases t
  case Stuck =>
    exact False.elim (hNe rfl)
  case Binary w n =>
    by_cases h : w = 0 ∧ n = 0
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨true, by simp [__eo_is_list_nil]⟩
    · have hTerm : Term.Binary w n ≠ Term.Binary 0 0 := by
        intro hEq
        cases hEq
        exact h ⟨rfl, rfl⟩
      exact ⟨false, by simp [__eo_is_list_nil, hTerm]⟩
  all_goals
    exact ⟨false, by simp [__eo_is_list_nil]⟩

private theorem smt_typeof_list_concat_rec_bv_aux
    (f a z : Term) :
    f = Term.UOp UserOp.concat ->
    ∀ wa wz : Nat,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
      __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
        SmtType.BitVec (wa + wz) := by
  intro hf
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro wa wz hList haTy hzTy
      subst f
      simp [__eo_is_list] at hList
  | case2 a hA =>
      intro wa wz hList haTy hzTy
      change __smtx_typeof SmtTerm.None = SmtType.BitVec wz at hzTy
      rw [TranslationProofs.smtx_typeof_none] at hzTy
      cases hzTy
  | case3 g x y z hZ ih =>
      intro wa wz hList haTy hzTy
      subst f
      have hg : g = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.concat) x y
          hList
      rcases smt_typeof_bv_concat_width_inv x y wa (by
          simpa [bvConcatTerm] using haTy) with
        ⟨wx, wy, hXTy, hYTy, hWa⟩
      have hZNonStuck : z ≠ Term.Stuck :=
        term_ne_stuck_of_smt_bitvec_type hzTy
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.concat)
          y z hTailList hZNonStuck
      have hTailTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y z)) =
            SmtType.BitVec (wy + wz) :=
        ih wy wz hTailList hYTy hzTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) x y z hTailConcat]
      have hConcatTy :=
        smt_typeof_bv_concat_eq x (__eo_list_concat_rec y z)
          wx (wy + wz) hXTy hTailTy
      simpa [bvConcatTerm, hWa, Nat.add_assoc] using hConcatTy
  | case4 nil z hNil hZ hNot =>
      intro wa wz hList haTy hzTy
      subst f
      have hWaZero :
          wa = 0 :=
        bv_concat_nil_width_zero nil wa hNot hList haTy
      subst wa
      simpa [__eo_list_concat_rec] using hzTy

private theorem smt_typeof_list_concat_rec_bv
    (a z : Term) (wa wz : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.BitVec (wa + wz) :=
  smt_typeof_list_concat_rec_bv_aux
    (Term.UOp UserOp.concat) a z rfl wa wz

private theorem bv_concat_seed_is_list_true (y : Term) :
    __eo_is_list (Term.UOp UserOp.concat)
        (bvConcatTerm y (Term.Binary 0 0)) =
      Term.Boolean true :=
  eo_is_list_cons_self_true_of_tail_list
    (Term.UOp UserOp.concat) y (Term.Binary 0 0)
    (by intro h; cases h) bv_concat_empty_is_list_true

private theorem smt_typeof_bv_concat_seed
    (y : Term) (wy : Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof
        (__eo_to_smt (bvConcatTerm y (Term.Binary 0 0))) =
      SmtType.BitVec wy := by
  intro hYTy
  have hTy :=
    smt_typeof_bv_concat_eq y (Term.Binary 0 0) wy 0
      hYTy smt_typeof_concat_empty
  simpa [Nat.add_zero] using hTy

private theorem bv_extract_concat1_seed_is_list_true
    (x y : Term) :
    __eo_is_list (Term.UOp UserOp.concat)
        (bvExtractConcat1Seed x y) =
      Term.Boolean true := by
  have hInnerList :
      __eo_is_list (Term.UOp UserOp.concat)
          (bvConcatTerm x (Term.Binary 0 0)) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat) x (Term.Binary 0 0)
      (by intro h; cases h) bv_concat_empty_is_list_true
  exact
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.concat) y
      (bvConcatTerm x (Term.Binary 0 0))
      (by intro h; cases h) hInnerList

private theorem smt_typeof_bv_extract_concat1_seed
    (x y : Term) (wx wy : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt (bvExtractConcat1Seed x y)) =
      SmtType.BitVec (wy + wx) := by
  intro hXTy hYTy
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) =
        SmtType.BitVec wx := by
    have hTy :=
      smt_typeof_bv_concat_eq x (Term.Binary 0 0) wx 0
        hXTy smt_typeof_concat_empty
    simpa [Nat.add_zero] using hTy
  simpa [bvExtractConcat1Seed] using
    smt_typeof_bv_concat_eq y
      (bvConcatTerm x (Term.Binary 0 0)) wy wx hYTy hInnerTy

private theorem smt_typeof_list_concat_bv
    (a z : Term) (wa wz : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_concat (Term.UOp UserOp.concat) a z)) =
      SmtType.BitVec (wa + wz) := by
  intro hListA hListZ hATy hZTy
  have hRecTy :=
    smt_typeof_list_concat_rec_bv a z wa wz hListA hATy hZTy
  simpa [__eo_list_concat, hListA, hListZ, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not] using hRecTy

private theorem smt_typeof_bv_extract_concat1_whole
    (x y xs : Term) (wx wy wxs : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
      SmtType.BitVec (wxs + (wy + wx)) := by
  intro hXsList hXTy hYTy hXsTy
  have hSeedList := bv_extract_concat1_seed_is_list_true x y
  have hSeedTy :=
    smt_typeof_bv_extract_concat1_seed x y wx wy hXTy hYTy
  simpa [bvExtractConcat1Whole] using
    smt_typeof_list_concat_bv xs (bvExtractConcat1Seed x y)
      wxs (wy + wx) hXsList hSeedList hXsTy hSeedTy

private theorem smt_typeof_concat_list_of_translation
    (t : Term) :
    __eo_is_list (Term.UOp UserOp.concat) t = Term.Boolean true ->
    RuleProofs.eo_has_smt_translation t ->
    ∃ w : Nat, __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
  intro hList hTrans
  revert hList hTrans
  induction t using __eo_get_elements_rec.induct with
  | case1 =>
      intro hList _hTrans
      simp [__eo_is_list] at hList
  | case2 f x xs ih =>
      intro hList hTrans
      have hf : f = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.concat) f x xs hList
      subst f
      have hNN : term_has_non_none_type
          (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt xs)) := by
        simpa [RuleProofs.eo_has_smt_translation,
          term_has_non_none_type] using hTrans
      rcases bv_concat_args_of_non_none hNN with
        ⟨wx, wxs, hXTy, hXsTy⟩
      exact ⟨wx + wxs,
        by simpa [bvConcatTerm] using
          smt_typeof_bv_concat_eq x xs wx wxs hXTy hXsTy⟩
  | case3 t _hNil hNot =>
      intro hList hTrans
      cases t with
      | Binary w n =>
          by_cases hEq : Term.Binary w n = Term.Binary 0 0
          · cases hEq
            exact ⟨0, smt_typeof_concat_empty⟩
          · exfalso
            simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
              __eo_requires, __eo_is_ok, native_ite, native_teq,
              native_not, SmtEval.native_not, hEq] at hList
      | Apply f arg =>
          cases f with
          | Apply g head =>
              exact False.elim (hNot g head arg rfl)
          | _ =>
              exfalso
              simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
                __eo_requires, __eo_is_ok, native_ite, native_teq,
                native_not, SmtEval.native_not] at hList
      | Stuck =>
          simp [__eo_is_list] at hList
      | UOp op =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | UOp1 op a =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | UOp2 op a b =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | UOp3 op a b c =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | __eo_List =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | __eo_List_nil =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | __eo_List_cons =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Bool =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Boolean b =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Numeral n =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Rational r =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | String s =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | «Type» =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | FunType =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | Var s T =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DatatypeType s d =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DatatypeTypeRef s =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DtcAppType a b =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DtCons s d i =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | DtSel s d i j =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | USort s =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList
      | UConst i T =>
          exfalso
          simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
            __eo_requires, __eo_is_ok, native_ite, native_teq,
            native_not, SmtEval.native_not] at hList

private theorem bv_list_concat_lists_of_ne_stuck (f a b : Term) :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true ∧
      __eo_is_list f b = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) ≠ Term.Stuck := by
    simpa [__eo_list_concat] using h
  have ha : __eo_is_list f a = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list f a) (Term.Boolean true)
      (__eo_requires (__eo_is_list f b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) hReq
  have hReqEq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) =
        __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) :=
    eo_requires_eq_result_of_ne_stuck
      (__eo_is_list f a) (Term.Boolean true)
      (__eo_requires (__eo_is_list f b) (Term.Boolean true)
        (__eo_list_concat_rec a b)) hReq
  have hReqTail :
      __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) ≠ Term.Stuck := by
    rwa [hReqEq] at hReq
  have hb : __eo_is_list f b = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_is_list f b) (Term.Boolean true)
      (__eo_list_concat_rec a b) hReqTail
  exact ⟨ha, hb⟩

private theorem bv_extract_concat4_tail_is_list_true
    (y xs : Term) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat)
        (bvExtractConcat4Tail y xs) =
      Term.Boolean true := by
  intro hXsList
  have hSeedList := bv_concat_seed_is_list_true y
  have hRecList :
      __eo_is_list (Term.UOp UserOp.concat)
          (__eo_list_concat_rec xs (bvConcatTerm y (Term.Binary 0 0))) =
        Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists
      (Term.UOp UserOp.concat) xs (bvConcatTerm y (Term.Binary 0 0))
      hXsList hSeedList
  simpa [bvExtractConcat4Tail, __eo_list_concat, hXsList, hSeedList,
    __eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
    using hRecList

private theorem smt_typeof_bv_extract_concat4_tail
    (y xs : Term) (wy wxs : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    __smtx_typeof (__eo_to_smt (bvExtractConcat4Tail y xs)) =
      SmtType.BitVec (wxs + wy) := by
  intro hXsList hYTy hXsTy
  have hSeedList := bv_concat_seed_is_list_true y
  have hSeedTy := smt_typeof_bv_concat_seed y wy hYTy
  exact smt_typeof_list_concat_bv xs
    (bvConcatTerm y (Term.Binary 0 0)) wxs wy
    hXsList hSeedList hXsTy hSeedTy

private theorem smt_typeof_bv_singleton_elim
    (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)) =
      SmtType.BitVec w := by
  intro hList hTy
  change __smtx_typeof
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))) =
    SmtType.BitVec w
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.concat) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.concat) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases bv_concat_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · simpa [bvConcatTerm] using hTy
          · rcases smt_typeof_bv_concat_width_inv head tail w (by
                simpa [bvConcatTerm] using hTy) with
              ⟨wh, wt, hHeadTy, hTailTy, hW⟩
            have hWtZero :
                wt = 0 :=
              bv_concat_nil_width_zero_of_nil_true tail wt hNil hTailTy
            subst wt
            simp [Nat.add_zero] at hW
            subst w
            exact hHeadTy
      | _ =>
          simpa [__eo_list_singleton_elim_2] using hTy
  | _ =>
      simpa [__eo_list_singleton_elim_2] using hTy

private theorem extractLsb'_append_low
    {x : BitVec W} {y : BitVec T} {L D : Nat}
    (hFit : L + D ≤ T) :
    (x ++ y).extractLsb' L D = y.extractLsb' L D := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getElem_extractLsb' hi]
  have hTail : L + i < T := by omega
  have hApp : L + i < W + T := by omega
  rw [BitVec.getLsbD_eq_getElem hApp, BitVec.getElem_append]
  simp [hTail, BitVec.getLsbD_eq_getElem hTail]

private theorem concat_bitvec_values
    (x : BitVec A) (y : BitVec B) :
    __smtx_model_eval_concat
        (SmtValue.Binary (↑A : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑B : Int) (↑y.toNat : Int)) =
      SmtValue.Binary (↑(A + B) : Int) (↑(x ++ y).toNat : Int) := by
  simp only [__smtx_model_eval_concat, SmtEval.native_zplus,
    native_mod_total, native_binary_concat, native_zmult]
  have hWidth : (↑A + ↑B : Int) = ↑(A + B) := by norm_cast
  rw [hWidth, natpow2_eq B, natpow2_eq (A + B),
    show ((2 : Int) ^ B) = ((2 ^ B : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ (A + B)) = ((2 ^ (A + B) : Nat) : Int) by
      norm_cast]
  norm_cast
  have hyLt : y.toNat < 2 ^ B := y.isLt
  have hShiftOr := Nat.shiftLeft_add_eq_or_of_lt hyLt x.toNat
  have hFormula : x.toNat * 2 ^ B + y.toNat = (x ++ y).toNat := by
    rw [BitVec.toNat_append, ← hShiftOr, Nat.shiftLeft_eq]
  rw [hFormula, Nat.mod_eq_of_lt (x ++ y).isLt]

private theorem eval_bv_extract_concat_low
    (M : SmtModel) (hM : model_total_typed M)
    (x tail : Term) (wx wt : Nat) (h l : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt tail) = SmtType.BitVec wt ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wt) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvConcatTerm x tail)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm tail (Term.Numeral h)
          (Term.Numeral l))) := by
  intro hXTy hTailTy hl0 hHTail hd0
  let d : native_Int :=
    native_zplus (native_zplus h 1) (native_zneg l)
  let L : Nat := native_int_to_nat l
  let D : Nat := native_int_to_nat d
  have hLRound : (↑L : Int) = l := by
    simpa [L, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip l hl0
  have hDRound : (↑D : Int) = d := by
    simpa [D, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip d hd0
  have hDDef : d = h + 1 + -l := by
    simp [d, SmtEval.native_zplus, SmtEval.native_zneg,
      Int.add_assoc]
  have hTailBoundInt : h < (↑wt : Int) := by
    simpa [SmtEval.native_zlt, native_nat_to_int,
      SmtEval.native_nat_to_int] using hHTail
  have hFitInt : (↑L : Int) + (↑D : Int) ≤ (↑wt : Int) := by
    rw [hLRound, hDRound]
    calc
      l + d = h + 1 := by
        rw [hDDef]
        calc
          l + (h + 1 + -l) = (l + (h + 1)) + -l :=
            (Int.add_assoc l (h + 1) (-l)).symm
          _ = ((h + 1) + l) + -l := by
            rw [Int.add_comm l (h + 1)]
          _ = h + 1 := Int.add_neg_cancel_right (h + 1) l
      _ ≤ (↑wt : Int) := Int.add_one_le_iff.mpr hTailBoundInt
  have hFit : L + D ≤ wt := by
    exact_mod_cast hFitInt
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) wx
      hXTy with
    ⟨px, hXEval, hXCan⟩
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt tail) wt
      hTailTy with
    ⟨pt, hTailEval, hTailCan⟩
  have hWx0 : native_zleq 0 (native_nat_to_int wx) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hWt0 : native_zleq 0 (native_nat_to_int wt) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hXRange := bitvec_payload_range_of_canonical hWx0 hXCan
  have hTailRange := bitvec_payload_range_of_canonical hWt0 hTailCan
  let bx : BitVec wx := BitVec.ofInt wx px
  let bt : BitVec wt := BitVec.ofInt wt pt
  have hBxPayload : (↑bx.toNat : Int) = px := by
    rw [show bx.toNat = px.toNat by
      exact ofInt_toNat_canonical wx px hXRange.1 (by
        simpa [natpow2_eq, native_nat_to_int,
          SmtEval.native_nat_to_int] using hXRange.2)]
    exact Int.toNat_of_nonneg hXRange.1
  have hBtPayload : (↑bt.toNat : Int) = pt := by
    rw [show bt.toNat = pt.toNat by
      exact ofInt_toNat_canonical wt pt hTailRange.1 (by
        simpa [natpow2_eq, native_nat_to_int,
          SmtEval.native_nat_to_int] using hTailRange.2)]
    exact Int.toNat_of_nonneg hTailRange.1
  have hXEvalB :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑wx : Int) (↑bx.toNat : Int) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int, hBxPayload]
      using hXEval
  have hTailEvalB :
      __smtx_model_eval M (__eo_to_smt tail) =
        SmtValue.Binary (↑wt : Int) (↑bt.toNat : Int) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int, hBtPayload]
      using hTailEval
  have hConcatEval :
      __smtx_model_eval M (__eo_to_smt (bvConcatTerm x tail)) =
        SmtValue.Binary (↑(wx + wt) : Int) (↑(bx ++ bt).toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt tail)) =
      SmtValue.Binary (↑(wx + wt) : Int) (↑(bx ++ bt).toNat : Int)
    simp [__smtx_model_eval, hXEvalB, hTailEvalB,
      concat_bitvec_values bx bt]
  have hConcatPayload0 :
      (0 : Int) ≤ (↑(bx ++ bt).toNat : Int) :=
    Int.natCast_nonneg _
  have hConcatPayloadLt :
      (↑(bx ++ bt).toNat : Int) < (2 : Int) ^ (wx + wt) := by
    exact_mod_cast (bx ++ bt).isLt
  have hTailPayload0 : (0 : Int) ≤ (↑bt.toNat : Int) :=
    Int.natCast_nonneg _
  have hTailPayloadLt :
      (↑bt.toNat : Int) < (2 : Int) ^ wt := by
    exact_mod_cast bt.isLt
  rw [eval_extract_term M (bvConcatTerm x tail) h l,
    eval_extract_term M tail h l, hConcatEval, hTailEvalB]
  rw [extract_val_bitvec_start_len (wx + wt) L D
      (↑(bx ++ bt).toNat : Int) h l hConcatPayload0
      hConcatPayloadLt hLRound.symm (by rw [hDRound, hDDef])]
  rw [extract_val_bitvec_start_len wt L D
      (↑bt.toNat : Int) h l hTailPayload0 hTailPayloadLt
      hLRound.symm (by rw [hDRound, hDDef])]
  rw [bitvec_ofInt_natCast_toNat (bx ++ bt),
    bitvec_ofInt_natCast_toNat bt]
  congr 2
  exact congrArg BitVec.toNat
    (extractLsb'_append_low (x := bx) (y := bt) (L := L) (D := D)
      hFit)

private theorem native_zlt_nat_add_right_local
    {h : native_Int} {w extra : Nat} :
    native_zlt h (native_nat_to_int w) = true ->
    native_zlt h (native_nat_to_int (extra + w)) = true := by
  intro hlt
  have hltInt : h < (↑w : Int) := by
    simpa [SmtEval.native_zlt, native_nat_to_int,
      SmtEval.native_nat_to_int] using hlt
  have hleNat : w ≤ extra + w := by
    omega
  have hleInt : (↑w : Int) ≤ ↑(extra + w) := by
    exact_mod_cast hleNat
  have hltAdd : h < (↑(extra + w) : Int) :=
    Int.lt_of_lt_of_le hltInt hleInt
  simpa [SmtEval.native_zlt, native_nat_to_int,
    SmtEval.native_nat_to_int] using hltAdd

private theorem eval_bv_extract_list_concat_rec_low
    (M : SmtModel) (hM : model_total_typed M)
    (a z : Term) (wa wz : Nat) (h l : native_Int) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wz) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (__eo_list_concat_rec a z)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm z (Term.Numeral h) (Term.Numeral l))) := by
  intro hList hATy hZTy hl0 hBound hd0
  revert wa hList hATy
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro wa hList hATy
      simp [__eo_is_list] at hList
  | case2 a =>
      intro wa hList hATy
      change __smtx_typeof SmtTerm.None = SmtType.BitVec wz at hZTy
      rw [TranslationProofs.smtx_typeof_none] at hZTy
      cases hZTy
  | case3 g x y z hZ ih =>
      intro wa hList hATy
      have hg : g = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.concat) g x y hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.concat) x y hList
      rcases smt_typeof_bv_concat_width_inv x y wa (by
          simpa [bvConcatTerm] using hATy) with
        ⟨wx, wy, hXTy, hYTy, _hWa⟩
      have hZNonStuck : z ≠ Term.Stuck :=
        term_ne_stuck_of_smt_bitvec_type hZTy
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.concat)
          y z hTailList hZNonStuck
      have hTailTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y z)) =
            SmtType.BitVec (wy + wz) :=
        smt_typeof_list_concat_rec_bv y z wy wz hTailList hYTy hZTy
      have hTailBound :
          native_zlt h (native_nat_to_int (wy + wz)) = true :=
        native_zlt_nat_add_right_local (extra := wy) hBound
      have hHeadLow :=
        eval_bv_extract_concat_low M hM x (__eo_list_concat_rec y z)
          wx (wy + wz) h l hXTy hTailTy hl0 hTailBound hd0
      have hTailLow :=
        ih hZTy wy hTailList hYTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) x y z hTailConcat]
      change __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm (bvConcatTerm x (__eo_list_concat_rec y z))
              (Term.Numeral h) (Term.Numeral l))) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm z (Term.Numeral h) (Term.Numeral l)))
      rw [hHeadLow, hTailLow]
  | case4 nil z hNil hZ hNot =>
      intro wa hList hATy
      simpa [__eo_list_concat_rec]

private theorem eval_bv_extract_list_concat_low
    (M : SmtModel) (hM : model_total_typed M)
    (a z : Term) (wa wz : Nat) (h l : native_Int) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt z) = SmtType.BitVec wz ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wz) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (__eo_list_concat (Term.UOp UserOp.concat) a z)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm z (Term.Numeral h) (Term.Numeral l))) := by
  intro hListA hListZ hATy hZTy hl0 hBound hd0
  have hRec :=
    eval_bv_extract_list_concat_rec_low M hM a z wa wz h l
      hListA hATy hZTy hl0 hBound hd0
  simpa [__eo_list_concat, hListA, hListZ, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not] using hRec

private theorem eval_bvsize_of_smt_bitvec
    (M : SmtModel) (x : Term) (w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral w := by
  have hRound := native_int_to_nat_roundtrip w hw0
  have hSize :
      __smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)) = w := by
    rw [hXSmtTy]
    exact hRound
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0
          (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral w
  rw [hSize]
  simp [native_ite, hw0, __smtx_model_eval,
    __smtx_model_eval__at_purify]

private theorem eval_bvsize_of_smt_bitvec_nat
    (M : SmtModel) (x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral (native_nat_to_int w) := by
  intro hTy
  have hw0 : native_zleq 0 (native_nat_to_int w) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hTy' :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat (native_nat_to_int w)) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int,
      native_int_to_nat, SmtEval.native_int_to_nat] using hTy
  exact eval_bvsize_of_smt_bitvec M x (native_nat_to_int w) hw0 hTy'

private theorem bool_eq_true_of_model_eval_eq_true
    (b : native_Bool) :
    __smtx_model_eval_eq (SmtValue.Boolean b) (SmtValue.Boolean true) =
      SmtValue.Boolean true ->
    b = true := by
  cases b <;> simp [__smtx_model_eval_eq, native_veq]

private theorem model_eval_eq_true_of_eo_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) =
        SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem bvExtractConcat4Prem_bound
    (M : SmtModel) (x y xs : Term) (wx wy wxs : Nat)
    (j : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    eo_interprets M
      (bvExtractConcat4Prem x y xs (Term.Numeral j)) true ->
    native_zlt j (native_nat_to_int (wxs + wy)) = true := by
  intro hXTy hYTy hXsTy hPrem
  have hYXsTy :
      __smtx_typeof (__eo_to_smt (bvConcatTerm y xs)) =
        SmtType.BitVec (wy + wxs) :=
    smt_typeof_bv_concat_eq y xs wy wxs hYTy hXsTy
  have hTotalTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatTerm x (bvConcatTerm y xs))) =
        SmtType.BitVec (wx + (wy + wxs)) :=
    smt_typeof_bv_concat_eq x (bvConcatTerm y xs)
      wx (wy + wxs) hXTy hYXsTy
  have hTotalSize :=
    eval_bvsize_of_smt_bitvec_nat M
      (bvConcatTerm x (bvConcatTerm y xs))
      (wx + (wy + wxs)) hTotalTy
  have hXSize :=
    eval_bvsize_of_smt_bitvec_nat M x wx hXTy
  have hBoundWidth :
      native_zplus (native_nat_to_int (wx + (wy + wxs)))
          (native_zneg (native_nat_to_int wx)) =
        native_nat_to_int (wxs + wy) := by
    simp [SmtEval.native_zplus, SmtEval.native_zneg,
      native_nat_to_int, SmtEval.native_nat_to_int]
    calc
      (↑wx : Int) + (↑wy + ↑wxs) + -↑wx =
          ((↑wy + ↑wxs) + ↑wx) + -↑wx := by
        simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]
      _ = ↑wy + ↑wxs :=
          Int.add_neg_cancel_right ((↑wy : Int) + ↑wxs) (↑wx : Int)
      _ = ↑wxs + ↑wy := by
          rw [Int.add_comm]
  have hEqEval :=
    model_eval_eq_true_of_eo_eq_true M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral j))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
      (Term.Boolean true) (by
        simpa [bvExtractConcat4Prem, bvExtractConcat4PremRaw] using hPrem)
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.lt (SmtTerm.Numeral j)
          (SmtTerm.neg
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp._at_bvsize)
                (bvConcatTerm x (bvConcatTerm y xs))))
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp._at_bvsize) x)))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hEqEval
  simp [__smtx_model_eval, __smtx_model_eval__, __smtx_model_eval_lt,
    hTotalSize, hXSize, hBoundWidth] at hEqEval
  exact bool_eq_true_of_model_eval_eq_true
    (native_zlt j (native_nat_to_int (wxs + wy))) hEqEval

private theorem smt_typeof_bvsize_int_inv (t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) =
      SmtType.Int ->
    ∃ w, __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
  intro hTy
  change __smtx_typeof
      (native_ite
        (native_zleq 0
          (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt t))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt t)))))
        SmtTerm.None) = SmtType.Int at hTy
  generalize hT : __smtx_typeof (__eo_to_smt t) = T at hTy
  cases T <;>
    simp [__smtx_bv_sizeof_type, SmtEval.native_zleq,
      SmtEval.native_zneg, native_nat_to_int, SmtEval.native_nat_to_int,
      native_ite, __smtx_typeof] at hTy ⊢

private theorem smt_typeof_bvsize_ne_real (t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) t)) ≠
      SmtType.Real := by
  intro hTy
  change __smtx_typeof
      (native_ite
        (native_zleq 0
          (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt t))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt t)))))
        SmtTerm.None) = SmtType.Real at hTy
  generalize hT : __smtx_typeof (__eo_to_smt t) = T at hTy
  cases T <;>
    simp [__smtx_bv_sizeof_type, SmtEval.native_zleq,
      SmtEval.native_zneg, native_nat_to_int, SmtEval.native_nat_to_int,
      native_ite, __smtx_typeof] at hTy

private theorem smt_typeof_neg_int_args
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.neg a b) = SmtType.Int ->
    __smtx_typeof a = SmtType.Int ∧
      __smtx_typeof b = SmtType.Int := by
  intro hTy
  have hNN : term_has_non_none_type (SmtTerm.neg a b) := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq a b) hNN with hArgs | hArgs
  · exact hArgs
  · rw [typeof_neg_eq] at hTy
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2] at hTy

private theorem smt_typeof_neg_real_left
    (a b : SmtTerm) :
    __smtx_typeof (SmtTerm.neg a b) = SmtType.Real ->
    __smtx_typeof a = SmtType.Real := by
  intro hTy
  have hNN : term_has_non_none_type (SmtTerm.neg a b) := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq a b) hNN with hArgs | hArgs
  · rw [typeof_neg_eq] at hTy
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2] at hTy
  · exact hArgs.1

private theorem bvExtractConcat4Prem_smt_context
    (x y xs j : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat4Prem x y xs j) ->
    ∃ wx wy wxs,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __smtx_typeof (__eo_to_smt j) = SmtType.Int := by
  intro hPremBool
  let cond :=
    Term.Apply
      (Term.Apply (Term.UOp UserOp.lt) j)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.neg)
          (Term.Apply (Term.UOp UserOp._at_bvsize)
            (bvConcatTerm x (bvConcatTerm y xs))))
        (Term.Apply (Term.UOp UserOp._at_bvsize) x))
  have hCondTy : __smtx_typeof (__eo_to_smt cond) = SmtType.Bool := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        cond (Term.Boolean true) (by
          simpa [bvExtractConcat4Prem, bvExtractConcat4PremRaw, cond]
            using hPremBool) with
      ⟨hEqTy, _hNN⟩
    simpa [RuleProofs.eo_has_bool_type] using hEqTy
  change __smtx_typeof
      (SmtTerm.lt (__eo_to_smt j)
        (SmtTerm.neg
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) =
    SmtType.Bool at hCondTy
  have hLtNN : term_has_non_none_type
      (SmtTerm.lt (__eo_to_smt j)
        (SmtTerm.neg
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))) := by
    unfold term_has_non_none_type
    rw [hCondTy]
    intro h
    cases h
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt)
      (typeof_lt_eq (__eo_to_smt j)
        (SmtTerm.neg
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))))
      hLtNN with hLtArgs | hLtArgs
  · have hBoundTy : __smtx_typeof
        (SmtTerm.neg
          (__eo_to_smt
            (Term.Apply (Term.UOp UserOp._at_bvsize)
              (bvConcatTerm x (bvConcatTerm y xs))))
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) =
        SmtType.Int := hLtArgs.2
    rcases smt_typeof_neg_int_args
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp._at_bvsize)
            (bvConcatTerm x (bvConcatTerm y xs))))
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        hBoundTy with ⟨hTotalSizeTy, hXSizeTy⟩
    rcases smt_typeof_bvsize_int_inv
        (bvConcatTerm x (bvConcatTerm y xs)) hTotalSizeTy with
      ⟨wTotal, hTotalTy⟩
    rcases smt_typeof_bvsize_int_inv x hXSizeTy with
      ⟨wx, hXTy⟩
    have hTotalNN : term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt x)
          (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt xs))) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (SmtTerm.concat (__eo_to_smt x)
            (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt xs))) ≠
        SmtType.None
      rw [show __smtx_typeof
          (SmtTerm.concat (__eo_to_smt x)
            (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt xs))) =
          SmtType.BitVec wTotal by
        simpa [bvConcatTerm] using hTotalTy]
      intro h
      cases h
    rcases bv_concat_args_of_non_none hTotalNN with
      ⟨_wx', wTail, hXTy', hTailTy⟩
    have hTailNN : term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt xs)) := by
      unfold term_has_non_none_type
      rw [hTailTy]
      intro h
      cases h
    rcases bv_concat_args_of_non_none hTailNN with
      ⟨wy, wxs, hYTy, hXsTy⟩
    exact ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, hLtArgs.1⟩
  · rw [typeof_lt_eq] at hCondTy
    simp [__smtx_typeof_arith_overload_op_2_ret, hLtArgs.1, hLtArgs.2]
      at hCondTy
    have hLeftReal := smt_typeof_neg_real_left
      (__eo_to_smt
        (Term.Apply (Term.UOp UserOp._at_bvsize)
          (bvConcatTerm x (bvConcatTerm y xs))))
      (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
      hLtArgs.2
    exact False.elim
      (smt_typeof_bvsize_ne_real (bvConcatTerm x (bvConcatTerm y xs))
        hLeftReal)

private theorem bvExtractConcat1Prem_smt_context
    (x j : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat1Prem x j) ->
    ∃ wx,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt j) = SmtType.Int := by
  intro hPremBool
  let cond :=
    Term.Apply (Term.Apply (Term.UOp UserOp.leq) j)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x)
  have hCondTy : __smtx_typeof (__eo_to_smt cond) = SmtType.Bool := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        cond (Term.Boolean true) (by
          simpa [bvExtractConcat1Prem, bvExtractConcat1PremRaw, cond]
            using hPremBool) with
      ⟨hEqTy, _hNN⟩
    simpa [RuleProofs.eo_has_bool_type] using hEqTy
  change __smtx_typeof
      (SmtTerm.leq (__eo_to_smt j)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) =
    SmtType.Bool at hCondTy
  have hLeqNN : term_has_non_none_type
      (SmtTerm.leq (__eo_to_smt j)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) := by
    unfold term_has_non_none_type
    rw [hCondTy]
    intro h
    cases h
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
      (typeof_leq_eq (__eo_to_smt j)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
      hLeqNN with hLeqArgs | hLeqArgs
  · rcases smt_typeof_bvsize_int_inv x hLeqArgs.2 with
      ⟨wx, hXTy⟩
    exact ⟨wx, hXTy, hLeqArgs.1⟩
  · exact False.elim
      (smt_typeof_bvsize_ne_real x hLeqArgs.2)

private theorem bv_extract_concat4_guard_refs
    {j x y xs jRef xRef yRef xsRef xRef' body : Term} :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq j jRef) (__eo_eq x xRef))
              (__eo_eq y yRef))
            (__eo_eq xs xsRef))
          (__eo_eq x xRef'))
        (Term.Boolean true) body ≠ Term.Stuck ->
    jRef = j ∧ xRef = x ∧ yRef = y ∧ xsRef = xs ∧ xRef' = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hG1, hX2⟩
  rcases bv_extract_support_and_true hG1 with ⟨hG2, hXs⟩
  rcases bv_extract_support_and_true hG2 with ⟨hG3, hY⟩
  rcases bv_extract_support_and_true hG3 with ⟨hJ, hX1⟩
  exact ⟨(bv_extract_support_eq_true hJ).symm,
    (bv_extract_support_eq_true hX1).symm,
    (bv_extract_support_eq_true hY).symm,
    (bv_extract_support_eq_true hXs).symm,
    (bv_extract_support_eq_true hX2).symm⟩

private theorem bv_extract_concat1_guard_refs
    {j x jRef xRef body : Term} :
    __eo_requires
        (__eo_and (__eo_eq j jRef) (__eo_eq x xRef))
        (Term.Boolean true) body ≠ Term.Stuck ->
    jRef = j ∧ xRef = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hJ, hX⟩
  exact ⟨(bv_extract_support_eq_true hJ).symm,
    (bv_extract_support_eq_true hX).symm⟩

private theorem bv_extract_concat1_premise_shape
    (x xs y i j P : Term) :
    x ≠ Term.Stuck -> xs ≠ Term.Stuck -> y ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractConcat1Program x xs y i j (Proof.pf P) ≠ Term.Stuck ->
    ∃ jRef xRef, P = bvExtractConcat1PremRaw jRef xRef := by
  intro hX hXs hY hI hJ hProg
  by_cases hShape :
      ∃ jRef xRef, P = bvExtractConcat1PremRaw jRef xRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_concat_1.eq_7 x xs y i j
      (Proof.pf P) hX hXs hY hI hJ (by
        intro jRef xRef hP
        cases hP
        exact hShape ⟨jRef, xRef, rfl⟩)

private theorem bv_extract_concat1_program_body_canonical
    (x xs y i j : Term) :
    x ≠ Term.Stuck -> xs ≠ Term.Stuck -> y ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractConcat1Program x xs y i j
        (Proof.pf (bvExtractConcat1Prem x j)) =
      bvExtractConcat1ProgramBody x xs y i j := by
  intro hX hXs hY hI hJ
  unfold bvExtractConcat1Program bvExtractConcat1Prem
    bvExtractConcat1PremRaw bvExtractConcat1ProgramBody
    bvExtractConcat1Whole bvExtractConcat1Seed bvConcatTerm
  rw [__eo_prog_bv_extract_concat_1.eq_6 x xs y i j j x
    hX hXs hY hI hJ]
  simp [bvExtractTerm, __eo_requires, __eo_and, __eo_eq, native_ite,
    native_teq, native_not, SmtEval.native_not, SmtEval.native_and,
    hX, hJ]

theorem bvExtractConcat1Program_normalize
    (x xs y i j P : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    bvExtractConcat1Program x xs y i j (Proof.pf P) ≠ Term.Stuck ->
    P = bvExtractConcat1Prem x j ∧
      bvExtractConcat1Program x xs y i j (Proof.pf P) =
        bvExtractConcat1ProgramBody x xs y i j := by
  intro hXTrans hXsTrans hYTrans hITrans hJTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  rcases bv_extract_concat1_premise_shape x xs y i j P
      hX hXs hY hI hJ hProg with
    ⟨jRef, xRef, hP⟩
  have hReq := hProg
  rw [hP] at hReq
  unfold bvExtractConcat1Program bvExtractConcat1PremRaw at hReq
  rw [__eo_prog_bv_extract_concat_1.eq_6 x xs y i j
    jRef xRef hX hXs hY hI hJ] at hReq
  rcases bv_extract_concat1_guard_refs hReq with ⟨hJRef, hXRef⟩
  subst jRef
  subst xRef
  have hPCanon : P = bvExtractConcat1Prem x j := hP
  refine ⟨hPCanon, ?_⟩
  rw [hPCanon]
  exact bv_extract_concat1_program_body_canonical x xs y i j
    hX hXs hY hI hJ

private theorem bv_extract_concat4_premise_shape
    (x y xs i j P : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> xs ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractConcat4Program x y xs i j (Proof.pf P) ≠ Term.Stuck ->
    ∃ jRef xRef yRef xsRef xRef',
      P = bvExtractConcat4PremRaw jRef xRef yRef xsRef xRef' := by
  intro hX hY hXs hI hJ hProg
  by_cases hShape :
      ∃ jRef xRef yRef xsRef xRef',
        P = bvExtractConcat4PremRaw jRef xRef yRef xsRef xRef'
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_concat_4.eq_7 x y xs i j
      (Proof.pf P) hX hY hXs hI hJ (by
        intro jRef xRef yRef xsRef xRef' hP
        cases hP
        exact hShape ⟨jRef, xRef, yRef, xsRef, xRef', rfl⟩)

private theorem bv_extract_concat4_program_body_canonical
    (x y xs i j : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> xs ≠ Term.Stuck ->
    i ≠ Term.Stuck -> j ≠ Term.Stuck ->
    bvExtractConcat4Program x y xs i j
        (Proof.pf (bvExtractConcat4Prem x y xs j)) =
      bvExtractConcat4ProgramBody x y xs i j := by
  intro hX hY hXs hI hJ
  unfold bvExtractConcat4Program bvExtractConcat4Prem
    bvExtractConcat4PremRaw bvConcatTerm
  rw [__eo_prog_bv_extract_concat_4.eq_6 x y xs i j j x y xs x
    hX hY hXs hI hJ]
  simp [bvExtractConcat4ProgramBody, bvExtractConcat4Tail, bvConcatTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, SmtEval.native_not, SmtEval.native_and,
    hX, hY, hXs, hI, hJ]

theorem bvExtractConcat4Program_normalize
    (x y xs i j P : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    bvExtractConcat4Program x y xs i j (Proof.pf P) ≠ Term.Stuck ->
    P = bvExtractConcat4Prem x y xs j ∧
      bvExtractConcat4Program x y xs i j (Proof.pf P) =
        bvExtractConcat4ProgramBody x y xs i j := by
  intro hXTrans hYTrans hXsTrans hITrans hJTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hXs := RuleProofs.term_ne_stuck_of_has_smt_translation xs hXsTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  rcases bv_extract_concat4_premise_shape x y xs i j P
      hX hY hXs hI hJ hProg with
    ⟨jRef, xRef, yRef, xsRef, xRef', hP⟩
  have hReq := hProg
  rw [hP] at hReq
  unfold bvExtractConcat4Program bvExtractConcat4PremRaw bvConcatTerm at hReq
  rw [__eo_prog_bv_extract_concat_4.eq_6 x y xs i j
    jRef xRef yRef xsRef xRef' hX hY hXs hI hJ] at hReq
  rcases bv_extract_concat4_guard_refs hReq with
    ⟨hJRef, hXRef, hYRef, hXsRef, hXRef'⟩
  subst jRef
  subst xRef
  subst yRef
  subst xsRef
  subst xRef'
  have hPCanon : P = bvExtractConcat4Prem x y xs j := hP
  refine ⟨hPCanon, ?_⟩
  rw [hPCanon]
  exact bv_extract_concat4_program_body_canonical x y xs i j
    hX hY hXs hI hJ

private theorem eo_mk_apply_args_ne_stuck
    {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck -> f ≠ Term.Stuck ∧ x ≠ Term.Stuck := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem eo_mk_apply_eq_apply_of_ne_stuck_local
    {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem bvExtractConcat4Tail_ne_of_body_bool
    (x y xs i j : Term) :
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    bvExtractConcat4Tail y xs ≠ Term.Stuck := by
  intro hTy
  let tail := bvExtractConcat4Tail y xs
  let ext := Term.UOp2 UserOp2.extract j i
  let inner :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.concat) x) tail
  let lhs := __eo_mk_apply ext inner
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  let rhs :=
    __eo_mk_apply ext
      (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail)
  have hBodyNe :
      __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat4ProgramBody, tail, ext, inner, lhs, eqHead, rhs]
      using hNe
  have hEqHeadNe : eqHead ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe : lhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  have hInnerNe : inner ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hLhsNe).2
  exact (eo_mk_apply_args_ne_stuck hInnerNe).2

private theorem bvExtractConcat4Xs_list_of_body_bool
    (x y xs i j : Term) :
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true := by
  intro hTy
  have hTailNe := bvExtractConcat4Tail_ne_of_body_bool x y xs i j hTy
  exact (bv_list_concat_lists_of_ne_stuck
    (Term.UOp UserOp.concat) xs (bvConcatTerm y (Term.Binary 0 0))
    hTailNe).1

theorem bvExtractConcat4ProgramBody_eq_term_of_type_bool
    (x y xs i j : Term) :
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    bvExtractConcat4ProgramBody x y xs i j =
      bvExtractConcat4Term x y xs i j := by
  intro hTy
  let tail := bvExtractConcat4Tail y xs
  let ext := Term.UOp2 UserOp2.extract j i
  let inner :=
    __eo_mk_apply (Term.Apply (Term.UOp UserOp.concat) x) tail
  let lhs := __eo_mk_apply ext inner
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  let rhs :=
    __eo_mk_apply ext
      (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail)
  have hBodyNe :
      __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat4ProgramBody, tail, ext, inner, lhs, eqHead, rhs]
      using hNe
  have hEqHeadNe : eqHead ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hRhsNe : rhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).2
  have hLhsNe : lhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  have hInnerNe : inner ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hLhsNe).2
  have hSingletonNe :
      __eo_list_singleton_elim (Term.UOp UserOp.concat) tail ≠
        Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hRhsNe).2
  have hOuterEq :
      __eo_mk_apply eqHead rhs = Term.Apply eqHead rhs :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hBodyNe
  have hEqHeadEq :
      eqHead = Term.Apply (Term.UOp UserOp.eq) lhs :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hEqHeadNe
  have hLhsEq : lhs = Term.Apply ext inner :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hLhsNe
  have hInnerEq :
      inner = Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) tail :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hInnerNe
  have hRhsEq :
      rhs =
        Term.Apply ext
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail) :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hRhsNe
  calc
    bvExtractConcat4ProgramBody x y xs i j =
        __eo_mk_apply eqHead rhs := by
          simp [bvExtractConcat4ProgramBody, tail, ext, inner, lhs,
            eqHead, rhs]
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply ext
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) tail)))
        (Term.Apply ext
          (__eo_list_singleton_elim (Term.UOp UserOp.concat) tail)) := by
          rw [hOuterEq, hEqHeadEq, hLhsEq, hInnerEq, hRhsEq]
    _ = bvExtractConcat4Term x y xs i j := by
          simp [bvExtractConcat4Term, bvExtractConcat4Lhs,
            bvExtractConcat4Rhs, bvExtractTerm, bvConcatTerm,
            bvExtractConcat4TailElim, tail, ext]

private theorem bvExtractConcat1Whole_ne_of_body_bool
    (x xs y i j : Term) :
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    bvExtractConcat1Whole x y xs ≠ Term.Stuck := by
  intro hTy
  let ext := Term.UOp2 UserOp2.extract j i
  let whole := bvExtractConcat1Whole x y xs
  let lhs := __eo_mk_apply ext whole
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  let rhs := Term.Apply ext x
  have hBodyNe :
      __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat1ProgramBody, ext, whole, lhs, eqHead, rhs]
      using hNe
  have hEqHeadNe : eqHead ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe : lhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  exact (eo_mk_apply_args_ne_stuck hLhsNe).2

private theorem bvExtractConcat1Xs_list_of_body_bool
    (x xs y i j : Term) :
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true := by
  intro hTy
  have hWholeNe := bvExtractConcat1Whole_ne_of_body_bool x xs y i j hTy
  exact (bv_list_concat_lists_of_ne_stuck
    (Term.UOp UserOp.concat) xs (bvExtractConcat1Seed x y)
    hWholeNe).1

theorem bvExtractConcat1ProgramBody_eq_term_of_type_bool
    (x xs y i j : Term) :
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    bvExtractConcat1ProgramBody x xs y i j =
      bvExtractConcat1Term x y xs i j := by
  intro hTy
  let ext := Term.UOp2 UserOp2.extract j i
  let whole := bvExtractConcat1Whole x y xs
  let lhs := __eo_mk_apply ext whole
  let eqHead := __eo_mk_apply (Term.UOp UserOp.eq) lhs
  let rhs := Term.Apply ext x
  have hBodyNe :
      __eo_mk_apply eqHead rhs ≠ Term.Stuck := by
    have hNe := term_ne_stuck_of_typeof_bool hTy
    simpa [bvExtractConcat1ProgramBody, ext, whole, lhs, eqHead, rhs]
      using hNe
  have hEqHeadNe : eqHead ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hBodyNe).1
  have hLhsNe : lhs ≠ Term.Stuck :=
    (eo_mk_apply_args_ne_stuck hEqHeadNe).2
  have hOuterEq :
      __eo_mk_apply eqHead rhs = Term.Apply eqHead rhs :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hBodyNe
  have hEqHeadEq :
      eqHead = Term.Apply (Term.UOp UserOp.eq) lhs :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hEqHeadNe
  have hLhsEq : lhs = Term.Apply ext whole :=
    eo_mk_apply_eq_apply_of_ne_stuck_local hLhsNe
  calc
    bvExtractConcat1ProgramBody x xs y i j =
        __eo_mk_apply eqHead rhs := by
          simp [bvExtractConcat1ProgramBody, ext, whole, lhs,
            eqHead, rhs]
    _ = Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply ext whole)) (Term.Apply ext x) := by
          rw [hOuterEq, hEqHeadEq, hLhsEq]
    _ = bvExtractConcat1Term x y xs i j := by
          simp [bvExtractConcat1Term, bvExtractConcat1Lhs,
            bvExtractConcat1Rhs, bvExtractTerm, whole, ext]

private theorem eo_typeof_concat_args_bitvec_of_ne_stuck_local
    {A B : Term}
    (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    ∃ n m,
      A = Term.Apply (Term.UOp UserOp.BitVec) n ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) m := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | BitVec =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | BitVec =>
                          exact ⟨n, m, rfl, rfl⟩
                      | _ =>
                          simp [__eo_typeof_concat] at h
                  | _ =>
                      simp [__eo_typeof_concat] at h
              | _ =>
                  simp [__eo_typeof_concat] at h
          | _ =>
              simp [__eo_typeof_concat] at h
      | _ =>
          simp [__eo_typeof_concat] at h
  | _ =>
      simp [__eo_typeof_concat] at h

private theorem eo_typeof_list_concat_rec_right_bitvec_of_result
    (a z : Term) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    ∀ w,
      __eo_typeof (__eo_list_concat_rec a z) =
        Term.Apply (Term.UOp UserOp.BitVec) w ->
      ∃ wz,
        __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) wz := by
  intro hList
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      simp [__eo_is_list] at hList
  | case2 a =>
      intro w hTy
      cases a <;> simp [__eo_list_concat_rec] at hTy <;> cases hTy
  | case3 g x y z hZ ih =>
      intro w hTy
      have hg : g = Term.UOp UserOp.concat :=
        eo_is_list_cons_head_eq_of_true
          (Term.UOp UserOp.concat) g x y hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self
          (Term.UOp UserOp.concat) x y hList
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck := by
        intro hStuck
        simp [__eo_list_concat_rec, hStuck, __eo_mk_apply] at hTy
        cases hTy
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
        (Term.UOp UserOp.concat) x y z hTailConcat] at hTy
      change __eo_typeof_concat (__eo_typeof x)
          (__eo_typeof (__eo_list_concat_rec y z)) =
        Term.Apply (Term.UOp UserOp.BitVec) w at hTy
      have hConcatNe :
          __eo_typeof_concat (__eo_typeof x)
              (__eo_typeof (__eo_list_concat_rec y z)) ≠
            Term.Stuck := by
        rw [hTy]
        intro h
        cases h
      rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local
          hConcatNe with
        ⟨_wh, wt, _hHeadTy, hTailTy⟩
      exact ih hTailList wt hTailTy
  | case4 nil z hNil hZ hNot =>
      intro w hTy
      exact ⟨w, by simpa [__eo_list_concat_rec] using hTy⟩

private theorem eo_typeof_list_concat_right_bitvec_of_result
    (a z w : Term) :
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    __eo_typeof (__eo_list_concat (Term.UOp UserOp.concat) a z) =
      Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ wz,
      __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) wz := by
  intro hListA hListZ hTy
  have hRecTy :
      __eo_typeof (__eo_list_concat_rec a z) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    simpa [__eo_list_concat, hListA, hListZ, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not] using hTy
  exact eo_typeof_list_concat_rec_right_bitvec_of_result
    a z hListA w hRecTy

private theorem bvExtractConcat1_body_smt_context
    (x xs y i j : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_bool_type (bvExtractConcat1Prem x j) ->
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    ∃ wx wy wxs,
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
      __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ∧
      __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ∧
      __eo_is_list (Term.UOp UserOp.concat)
          (bvExtractConcat1Seed x y) = Term.Boolean true ∧
      __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
        SmtType.BitVec (wxs + (wy + wx)) := by
  intro hXsTrans hYTrans hPremBool hBodyTy
  rcases bvExtractConcat1Prem_smt_context x j hPremBool with
    ⟨wx, hXTy, _hJTy⟩
  have hBodyEq :=
    bvExtractConcat1ProgramBody_eq_term_of_type_bool x xs y i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat1Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat1Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat1Rhs x i j))
      (by simpa [bvExtractConcat1Term] using hTermTy) with
    ⟨hLhsNe, _hRhsNe⟩
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck
      (by simpa [bvExtractConcat1Lhs, bvExtractTerm] using hLhsNe) with
    ⟨wWhole, hWholeEoTy⟩
  have hXsList :=
    bvExtractConcat1Xs_list_of_body_bool x xs y i j hBodyTy
  have hSeedList := bv_extract_concat1_seed_is_list_true x y
  rcases eo_typeof_list_concat_right_bitvec_of_result
      xs (bvExtractConcat1Seed x y) wWhole hXsList hSeedList
      (by simpa [bvExtractConcat1Whole] using hWholeEoTy) with
    ⟨wSeed, hSeedEoTy⟩
  have hSeedNe :
      __eo_typeof (bvExtractConcat1Seed x y) ≠ Term.Stuck := by
    rw [hSeedEoTy]
    intro h
    cases h
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local
      (by
        change __eo_typeof_concat (__eo_typeof y)
            (__eo_typeof (bvConcatTerm x (Term.Binary 0 0))) ≠
          Term.Stuck
        simpa [bvExtractConcat1Seed, bvConcatTerm] using hSeedNe) with
    ⟨wYTerm, _wInnerTerm, hYEoTy, _hInnerEoTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width
      y wYTerm hYTrans hYEoTy with
    ⟨wyInt, rfl, _hWy0, hYTy⟩
  let wy : Nat := native_int_to_nat wyInt
  rcases smt_typeof_concat_list_of_translation xs hXsList hXsTrans with
    ⟨wxs, hXsTy⟩
  have hWholeTy :
      __smtx_typeof (__eo_to_smt (bvExtractConcat1Whole x y xs)) =
        SmtType.BitVec (wxs + (wy + wx)) := by
    simpa [wy] using
      smt_typeof_bv_extract_concat1_whole x y xs wx wy wxs
        hXsList hXTy hYTy hXsTy
  exact ⟨wx, wy, wxs, hXTy, by simpa [wy] using hYTy,
    hXsTy, hXsList, hSeedList, hWholeTy⟩

theorem typed_bv_extract_concat1_program_body
    (x xs y i j : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_bool_type (bvExtractConcat1Prem x j) ->
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractConcat1ProgramBody x xs y i j) := by
  intro hXsTrans hYTrans hPremBool hBodyTy
  rcases bvExtractConcat1_body_smt_context x xs y i j
      hXsTrans hYTrans hPremBool hBodyTy with
    ⟨wx, wy, wxs, hXTy, _hYTy, _hXsTy, _hXsList,
      _hSeedList, hWholeTy⟩
  have hBodyEq :=
    bvExtractConcat1ProgramBody_eq_term_of_type_bool x xs y i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat1Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    intro h
    cases h
  have hWholeTrans :
      RuleProofs.eo_has_smt_translation (bvExtractConcat1Whole x y xs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hWholeTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat1Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat1Rhs x i j))
      (by simpa [bvExtractConcat1Term] using hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      x j i hXTrans (by
        simpa [bvExtractConcat1Rhs] using hRhsNe) with
    ⟨wRhs, h, l, _hXEoTy, hJ, hI, hwRhs0, hl0, hhRhs,
      hd0, hXSmtTy⟩
  subst j
  subst i
  rcases bv_extract_context_of_non_stuck
      (bvExtractConcat1Whole x y xs) (Term.Numeral h) (Term.Numeral l)
      hWholeTrans (by
        simpa [bvExtractConcat1Lhs] using hLhsNe) with
    ⟨wLhs, hL, lL, _hWholeEoTy, hHL, hLL, hwLhs0, hlL0,
      hhLhs, hdLhs0, hWholeSmtTy⟩
  cases hHL
  cases hLL
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractConcat1Lhs x y xs (Term.Numeral l)
              (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    simpa [bvExtractConcat1Lhs, bvExtractTerm, d] using
      smt_typeof_extract_of_context (bvExtractConcat1Whole x y xs)
        wLhs h l hWholeSmtTy hwLhs0 hl0 hhLhs hdLhs0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractConcat1Rhs x (Term.Numeral l)
              (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    simpa [bvExtractConcat1Rhs, bvExtractTerm, d] using
      smt_typeof_extract_of_context x wRhs h l hXSmtTy
        hwRhs0 hl0 hhRhs hd0
  have hTermBool :
      RuleProofs.eo_has_bool_type
        (bvExtractConcat1Term x y xs (Term.Numeral l)
          (Term.Numeral h)) := by
    unfold bvExtractConcat1Term
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (bvExtractConcat1Lhs x y xs (Term.Numeral l) (Term.Numeral h))
      (bvExtractConcat1Rhs x (Term.Numeral l) (Term.Numeral h))
      (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; simp)
  simpa [hBodyEq]
    using hTermBool

theorem typed_bv_extract_concat4_program_body
    (x y xs i j : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat4Prem x y xs j) ->
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractConcat4ProgramBody x y xs i j) := by
  intro hPremBool hBodyTy
  rcases bvExtractConcat4Prem_smt_context x y xs j hPremBool with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, _hJTy⟩
  have hBodyEq :=
    bvExtractConcat4ProgramBody_eq_term_of_type_bool x y xs i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat4Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXsList :=
    bvExtractConcat4Xs_list_of_body_bool x y xs i j hBodyTy
  let tail := bvExtractConcat4Tail y xs
  let tailElim := bvExtractConcat4TailElim y xs
  have hTailList :
      __eo_is_list (Term.UOp UserOp.concat) tail = Term.Boolean true := by
    simpa [tail] using bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) =
        SmtType.BitVec (wxs + wy) := by
    simpa [tail] using
      smt_typeof_bv_extract_concat4_tail y xs wy wxs
        hXsList hYTy hXsTy
  have hTailElimTy :
      __smtx_typeof (__eo_to_smt tailElim) =
        SmtType.BitVec (wxs + wy) := by
    simpa [tailElim, bvExtractConcat4TailElim, tail] using
      smt_typeof_bv_singleton_elim tail (wxs + wy)
        hTailList hTailTy
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (bvConcatTerm x tail)) =
        SmtType.BitVec (wx + (wxs + wy)) :=
    smt_typeof_bv_concat_eq x tail wx (wxs + wy) hXTy hTailTy
  have hConcatTrans :
      RuleProofs.eo_has_smt_translation (bvConcatTerm x tail) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConcatTy]
    intro h
    cases h
  have hTailElimTrans :
      RuleProofs.eo_has_smt_translation tailElim := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hTailElimTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat4Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat4Rhs y xs i j))
      (by simpa [bvExtractConcat4Term] using hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      (bvConcatTerm x tail) j i hConcatTrans (by
        simpa [bvExtractConcat4Lhs, bvConcatTerm, tail] using hLhsNe) with
    ⟨wTotal, h, l, _hConcatEOType, hJ, hI, hw0, hl0, hhTotal,
      hd0, hConcatSmtTy⟩
  subst j
  subst i
  rcases bv_extract_context_of_non_stuck
      tailElim (Term.Numeral h) (Term.Numeral l) hTailElimTrans (by
        simpa [bvExtractConcat4Rhs, bvExtractConcat4TailElim, tailElim]
          using hRhsNe) with
    ⟨wRhs, hR, lR, _hTailElimEOType, hHR, hLR, hwRhs0, hlR0,
      hhRhs, hdRhs0, hTailElimSmtTy⟩
  cases hHR
  cases hLR
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (bvExtractConcat4Lhs x y xs (Term.Numeral l)
            (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    simpa [bvExtractConcat4Lhs, bvExtractTerm, bvConcatTerm, tail, d] using
      smt_typeof_extract_of_context (bvConcatTerm x tail)
        wTotal h l hConcatSmtTy hw0 hl0 hhTotal hd0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt (bvExtractConcat4Rhs y xs (Term.Numeral l)
            (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    simpa [bvExtractConcat4Rhs, bvExtractTerm,
      bvExtractConcat4TailElim, tailElim, d] using
      smt_typeof_extract_of_context tailElim
        wRhs h l hTailElimSmtTy hwRhs0 hl0 hhRhs hdRhs0
  have hTermBool :
      RuleProofs.eo_has_bool_type
        (bvExtractConcat4Term x y xs (Term.Numeral l)
          (Term.Numeral h)) := by
    unfold bvExtractConcat4Term
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
      (bvExtractConcat4Lhs x y xs (Term.Numeral l) (Term.Numeral h))
      (bvExtractConcat4Rhs y xs (Term.Numeral l) (Term.Numeral h))
      (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; simp)
  simpa [hBodyEq]
    using hTermBool

private theorem bvConcatListCanonical_of_smt_type
    (M : SmtModel) (hM : model_total_typed M) :
    (t : Term) -> (w : Nat) ->
    __eo_is_list (Term.UOp UserOp.concat) t = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    BvConcatListCanonical M t
  | t, w, hList, hTy => by
      revert w hList hTy
      induction t using __eo_get_elements_rec.induct with
      | case1 =>
          intro w hList hTy
          simp [__eo_is_list] at hList
      | case2 f x xs ih =>
          intro w hList hTy
          have hf : f = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) f x xs hList
          subst f
          have hXsList :
              __eo_is_list (Term.UOp UserOp.concat) xs =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.concat) x xs hList
          rcases bvConcat_args_of_bitvec_type x xs w (by
              simpa [bvConcatTerm] using hTy) with
            ⟨wx, wxs, hXTy, hXsTy⟩
          exact ⟨
            bvEvalCanonical_of_smt_type M hM x wx hXTy,
            ih wxs hXsList hXsTy⟩
      | case3 t _hNil hNot =>
          intro w hList hTy
          cases t with
          | Apply f xs =>
              cases f with
              | Apply g x =>
                  exact False.elim (hNot g x xs rfl)
              | _ =>
                  simpa [BvConcatListCanonical] using
                    bvEvalCanonical_of_smt_type M hM _ w hTy
          | _ =>
              simpa [BvConcatListCanonical] using
                bvEvalCanonical_of_smt_type M hM _ w hTy

private theorem concat_is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.concat) t = Term.Boolean b := by
  intro hNe
  cases t
  case Stuck =>
    exact False.elim (hNe rfl)
  case Binary w n =>
    by_cases h : w = 0 ∧ n = 0
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨true, by simp [__eo_is_list_nil]⟩
    · have hTerm : Term.Binary w n ≠ Term.Binary 0 0 := by
        intro hEq
        cases hEq
        exact h ⟨rfl, rfl⟩
      exact ⟨false, by simp [__eo_is_list_nil, hTerm]⟩
  all_goals
    exact ⟨false, by simp [__eo_is_list_nil]⟩

private theorem concat_nil_eval_binary_zero_of_is_list_nil_true
    (M : SmtModel) (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.concat) nil = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0 := by
  cases nil <;> simp [__eo_is_list_nil] at hNil ⊢
  case Binary w n =>
    split at hNil <;> simp_all
    rfl

private theorem bvConcat_right_empty_rel_of_canonical
    (M : SmtModel) (x nil : Term)
    (hx : BvEvalCanonical M x)
    (hnil : __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvConcatTerm x nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases hx with ⟨w, n, hxEval, hn0, hn1⟩
  have hModEq :
      native_mod_total n (native_int_pow2 (↑w : Int)) = n := by
    rw [natpow2_eq w]
    simpa [native_mod_total] using Int.emod_eq_of_lt hn0 hn1
  have hPow0 : native_int_pow2 (0 : native_Int) = 1 := by decide
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt nil)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_concat, hxEval, hnil]
  simp [SmtEval.native_binary_concat, SmtEval.native_zplus,
    SmtEval.native_zmult, hPow0, hModEq, __smtx_model_eval_eq, native_veq]

private theorem bvConcatListCanonical_eval
    (M : SmtModel) :
    (t : Term) -> BvConcatListCanonical M t -> BvEvalCanonical M t
  | t, h => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case concat =>
                    rcases h.1 with ⟨wx, nx, hxEval, hx0, hx1⟩
                    rcases bvConcatListCanonical_eval M xs h.2 with
                      ⟨wxs, nxs, hXsEval, hxs0, hxs1⟩
                    let wsum : Nat := wx + wxs
                    let payload : Int :=
                      native_mod_total (native_binary_concat (↑wx) nx (↑wxs) nxs)
                        (native_int_pow2 (↑wsum : Int))
                    refine ⟨wsum, payload, ?_, ?_, ?_⟩
                    have hWidth :
                        (↑wsum : Int) = native_zplus (↑wx : Int) (↑wxs : Int) := by
                      simp [wsum, SmtEval.native_zplus]
                    have hPayload :
                        payload =
                        native_mod_total (native_binary_concat wx nx wxs nxs)
                          (native_int_pow2 (native_zplus wx wxs)) := by
                      simp [payload, hWidth]
                    · change __smtx_model_eval M
                          (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt xs)) =
                        SmtValue.Binary (↑wsum) payload
                      rw [hWidth, hPayload]
                      change __smtx_model_eval M
                          (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt xs)) =
                        SmtValue.Binary (native_zplus (↑wx) (↑wxs))
                          (native_mod_total
                            (native_binary_concat (↑wx) nx (↑wxs) nxs)
                            (native_int_pow2 (native_zplus (↑wx) (↑wxs))))
                      simp [__smtx_model_eval, __smtx_model_eval_concat,
                        hxEval, hXsEval]
                    · have hWidth0 : native_zleq 0 (↑wsum : Int) = true := by
                        simp [SmtEval.native_zleq]
                      have hCan :
                          native_zeq payload
                              (native_mod_total payload
                                (native_int_pow2 (↑wsum : Int))) = true := by
                        simpa [payload] using native_mod_total_canonical
                          (↑wsum : Int)
                          (native_binary_concat (↑wx) nx (↑wxs) nxs)
                      exact (bitvec_payload_range_of_canonical hWidth0 hCan).1
                    · have hWidth0 : native_zleq 0 (↑wsum : Int) = true := by
                        simp [SmtEval.native_zleq]
                      have hCan :
                          native_zeq payload
                              (native_mod_total payload
                                (native_int_pow2 (↑wsum : Int))) = true := by
                        simpa [payload] using native_mod_total_canonical
                          (↑wsum : Int)
                          (native_binary_concat (↑wx) nx (↑wxs) nxs)
                      simpa [natpow2_eq] using
                        (bitvec_payload_range_of_canonical hWidth0 hCan).2
                  all_goals
                    simpa [BvConcatListCanonical] using h
              | _ =>
                  simpa [BvConcatListCanonical] using h
          | _ =>
              simpa [BvConcatListCanonical] using h
      | _ =>
          simpa [BvConcatListCanonical] using h

theorem bvConcatSingletonElimEvalRel
    (M : SmtModel) (hM : model_total_typed M) (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec w ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hTy
  have hCan := bvConcatListCanonical_of_smt_type M hM c w hList hTy
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg : g = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) g head tail hList
          subst g
          have hHeadCan : BvEvalCanonical M head := hCan.1
          have hTailCan : BvConcatListCanonical M tail := hCan.2
          have hTailList :
              __eo_is_list (Term.UOp UserOp.concat) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.concat) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases concat_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact RuleProofs.smt_value_rel_refl
              (__smtx_model_eval M
                (__eo_to_smt (bvConcatTerm head tail)))
          · exact RuleProofs.smt_value_rel_symm _ _
              (bvConcat_right_empty_rel_of_canonical M head tail hHeadCan
                (concat_nil_eval_binary_zero_of_is_list_nil_true M tail hNil))
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

private theorem bvConcat_right_empty_eval_eq
    (M : SmtModel) (hM : model_total_typed M)
    (x : Term) (wx : Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_model_eval M
        (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hXTy
  have hCan := bvEvalCanonical_of_smt_type M hM x wx hXTy
  have hRel :=
    bvConcat_right_empty_rel_of_canonical M x (Term.Binary 0 0)
      hCan (by rfl)
  have hConcatTy :
      __smtx_typeof
          (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) =
        SmtType.BitVec wx := by
    have hTy :=
      smt_typeof_bv_concat_eq x (Term.Binary 0 0) wx 0
        hXTy smt_typeof_concat_empty
    simpa [Nat.add_zero] using hTy
  have hConcatValueTy :
      __smtx_typeof_value
          (__smtx_model_eval M
            (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0)))) =
        SmtType.BitVec wx := by
    have hNN : term_has_non_none_type
        (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) := by
      unfold term_has_non_none_type
      rw [hConcatTy]
      intro h
      cases h
    simpa [hConcatTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt (bvConcatTerm x (Term.Binary 0 0))) hNN
  exact (RuleProofs.smt_value_rel_iff_eq _ _ (by
    rintro ⟨r1, r2, hLeft, _hRight⟩
    rw [hLeft] at hConcatValueTy
    cases hConcatValueTy)).mp hRel

private theorem eval_bv_extract_concat1_seed_low
    (M : SmtModel) (hM : model_total_typed M)
    (x y : Term) (wx wy : Nat) (h l : native_Int) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wx) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Seed x y)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm x (Term.Numeral h)
          (Term.Numeral l))) := by
  intro hXTy hYTy hl0 hBound hd0
  let inner := bvConcatTerm x (Term.Binary 0 0)
  have hInnerTy :
      __smtx_typeof (__eo_to_smt inner) = SmtType.BitVec wx := by
    have hTy :=
      smt_typeof_bv_concat_eq x (Term.Binary 0 0) wx 0
        hXTy smt_typeof_concat_empty
    simpa [inner, Nat.add_zero] using hTy
  have hStrip :=
    eval_bv_extract_concat_low M hM y inner wy wx h l
      hYTy hInnerTy hl0 hBound hd0
  have hStrip' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm (bvExtractConcat1Seed x y)
              (Term.Numeral h) (Term.Numeral l))) =
        __smtx_model_eval M
          (__eo_to_smt (bvExtractTerm inner (Term.Numeral h)
            (Term.Numeral l))) := by
    simpa [bvExtractConcat1Seed, inner] using hStrip
  have hInnerEval :=
    bvConcat_right_empty_eval_eq M hM x wx hXTy
  rw [hStrip']
  rw [eval_extract_term M inner h l, eval_extract_term M x h l,
    hInnerEval]

private theorem eval_bv_extract_concat1_whole_low
    (M : SmtModel) (hM : model_total_typed M)
    (x y xs : Term) (wx wy wxs : Nat) (h l : native_Int) :
    __eo_is_list (Term.UOp UserOp.concat) xs = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec wxs ->
    native_zleq 0 l = true ->
    native_zlt h (native_nat_to_int wx) = true ->
    native_zleq 0 (native_zplus (native_zplus h 1) (native_zneg l)) =
      true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Whole x y xs)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm x (Term.Numeral h)
          (Term.Numeral l))) := by
  intro hXsList hXTy hYTy hXsTy hl0 hBound hd0
  have hSeedList := bv_extract_concat1_seed_is_list_true x y
  have hSeedTy :=
    smt_typeof_bv_extract_concat1_seed x y wx wy hXTy hYTy
  have hSeedBound :
      native_zlt h (native_nat_to_int (wy + wx)) = true :=
    native_zlt_nat_add_right_local (extra := wy) hBound
  have hStrip :=
    eval_bv_extract_list_concat_low M hM xs
      (bvExtractConcat1Seed x y) wxs (wy + wx) h l
      hXsList hSeedList hXsTy hSeedTy hl0 hSeedBound hd0
  have hSeedLow :=
    eval_bv_extract_concat1_seed_low M hM x y wx wy h l
      hXTy hYTy hl0 hBound hd0
  calc
    __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Whole x y xs)
            (Term.Numeral h) (Term.Numeral l))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Seed x y)
            (Term.Numeral h) (Term.Numeral l))) := by
        simpa [bvExtractConcat1Whole] using hStrip
    _ = __smtx_model_eval M
        (__eo_to_smt (bvExtractTerm x (Term.Numeral h)
          (Term.Numeral l))) := hSeedLow

theorem facts_bv_extract_concat1_program_body
    (M : SmtModel) (hM : model_total_typed M)
    (x xs y i j : Term) :
    RuleProofs.eo_has_smt_translation xs ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_bool_type (bvExtractConcat1Prem x j) ->
    __eo_typeof (bvExtractConcat1ProgramBody x xs y i j) = Term.Bool ->
    eo_interprets M (bvExtractConcat1Prem x j) true ->
    eo_interprets M (bvExtractConcat1ProgramBody x xs y i j) true := by
  intro hXsTrans hYTrans hPremBool hBodyTy _hPremTrue
  rcases bvExtractConcat1_body_smt_context x xs y i j
      hXsTrans hYTrans hPremBool hBodyTy with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, hXsList,
      _hSeedList, hWholeTy⟩
  have hBodyEq :=
    bvExtractConcat1ProgramBody_eq_term_of_type_bool x xs y i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat1Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hXTy]
    intro h
    cases h
  have hWholeTrans :
      RuleProofs.eo_has_smt_translation (bvExtractConcat1Whole x y xs) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hWholeTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat1Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat1Rhs x i j))
      (by simpa [bvExtractConcat1Term] using hTermTy) with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      x j i hXTrans (by
        simpa [bvExtractConcat1Rhs] using hRhsNe) with
    ⟨wRhs, h, l, _hXEoTy, hJ, hI, hwRhs0, hl0, hhRhs,
      hd0, hXSmtTy⟩
  subst j
  subst i
  have hBoundNat :
      native_zlt h (native_nat_to_int (native_int_to_nat wRhs)) = true := by
    have hRound := native_int_to_nat_roundtrip wRhs hwRhs0
    have hWidthEq :
        native_nat_to_int (native_int_to_nat wRhs) = wRhs := by
      simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hRound
    simpa [hWidthEq] using hhRhs
  have hEvalEq :=
    eval_bv_extract_concat1_whole_low M hM x y xs
      (native_int_to_nat wRhs) wy wxs h l hXsList hXSmtTy
      hYTy hXsTy hl0 hBoundNat (native_zleq_of_zlt_true _ _ hd0)
  have hBool :=
    typed_bv_extract_concat1_program_body x xs y
      (Term.Numeral l) (Term.Numeral h)
      hXsTrans hYTrans (by simpa using hPremBool) hBodyTy
  rw [hBodyEq] at hBool
  rw [hBodyEq]
  unfold bvExtractConcat1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractConcat1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvExtractConcat1Whole x y xs)
            (Term.Numeral h) (Term.Numeral l))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm x (Term.Numeral h) (Term.Numeral l))))
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_bv_extract_concat4_program_body
    (M : SmtModel) (hM : model_total_typed M)
    (x y xs i j : Term) :
    RuleProofs.eo_has_bool_type (bvExtractConcat4Prem x y xs j) ->
    __eo_typeof (bvExtractConcat4ProgramBody x y xs i j) = Term.Bool ->
    eo_interprets M (bvExtractConcat4Prem x y xs j) true ->
    eo_interprets M (bvExtractConcat4ProgramBody x y xs i j) true := by
  intro hPremBool hBodyTy hPremTrue
  rcases bvExtractConcat4Prem_smt_context x y xs j hPremBool with
    ⟨wx, wy, wxs, hXTy, hYTy, hXsTy, _hJTy⟩
  have hBodyEq :=
    bvExtractConcat4ProgramBody_eq_term_of_type_bool x y xs i j hBodyTy
  have hTermTy :
      __eo_typeof (bvExtractConcat4Term x y xs i j) = Term.Bool := by
    rw [← hBodyEq]
    exact hBodyTy
  have hXsList :=
    bvExtractConcat4Xs_list_of_body_bool x y xs i j hBodyTy
  let tail := bvExtractConcat4Tail y xs
  let tailElim := bvExtractConcat4TailElim y xs
  have hTailList :
      __eo_is_list (Term.UOp UserOp.concat) tail = Term.Boolean true := by
    simpa [tail] using bv_extract_concat4_tail_is_list_true y xs hXsList
  have hTailTy :
      __smtx_typeof (__eo_to_smt tail) =
        SmtType.BitVec (wxs + wy) := by
    simpa [tail] using
      smt_typeof_bv_extract_concat4_tail y xs wy wxs
        hXsList hYTy hXsTy
  have hTailElimTy :
      __smtx_typeof (__eo_to_smt tailElim) =
        SmtType.BitVec (wxs + wy) := by
    simpa [tailElim, bvExtractConcat4TailElim, tail] using
      smt_typeof_bv_singleton_elim tail (wxs + wy)
        hTailList hTailTy
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (bvConcatTerm x tail)) =
        SmtType.BitVec (wx + (wxs + wy)) :=
    smt_typeof_bv_concat_eq x tail wx (wxs + wy) hXTy hTailTy
  have hConcatTrans :
      RuleProofs.eo_has_smt_translation (bvConcatTerm x tail) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConcatTy]
    intro h
    cases h
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvExtractConcat4Lhs x y xs i j))
      (__eo_typeof (bvExtractConcat4Rhs y xs i j))
      (by simpa [bvExtractConcat4Term] using hTermTy) with
    ⟨hLhsNe, _hRhsNe⟩
  rcases bv_extract_context_of_non_stuck
      (bvConcatTerm x tail) j i hConcatTrans (by
        simpa [bvExtractConcat4Lhs, bvConcatTerm, tail] using hLhsNe) with
    ⟨wTotal, h, l, _hConcatEOType, hJ, hI, hw0, hl0, hhTotal,
      hd0, hConcatSmtTy⟩
  subst j
  subst i
  have hTailBound :
      native_zlt h (native_nat_to_int (wxs + wy)) = true :=
    bvExtractConcat4Prem_bound M x y xs wx wy wxs h
      hXTy hYTy hXsTy (by simpa using hPremTrue)
  have hLowExtract :=
    eval_bv_extract_concat_low M hM x tail wx (wxs + wy) h l
      hXTy hTailTy hl0 hTailBound (native_zleq_of_zlt_true _ _ hd0)
  have hTailElimRel :=
    bvConcatSingletonElimEvalRel M hM tail (wxs + wy)
      hTailList hTailTy
  have hTailValueTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt tail)) =
        SmtType.BitVec (wxs + wy) := by
    have hNN : term_has_non_none_type (__eo_to_smt tail) := by
      unfold term_has_non_none_type
      rw [hTailTy]
      intro hNone
      cases hNone
    simpa [hTailTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt tail) hNN
  have hTailElimEq :
      __smtx_model_eval M (__eo_to_smt tailElim) =
        __smtx_model_eval M (__eo_to_smt tail) :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, _hElimReg, hTailReg⟩
      rw [hTailReg] at hTailValueTy
      cases hTailValueTy)).mp (by
        simpa [tailElim, bvExtractConcat4TailElim] using hTailElimRel)
  have hBool :=
    typed_bv_extract_concat4_program_body x y xs
      (Term.Numeral l) (Term.Numeral h)
      (by simpa using hPremBool) hBodyTy
  rw [hBodyEq] at hBool
  rw [hBodyEq]
  unfold bvExtractConcat4Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractConcat4Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm (bvConcatTerm x tail)
            (Term.Numeral h) (Term.Numeral l))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm tailElim (Term.Numeral h)
            (Term.Numeral l))))
    rw [hLowExtract]
    rw [eval_extract_term M tail h l,
      eval_extract_term M tailElim h l, hTailElimEq]
    exact RuleProofs.smt_value_rel_refl _
