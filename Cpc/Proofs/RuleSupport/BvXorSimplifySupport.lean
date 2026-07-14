import Cpc.Proofs.RuleSupport.BvCommutativeXorSupport
import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import Cpc.Proofs.Rules.Aci_norm

/-! Shared support for the three n-ary bit-vector XOR simplification rules. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvXorSimplifySupport

private def op : Term := Term.UOp UserOp.bvxor

private def xor (x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private def bvnot (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) x

private def eqTerm (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private def guardedInner (ys zs second : Term) : Term :=
  __eo_list_concat op ys (xor second zs)

private def guardedInserted (ys zs first second : Term) : Term :=
  __eo_mk_apply (Term.Apply op first) (guardedInner ys zs second)

private def guardedLhs (xs ys zs first second : Term) : Term :=
  __eo_list_concat op xs (guardedInserted ys zs first second)

private def guardedBase (xs ys zs : Term) : Term :=
  __eo_list_singleton_elim op
    (__eo_list_concat op xs (__eo_list_concat op ys zs))

private def inner (ys zs second : Term) : Term :=
  __eo_list_concat_rec ys (xor second zs)

private def inserted (ys zs first second : Term) : Term :=
  xor first (inner ys zs second)

private def lhs (xs ys zs first second : Term) : Term :=
  __eo_list_concat_rec xs (inserted ys zs first second)

private def baseList (xs ys zs : Term) : Term :=
  __eo_list_concat_rec xs (__eo_list_concat_rec ys zs)

private def base (xs ys zs : Term) : Term :=
  __eo_list_singleton_elim op (baseList xs ys zs)

def term1 (xs ys zs x : Term) : Term :=
  eqTerm (lhs xs ys zs x x) (base xs ys zs)

def term2 (xs ys zs x : Term) : Term :=
  eqTerm (lhs xs ys zs x (bvnot x)) (bvnot (base xs ys zs))

def term3 (xs ys zs x : Term) : Term :=
  eqTerm (lhs xs ys zs (bvnot x) x) (bvnot (base xs ys zs))

private def skeleton1 (xs ys zs x : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq) (guardedLhs xs ys zs x x))
    (guardedBase xs ys zs)

private def skeleton2 (xs ys zs x : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (guardedLhs xs ys zs x (bvnot x)))
    (__eo_mk_apply (Term.UOp UserOp.bvnot) (guardedBase xs ys zs))

private def skeleton3 (xs ys zs x : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (guardedLhs xs ys zs (bvnot x) x))
    (__eo_mk_apply (Term.UOp UserOp.bvnot) (guardedBase xs ys zs))

private theorem list_concat_reduce (f a b : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f b = Term.Boolean true ->
    __eo_list_concat f a b = __eo_list_concat_rec a b := by
  intro hA hB
  simp [__eo_list_concat, hA, hB, __eo_requires, native_ite,
    native_teq, native_not, SmtEval.native_not]

private theorem list_concat_parts_of_ne_stuck (f a b : Term) :
    __eo_list_concat f a b ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true ∧
      __eo_is_list f b = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_requires (__eo_is_list f b) (Term.Boolean true)
            (__eo_list_concat_rec a b)) ≠ Term.Stuck := by
    simpa [__eo_list_concat] using h
  have hA := support_eo_requires_cond_eq_of_non_stuck hReq
  have hTail :
      __eo_requires (__eo_is_list f b) (Term.Boolean true)
          (__eo_list_concat_rec a b) ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hReq
  exact ⟨hA, support_eo_requires_cond_eq_of_non_stuck hTail⟩

private theorem term_ne_stuck_of_is_list_true (f t : Term) :
    __eo_is_list f t = Term.Boolean true ->
    t ≠ Term.Stuck := by
  intro hList h
  subst t
  cases f <;> simp [__eo_is_list] at hList

private theorem guardedLhs_lists_of_ne_stuck
    (xs ys zs first second : Term) :
    guardedLhs xs ys zs first second ≠ Term.Stuck ->
    __eo_is_list op xs = Term.Boolean true ∧
      __eo_is_list op ys = Term.Boolean true ∧
      __eo_is_list op zs = Term.Boolean true := by
  intro hLhs
  have hOuter := list_concat_parts_of_ne_stuck op xs
    (guardedInserted ys zs first second) (by
      simpa [guardedLhs] using hLhs)
  have hInsertedNe :=
    term_ne_stuck_of_is_list_true op (guardedInserted ys zs first second)
      hOuter.2
  have hInsertedEq :
      guardedInserted ys zs first second =
        xor first (guardedInner ys zs second) := by
    exact eo_mk_apply_eq_apply_of_ne_stuck _ _ hInsertedNe
  have hInnerList :
      __eo_is_list op (guardedInner ys zs second) =
        Term.Boolean true := by
    rw [hInsertedEq] at hOuter
    exact eo_is_list_tail_true_of_cons_self op first
      (guardedInner ys zs second) hOuter.2
  have hInnerNe := term_ne_stuck_of_is_list_true op
    (guardedInner ys zs second) hInnerList
  have hInner := list_concat_parts_of_ne_stuck op ys (xor second zs) (by
    simpa [guardedInner] using hInnerNe)
  have hZs : __eo_is_list op zs = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self op second zs hInner.2
  exact ⟨hOuter.1, hInner.1, hZs⟩

private theorem guardedLhs_eq_lhs_of_ne_stuck
    (xs ys zs first second : Term) :
    guardedLhs xs ys zs first second ≠ Term.Stuck ->
    guardedLhs xs ys zs first second = lhs xs ys zs first second := by
  intro hLhs
  have hOuter := list_concat_parts_of_ne_stuck op xs
    (guardedInserted ys zs first second) (by
      simpa [guardedLhs] using hLhs)
  have hInsertedNe :=
    term_ne_stuck_of_is_list_true op (guardedInserted ys zs first second)
      hOuter.2
  have hInsertedEq :
      guardedInserted ys zs first second =
        xor first (guardedInner ys zs second) :=
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hInsertedNe
  have hInnerList :
      __eo_is_list op (guardedInner ys zs second) =
        Term.Boolean true := by
    rw [hInsertedEq] at hOuter
    exact eo_is_list_tail_true_of_cons_self op first
      (guardedInner ys zs second) hOuter.2
  have hInnerNe := term_ne_stuck_of_is_list_true op
    (guardedInner ys zs second) hInnerList
  have hInnerParts := list_concat_parts_of_ne_stuck op ys
    (xor second zs) (by simpa [guardedInner] using hInnerNe)
  have hOuterReduce := list_concat_reduce op xs
    (guardedInserted ys zs first second) hOuter.1 hOuter.2
  have hInnerReduce := list_concat_reduce op ys (xor second zs)
    hInnerParts.1 hInnerParts.2
  calc
    guardedLhs xs ys zs first second =
        __eo_list_concat_rec xs (guardedInserted ys zs first second) := by
      simpa [guardedLhs] using hOuterReduce
    _ = __eo_list_concat_rec xs
        (xor first (guardedInner ys zs second)) := by rw [hInsertedEq]
    _ = lhs xs ys zs first second := by
      rw [show guardedInner ys zs second = inner ys zs second by
        simpa [guardedInner, inner] using hInnerReduce]
      rfl

private theorem guardedBase_eq_base_of_lists
    (xs ys zs : Term) :
    __eo_is_list op xs = Term.Boolean true ->
    __eo_is_list op ys = Term.Boolean true ->
    __eo_is_list op zs = Term.Boolean true ->
    guardedBase xs ys zs = base xs ys zs := by
  intro hXs hYs hZs
  have hYZReduce := list_concat_reduce op ys zs hYs hZs
  have hYZRecList :
      __eo_is_list op (__eo_list_concat_rec ys zs) = Term.Boolean true :=
    eo_list_concat_rec_is_list_true_of_lists op ys zs hYs hZs
  have hYZGuardList :
      __eo_is_list op (__eo_list_concat op ys zs) = Term.Boolean true := by
    rw [hYZReduce]
    exact hYZRecList
  have hOuterReduce := list_concat_reduce op xs
    (__eo_list_concat op ys zs) hXs hYZGuardList
  unfold guardedBase base baseList
  rw [hOuterReduce, hYZReduce]

private theorem prog1_eq_skeleton_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_prog_bv_xor_simplify_1 xs ys zs x = skeleton1 xs ys zs x := by
  intro hXs hYs hZs hX
  cases xs <;> cases ys <;> cases zs <;> cases x <;>
    simp [__eo_prog_bv_xor_simplify_1, skeleton1, guardedLhs,
      guardedInserted, guardedInner, guardedBase, xor, op, eqTerm] at
      hXs hYs hZs hX ⊢

private theorem prog2_eq_skeleton_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_prog_bv_xor_simplify_2 xs ys zs x = skeleton2 xs ys zs x := by
  intro hXs hYs hZs hX
  cases xs <;> cases ys <;> cases zs <;> cases x <;>
    simp [__eo_prog_bv_xor_simplify_2, skeleton2, guardedLhs,
      guardedInserted, guardedInner, guardedBase, xor, bvnot, op, eqTerm] at
      hXs hYs hZs hX ⊢

private theorem prog3_eq_skeleton_of_ne_stuck
    (xs ys zs x : Term) :
    xs ≠ Term.Stuck -> ys ≠ Term.Stuck ->
    zs ≠ Term.Stuck -> x ≠ Term.Stuck ->
    __eo_prog_bv_xor_simplify_3 xs ys zs x = skeleton3 xs ys zs x := by
  intro hXs hYs hZs hX
  cases xs <;> cases ys <;> cases zs <;> cases x <;>
    simp [__eo_prog_bv_xor_simplify_3, skeleton3, guardedLhs,
      guardedInserted, guardedInner, guardedBase, xor, bvnot, op, eqTerm] at
      hXs hYs hZs hX ⊢

private theorem ne_stuck_of_bitvec_smt_type (t : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.term_ne_stuck_of_has_smt_translation t (by
    intro hNone
    rw [hTy] at hNone
    cases hNone)

private theorem skeleton_lhs_ne_of_type_bool (left right : Term) :
    __eo_typeof
        (__eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) left) right) =
      Term.Bool ->
    left ≠ Term.Stuck := by
  intro hTy
  have hTop := term_ne_stuck_of_typeof_bool hTy
  have hEqFun := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hTop
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hEqFun

private theorem program1_lhs_ne
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs x x ≠ Term.Stuck := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hProgEq := prog1_eq_skeleton_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)
  apply skeleton_lhs_ne_of_type_bool
    (guardedLhs xs ys zs x x) (guardedBase xs ys zs)
  rwa [← hProgEq]

private theorem program2_lhs_ne
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs x (bvnot x) ≠ Term.Stuck := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hProgEq := prog2_eq_skeleton_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)
  apply skeleton_lhs_ne_of_type_bool
    (guardedLhs xs ys zs x (bvnot x))
    (__eo_mk_apply (Term.UOp UserOp.bvnot) (guardedBase xs ys zs))
  rwa [← hProgEq]

private theorem program3_lhs_ne
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    guardedLhs xs ys zs (bvnot x) x ≠ Term.Stuck := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hProgEq := prog3_eq_skeleton_of_ne_stuck xs ys zs x
    (ne_stuck_of_bitvec_smt_type xs w hXsTy)
    (ne_stuck_of_bitvec_smt_type ys w hYsTy)
    (ne_stuck_of_bitvec_smt_type zs w hZsTy)
    (ne_stuck_of_bitvec_smt_type x w hXTy)
  apply skeleton_lhs_ne_of_type_bool
    (guardedLhs xs ys zs (bvnot x) x)
    (__eo_mk_apply (Term.UOp UserOp.bvnot) (guardedBase xs ys zs))
  rwa [← hProgEq]

theorem program1_eq_term
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_1 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_1 xs ys zs x = term1 xs ys zs x := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hXsNe := ne_stuck_of_bitvec_smt_type xs w hXsTy
  have hYsNe := ne_stuck_of_bitvec_smt_type ys w hYsTy
  have hZsNe := ne_stuck_of_bitvec_smt_type zs w hZsTy
  have hXNe := ne_stuck_of_bitvec_smt_type x w hXTy
  have hProgEq := prog1_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  have hSkeletonTy : __eo_typeof (skeleton1 xs ys zs x) = Term.Bool := by
    rw [← hProgEq]
    exact hResultTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := program1_lhs_ne xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := guardedLhs_lists_of_ne_stuck xs ys zs x x hLhsNe
  have hLhsEq := guardedLhs_eq_lhs_of_ne_stuck xs ys zs x x hLhsNe
  have hBaseEq := guardedBase_eq_base_of_lists xs ys zs
    hLists.1 hLists.2.1 hLists.2.2
  calc
    __eo_prog_bv_xor_simplify_1 xs ys zs x = skeleton1 xs ys zs x := hProgEq
    _ = eqTerm (guardedLhs xs ys zs x x) (guardedBase xs ys zs) := by
      unfold skeleton1 eqTerm
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
    _ = term1 xs ys zs x := by rw [hLhsEq, hBaseEq]; rfl

theorem program2_eq_term
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_2 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_2 xs ys zs x = term2 xs ys zs x := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hXsNe := ne_stuck_of_bitvec_smt_type xs w hXsTy
  have hYsNe := ne_stuck_of_bitvec_smt_type ys w hYsTy
  have hZsNe := ne_stuck_of_bitvec_smt_type zs w hZsTy
  have hXNe := ne_stuck_of_bitvec_smt_type x w hXTy
  have hProgEq := prog2_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  have hSkeletonTy : __eo_typeof (skeleton2 xs ys zs x) = Term.Bool := by
    rw [← hProgEq]
    exact hResultTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := program2_lhs_ne xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := guardedLhs_lists_of_ne_stuck
    xs ys zs x (bvnot x) hLhsNe
  have hLhsEq := guardedLhs_eq_lhs_of_ne_stuck
    xs ys zs x (bvnot x) hLhsNe
  have hBaseEq := guardedBase_eq_base_of_lists xs ys zs
    hLists.1 hLists.2.1 hLists.2.2
  calc
    __eo_prog_bv_xor_simplify_2 xs ys zs x = skeleton2 xs ys zs x := hProgEq
    _ = eqTerm (guardedLhs xs ys zs x (bvnot x))
        (bvnot (guardedBase xs ys zs)) := by
      unfold skeleton2 eqTerm bvnot
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe]
    _ = term2 xs ys zs x := by rw [hLhsEq, hBaseEq]; rfl

theorem program3_eq_term
    (xs ys zs x : Term) (w : Nat) :
    __smtx_typeof (__eo_to_smt xs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt ys) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt zs) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __eo_typeof (__eo_prog_bv_xor_simplify_3 xs ys zs x) = Term.Bool ->
    __eo_prog_bv_xor_simplify_3 xs ys zs x = term3 xs ys zs x := by
  intro hXsTy hYsTy hZsTy hXTy hResultTy
  have hXsNe := ne_stuck_of_bitvec_smt_type xs w hXsTy
  have hYsNe := ne_stuck_of_bitvec_smt_type ys w hYsTy
  have hZsNe := ne_stuck_of_bitvec_smt_type zs w hZsTy
  have hXNe := ne_stuck_of_bitvec_smt_type x w hXTy
  have hProgEq := prog3_eq_skeleton_of_ne_stuck xs ys zs x
    hXsNe hYsNe hZsNe hXNe
  have hSkeletonTy : __eo_typeof (skeleton3 xs ys zs x) = Term.Bool := by
    rw [← hProgEq]
    exact hResultTy
  have hSkeletonNe := term_ne_stuck_of_typeof_bool hSkeletonTy
  have hEqFunNe := eo_mk_apply_fun_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hRhsNe := eo_mk_apply_arg_ne_stuck_of_ne_stuck _ _ hSkeletonNe
  have hLhsNe := program3_lhs_ne xs ys zs x w
    hXsTy hYsTy hZsTy hXTy hResultTy
  have hLists := guardedLhs_lists_of_ne_stuck
    xs ys zs (bvnot x) x hLhsNe
  have hLhsEq := guardedLhs_eq_lhs_of_ne_stuck
    xs ys zs (bvnot x) x hLhsNe
  have hBaseEq := guardedBase_eq_base_of_lists xs ys zs
    hLists.1 hLists.2.1 hLists.2.2
  calc
    __eo_prog_bv_xor_simplify_3 xs ys zs x = skeleton3 xs ys zs x := hProgEq
    _ = eqTerm (guardedLhs xs ys zs (bvnot x) x)
        (bvnot (guardedBase xs ys zs)) := by
      unfold skeleton3 eqTerm bvnot
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hSkeletonNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqFunNe]
      rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hRhsNe]
    _ = term3 xs ys zs x := by rw [hLhsEq, hBaseEq]; rfl

end BvXorSimplifySupport
