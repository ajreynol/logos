import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Quantifiers
import Cpc.Proofs.Translation.Special
import Cpc.Proofs.Translation.Inversions
import Cpc.Proofs.Translation.Heads
import Cpc.Proofs.TypePreservation

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof
attribute [local reducible] __eo_to_smt

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_concat`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_concat
    (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply Term.concat y) x) =
        theory2 SmtTheoryOp.concat (__eo_to_smt y) (__eo_to_smt x))
    (hEo :
      ∀ w1 w2 : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w1 ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w2 ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.concat y) x)) =
          SmtType.BitVec
            (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.concat y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.concat y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.concat y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (theory2 SmtTheoryOp.concat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_concat_args_of_non_none hApplyNN with ⟨w1, w2, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.concat y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
    rw [hTranslate]
    rw [typeof_concat_eq (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_concat, hy, hx]
  exact hSmt.trans (hEo w1 w2 hy hx).symm

/-- Computes `generic_apply_type` for `none` heads. -/
private theorem generic_apply_type_none
    (x : SmtTerm) :
    generic_apply_type SmtTerm.None x := by
  rw [generic_apply_type, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for boolean heads. -/
private theorem generic_apply_type_boolean
    (b : native_Bool) (x : SmtTerm) :
    generic_apply_type (SmtTerm.Boolean b) x := by
  rw [generic_apply_type, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for variable heads. -/
private theorem generic_apply_type_var
    (s : native_String) (T : SmtType) (x : SmtTerm) :
    generic_apply_type (SmtTerm.Var s T) x := by
  rw [generic_apply_type, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for datatype constructor heads. -/
private theorem generic_apply_type_dt_cons
    (s : native_String) (d : SmtDatatype) (i : native_Nat) (x : SmtTerm) :
    generic_apply_type (SmtTerm.DtCons s d i) x := by
  rw [generic_apply_type, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for universal-constant heads. -/
private theorem generic_apply_type_uconst
    (s : native_String) (T : SmtType) (x : SmtTerm) :
    generic_apply_type (SmtTerm.UConst s T) x := by
  rw [generic_apply_type, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `and`. -/
private theorem generic_apply_type_and
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.and t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `not`. -/
private theorem generic_apply_type_not
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.not t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `to_real`. -/
private theorem generic_apply_type_to_real
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.to_real t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `to_int`. -/
private theorem generic_apply_type_to_int
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.to_int t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `is_int`. -/
private theorem generic_apply_type_is_int
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.is_int t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `abs`. -/
private theorem generic_apply_type_abs
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.abs t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `str_to_re`. -/
private theorem generic_apply_type_str_to_re
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.str_to_re t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `re_mult`. -/
private theorem generic_apply_type_re_mult
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.re_mult t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `re_plus`. -/
private theorem generic_apply_type_re_plus
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.re_plus t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `re_opt`. -/
private theorem generic_apply_type_re_opt
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.re_opt t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `re_comp`. -/
private theorem generic_apply_type_re_comp
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.re_comp t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `set_singleton`. -/
private theorem generic_apply_type_set_singleton
    (t x : SmtTerm) :
    generic_apply_type (theory1 SmtTheoryOp.set_singleton t) x := by
  rw [generic_apply_type, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `re_exp`. -/
private theorem generic_apply_type_re_exp
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.re_exp t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `set_union`. -/
private theorem generic_apply_type_set_union
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.set_union t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `set_inter`. -/
private theorem generic_apply_type_set_inter
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.set_inter t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `set_minus`. -/
private theorem generic_apply_type_set_minus
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.set_minus t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `set_member`. -/
private theorem generic_apply_type_set_member
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.set_member t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `set_subset`. -/
private theorem generic_apply_type_set_subset
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.set_subset t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `qdiv_total`. -/
private theorem generic_apply_type_qdiv_total
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.qdiv_total t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Computes `generic_apply_type` for partially-applied `int_to_bv`. -/
private theorem generic_apply_type_int_to_bv
    (t1 t2 x : SmtTerm) :
    generic_apply_type (theory2 SmtTheoryOp.int_to_bv t1 t2) x := by
  rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_bv_binop`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bv_binop
    (eoOp : Term) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply eoOp y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ w : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) = SmtType.BitVec w)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_binop_args_of_non_none hTy hApplyNN with ⟨w, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) = SmtType.BitVec w := by
    rw [hTranslate]
    rw [hTy, hy, hx]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq, SmtEval.native_nateq]
  exact hSmt.trans (hEo w hy hx).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_bv_binop_ret`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
    (eoOp : Term) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply eoOp y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x))
          ret)
    (hEo :
      ∀ w : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) = ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_binop_ret_args_of_non_none hTy hApplyNN with
    ⟨w, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) = ret := by
    rw [hTranslate]
    rw [hTy, hy, hx]
    simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, SmtEval.native_nateq]
  exact hSmt.trans (hEo w hy hx).symm

/-- Extracts non-`none` from a function-like apply head. -/
private theorem smtx_head_non_none_of_apply_cases
    {T A B : SmtType}
    (hHead : T = SmtType.FunType A B ∨ T = SmtType.DtcAppType A B) :
    T ≠ SmtType.None := by
  intro hNone
  rcases hHead with hHead | hHead
  · cases hNone.symm.trans hHead
  · cases hNone.symm.trans hHead

/-- Computes `__smtx_typeof_apply` for function-like apply heads. -/
private theorem smtx_typeof_apply_of_head_cases
    {F X A B : SmtType}
    (hHead : F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B)
    (hX : X = A)
    (hA : A ≠ SmtType.None) :
    __smtx_typeof_apply F X = B := by
  rcases hHead with hHead | hHead
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]

/-- Rewrites the typing equation for `bvnot`. -/
private theorem typeof_bvnot_eq
    (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.bvnot t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  change __smtx_typeof (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnot) t) = _
  rw [__smtx_typeof.eq_def]

/-- Rewrites the typing equation for `bvcomp`. -/
private theorem typeof_bvcomp_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.bvcomp t1 t2) =
      __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) (SmtType.BitVec 1) := by
  change __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvcomp) t1) t2) = _
  rw [__smtx_typeof.eq_def]

/-- Rewrites the typing equation for `bvneg`. -/
private theorem typeof_bvneg_eq
    (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.bvneg t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  change __smtx_typeof (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvneg) t) = _
  rw [__smtx_typeof.eq_def]

/-- Rewrites the typing equation for `bvnego`. -/
private theorem typeof_bvnego_eq
    (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.bvnego t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Bool := by
  change __smtx_typeof (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnego) t) = _
  rw [__smtx_typeof.eq_def]

/-- Rewrites the typing equation for `seq_unit`. -/
private theorem typeof_seq_unit_eq
    (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.seq_unit t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.None) SmtType.None
        (SmtType.Seq (__smtx_typeof t)) := by
  change __smtx_typeof (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.seq_unit) t) = _
  rw [__smtx_typeof.eq_def]

/-- Rewrites the typing equation for `set_empty`. -/
private theorem typeof_set_empty_eq
    (T : SmtType) :
    __smtx_typeof (SmtTerm.set_empty T) =
      __smtx_typeof_guard_wf T (SmtType.Set T) := by
  change __smtx_typeof (SmtTerm.set_empty T) = _
  rw [__smtx_typeof.eq_def]

/-- Rewrites the typing equation for `set_singleton`. -/
private theorem typeof_set_singleton_eq
    (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.set_singleton t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.None) SmtType.None
        (SmtType.Set (__smtx_typeof t)) := by
  change __smtx_typeof (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.set_singleton) t) = _
  rw [__smtx_typeof.eq_def]

/-- Rewrites the typing equation for `exists`. -/
private theorem typeof_exists_eq
    (s : native_String) (T : SmtType) (t : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None := by
  change __smtx_typeof (SmtTerm.exists s T t) = _
  rw [__smtx_typeof.eq_def]

/-- Computes the type of applying `none`. -/
private theorem typeof_apply_none_eq
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x := by
    exact generic_apply_type_none x
  rw [hGeneric, smtx_typeof_none]
  simp [__smtx_typeof_apply]

/-- Rewrites the typing equation for rationals. -/
private theorem typeof_rational_eq
    (q : native_Rat) :
    __smtx_typeof (SmtTerm.Rational q) = SmtType.Real := by
  unfold __smtx_typeof
  rfl

/-- Computes the type of the one-bit literal used by `bvite`. -/
private theorem typeof_binary_one_eq :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [native_ite, SmtEval.native_and, native_zleq, native_zeq, native_mod_total,
      native_int_pow2]
    native_decide
  simpa using smtx_typeof_binary_of_non_none 1 1 hNN

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_apply_apply_generic`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
    (g z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate] using hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) ≠ SmtType.None := by
    cases hHead with
    | inl hHead =>
        rw [hHead]
        simp
    | inr hHead =>
        rw [hHead]
        simp
  have hHeadEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)) = SmtType.FunType A B ∨
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)) = SmtType.DtcAppType A B := by
    rw [← ihF hHeadNN]
    exact hHead
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) = B := by
    rw [hTranslate]
    rw [hGeneric]
    cases hHead with
    | inl hHead =>
        rw [hHead, hX]
        simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
    | inr hHead =>
        rw [hHead, hX]
        simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
  exact hSmt.trans
    (eo_to_smt_type_typeof_apply_of_smt_apply
      x (Term.Apply (Term.Apply g z) y) A B hHeadEo hX).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_apply_generic`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_generic
    (g y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply g y)))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g y) x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply g y)))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate] using hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN :
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) ≠ SmtType.None := by
    cases hHead with
    | inl hHead =>
        rw [hHead]
        simp
    | inr hHead =>
        rw [hHead]
        simp
  have hHeadEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply g y)) = SmtType.FunType A B ∨
        __eo_to_smt_type (__eo_typeof (Term.Apply g y)) = SmtType.DtcAppType A B := by
    rw [← ihF hHeadNN]
    exact hHead
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) = B := by
    rw [hTranslate]
    rw [hGeneric]
    cases hHead with
    | inl hHead =>
        rw [hHead, hX]
        simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
    | inr hHead =>
        rw [hHead, hX]
        simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
  exact hSmt.trans
    (eo_to_smt_type_typeof_apply_of_smt_apply
      x (Term.Apply g y) A B hHeadEo hX).symm

/-- Computes `__smtx_typeof` for `eq_non_none`. -/
private theorem smtx_typeof_eq_non_none
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None := by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, hNone, hEq])

/-- Lemma about `smt_type_ne_set_self`. -/
private theorem smt_type_ne_set_self
    (T : SmtType) :
    T ≠ SmtType.Set T := by
  cases T <;> intro h <;> cases h

/-- Lemma about `smt_type_ne_guard_wf_set_self`. -/
private theorem smt_type_ne_guard_wf_set_self
    {T : SmtType}
    (hT : T ≠ SmtType.None) :
    T ≠ __smtx_typeof_guard_wf T (SmtType.Set T) := by
  intro h
  by_cases hInh : native_inhabited_type T = true
  · by_cases hWf : __smtx_type_wf T = true
    · have hSet : T = SmtType.Set T := by
        simpa [__smtx_typeof_guard_wf, hInh, hWf, native_ite] using h
      exact smt_type_ne_set_self T hSet
    · have hNone : T = SmtType.None := by
        simpa [__smtx_typeof_guard_wf, hInh, hWf, native_ite] using h
      exact hT hNone
  · have hNone : T = SmtType.None := by
      simpa [__smtx_typeof_guard_wf, hInh, native_ite] using h
    exact hT hNone

/-- Computes `__smtx_typeof` for `apply_eo_to_smt_set_empty_eq_none`. -/
private theorem smtx_typeof_apply_eo_to_smt_set_empty_eq_none
    (T X : SmtType) :
    __smtx_typeof_apply (__smtx_typeof (__eo_to_smt_set_empty T)) X = SmtType.None := by
  cases T with
  | None
  | Bool
  | Int
  | Real
  | RegLan
  | BitVec _
  | Seq _
  | Char
  | Datatype _ _
  | TypeRef _
  | USort _
  | Map _ _
  | FunType _ _
  | DtcAppType _ _ =>
      simp [__eo_to_smt_set_empty, __smtx_typeof, __smtx_typeof_apply]
  | Set U =>
      rw [show __smtx_typeof (__eo_to_smt_set_empty (SmtType.Set U)) =
          __smtx_typeof_guard_wf U (SmtType.Set U) by
        simp [__eo_to_smt_set_empty]
        rw [__smtx_typeof.eq_def]]
      cases hInh : native_inhabited_type U <;>
      cases hWf : __smtx_type_wf U <;>
        simp [__smtx_typeof_apply, __smtx_typeof_guard_wf, native_ite, hInh, hWf]

/-- Computes `__smtx_typeof` for `not` terms. -/
private theorem smtx_typeof_not_bool_or_none
    (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.not t) = SmtType.Bool ∨
      __smtx_typeof (theory1 SmtTheoryOp.not t) = SmtType.None := by
  cases hT : __smtx_typeof t <;>
    (rw [typeof_not_eq]; simp [hT, native_ite, native_Teq])

/-- Computes `__smtx_typeof` for `and` terms. -/
private theorem smtx_typeof_and_bool_or_none
    (s t : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.and s t) = SmtType.Bool ∨
      __smtx_typeof (theory2 SmtTheoryOp.and s t) = SmtType.None := by
  cases hs : __smtx_typeof s <;>
    cases ht : __smtx_typeof t <;>
      (rw [typeof_and_eq]; simp [hs, ht, native_ite, native_Teq])

/-- Computes `__smtx_typeof` for `__eo_to_smt_distinct_pairs`. -/
private theorem smtx_typeof_eo_to_smt_distinct_pairs_bool_or_none
    (s : SmtTerm) (xs : Term) :
    __smtx_typeof (__eo_to_smt_distinct_pairs s xs) = SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt_distinct_pairs s xs) = SmtType.None := by
  cases xs
  case Apply f a =>
    cases f
    case _at__at_TypedList_nil =>
      left
      simpa [__eo_to_smt_distinct_pairs] using
        (show __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool by
          rw [__smtx_typeof.eq_def])
    case Apply g b =>
      cases g
      case _at__at_TypedList_cons =>
        simpa [__eo_to_smt_distinct_pairs] using
          smtx_typeof_and_bool_or_none
            (theory1 SmtTheoryOp.not (SmtTerm.eq s (__eo_to_smt b)))
            (__eo_to_smt_distinct_pairs s a)
      all_goals
        right
        simpa [__eo_to_smt_distinct_pairs] using
          smtx_typeof_none
    all_goals
      right
      simpa [__eo_to_smt_distinct_pairs] using
        smtx_typeof_none
  all_goals
    right
    simpa [__eo_to_smt_distinct_pairs] using
      smtx_typeof_none

/-- Computes `__smtx_typeof` for `__eo_to_smt_distinct`. -/
private theorem smtx_typeof_eo_to_smt_distinct_bool_or_none
    (xs : Term) :
    __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.None := by
  cases xs
  case Apply f a =>
    cases f
    case _at__at_TypedList_nil =>
      left
      simpa [__eo_to_smt_distinct] using
        (show __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool by
          rw [__smtx_typeof.eq_def])
    case Apply g b =>
      cases g
      case _at__at_TypedList_cons =>
        simpa [__eo_to_smt_distinct] using
          smtx_typeof_and_bool_or_none
            (__eo_to_smt_distinct_pairs (__eo_to_smt b) a)
            (__eo_to_smt_distinct a)
      all_goals
        right
        simpa [__eo_to_smt_distinct] using
          smtx_typeof_none
    all_goals
      right
      simpa [__eo_to_smt_distinct] using
        smtx_typeof_none
  all_goals
    right
    simpa [__eo_to_smt_distinct] using
      smtx_typeof_none

/-- Computes `__smtx_typeof_apply` for translated `distinct`. -/
private theorem smtx_typeof_apply_eo_to_smt_distinct_eq_none
    (xs : Term) (X : SmtType) :
    __smtx_typeof_apply (__smtx_typeof (__eo_to_smt_distinct xs)) X = SmtType.None := by
  rcases smtx_typeof_eo_to_smt_distinct_bool_or_none xs with hBool | hNone
  · rw [hBool]
    simp [__smtx_typeof_apply]
  · rw [hNone]
    simp [__smtx_typeof_apply]

/-- Computes `__smtx_typeof` for applying translated `distinct`. -/
private theorem smtx_typeof_eo_to_smt_distinct_apply_eq_none
    (xs : Term) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt_distinct xs) x) = SmtType.None := by
  have hGeneric : generic_apply_type (__eo_to_smt_distinct xs) x := by
    cases xs
    case Apply f a =>
      cases f
      case _at__at_TypedList_nil =>
        simpa [__eo_to_smt_distinct] using
          (generic_apply_type_boolean true x)
      case Apply g b =>
        cases g
        case _at__at_TypedList_cons =>
          simpa [__eo_to_smt_distinct] using
            (generic_apply_type_and
              (__eo_to_smt_distinct_pairs (__eo_to_smt b) a)
              (__eo_to_smt_distinct a)
              x)
        all_goals
          simpa [__eo_to_smt_distinct] using
            (generic_apply_type_none x)
      all_goals
        simpa [__eo_to_smt_distinct] using
          (generic_apply_type_none x)
    all_goals
      simpa [__eo_to_smt_distinct] using
        (generic_apply_type_none x)
  rw [hGeneric]
  exact smtx_typeof_apply_eo_to_smt_distinct_eq_none xs (__smtx_typeof x)

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply`. -/
theorem eo_to_smt_typeof_matches_translation_apply
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  cases f <;> intro hNonNone
  case Var name T =>
    have hGeneric :
        __eo_to_smt (Term.Apply (Term.Var name T) x) =
          SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    cases hName : name
    case String s =>
        rw [hName] at hGeneric
        rw [hName] at hNonNone
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x) =
              SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x) := by
          rw [eo_to_smt_var] at hGeneric
          exact hGeneric
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hGenericApply :
              generic_apply_type
                (SmtTerm.Var s (__eo_to_smt_type T))
                (__eo_to_smt x) := by
            exact generic_apply_type_var s (__eo_to_smt_type T) (__eo_to_smt x)
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x)) ≠
                SmtType.None := by
            simpa [hTranslate] using hNonNone
          rw [hGenericApply] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hVarNN : __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠ SmtType.None := by
          intro hVarNone
          apply hApplyNN
          simp [__smtx_typeof_apply, hVarNone]
        have hHeadTy :
            __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) = __eo_to_smt_type T := by
          simpa using smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hVarNN
        have hT :
            __eo_to_smt_type T = SmtType.FunType A B ∨
              __eo_to_smt_type T = SmtType.DtcAppType A B := by
          rw [← hHeadTy]
          exact hHead
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x)) = B := by
          have hGenericApply :
              generic_apply_type
                (SmtTerm.Var s (__eo_to_smt_type T))
                (__eo_to_smt x) := by
            exact generic_apply_type_var s (__eo_to_smt_type T) (__eo_to_smt x)
          rw [hTranslate, hGenericApply]
          cases hHead with
          | inl hHead =>
              rw [hHead, hX]
              simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
          | inr hHead =>
              rw [hHead, hX]
              simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
        exact hSmt.trans (eo_to_smt_type_typeof_apply_var_of_smt_apply x T s A B hT hX).symm
    all_goals
      have hVarNone : __eo_to_smt (Term.Var name T) = SmtTerm.None := by
        rw [hName]
        rw [__eo_to_smt.eq_def]
      apply False.elim
      apply hNonNone
      simpa [hGeneric, hVarNone] using typeof_apply_none_eq (__eo_to_smt x)
  case DtCons s d i =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
          SmtTerm.Apply (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
            SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      simpa [eo_to_smt_term_dt_cons] using hGeneric
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)
            (__eo_to_smt x) := by
        exact generic_apply_type_dt_cons s (__eo_to_smt_datatype d) i (__eo_to_smt x)
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGenericApply] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hHeadEo :
        __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = SmtType.FunType A B ∨
          __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = SmtType.DtcAppType A B := by
      rw [eo_to_smt_type_typeof_dt_cons s d i]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtCons s d i) x)) = B := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)
            (__eo_to_smt x) := by
        exact generic_apply_type_dt_cons s (__eo_to_smt_datatype d) i (__eo_to_smt x)
      rw [hTranslate, hGenericApply]
      cases hHead with
      | inl hHead =>
          rw [hHead, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
      | inr hHead =>
          rw [hHead, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_dt_cons_of_smt_apply x s d i A B hHeadEo hX).symm
  case DtSel s d i j =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
          SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
            SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      simpa [eo_to_smt_term_dt_sel] using hGeneric
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg :
        __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype d) :=
      dt_sel_arg_datatype_of_non_none hApplyNN
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) =
          __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
      rw [hTranslate]
      exact dt_sel_term_typeof_of_non_none hApplyNN
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype x s d i j hArg).symm
  case UConst i T =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.UConst i T) x) =
          SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.UConst i T) x) =
            SmtTerm.Apply (__eo_to_smt (Term.UConst i T)) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      rw [eo_to_smt_uconst] at hGeneric
      exact hGeneric
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x) := by
        exact generic_apply_type_uconst (native_uconst_id i) (__eo_to_smt_type T) (__eo_to_smt x)
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
                (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGenericApply] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hUConstNN :
        __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) ≠ SmtType.None := by
      intro hUConstNone
      apply hApplyNN
      simp [__smtx_typeof_apply, hUConstNone]
    have hHeadTy :
        __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) =
          __eo_to_smt_type T := by
      simpa using
        smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T) hUConstNN
    have hT :
        __eo_to_smt_type T = SmtType.FunType A B ∨
          __eo_to_smt_type T = SmtType.DtcAppType A B := by
      rw [← hHeadTy]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.UConst i T) x)) = B := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T))
            (__eo_to_smt x) := by
        exact generic_apply_type_uconst (native_uconst_id i) (__eo_to_smt_type T) (__eo_to_smt x)
      rw [hTranslate, hGenericApply]
      cases hHead with
      | inl hHead =>
          rw [hHead, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
      | inr hHead =>
          rw [hHead, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_uconst_of_smt_apply x T i A B hT hX).symm
  case Apply f y =>
    cases f
    case eq =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.eq y) x) =
            SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hEqNN :
          __smtx_typeof_eq
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate, typeof_eq_eq] using hNonNone
      have hArgs := smtx_typeof_eq_non_none hEqNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.eq y) x)) =
            SmtType.Bool := by
        rw [hTranslate, typeof_eq_eq]
        rw [hArgs.1]
        cases hT : __smtx_typeof (__eo_to_smt x) <;>
          simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
            hT] at hArgs ⊢
      have hXNotNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [← hArgs.1]
        exact hArgs.2
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_eq_of_smt_same_non_none
          x y
          (__smtx_typeof (__eo_to_smt x))
          hArgs.1
          rfl
          hXNotNone).symm
    case distinct =>
      exfalso
      apply hNonNone
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.distinct y) x) =
            SmtTerm.Apply (__eo_to_smt (Term.Apply Term.distinct y)) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.distinct y) = __eo_to_smt_distinct y := by
        rw [__eo_to_smt.eq_def]
      rw [hTranslate, hHeadTranslate]
      exact smtx_typeof_eo_to_smt_distinct_apply_eq_none y (__eo_to_smt x)
    case not =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.not y) =
            theory1 SmtTheoryOp.not (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.not y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_not (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.not y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case to_real =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.to_real y) =
            theory1 SmtTheoryOp.to_real (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.to_real y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_to_real (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.to_real y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case to_int =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.to_int y) =
            theory1 SmtTheoryOp.to_int (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.to_int y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_to_int (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.to_int y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case is_int =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.is_int y) =
            theory1 SmtTheoryOp.is_int (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.is_int y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_is_int (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.is_int y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case abs =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.abs y) =
            theory1 SmtTheoryOp.abs (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.abs y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_abs (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.abs y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case str_to_re =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.str_to_re y) =
            theory1 SmtTheoryOp.str_to_re (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.str_to_re y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_str_to_re (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.str_to_re y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case re_mult =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.re_mult y) =
            theory1 SmtTheoryOp.re_mult (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.re_mult y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_re_mult (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.re_mult y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case re_plus =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.re_plus y) =
            theory1 SmtTheoryOp.re_plus (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.re_plus y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_re_plus (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.re_plus y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case re_opt =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.re_opt y) =
            theory1 SmtTheoryOp.re_opt (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.re_opt y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_re_opt (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.re_opt y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case re_comp =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.re_comp y) =
            theory1 SmtTheoryOp.re_comp (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.re_comp y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_re_comp (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.re_comp y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case set_singleton =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.set_singleton y) =
            theory1 SmtTheoryOp.set_singleton (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.set_singleton y)) (__eo_to_smt x) := by
        simpa [hHeadTranslate] using
          (generic_apply_type_set_singleton (__eo_to_smt y) (__eo_to_smt x))
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.set_singleton y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case set_is_empty =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.set_is_empty y) =
            let _v0 := __eo_to_smt y
            SmtTerm.eq _v0 (SmtTerm.set_empty (__smtx_typeof _v0)) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.set_is_empty y)) (__eo_to_smt x) := by
        rw [generic_apply_type, hHeadTranslate, __smtx_typeof.eq_def]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.set_is_empty y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case set_is_singleton =>
      let T := __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose y))
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.set_is_singleton y) =
            SmtTerm.exists "_at_x" T
              (SmtTerm.eq (__eo_to_smt y)
                (theory1 SmtTheoryOp.set_singleton (SmtTerm.Var "_at_x" T))) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.set_is_singleton y)) (__eo_to_smt x) := by
        rw [generic_apply_type, hHeadTranslate, __smtx_typeof.eq_def]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.set_is_singleton y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case str_contains =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_contains y) x) =
            theory2 SmtTheoryOp.str_contains (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.str_contains (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :
          ∃ T : SmtType,
            __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
              __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        exact seq_binop_args_of_non_none_ret (op := theory2 SmtTheoryOp.str_contains)
          (typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      rcases hArgs with ⟨T, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_contains y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [__smtx_typeof_seq_op_2_ret, hY, hX, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_contains_of_smt_seq x y T hY hX).symm
    case str_prefixof =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_prefixof y) x) =
            theory2 SmtTheoryOp.str_prefixof (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.str_prefixof (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :=
        seq_char_binop_args_of_non_none (op := theory2 SmtTheoryOp.str_prefixof)
          (typeof_str_prefixof_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_prefixof y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_str_prefixof_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_prefixof_of_smt_seq
          x y SmtType.Char hArgs.1 hArgs.2).symm
    case str_suffixof =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_suffixof y) x) =
            theory2 SmtTheoryOp.str_suffixof (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.str_suffixof (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :=
        seq_char_binop_args_of_non_none (op := theory2 SmtTheoryOp.str_suffixof)
          (typeof_str_suffixof_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_suffixof y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_str_suffixof_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_suffixof_of_smt_seq
          x y SmtType.Char hArgs.1 hArgs.2).symm
    case str_lt =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_lt y) x) =
            theory2 SmtTheoryOp.str_lt (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.str_lt (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := seq_char_binop_args_of_non_none (op := theory2 SmtTheoryOp.str_lt)
        (typeof_str_lt_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_lt y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_str_lt_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_lt_of_smt_seq_char x y hArgs.1 hArgs.2).symm
    case str_leq =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_leq y) x) =
            theory2 SmtTheoryOp.str_leq (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.str_leq (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := seq_char_binop_args_of_non_none (op := theory2 SmtTheoryOp.str_leq)
        (typeof_str_leq_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_leq y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_str_leq_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_leq_of_smt_seq_char x y hArgs.1 hArgs.2).symm
    case str_concat =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_concat y) x) =
            theory2 SmtTheoryOp.str_concat (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.str_concat (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases seq_binop_args_of_non_none (op := theory2 SmtTheoryOp.str_concat)
          (typeof_str_concat_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with
        ⟨T, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_concat y) x)) =
            SmtType.Seq T := by
        rw [hTranslate]
        rw [typeof_str_concat_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, hY, hX]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_concat_of_smt_seq x y T hY hX).symm
    case re_range =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_range y) x) =
            theory2 SmtTheoryOp.re_range (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.re_range (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := seq_char_binop_args_of_non_none (op := theory2 SmtTheoryOp.re_range)
        (typeof_re_range_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_range y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        rw [typeof_re_range_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_range_of_smt_seq_char x y hArgs.1 hArgs.2).symm
    case re_concat =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_concat y) x) =
            theory2 SmtTheoryOp.re_concat (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.re_concat (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := reglan_binop_args_of_non_none (op := theory2 SmtTheoryOp.re_concat)
        (typeof_re_concat_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_concat y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        rw [typeof_re_concat_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_concat_of_smt_reglan x y hArgs.1 hArgs.2).symm
    case re_inter =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_inter y) x) =
            theory2 SmtTheoryOp.re_inter (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.re_inter (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := reglan_binop_args_of_non_none (op := theory2 SmtTheoryOp.re_inter)
        (typeof_re_inter_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_inter y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        rw [typeof_re_inter_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_inter_of_smt_reglan x y hArgs.1 hArgs.2).symm
    case re_union =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_union y) x) =
            theory2 SmtTheoryOp.re_union (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.re_union (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := reglan_binop_args_of_non_none (op := theory2 SmtTheoryOp.re_union)
        (typeof_re_union_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_union y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        rw [typeof_re_union_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_union_of_smt_reglan x y hArgs.1 hArgs.2).symm
    case re_diff =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_diff y) x) =
            theory2 SmtTheoryOp.re_diff (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.re_diff (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := reglan_binop_args_of_non_none (op := theory2 SmtTheoryOp.re_diff)
        (typeof_re_diff_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_diff y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        rw [typeof_re_diff_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_diff_of_smt_reglan x y hArgs.1 hArgs.2).symm
    case str_in_re =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_in_re y) x) =
            theory2 SmtTheoryOp.str_in_re (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.str_in_re (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := seq_char_reglan_args_of_non_none (op := theory2 SmtTheoryOp.str_in_re)
        (typeof_str_in_re_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_in_re y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_str_in_re_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_in_re_of_smt_seq_char_reglan
          x y hArgs.1 hArgs.2).symm
    case seq_nth =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.seq_nth y) x) =
            theory2 SmtTheoryOp.seq_nth (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.seq_nth (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases seq_nth_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at hApplyNN
        rw [typeof_seq_nth_eq (__eo_to_smt y) (__eo_to_smt x)] at hApplyNN
        simpa [__smtx_typeof_seq_nth, hY, hX] using hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.seq_nth y) x)) = T := by
        rw [hTranslate]
        have hTy' : __smtx_typeof_guard_wf T T = T :=
          smtx_typeof_guard_wf_of_non_none T T hGuardNN
        rw [typeof_seq_nth_eq (__eo_to_smt y) (__eo_to_smt x)]
        simpa [__smtx_typeof_seq_nth, hY, hX] using hTy'
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_seq_nth_of_smt_seq_int x y T hY hX).symm
    case or =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.or y) x) =
            theory2 SmtTheoryOp.or (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.or (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.or)
        (typeof_or_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_or_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_apply_or_of_smt_bool x y hArgs.1 hArgs.2).symm
    case and =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.and y) x) =
            theory2 SmtTheoryOp.and (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.and (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.and)
        (typeof_and_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_and_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_and_of_smt_bool x y hArgs.1 hArgs.2).symm
    case imp =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.imp y) x) =
            theory2 SmtTheoryOp.imp (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.imp (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.imp)
        (typeof_imp_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_imp_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_imp_of_smt_bool x y hArgs.1 hArgs.2).symm
    case xor =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.xor y) x) =
            theory2 SmtTheoryOp.xor (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.xor (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.xor)
        (typeof_xor_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.xor y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_xor_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_xor_of_smt_bool x y hArgs.1 hArgs.2).symm
    case plus =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.plus y) x) =
            theory2 SmtTheoryOp.plus (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.plus (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_args_of_non_none (op := theory2 SmtTheoryOp.plus)
          (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.plus y) x)) =
              SmtType.Int := by
          rw [hTranslate]
          rw [typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_plus_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.plus y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          rw [typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_plus_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case neg =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.neg y) x) =
            theory2 SmtTheoryOp.neg (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.neg (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_args_of_non_none (op := theory2 SmtTheoryOp.neg)
          (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.neg y) x)) =
              SmtType.Int := by
          rw [hTranslate]
          rw [typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_neg_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.neg y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          rw [typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_neg_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case mult =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.mult y) x) =
            theory2 SmtTheoryOp.mult (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.mult (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_args_of_non_none (op := theory2 SmtTheoryOp.mult)
          (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.mult y) x)) =
              SmtType.Int := by
          rw [hTranslate]
          rw [typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_mult_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.mult y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          rw [typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_mult_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case lt =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.lt y) x) =
            theory2 SmtTheoryOp.lt (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.lt (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.lt)
          (typeof_lt_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.lt y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          rw [typeof_lt_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_lt_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.lt y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          rw [typeof_lt_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_lt_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case leq =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.leq y) x) =
            theory2 SmtTheoryOp.leq (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.leq (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.leq)
          (typeof_leq_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.leq y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          rw [typeof_leq_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_leq_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.leq y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          rw [typeof_leq_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_leq_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case gt =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.gt y) x) =
            theory2 SmtTheoryOp.gt (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.gt (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.gt)
          (typeof_gt_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.gt y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          rw [typeof_gt_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_gt_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.gt y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          rw [typeof_gt_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_gt_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case geq =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.geq y) x) =
            theory2 SmtTheoryOp.geq (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.geq (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.geq)
          (typeof_geq_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.geq y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          rw [typeof_geq_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_geq_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.geq y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          rw [typeof_geq_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_geq_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case div =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.div y) x) =
            theory2 SmtTheoryOp.div (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.div (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.div)
        (typeof_div_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.div y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        rw [typeof_div_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_div_of_smt_int x y hArgs.1 hArgs.2).symm
    case mod =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.mod y) x) =
            theory2 SmtTheoryOp.mod (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.mod (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.mod)
        (typeof_mod_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.mod y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        rw [typeof_mod_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_mod_of_smt_int x y hArgs.1 hArgs.2).symm
    case multmult =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.multmult y) x) =
            theory2 SmtTheoryOp.multmult (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.multmult (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.multmult)
        (typeof_multmult_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.multmult y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        rw [typeof_multmult_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_multmult_of_smt_int x y hArgs.1 hArgs.2).symm
    case divisible =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.divisible y) x) =
            theory2 SmtTheoryOp.divisible (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.divisible (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.divisible)
        (typeof_divisible_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.divisible y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        rw [typeof_divisible_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_divisible_of_smt_int x y hArgs.1 hArgs.2).symm
    case div_total =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.div_total y) x) =
            theory2 SmtTheoryOp.div_total (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.div_total (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.div_total)
        (typeof_div_total_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.div_total y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        rw [typeof_div_total_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_div_total_of_smt_int x y hArgs.1 hArgs.2).symm
    case mod_total =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.mod_total y) x) =
            theory2 SmtTheoryOp.mod_total (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.mod_total (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.mod_total)
        (typeof_mod_total_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.mod_total y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        rw [typeof_mod_total_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_mod_total_of_smt_int x y hArgs.1 hArgs.2).symm
    case multmult_total =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.multmult_total y) x) =
            theory2 SmtTheoryOp.multmult_total (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.multmult_total (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.multmult_total)
        (typeof_multmult_total_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.multmult_total y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        rw [typeof_multmult_total_eq (__eo_to_smt y) (__eo_to_smt x)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_multmult_total_of_smt_int x y hArgs.1 hArgs.2).symm
    case qdiv =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.qdiv y) x) =
            theory2 SmtTheoryOp.qdiv (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.qdiv (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_args_of_non_none (op := theory2 SmtTheoryOp.qdiv) (R := SmtType.Real)
          (typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with
        hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          rw [typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_qdiv_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          rw [typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_qdiv_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case qdiv_total =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total y) x) =
            theory2 SmtTheoryOp.qdiv_total (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.qdiv_total (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_args_of_non_none
          (op := theory2 SmtTheoryOp.qdiv_total) (R := SmtType.Real)
          (typeof_qdiv_total_eq (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          rw [typeof_qdiv_total_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_qdiv_total_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          rw [typeof_qdiv_total_eq (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_qdiv_total_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case select =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.select y) x) =
            theory2 SmtTheoryOp.select (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.select (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases select_args_of_non_none hApplyNN with ⟨A, B, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.select y) x)) = B := by
        rw [hTranslate, typeof_select_eq (__eo_to_smt y) (__eo_to_smt x), hY, hX]
        simp [__smtx_typeof_select, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_select_of_smt_map x y A B hY hX).symm
    case concat =>
      exact eo_to_smt_typeof_matches_translation_apply_concat x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (fun w1 w2 hy hx =>
          eo_to_smt_type_typeof_apply_apply_concat_of_smt_bitvec x y w1 w2 hy hx)
        hNonNone
    case bvand =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvand (theory2 SmtTheoryOp.bvand) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvand) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvand_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvor =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvor (theory2 SmtTheoryOp.bvor) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvor) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvor_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvnand =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvnand (theory2 SmtTheoryOp.bvnand) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnand) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvnand_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvnor =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvnor (theory2 SmtTheoryOp.bvnor) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvnor) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvnor_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvxor =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvxor (theory2 SmtTheoryOp.bvxor) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvxor) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvxor_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvxnor =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvxnor (theory2 SmtTheoryOp.bvxnor) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvxnor) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvxnor_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvcomp =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvcomp (theory2 SmtTheoryOp.bvcomp) (SmtType.BitVec 1) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (typeof_bvcomp_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvcomp_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvadd =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvadd (theory2 SmtTheoryOp.bvadd) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvadd) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvadd_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvmul =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvmul (theory2 SmtTheoryOp.bvmul) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvmul) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvmul_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvudiv =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvudiv (theory2 SmtTheoryOp.bvudiv) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvudiv) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvudiv_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvurem =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvurem (theory2 SmtTheoryOp.bvurem) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvurem) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvurem_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsub =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvsub (theory2 SmtTheoryOp.bvsub) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsub) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsub_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsdiv =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvsdiv (theory2 SmtTheoryOp.bvsdiv) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsdiv) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsdiv_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsrem =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvsrem (theory2 SmtTheoryOp.bvsrem) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsrem) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsrem_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsmod =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvsmod (theory2 SmtTheoryOp.bvsmod) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsmod) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsmod_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvult =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvult (theory2 SmtTheoryOp.bvult) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvult) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvult_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvule =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvule (theory2 SmtTheoryOp.bvule) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvule) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvule_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvugt =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvugt (theory2 SmtTheoryOp.bvugt) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvugt) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvugt_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvuge =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvuge (theory2 SmtTheoryOp.bvuge) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvuge) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvuge_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvslt =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvslt (theory2 SmtTheoryOp.bvslt) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvslt) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvslt_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsle =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsle (theory2 SmtTheoryOp.bvsle) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsle) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsle_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsgt =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsgt (theory2 SmtTheoryOp.bvsgt) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsgt) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsgt_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsge =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsge (theory2 SmtTheoryOp.bvsge) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsge) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsge_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvshl =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvshl (theory2 SmtTheoryOp.bvshl) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvshl) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvshl_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvlshr =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvlshr (theory2 SmtTheoryOp.bvlshr) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvlshr) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvlshr_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvashr =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvashr (theory2 SmtTheoryOp.bvashr) x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvashr) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvashr_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvuaddo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvuaddo (theory2 SmtTheoryOp.bvuaddo) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvuaddo) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvuaddo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsaddo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsaddo (theory2 SmtTheoryOp.bvsaddo) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsaddo) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsaddo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvumulo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvumulo (theory2 SmtTheoryOp.bvumulo) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvumulo) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvumulo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsmulo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsmulo (theory2 SmtTheoryOp.bvsmulo) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsmulo) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsmulo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvusubo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvusubo (theory2 SmtTheoryOp.bvusubo) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvusubo) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvusubo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvssubo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvssubo (theory2 SmtTheoryOp.bvssubo) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvssubo) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvssubo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsdivo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsdivo (theory2 SmtTheoryOp.bvsdivo) SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def]; rfl)
        (by
          change __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.bvsdivo) (__eo_to_smt y))
                (__eo_to_smt x)) = _
          rw [__smtx_typeof.eq_def])
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsdivo_of_smt_bitvec x y w hy hx)
        hNonNone
    case «repeat» =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.repeat y) x) =
            theory2 SmtTheoryOp.repeat (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.repeat (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases repeat_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.repeat y) x)) =
            SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w))) := by
        rw [hTranslate, typeof_repeat_eq, hy, hx]
        simp [__smtx_typeof_repeat, native_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_repeat_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case zero_extend =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.zero_extend y) x) =
            theory2 SmtTheoryOp.zero_extend (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.zero_extend (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases zero_extend_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.zero_extend y) x)) =
            SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
        rw [hTranslate, typeof_zero_extend_eq, hy, hx]
        simp [__smtx_typeof_zero_extend, native_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_zero_extend_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case sign_extend =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.sign_extend y) x) =
            theory2 SmtTheoryOp.sign_extend (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.sign_extend (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases sign_extend_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.sign_extend y) x)) =
            SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
        rw [hTranslate, typeof_sign_extend_eq, hy, hx]
        simp [__smtx_typeof_sign_extend, native_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_sign_extend_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case rotate_left =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.rotate_left y) x) =
            theory2 SmtTheoryOp.rotate_left (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.rotate_left (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases rotate_left_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.rotate_left y) x)) =
            SmtType.BitVec w := by
        rw [hTranslate, typeof_rotate_left_eq, hy, hx]
        simp [__smtx_typeof_rotate_left, native_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_rotate_left_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case rotate_right =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.rotate_right y) x) =
            theory2 SmtTheoryOp.rotate_right (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.rotate_right (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases rotate_right_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.rotate_right y) x)) =
            SmtType.BitVec w := by
        rw [hTranslate, typeof_rotate_right_eq, hy, hx]
        simp [__smtx_typeof_rotate_right, native_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_rotate_right_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case int_to_bv =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv y) x) =
            theory2 SmtTheoryOp.int_to_bv (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.int_to_bv (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases int_to_bv_args_of_non_none hApplyNN with ⟨i, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv y) x)) =
            SmtType.BitVec (native_int_to_nat i) := by
        rw [hTranslate, typeof_int_to_bv_eq, hy, hx]
        simp [__smtx_typeof_int_to_bv, native_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_int_to_bv_of_smt_numeral_int
          x y i hy hx hi).symm
    case str_at =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_at y) x) =
            theory2 SmtTheoryOp.str_at (__eo_to_smt y) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN :
          term_has_non_none_type
            (theory2 SmtTheoryOp.str_at (__eo_to_smt y) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases str_at_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_at y) x)) =
            SmtType.Seq T := by
        rw [hTranslate, typeof_str_at_eq (__eo_to_smt y) (__eo_to_smt x), hY, hX]
        simp [__smtx_typeof_str_at, native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_at_of_smt_seq_int x y T hY hX).symm
    case _at_strings_stoi_result =>
      let subTerm :=
        theory3 SmtTheoryOp.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0) (__eo_to_smt x)
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term._at_strings_stoi_result y) x) =
            theory1 SmtTheoryOp.str_to_int subTerm := by
        rw [__eo_to_smt.eq_def]
        rfl
      have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_to_int subTerm) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hSubTy : __smtx_typeof subTerm = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := theory1 SmtTheoryOp.str_to_int) (typeof_str_to_int_eq subTerm) hApplyNN
      have hSubNN : term_has_non_none_type subTerm := by
        unfold term_has_non_none_type
        rw [hSubTy]
        simp
      rcases str_substr_args_of_non_none hSubNN with ⟨T, hY, hZero, hX⟩
      have hSubTy' : __smtx_typeof subTerm = SmtType.Seq T := by
        rw [show subTerm = theory3 SmtTheoryOp.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0) (__eo_to_smt x)
          by rfl]
        rw [typeof_str_substr_eq (__eo_to_smt y) (SmtTerm.Numeral 0) (__eo_to_smt x), hY, hZero, hX]
        simp [__smtx_typeof_str_substr, native_ite, native_Teq]
      have hTChar : T = SmtType.Char := by
        have hEq : SmtType.Seq SmtType.Char = SmtType.Seq T := hSubTy.symm.trans hSubTy'
        injection hEq with hT
        exact hT.symm
      have hYChar : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char := by
        simpa [hTChar] using hY
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term._at_strings_stoi_result y) x)) =
            SmtType.Int := by
        rw [hTranslate, typeof_str_to_int_eq subTerm, hSubTy]
        simp [native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_at_strings_stoi_result_of_smt_seq_char_int x y
          hYChar hX).symm
    case Apply f z =>
      cases f
      case ite =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.ite z) y) x) =
              SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases ite_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX, hT⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.ite z) y) x)) =
              T := by
          rw [hTranslate, typeof_ite_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          rw [hZ, hY, hX]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_ite_of_smt_bool_same_non_none
            x y z T hZ hY hX hT).symm
      case bvite =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.bvite z) y) x) =
              SmtTerm.ite
                (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
                (__eo_to_smt y)
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.ite
                (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
                (__eo_to_smt y)
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases ite_args_of_non_none hApplyNN with ⟨T, hCond, hY, hX, hT⟩
        have hCondNN :
            __smtx_typeof
              (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1)) ≠
              SmtType.None := by
          rw [hCond]
          simp
        have hEqNN :
            __smtx_typeof_eq (__smtx_typeof (__eo_to_smt z)) (SmtType.BitVec 1) ≠
              SmtType.None := by
          rw [typeof_eq_eq, typeof_binary_one_eq] at hCondNN
          exact hCondNN
        have hZ : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec 1 := (smtx_typeof_eq_non_none hEqNN).1
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.bvite z) y) x)) =
              T := by
          rw [hTranslate]
          rw [typeof_ite_eq]
          rw [hCond, hY, hX]
          simp [__smtx_typeof_ite, native_ite, native_Teq, hT]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_bvite_of_smt_bitvec1_same_non_none
            x y z T hZ hY hX hT).symm
      case extract =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.extract z) y) x) =
              theory3 SmtTheoryOp.extract (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.extract (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases extract_args_of_non_none hApplyNN with ⟨i, j, w, hZ, hY, hX, hj0, hji, hiw⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.extract z) y) x)) =
              SmtType.BitVec
                (native_int_to_nat (native_zplus (native_zplus i (native_zneg j)) 1)) := by
          rw [hTranslate, typeof_extract_eq, hZ, hY, hX]
          simp [__smtx_typeof_extract, native_ite, hj0, hji, hiw]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_extract_of_smt_numeral_numeral_bitvec
            x y z i j w hZ hY hX hj0 hji hiw).symm
      case str_substr =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_substr z) y) x) =
              theory3 SmtTheoryOp.str_substr (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.str_substr (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases str_substr_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_substr z) y) x)) =
              SmtType.Seq T := by
          rw [hTranslate, typeof_str_substr_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_str_substr, native_ite, native_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_smt_seq_int_int
            x y z T hZ hY hX).symm
      case str_indexof =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof z) y) x) =
              theory3 SmtTheoryOp.str_indexof (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.str_indexof (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases str_indexof_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof z) y) x)) =
              SmtType.Int := by
          rw [hTranslate, typeof_str_indexof_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_str_indexof, native_ite, native_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_indexof_of_smt_seq_seq_int
            x y z T hZ hY hX).symm
      case str_update =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_update z) y) x) =
              theory3 SmtTheoryOp.str_update (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.str_update (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases str_update_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_update z) y) x)) =
              SmtType.Seq T := by
          rw [hTranslate, typeof_str_update_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_str_update, native_ite, native_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_update_of_smt_seq_int_seq
            x y z T hZ hY hX).symm
      case str_replace =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace z) y) x) =
              theory3 SmtTheoryOp.str_replace (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.str_replace (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases seq_triop_args_of_non_none (op := theory3 SmtTheoryOp.str_replace)
            (typeof_str_replace_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with
          ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace z) y) x)) =
              SmtType.Seq T := by
          rw [hTranslate, typeof_str_replace_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_seq_op_3, native_ite, native_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_smt_seq
            x y z T hZ hY hX).symm
      case str_replace_all =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all z) y) x) =
              theory3 SmtTheoryOp.str_replace_all (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.str_replace_all (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases seq_triop_args_of_non_none (op := theory3 SmtTheoryOp.str_replace_all)
            (typeof_str_replace_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) hApplyNN with
          ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all z) y) x)) =
              SmtType.Seq T := by
          rw [hTranslate, typeof_str_replace_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_seq_op_3, native_ite, native_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_smt_seq
            x y z T hZ hY hX).symm
      case str_replace_re =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re z) y) x) =
              theory3 SmtTheoryOp.str_replace_re (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.str_replace_re (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        have hArgs := str_replace_re_args_of_non_none (op := theory3 SmtTheoryOp.str_replace_re)
          (typeof_str_replace_re_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re z) y) x)) =
              SmtType.Seq SmtType.Char := by
          rw [hTranslate, typeof_str_replace_re_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_smt_seq_char_reglan
            x y z hArgs.1 hArgs.2.1 hArgs.2.2).symm
      case str_replace_re_all =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all z) y) x) =
              theory3 SmtTheoryOp.str_replace_re_all (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.str_replace_re_all (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        have hArgs :=
          str_replace_re_args_of_non_none (op := theory3 SmtTheoryOp.str_replace_re_all)
            (typeof_str_replace_re_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) hApplyNN
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all z) y) x)) =
              SmtType.Seq SmtType.Char := by
          rw [hTranslate, typeof_str_replace_re_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_smt_seq_char_reglan
            x y z hArgs.1 hArgs.2.1 hArgs.2.2).symm
      case str_indexof_re =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re z) y) x) =
              theory3 SmtTheoryOp.str_indexof_re (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.str_indexof_re (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        have hArgs := str_indexof_re_args_of_non_none hApplyNN
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re z) y) x)) =
              SmtType.Int := by
          rw [hTranslate, typeof_str_indexof_re_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_smt_seq_char_reglan
            x y z hArgs.1 hArgs.2.1 hArgs.2.2).symm
      case store =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store z) y) x) =
              theory3 SmtTheoryOp.store (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.store (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases store_args_of_non_none hApplyNN with ⟨A, B, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store z) y) x)) =
              SmtType.Map A B := by
          rw [hTranslate, typeof_store_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
          simp [__smtx_typeof_store, native_ite, native_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_store_of_smt_map x y z A B hZ hY hX).symm
      case re_loop =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.re_loop z) y) x) =
              theory3 SmtTheoryOp.re_loop (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hApplyNN :
            term_has_non_none_type
              (theory3 SmtTheoryOp.re_loop (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        cases hz : __eo_to_smt z with
        | Numeral n1 =>
            cases hy : __eo_to_smt y with
            | Numeral n2 =>
                have hLoopNN :
                    term_has_non_none_type
                      (theory3 SmtTheoryOp.re_loop
                        (SmtTerm.Numeral n1)
                        (SmtTerm.Numeral n2)
                        (__eo_to_smt x)) := by
                  simpa [hz, hy] using hApplyNN
                rcases re_loop_arg_of_non_none hLoopNN with ⟨hn1, hn2, hX⟩
                have hSmt :
                    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.re_loop z) y) x)) =
                      SmtType.RegLan := by
                  rw [hTranslate, hz, hy]
                  rw [typeof_re_loop_eq (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) (__eo_to_smt x)]
                  simp [__smtx_typeof_re_loop, hX, hn1, hn2, native_ite]
                exact hSmt.trans
                  (eo_to_smt_type_typeof_apply_apply_apply_re_loop_of_smt_numeral_numeral_reglan
                    x y z n1 n2 hz hy hX hn1 hn2).symm
            | _ =>
                exfalso
                unfold term_has_non_none_type at hApplyNN
                rw [hz, hy, typeof_re_loop_eq] at hApplyNN
                simp [__smtx_typeof_re_loop, native_ite] at hApplyNN
        | _ =>
            exfalso
            unfold term_has_non_none_type at hApplyNN
            rw [hz, typeof_re_loop_eq] at hApplyNN
            simp [__smtx_typeof_re_loop, native_ite] at hApplyNN
      case re_exp =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.re_exp z) y) =
              theory2 SmtTheoryOp.re_exp (__eo_to_smt z) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.re_exp z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate] using
            (generic_apply_type_re_exp (__eo_to_smt z) (__eo_to_smt y)
              (__eo_to_smt x))
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.re_exp z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case _at_strings_deq_diff =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term._at_strings_deq_diff z) y) =
              let _v0 := SmtTerm.Numeral 1
              let _v2 := SmtTerm.Var "_at_x" SmtType.Int
              SmtTerm.choice_nth "_at_x" SmtType.Int
                (theory1 SmtTheoryOp.not
                  (SmtTerm.eq
                    (theory3 SmtTheoryOp.str_substr (__eo_to_smt z) _v2 _v0)
                    (theory3 SmtTheoryOp.str_substr (__eo_to_smt y) _v2 _v0))) 0 := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term._at_strings_deq_diff z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate, generic_apply_type, theory1, theory2, theory3, theory0,
            __smtx_typeof.eq_def]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term._at_strings_deq_diff z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case _at_strings_itos_result =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term._at_strings_itos_result z) y) =
              theory1 SmtTheoryOp.str_from_int
                (theory2 SmtTheoryOp.mod (__eo_to_smt z)
                  (theory2 SmtTheoryOp.multmult (SmtTerm.Numeral 10) (__eo_to_smt y))) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hGeneric :
            generic_apply_type
              (__eo_to_smt (Term.Apply (Term.Apply Term._at_strings_itos_result z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate, generic_apply_type, theory1, theory2, theory0,
            __smtx_typeof.eq_def]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term._at_strings_itos_result z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case _at_strings_num_occur =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term._at_strings_num_occur z) y) =
              let _v0 := __eo_to_smt y
              let _v1 := __eo_to_smt z
              theory2 SmtTheoryOp.div
                (theory2 SmtTheoryOp.neg
                  (theory1 SmtTheoryOp.str_len _v1)
                  (theory1 SmtTheoryOp.str_len
                    (theory3 SmtTheoryOp.str_replace_all
                      _v1
                      _v0
                      (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
                (theory1 SmtTheoryOp.str_len _v0) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type
              (__eo_to_smt (Term.Apply (Term.Apply Term._at_strings_num_occur z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate, generic_apply_type, theory1, theory2, theory3, theory0,
            __smtx_typeof.eq_def]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term._at_strings_num_occur z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case bvultbv =>
        let head :=
          SmtTerm.ite
            (theory2 SmtTheoryOp.bvult (__eo_to_smt z) (__eo_to_smt y))
            (SmtTerm.Binary 1 1)
            (SmtTerm.Binary 1 0)
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.bvultbv z) y) = head := by
          rw [__eo_to_smt.eq_def]
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.bvultbv z) y) x) =
              SmtTerm.Apply head (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          simp [hHeadTranslate]
        have hApplyNN :
            __smtx_typeof_apply (__smtx_typeof head) (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hHeadGeneric : generic_apply_type head (__eo_to_smt x) := by
            unfold head
            rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]
          have hApplyNN' :
              __smtx_typeof (SmtTerm.Apply head (__eo_to_smt x)) ≠ SmtType.None := by
            simpa [hTranslate] using hNonNone
          rw [hHeadGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN : __smtx_typeof head ≠ SmtType.None := by
          cases hHead with
          | inl hHead =>
              rw [hHead]
              simp
          | inr hHead =>
              rw [hHead]
              simp
        have hIteNN : term_has_non_none_type head := by
          unfold term_has_non_none_type
          exact hHeadNN
        rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
        have hThenNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
          rw [hThen]
          exact hT
        have hElseNN : __smtx_typeof (SmtTerm.Binary 1 0) ≠ SmtType.None := by
          rw [hElse]
          exact hT
        have hBitVec1 : T = SmtType.BitVec 1 := by
          exact hThen.symm.trans (smtx_typeof_binary_of_non_none 1 1 hThenNN)
        have hBranchEq :
            __smtx_typeof (SmtTerm.Binary 1 1) = __smtx_typeof (SmtTerm.Binary 1 0) := by
          exact hThen.trans hElse.symm
        have hTeq :
            native_Teq (__smtx_typeof (SmtTerm.Binary 1 1))
              (__smtx_typeof (SmtTerm.Binary 1 0)) = true := by
          simpa [native_Teq] using hBranchEq
        have hHeadTy : __smtx_typeof head = T := by
          unfold head
          rw [typeof_ite_eq]
          rw [hCond, hThen, hElse]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        cases hHead with
        | inl hHead =>
            cases (hBitVec1.symm.trans (hHeadTy.symm.trans hHead))
        | inr hHead =>
            cases (hBitVec1.symm.trans (hHeadTy.symm.trans hHead))
      case bvsltbv =>
        let head :=
          SmtTerm.ite
            (theory2 SmtTheoryOp.bvslt (__eo_to_smt z) (__eo_to_smt y))
            (SmtTerm.Binary 1 1)
            (SmtTerm.Binary 1 0)
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.bvsltbv z) y) = head := by
          rw [__eo_to_smt.eq_def]
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.bvsltbv z) y) x) =
              SmtTerm.Apply head (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          simp [hHeadTranslate]
        have hApplyNN :
            __smtx_typeof_apply (__smtx_typeof head) (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hHeadGeneric : generic_apply_type head (__eo_to_smt x) := by
            unfold head
            rw [generic_apply_type, theory2, theory1, theory0, __smtx_typeof.eq_def]
          have hApplyNN' :
              __smtx_typeof (SmtTerm.Apply head (__eo_to_smt x)) ≠ SmtType.None := by
            simpa [hTranslate] using hNonNone
          rw [hHeadGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN : __smtx_typeof head ≠ SmtType.None := by
          cases hHead with
          | inl hHead =>
              rw [hHead]
              simp
          | inr hHead =>
              rw [hHead]
              simp
        have hIteNN : term_has_non_none_type head := by
          unfold term_has_non_none_type
          exact hHeadNN
        rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
        have hThenNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
          rw [hThen]
          exact hT
        have hElseNN : __smtx_typeof (SmtTerm.Binary 1 0) ≠ SmtType.None := by
          rw [hElse]
          exact hT
        have hBitVec1 : T = SmtType.BitVec 1 := by
          exact hThen.symm.trans (smtx_typeof_binary_of_non_none 1 1 hThenNN)
        have hBranchEq :
            __smtx_typeof (SmtTerm.Binary 1 1) = __smtx_typeof (SmtTerm.Binary 1 0) := by
          exact hThen.trans hElse.symm
        have hTeq :
            native_Teq (__smtx_typeof (SmtTerm.Binary 1 1))
              (__smtx_typeof (SmtTerm.Binary 1 0)) = true := by
          simpa [native_Teq] using hBranchEq
        have hHeadTy : __smtx_typeof head = T := by
          unfold head
          rw [typeof_ite_eq]
          rw [hCond, hThen, hElse]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        cases hHead with
        | inl hHead =>
            cases (hBitVec1.symm.trans (hHeadTy.symm.trans hHead))
        | inr hHead =>
            cases (hBitVec1.symm.trans (hHeadTy.symm.trans hHead))
      case _at_re_unfold_pos_component =>
        sorry
      case _at_witness_string_length =>
        sorry
      case update =>
        cases hz : __eo_to_smt z with
        | DtSel s d n m =>
            have hTranslate :
                __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.update z) y) x) =
                  __eo_to_smt_updater (SmtTerm.DtSel s d n m) (__eo_to_smt y) (__eo_to_smt x) := by
              rw [__eo_to_smt.eq_def]
              simp [hz]
            have hUpdaterNN :
                __smtx_typeof
                    (__eo_to_smt_updater (SmtTerm.DtSel s d n m) (__eo_to_smt y) (__eo_to_smt x)) ≠
                  SmtType.None := by
              rw [← hTranslate]
              exact hNonNone
            have hIteNN :
                term_has_non_none_type
                  (SmtTerm.ite
                    (SmtTerm.Apply (SmtTerm.DtTester s d n) (__eo_to_smt y))
                    (__eo_to_smt_updater_rec
                      (SmtTerm.DtSel s d n m) (__smtx_dt_num_sels d n) (__eo_to_smt y)
                      (__eo_to_smt x) (SmtTerm.DtCons s d n))
                    (__eo_to_smt y)) := by
              unfold term_has_non_none_type
              simpa [__eo_to_smt_updater] using hUpdaterNN
            rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
            have hCondNN :
                term_has_non_none_type
                  (SmtTerm.Apply (SmtTerm.DtTester s d n) (__eo_to_smt y)) := by
              unfold term_has_non_none_type
              rw [hCond]
              simp
            have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype s d := by
              exact dt_tester_arg_datatype_of_non_none hCondNN
            have hTTy : T = SmtType.Datatype s d := by
              exact hElse.symm.trans hYTy
            have hSmt :
                __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.update z) y) x)) =
                  SmtType.Datatype s d := by
              rw [hTranslate, __eo_to_smt_updater]
              rw [typeof_ite_eq]
              rw [hCond, hThen, hElse, hTTy]
              simp [__smtx_typeof_ite, native_ite, native_Teq]
            exact hSmt.trans
              (eo_to_smt_type_typeof_apply_apply_apply_update_of_smt_dt_sel
                x y z s d n m hz hNonNone).symm
        | _ =>
            have hBad := hNonNone
            rw [__eo_to_smt.eq_def] at hBad
            simp [hz] at hBad
            simp [__eo_to_smt_updater] at hBad
      case tuple_update =>
        cases hy : __eo_to_smt_type (__eo_typeof y) with
        | Datatype s d =>
            by_cases hTuple : s = "_at_Tuple"
            · subst hTuple
              cases hz : __eo_to_smt z with
              | Numeral n =>
                  have hTranslate :
                      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.tuple_update z) y) x) =
                        __eo_to_smt_tuple_update (SmtType.Datatype "_at_Tuple" d)
                          (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x) := by
                    rw [__eo_to_smt.eq_def]
                    simp [hy, hz]
                  have hTupleNN :
                      __smtx_typeof
                          (__eo_to_smt_tuple_update (SmtType.Datatype "_at_Tuple" d)
                            (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)) ≠
                        SmtType.None := by
                    rw [← hTranslate]
                    exact hNonNone
                  have hGe : native_zleq 0 n = true := by
                    cases hTest : native_zleq 0 n <;>
                      simp [__eo_to_smt_tuple_update, hTest, native_ite] at hTupleNN
                    simpa using hTest
                  have hUpdaterNN :
                      __smtx_typeof
                          (__eo_to_smt_updater
                            (SmtTerm.DtSel "_at_Tuple" d native_nat_zero
                              (native_int_to_nat n))
                            (__eo_to_smt y) (__eo_to_smt x)) ≠
                        SmtType.None := by
                    simpa [__eo_to_smt_tuple_update, hGe, native_ite] using hTupleNN
                  have hIteNN :
                      term_has_non_none_type
                        (SmtTerm.ite
                          (SmtTerm.Apply (SmtTerm.DtTester "_at_Tuple" d native_nat_zero)
                            (__eo_to_smt y))
                          (__eo_to_smt_updater_rec
                            (SmtTerm.DtSel "_at_Tuple" d native_nat_zero
                              (native_int_to_nat n))
                            (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt y)
                            (__eo_to_smt x)
                            (SmtTerm.DtCons "_at_Tuple" d native_nat_zero))
                          (__eo_to_smt y)) := by
                    unfold term_has_non_none_type
                    simpa [__eo_to_smt_updater] using hUpdaterNN
                  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
                  have hCondNN :
                      term_has_non_none_type
                        (SmtTerm.Apply (SmtTerm.DtTester "_at_Tuple" d native_nat_zero)
                          (__eo_to_smt y)) := by
                    unfold term_has_non_none_type
                    rw [hCond]
                    simp
                  have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype "_at_Tuple" d := by
                    exact dt_tester_arg_datatype_of_non_none hCondNN
                  have hTTy : T = SmtType.Datatype "_at_Tuple" d := by
                    exact hElse.symm.trans hYTy
                  have hInnerTy :
                      __smtx_typeof
                          (__eo_to_smt_updater
                            (SmtTerm.DtSel "_at_Tuple" d native_nat_zero
                              (native_int_to_nat n))
                            (__eo_to_smt y) (__eo_to_smt x)) =
                        SmtType.Datatype "_at_Tuple" d := by
                    rw [__eo_to_smt_updater]
                    rw [typeof_ite_eq]
                    rw [hCond, hThen, hElse, hTTy]
                    simp [__smtx_typeof_ite, native_ite, native_Teq]
                  have hSmt :
                      __smtx_typeof
                          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.tuple_update z) y) x)) =
                        SmtType.Datatype "_at_Tuple" d := by
                    rw [hTranslate]
                    simpa [__eo_to_smt_tuple_update, hGe, native_ite] using hInnerTy
                  exact hSmt.trans
                    (eo_to_smt_type_typeof_apply_apply_apply_tuple_update_of_smt_numeral_tuple
                      x y z d n hy hz hNonNone).symm
              | _ =>
                  have hBad := hNonNone
                  rw [__eo_to_smt.eq_def] at hBad
                  simp [hy, hz] at hBad
                  simp [__eo_to_smt_tuple_update] at hBad
            · have hBad := hNonNone
              rw [__eo_to_smt.eq_def] at hBad
              simp [hy] at hBad
              simp [__eo_to_smt_tuple_update, hTuple] at hBad
        | _ =>
            have hBad := hNonNone
            rw [__eo_to_smt.eq_def] at hBad
            simp [hy] at hBad
            simp [__eo_to_smt_tuple_update] at hBad
      case set_union =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_union z) y) =
              theory2 SmtTheoryOp.set_union (__eo_to_smt z) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_union z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate] using
            (generic_apply_type_set_union (__eo_to_smt z) (__eo_to_smt y)
              (__eo_to_smt x))
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.set_union z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case set_inter =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_inter z) y) =
              theory2 SmtTheoryOp.set_inter (__eo_to_smt z) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_inter z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate] using
            (generic_apply_type_set_inter (__eo_to_smt z) (__eo_to_smt y)
              (__eo_to_smt x))
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.set_inter z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case set_minus =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_minus z) y) =
              theory2 SmtTheoryOp.set_minus (__eo_to_smt z) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_minus z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate] using
            (generic_apply_type_set_minus (__eo_to_smt z) (__eo_to_smt y)
              (__eo_to_smt x))
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.set_minus z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case set_choose =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_choose z) y) =
              let _v0 := __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose z))
              SmtTerm.choice_nth "_at_x" _v0
                (theory2 SmtTheoryOp.set_member (SmtTerm.Var "_at_x" _v0) (__eo_to_smt z)) 0 := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_choose z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate, generic_apply_type, theory2, theory1, theory0,
            __smtx_typeof.eq_def]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.set_choose z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case set_member =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y) =
              theory2 SmtTheoryOp.set_member (__eo_to_smt z) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
          rfl
        have hOuterTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.set_member z) y) x) =
              SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate] using
            (generic_apply_type_set_member (__eo_to_smt z) (__eo_to_smt y)
              (__eo_to_smt x))
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            rw [← hOuterTranslate]
            exact hNonNone
          rw [hGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN :
            term_has_non_none_type
              (theory2 SmtTheoryOp.set_member (__eo_to_smt z) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [← hHeadTranslate]
          cases hHead with
          | inl hHead =>
              rw [hHead]
              simp
          | inr hHead =>
              rw [hHead]
              simp
        have hHeadTy :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y)) =
              SmtType.Bool := by
          rcases set_member_args_of_non_none hHeadNN with ⟨A, hzTy, hyTy⟩
          rw [hHeadTranslate, typeof_set_member_eq]
          simp [__smtx_typeof_set_member, hzTy, hyTy,
            native_ite, native_Teq]
        cases hHead with
        | inl hHead =>
            cases (hHeadTy.symm.trans hHead)
        | inr hHead =>
            cases (hHeadTy.symm.trans hHead)
      case set_subset =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y) =
              theory2 SmtTheoryOp.set_subset (__eo_to_smt z) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hOuterTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.set_subset z) y) x) =
              SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate] using
            (generic_apply_type_set_subset (__eo_to_smt z) (__eo_to_smt y)
              (__eo_to_smt x))
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            rw [← hOuterTranslate]
            exact hNonNone
          rw [hGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN :
            term_has_non_none_type
              (theory2 SmtTheoryOp.set_subset (__eo_to_smt z) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [← hHeadTranslate]
          cases hHead with
          | inl hHead =>
              rw [hHead]
              simp
          | inr hHead =>
              rw [hHead]
              simp
        have hHeadTy :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y)) =
              SmtType.Bool := by
          rcases set_binop_ret_args_of_non_none
              (op := theory2 SmtTheoryOp.set_subset) (T := SmtType.Bool)
              (typeof_set_subset_eq (__eo_to_smt z) (__eo_to_smt y)) hHeadNN with
            ⟨A, hzTy, hyTy⟩
          rw [hHeadTranslate, typeof_set_subset_eq (__eo_to_smt z) (__eo_to_smt y)]
          simp [__smtx_typeof_sets_op_2_ret, hzTy, hyTy,
            native_ite, native_Teq]
        cases hHead with
        | inl hHead =>
            cases (hHeadTy.symm.trans hHead)
        | inr hHead =>
            cases (hHeadTy.symm.trans hHead)
      case qdiv_total =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y) =
              theory2 SmtTheoryOp.qdiv_total (__eo_to_smt z) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hOuterTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.qdiv_total z) y) x) =
              SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate] using
            (generic_apply_type_qdiv_total (__eo_to_smt z) (__eo_to_smt y)
              (__eo_to_smt x))
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            rw [← hOuterTranslate]
            exact hNonNone
          rw [hGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN :
            term_has_non_none_type
              (theory2 SmtTheoryOp.qdiv_total (__eo_to_smt z) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [← hHeadTranslate]
          cases hHead with
          | inl hHead =>
              rw [hHead]
              simp
          | inr hHead =>
              rw [hHead]
              simp
        rcases arith_binop_ret_args_of_non_none
            (op := theory2 SmtTheoryOp.qdiv_total) (R := SmtType.Real)
            (typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)) hHeadNN with hArgs | hArgs
        · have hHeadTy :
              __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y)) =
                SmtType.Real := by
            rw [hHeadTranslate, typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)]
            simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
          cases hHead with
          | inl hHead =>
              cases (hHeadTy.symm.trans hHead)
          | inr hHead =>
              cases (hHeadTy.symm.trans hHead)
        · have hHeadTy :
              __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y)) =
                SmtType.Real := by
            rw [hHeadTranslate, typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)]
            simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
          cases hHead with
          | inl hHead =>
              cases (hHeadTy.symm.trans hHead)
          | inr hHead =>
              cases (hHeadTy.symm.trans hHead)
      case int_to_bv =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y) =
              theory2 SmtTheoryOp.int_to_bv (__eo_to_smt z) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hOuterTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.int_to_bv z) y) x) =
              SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y))
              (__eo_to_smt x) := by
          simpa [hHeadTranslate] using
            (generic_apply_type_int_to_bv (__eo_to_smt z) (__eo_to_smt y)
              (__eo_to_smt x))
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            rw [← hOuterTranslate]
            exact hNonNone
          rw [hGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN :
            term_has_non_none_type
              (theory2 SmtTheoryOp.int_to_bv (__eo_to_smt z) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [← hHeadTranslate]
          cases hHead with
          | inl hHead =>
              rw [hHead]
              simp
          | inr hHead =>
              rw [hHead]
              simp
        rcases int_to_bv_args_of_non_none hHeadNN with ⟨i, hz', hy', hi⟩
        have hHeadTy :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y)) =
              SmtType.BitVec (native_int_to_nat i) := by
          rw [hHeadTranslate, typeof_int_to_bv_eq, hz', hy']
          simp [__smtx_typeof_int_to_bv, native_ite, hi]
        cases hHead with
        | inl hHead =>
            cases (hHeadTy.symm.trans hHead)
        | inr hHead =>
            cases (hHeadTy.symm.trans hHead)
      all_goals sorry
    all_goals sorry
  case not =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.not x) =
          theory1 SmtTheoryOp.not (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.not (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
      have hNotTy : __smtx_typeof (theory1 SmtTheoryOp.not (__eo_to_smt x)) = SmtType.Bool := by
        rcases smtx_typeof_not_bool_or_none (__eo_to_smt x) with hBool | hNone
        · exact hBool
        · exfalso
          exact hApplyNN hNone
      rw [typeof_not_eq] at hNotTy
      cases h : __smtx_typeof (__eo_to_smt x) <;>
        simp [native_ite, native_Teq, h] at hNotTy
      rfl
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Bool := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Bool := eo_to_smt_type_eq_bool hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) = SmtType.Bool := by
      rw [hTranslate, typeof_not_eq]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_not_of_bool x hxEo).symm
  case _at_purify y =>
    sorry
  case to_real =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.to_real x) =
          theory1 SmtTheoryOp.to_real (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.to_real (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
      to_real_arg_of_non_none (t := __eo_to_smt x) hApplyNN
    cases hArg with
    | inl hArgInt =>
        have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgInt]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
          rw [← hXTyped]
          exact hArgInt
        have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
        have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.to_real x)) = SmtType.Real := by
          rw [hTranslate, typeof_to_real_eq]
          simp [hArgInt, native_ite, native_Teq]
        exact hSmt.trans (eo_to_smt_type_typeof_apply_to_real_of_int x hxEo).symm
    | inr hArgReal =>
        have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgReal]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
          rw [← hXTyped]
          exact hArgReal
        have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
        have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.to_real x)) = SmtType.Real := by
          rw [hTranslate, typeof_to_real_eq]
          simp [hArgReal, native_ite, native_Teq]
        exact hSmt.trans (eo_to_smt_type_typeof_apply_to_real_of_real x hxEo).symm
  case to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.to_int x) =
          theory1 SmtTheoryOp.to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
      real_arg_of_non_none (op := theory1 SmtTheoryOp.to_int) (t := __eo_to_smt x)
        (typeof_to_int_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.to_int x)) = SmtType.Int := by
      rw [hTranslate, typeof_to_int_eq]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_to_int_of_real x hxEo).symm
  case is_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.is_int x) =
          theory1 SmtTheoryOp.is_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.is_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
      real_arg_of_non_none (op := theory1 SmtTheoryOp.is_int) (t := __eo_to_smt x)
        (typeof_is_int_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.is_int x)) = SmtType.Bool := by
      rw [hTranslate, typeof_is_int_eq]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_is_int_of_real x hxEo).symm
  case abs =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.abs x) =
          theory1 SmtTheoryOp.abs (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.abs (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_arg_of_non_none (t := __eo_to_smt x) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.abs x)) = SmtType.Int := by
      rw [hTranslate, typeof_abs_eq]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_abs_of_int x hxEo).symm
  case int_pow2 =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.int_pow2 x) =
          theory1 SmtTheoryOp.int_pow2 (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.int_pow2 (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := theory1 SmtTheoryOp.int_pow2)
        (typeof_int_pow2_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.int_pow2 x)) = SmtType.Int := by
      rw [hTranslate, typeof_int_pow2_eq]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_int_pow2_of_int x hxEo).symm
  case int_log2 =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.int_log2 x) =
          theory1 SmtTheoryOp.int_log2 (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.int_log2 (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := theory1 SmtTheoryOp.int_log2)
        (typeof_int_log2_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.int_log2 x)) = SmtType.Int := by
      rw [hTranslate, typeof_int_log2_eq]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_int_log2_of_int x hxEo).symm
  case int_ispow2 =>
    let geqTerm :=
      theory2 SmtTheoryOp.geq (__eo_to_smt x) (SmtTerm.Numeral 0)
    let eqTerm :=
      SmtTerm.eq (__eo_to_smt x)
        (theory1 SmtTheoryOp.int_pow2 (theory1 SmtTheoryOp.int_log2 (__eo_to_smt x)))
    have hTranslate :
        __eo_to_smt (Term.Apply Term.int_ispow2 x) =
          theory2 SmtTheoryOp.and geqTerm eqTerm := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type (theory2 SmtTheoryOp.and geqTerm eqTerm) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs :
        __smtx_typeof geqTerm = SmtType.Bool ∧
          __smtx_typeof eqTerm = SmtType.Bool :=
      bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.and)
        (typeof_and_eq geqTerm eqTerm) hApplyNN
    have hGeqNN : term_has_non_none_type geqTerm := by
      unfold term_has_non_none_type
      rw [hArgs.1]
      simp
    have hGeqArgs :
        (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
            __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int) ∨
          (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
            __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Real) :=
      arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.geq)
        (typeof_geq_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hGeqNN
      
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
      rcases hGeqArgs with hInt | hReal
      · exact hInt.1
      · have hZeroReal := hReal.2
        rw [__smtx_typeof.eq_def] at hZeroReal
        simp at hZeroReal
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.int_ispow2 x)) = SmtType.Bool := by
      rw [hTranslate, typeof_and_eq geqTerm eqTerm]
      simp [hArgs.1, hArgs.2, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_int_ispow2_of_int x hxEo).symm
  case _at_int_div_by_zero =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_int_div_by_zero x) =
          theory2 SmtTheoryOp.div (__eo_to_smt x) (SmtTerm.Numeral 0) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (theory2 SmtTheoryOp.div (__eo_to_smt x) (SmtTerm.Numeral 0)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
        __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int :=
      int_binop_args_of_non_none (op := theory2 SmtTheoryOp.div) (R := SmtType.Int)
        (typeof_div_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgs.1]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArgs.1
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term._at_int_div_by_zero x)) = SmtType.Int := by
      rw [hTranslate, typeof_div_eq (__eo_to_smt x) (SmtTerm.Numeral 0)]
      simp [hArgs.1, hArgs.2, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_at_int_div_by_zero_of_int x hxEo).symm
  case _at_mod_by_zero =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_mod_by_zero x) =
          theory2 SmtTheoryOp.mod (__eo_to_smt x) (SmtTerm.Numeral 0) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (theory2 SmtTheoryOp.mod (__eo_to_smt x) (SmtTerm.Numeral 0)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
        __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int :=
      int_binop_args_of_non_none (op := theory2 SmtTheoryOp.mod) (R := SmtType.Int)
        (typeof_mod_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgs.1]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArgs.1
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term._at_mod_by_zero x)) = SmtType.Int := by
      rw [hTranslate, typeof_mod_eq (__eo_to_smt x) (SmtTerm.Numeral 0)]
      simp [hArgs.1, hArgs.2, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_at_mod_by_zero_of_int x hxEo).symm
  case _at_array_deq_diff x1 x2 =>
    have hHeadTranslate :
        __eo_to_smt (Term._at_array_deq_diff x1 x2) =
      let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
      let _v2 := SmtTerm.Var "_at_x" _v0
      SmtTerm.choice_nth "_at_x" _v0
        (theory1 SmtTheoryOp.not
          (SmtTerm.eq
            (theory2 SmtTheoryOp.select (__eo_to_smt x1) _v2)
            (theory2 SmtTheoryOp.select (__eo_to_smt x2) _v2))) 0 := by
      rw [__eo_to_smt.eq_def]
      rfl
    have hTranslate :
        __eo_to_smt (Term.Apply (Term._at_array_deq_diff x1 x2) x) =
          SmtTerm.Apply (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hGeneric :
        generic_apply_type (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x) := by
      simpa [hHeadTranslate, generic_apply_type, theory1, theory2, theory0,
        __smtx_typeof.eq_def]
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGeneric] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hHeadNN :
        __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) ≠ SmtType.None := by
      cases hHead with
      | inl hHead =>
          rw [hHead]
          simp
      | inr hHead =>
          rw [hHead]
          simp
    have hHeadEo :
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = SmtType.FunType A B ∨
          __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = SmtType.DtcAppType A B := by
      rw [← ihF hHeadNN]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term._at_array_deq_diff x1 x2) x)) = B := by
      rw [hTranslate]
      rw [hGeneric]
      cases hHead with
      | inl hHead =>
          rw [hHead, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
      | inr hHead =>
          rw [hHead, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_at_array_deq_diff_of_smt_apply x x1 x2 A B hHeadEo hX).symm
  case _at_bvsize =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_bvsize x) =
          SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) := by
      rw [__eo_to_smt.eq_def]
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term._at_bvsize x)) = SmtType.Int := by
      rw [hTranslate, __smtx_typeof.eq_def]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_at_bvsize x).symm
  case bvnot =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvnot x) =
          theory1 SmtTheoryOp.bvnot (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.bvnot (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_arg_of_non_none (op := theory1 SmtTheoryOp.bvnot)
        (typeof_bvnot_eq (__eo_to_smt x)) hApplyNN with ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w)) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.bvnot x)) = SmtType.BitVec w := by
      rw [hTranslate, typeof_bvnot_eq (__eo_to_smt x), hArg]
      simp [__smtx_typeof_bv_op_1, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvnot_of_bitvec x w hxEo).symm
  case bvneg =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvneg x) =
          theory1 SmtTheoryOp.bvneg (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.bvneg (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_arg_of_non_none (op := theory1 SmtTheoryOp.bvneg)
        (typeof_bvneg_eq (__eo_to_smt x)) hApplyNN with ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w)) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.bvneg x)) = SmtType.BitVec w := by
      rw [hTranslate, typeof_bvneg_eq (__eo_to_smt x), hArg]
      simp [__smtx_typeof_bv_op_1, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvneg_of_bitvec x w hxEo).symm
  case bvnego =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvnego x) =
          theory1 SmtTheoryOp.bvnego (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.bvnego (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_ret_arg_of_non_none (op := theory1 SmtTheoryOp.bvnego) (ret := SmtType.Bool)
        (typeof_bvnego_eq (__eo_to_smt x)) hApplyNN with
      ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w)) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.bvnego x)) = SmtType.Bool := by
      rw [hTranslate, typeof_bvnego_eq (__eo_to_smt x), hArg]
      simp [__smtx_typeof_bv_op_1_ret, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvnego_of_bitvec x w hxEo).symm
  case bvredand =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvredand x) =
          let _v0 := __eo_to_smt x
          theory2 SmtTheoryOp.bvcomp _v0
            (theory1 SmtTheoryOp.bvnot
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (let _v0 := __eo_to_smt x
           theory2 SmtTheoryOp.bvcomp _v0
             (theory1 SmtTheoryOp.bvnot
               (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0))) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_binop_ret_args_of_non_none
        (op := theory2 SmtTheoryOp.bvcomp) (ret := SmtType.BitVec 1)
        (typeof_bvcomp_eq
          (__eo_to_smt x)
          (theory1 SmtTheoryOp.bvnot (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)))
        hApplyNN with
      ⟨w, hArgX, hArgY⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgX]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArgX
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w)) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hArgY' :
        __smtx_typeof
            (theory1 SmtTheoryOp.bvnot
              (SmtTerm.Binary (__smtx_bv_sizeof_type (SmtType.BitVec w)) 0)) =
          SmtType.BitVec w := by
      simpa [hArgX] using hArgY
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.bvredand x)) = SmtType.BitVec 1 := by
      rw [hTranslate]
      rw [typeof_bvcomp_eq]
      rw [hArgX, hArgY']
      simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, SmtEval.native_nateq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvredand_of_bitvec x w hxEo).symm
  case bvredor =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvredor x) =
          let _v0 := __eo_to_smt x
          theory1 SmtTheoryOp.bvnot
            (theory2 SmtTheoryOp.bvcomp _v0
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (let _v0 := __eo_to_smt x
           theory1 SmtTheoryOp.bvnot
             (theory2 SmtTheoryOp.bvcomp _v0
               (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0))) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hInner :
        ∃ w : native_Nat,
          __smtx_typeof
              (theory2 SmtTheoryOp.bvcomp
                (__eo_to_smt x)
                (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) =
            SmtType.BitVec w := by
      rcases bv_unop_arg_of_non_none (op := theory1 SmtTheoryOp.bvnot)
          (typeof_bvnot_eq
            (theory2 SmtTheoryOp.bvcomp
              (__eo_to_smt x)
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)))
          hApplyNN with ⟨w, hInner⟩
      exact ⟨w, hInner⟩
    rcases hInner with ⟨_, hInnerTy⟩
    have hInnerNN :
        term_has_non_none_type
          (theory2 SmtTheoryOp.bvcomp
            (__eo_to_smt x)
            (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) := by
      unfold term_has_non_none_type
      rw [hInnerTy]
      simp
    rcases bv_binop_ret_args_of_non_none
        (op := theory2 SmtTheoryOp.bvcomp) (ret := SmtType.BitVec 1)
        (typeof_bvcomp_eq
          (__eo_to_smt x)
          (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0))
        hInnerNN with
      ⟨w, hArgX, hArgY⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgX]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArgX
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w)) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hArgY' :
        __smtx_typeof (SmtTerm.Binary (__smtx_bv_sizeof_type (SmtType.BitVec w)) 0) =
          SmtType.BitVec w := by
      simpa [hArgX] using hArgY
    have hInnerOne :
        __smtx_typeof
            (theory2 SmtTheoryOp.bvcomp
              (__eo_to_smt x)
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) =
          SmtType.BitVec 1 := by
      rw [typeof_bvcomp_eq]
      rw [hArgX, hArgY']
      simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, SmtEval.native_nateq]
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.bvredor x)) = SmtType.BitVec 1 := by
      rw [hTranslate, typeof_bvnot_eq]
      rw [hInnerOne]
      simp [__smtx_typeof_bv_op_1, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvredor_of_bitvec x w hxEo).symm
  case str_len =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_len x) =
          theory1 SmtTheoryOp.str_len (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_len (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgExists : ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
      exact seq_arg_of_non_none_ret (op := theory1 SmtTheoryOp.str_len)
        (typeof_str_len_eq (__eo_to_smt x)) hApplyNN
    rcases hArgExists with ⟨T, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
      rw [← hXTyped]
      exact hArg
    rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len x)) = SmtType.Int := by
      rw [hTranslate, typeof_str_len_eq (__eo_to_smt x), hArg]
      simp [__smtx_typeof_seq_op_1_ret, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_len_of_seq x V hxEo).symm
  case str_rev =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_rev x) =
          theory1 SmtTheoryOp.str_rev (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_rev (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases seq_arg_of_non_none (op := theory1 SmtTheoryOp.str_rev)
        (typeof_str_rev_eq (__eo_to_smt x)) hApplyNN with ⟨T, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
      rw [← hXTyped]
      exact hArg
    rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_rev x)) = SmtType.Seq T := by
      rw [hTranslate, typeof_str_rev_eq (__eo_to_smt x)]
      simp [__smtx_typeof_seq_op_1, hArg]
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_rev x)) =
          SmtType.Seq (__eo_to_smt_type V) :=
      eo_to_smt_type_typeof_apply_str_rev_of_seq x V hxEo
    rw [hV] at hEo
    exact hSmt.trans hEo.symm
  case str_to_lower =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_lower x) =
          theory1 SmtTheoryOp.str_to_lower (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_to_lower (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := theory1 SmtTheoryOp.str_to_lower)
        (typeof_str_to_lower_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_lower x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate, typeof_str_to_lower_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char x hxEo).symm
  case str_to_upper =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_upper x) =
          theory1 SmtTheoryOp.str_to_upper (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_to_upper (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := theory1 SmtTheoryOp.str_to_upper)
        (typeof_str_to_upper_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_upper x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate, typeof_str_to_upper_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char x hxEo).symm
  case str_to_code =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_code x) =
          theory1 SmtTheoryOp.str_to_code (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_to_code (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := theory1 SmtTheoryOp.str_to_code)
        (typeof_str_to_code_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_code x)) = SmtType.Int := by
      rw [hTranslate, typeof_str_to_code_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_code_of_seq_char x hxEo).symm
  case str_from_code =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_from_code x) =
          theory1 SmtTheoryOp.str_from_code (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_from_code (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := theory1 SmtTheoryOp.str_from_code) (R := SmtType.Seq SmtType.Char)
        (typeof_str_from_code_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_from_code x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate, typeof_str_from_code_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_code_of_int x hxEo).symm
  case str_is_digit =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_is_digit x) =
          theory1 SmtTheoryOp.str_is_digit (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_is_digit (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := theory1 SmtTheoryOp.str_is_digit)
        (typeof_str_is_digit_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_is_digit x)) = SmtType.Bool := by
      rw [hTranslate, typeof_str_is_digit_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char x hxEo).symm
  case str_to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_int x) =
          theory1 SmtTheoryOp.str_to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := theory1 SmtTheoryOp.str_to_int)
        (typeof_str_to_int_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_int x)) = SmtType.Int := by
      rw [hTranslate, typeof_str_to_int_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_int_of_seq_char x hxEo).symm
  case str_from_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_from_int x) =
          theory1 SmtTheoryOp.str_from_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_from_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := theory1 SmtTheoryOp.str_from_int) (R := SmtType.Seq SmtType.Char)
        (typeof_str_from_int_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_from_int x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate, typeof_str_from_int_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_int_of_int x hxEo).symm
  case _at_strings_stoi_non_digit =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_strings_stoi_non_digit x) =
          theory3 SmtTheoryOp.str_indexof_re
            (__eo_to_smt x)
            (theory1 SmtTheoryOp.re_comp
              (theory2 SmtTheoryOp.re_range (SmtTerm.String "0") (SmtTerm.String "9")))
            (SmtTerm.Numeral 0) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (theory3 SmtTheoryOp.str_indexof_re
            (__eo_to_smt x)
            (theory1 SmtTheoryOp.re_comp
              (theory2 SmtTheoryOp.re_range (SmtTerm.String "0") (SmtTerm.String "9")))
            (SmtTerm.Numeral 0)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs := str_indexof_re_args_of_non_none hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgs.1]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArgs.1
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term._at_strings_stoi_non_digit x)) =
          SmtType.Int := by
      rw [hTranslate]
      rw [typeof_str_indexof_re_eq]
      rw [hArgs.1, hArgs.2.1, hArgs.2.2]
      simp [native_ite, native_Teq]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char x hxEo).symm
  case str_to_re =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_re x) =
          theory1 SmtTheoryOp.str_to_re (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.str_to_re (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := theory1 SmtTheoryOp.str_to_re)
        (typeof_str_to_re_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_re x)) = SmtType.RegLan := by
      rw [hTranslate, typeof_str_to_re_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_re_of_seq_char x hxEo).symm
  case re_mult =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_mult x) =
          theory1 SmtTheoryOp.re_mult (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.re_mult (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := theory1 SmtTheoryOp.re_mult)
        (typeof_re_mult_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_mult x)) = SmtType.RegLan := by
      rw [hTranslate, typeof_re_mult_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_mult_of_reglan x hxEo).symm
  case re_plus =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_plus x) =
          theory1 SmtTheoryOp.re_plus (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.re_plus (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := theory1 SmtTheoryOp.re_plus)
        (typeof_re_plus_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_plus x)) = SmtType.RegLan := by
      rw [hTranslate, typeof_re_plus_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_plus_of_reglan x hxEo).symm
  case re_opt =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_opt x) =
          theory1 SmtTheoryOp.re_opt (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.re_opt (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := theory1 SmtTheoryOp.re_opt)
        (typeof_re_opt_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_opt x)) = SmtType.RegLan := by
      rw [hTranslate, typeof_re_opt_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_opt_of_reglan x hxEo).symm
  case re_comp =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_comp x) =
          theory1 SmtTheoryOp.re_comp (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.re_comp (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := theory1 SmtTheoryOp.re_comp)
        (typeof_re_comp_eq (__eo_to_smt x)) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_comp x)) = SmtType.RegLan := by
      rw [hTranslate, typeof_re_comp_eq (__eo_to_smt x)]
      simp [hArg, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_comp_of_reglan x hxEo).symm
  case seq_unit =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.seq_unit x) =
          theory1 SmtTheoryOp.seq_unit (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      intro hXNone
      apply hNonNone
      rw [hTranslate, typeof_seq_unit_eq (__eo_to_smt x), hXNone]
      simp [native_ite, native_Teq]
    have hXTyped := ihX hXNonNone
    have hxEoNonNone : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
      rw [← hXTyped]
      exact hXNonNone
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.seq_unit x)) =
          SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
      rw [hTranslate, typeof_seq_unit_eq (__eo_to_smt x), hXTyped]
      simp [native_ite, native_Teq, hxEoNonNone]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_seq_unit_of_non_none x hxEoNonNone).symm
  case is =>
    exfalso
    apply hNonNone
    rw [__eo_to_smt.eq_def]
    simpa using smtx_typeof_eo_to_smt_tester_none (__eo_to_smt x)
  case set_empty T =>
    exfalso
    apply hNonNone
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.set_empty T) x) =
          SmtTerm.Apply (__eo_to_smt_set_empty (__eo_to_smt_type T)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
      change (__eo_to_smt (Term.set_empty T)).Apply (__eo_to_smt x) =
          SmtTerm.Apply (__eo_to_smt_set_empty (__eo_to_smt_type T)) (__eo_to_smt x)
      rw [eo_to_smt_set_empty]
    have hGeneric :
        generic_apply_type (__eo_to_smt_set_empty (__eo_to_smt_type T)) (__eo_to_smt x) := by
      cases hT : __eo_to_smt_type T <;> simp [__eo_to_smt_set_empty]
      all_goals
        rw [generic_apply_type, __smtx_typeof.eq_def]
    rw [hTranslate, hGeneric]
    exact smtx_typeof_apply_eo_to_smt_set_empty_eq_none
      (__eo_to_smt_type T) (__smtx_typeof (__eo_to_smt x))
  case set_singleton =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.set_singleton x) =
          theory1 SmtTheoryOp.set_singleton (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      intro hXNone
      apply hNonNone
      rw [hTranslate, typeof_set_singleton_eq (__eo_to_smt x), hXNone]
      simp [native_ite, native_Teq]
    have hXTyped := ihX hXNonNone
    have hxEoNonNone : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
      rw [← hXTyped]
      exact hXNonNone
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton x)) =
          SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
      rw [hTranslate, typeof_set_singleton_eq (__eo_to_smt x), hXTyped]
      simp [native_ite, native_Teq, hxEoNonNone]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_set_singleton_of_non_none x hxEoNonNone).symm
  case set_is_empty =>
    exfalso
    have hTranslate :
        __eo_to_smt (Term.Apply Term.set_is_empty x) =
          let _v0 := __eo_to_smt x
          SmtTerm.eq _v0 (SmtTerm.set_empty (__smtx_typeof _v0)) := by
      rw [__eo_to_smt.eq_def]
    have hEqNN :
        __smtx_typeof_eq
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof_guard_wf
              (__smtx_typeof (__eo_to_smt x))
              (SmtType.Set (__smtx_typeof (__eo_to_smt x)))) ≠
          SmtType.None := by
      simpa [hTranslate, typeof_eq_eq, typeof_set_empty_eq] using hNonNone
    have hEqArgs := smtx_typeof_eq_non_none hEqNN
    exact smt_type_ne_guard_wf_set_self hEqArgs.2 <| by
      simpa [typeof_set_empty_eq] using hEqArgs.1
  case set_is_singleton =>
    let T := __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose x))
    have hTranslate :
        __eo_to_smt (Term.Apply Term.set_is_singleton x) =
          SmtTerm.exists "_at_x" T
            (SmtTerm.eq (__eo_to_smt x)
              (theory1 SmtTheoryOp.set_singleton (SmtTerm.Var "_at_x" T))) := by
      rw [__eo_to_smt.eq_def]
    have hExistsNN :
        term_has_non_none_type
          (SmtTerm.exists "_at_x" T
            (SmtTerm.eq (__eo_to_smt x)
              (theory1 SmtTheoryOp.set_singleton (SmtTerm.Var "_at_x" T)))) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hBodyNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt x)
            (theory1 SmtTheoryOp.set_singleton (SmtTerm.Var "_at_x" T))) := by
      unfold term_has_non_none_type
      rw [exists_body_bool_of_non_none hExistsNN]
      simp
    have hEqNN :
        __smtx_typeof_eq
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (theory1 SmtTheoryOp.set_singleton (SmtTerm.Var "_at_x" T))) ≠
          SmtType.None := by
      unfold term_has_non_none_type at hBodyNN
      rw [typeof_eq_eq] at hBodyNN
      exact hBodyNN
    have hEqArgs := smtx_typeof_eq_non_none hEqNN
    have hSingletonNN :
        __smtx_typeof (theory1 SmtTheoryOp.set_singleton (SmtTerm.Var "_at_x" T)) ≠
          SmtType.None := by
      rw [← hEqArgs.1]
      exact hEqArgs.2
    have hVarNN : __smtx_typeof (SmtTerm.Var "_at_x" T) ≠ SmtType.None := by
      intro hVarNone
      apply hSingletonNN
      rw [typeof_set_singleton_eq, hVarNone]
      simp [native_ite, native_Teq]
    have hTNonNone : T ≠ SmtType.None := by
      intro hTNone
      have hVarTyNone := smtx_typeof_var_of_non_none "_at_x" T hVarNN
      exact hVarNN (hVarTyNone.trans hTNone)
    have hVarTy : __smtx_typeof (SmtTerm.Var "_at_x" T) = T := by
      simpa using smtx_typeof_var_of_non_none "_at_x" T hVarNN
    have hXTy :
        __smtx_typeof (__eo_to_smt x) = SmtType.Set T := by
      rw [hEqArgs.1, typeof_set_singleton_eq, hVarTy]
      simp [native_ite, native_Teq, hTNonNone]
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.set_is_singleton x)) = SmtType.Bool := by
      rw [hTranslate, typeof_exists_eq]
      rw [typeof_eq_eq, typeof_set_singleton_eq, hVarTy]
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
        hXTy, hTNonNone]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_set_is_singleton_of_smt_set x hXTy).symm
  case _at_sets_deq_diff x1 x2 =>
    have hHeadTranslate :
        __eo_to_smt (Term._at_sets_deq_diff x1 x2) =
          let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))
          let _v2 := SmtTerm.Var "_at_x" _v0
          SmtTerm.choice_nth "_at_x" _v0
            (theory1 SmtTheoryOp.not
              (SmtTerm.eq
                (theory2 SmtTheoryOp.set_member _v2 (__eo_to_smt x1))
                (theory2 SmtTheoryOp.set_member _v2 (__eo_to_smt x2)))) 0 := by
      rw [__eo_to_smt.eq_def]
    have hTranslate :
        __eo_to_smt (Term.Apply (Term._at_sets_deq_diff x1 x2) x) =
          SmtTerm.Apply (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hGeneric :
        generic_apply_type (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x) := by
      simpa [hHeadTranslate, generic_apply_type, theory1, theory2, theory0,
        __smtx_typeof.eq_def]
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGeneric] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hHeadNN :
        __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) ≠ SmtType.None := by
      cases hHead with
      | inl hHead =>
          rw [hHead]
          simp
      | inr hHead =>
          rw [hHead]
          simp
    have hHeadEo :
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = SmtType.FunType A B ∨
          __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = SmtType.DtcAppType A B := by
      rw [← ihF hHeadNN]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term._at_sets_deq_diff x1 x2) x)) = B := by
      rw [hTranslate]
      rw [hGeneric]
      cases hHead with
      | inl hHead =>
          rw [hHead, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
      | inr hHead =>
          rw [hHead, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_at_sets_deq_diff_of_smt_apply x x1 x2 A B hHeadEo hX).symm
  case _at_div_by_zero =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_div_by_zero x) =
          theory2 SmtTheoryOp.qdiv (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1)) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (theory2 SmtTheoryOp.qdiv (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1))) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs :
        (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
            __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) = SmtType.Int) ∨
          (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
            __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) = SmtType.Real) :=
      arith_binop_ret_args_of_non_none (op := theory2 SmtTheoryOp.qdiv) (R := SmtType.Real)
        (typeof_qdiv_eq (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1))) hApplyNN
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
      rcases hArgs with hInt | hReal
      · have hZeroInt := hInt.2
        rw [typeof_rational_eq] at hZeroInt
        cases hZeroInt
      · exact hReal.1
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term._at_div_by_zero x)) = SmtType.Real := by
      rw [hTranslate, typeof_qdiv_eq (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1)),
        typeof_rational_eq, hArg]
      simp [__smtx_typeof_arith_overload_op_2_ret, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_at_div_by_zero_of_real x hxEo).symm
  case _at_quantifiers_skolemize x1 x2 =>
    sorry
  case ubv_to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.ubv_to_int x) =
          theory1 SmtTheoryOp.ubv_to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.ubv_to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_ret_arg_of_non_none (op := theory1 SmtTheoryOp.ubv_to_int) (ret := SmtType.Int)
        (by
          show
            __smtx_typeof (theory1 SmtTheoryOp.ubv_to_int (__eo_to_smt x)) =
              __smtx_typeof_bv_op_1_ret (__smtx_typeof (__eo_to_smt x)) SmtType.Int
          rw [theory1, theory0, __smtx_typeof.eq_def]) hApplyNN with
      ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w)) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.ubv_to_int x)) = SmtType.Int := by
      rw [hTranslate]
      rw [show
          __smtx_typeof (theory1 SmtTheoryOp.ubv_to_int (__eo_to_smt x)) =
            __smtx_typeof_bv_op_1_ret (__smtx_typeof (__eo_to_smt x)) SmtType.Int by
          rw [theory1, theory0, __smtx_typeof.eq_def], hArg]
      simp [__smtx_typeof_bv_op_1_ret, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_ubv_to_int_of_bitvec x w hxEo).symm
  case sbv_to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.sbv_to_int x) =
          theory1 SmtTheoryOp.sbv_to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (theory1 SmtTheoryOp.sbv_to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_ret_arg_of_non_none (op := theory1 SmtTheoryOp.sbv_to_int) (ret := SmtType.Int)
        (by
          show
            __smtx_typeof (theory1 SmtTheoryOp.sbv_to_int (__eo_to_smt x)) =
              __smtx_typeof_bv_op_1_ret (__smtx_typeof (__eo_to_smt x)) SmtType.Int
          rw [theory1, theory0, __smtx_typeof.eq_def]) hApplyNN with
      ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w)) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.sbv_to_int x)) = SmtType.Int := by
      rw [hTranslate]
      rw [show
          __smtx_typeof (theory1 SmtTheoryOp.sbv_to_int (__eo_to_smt x)) =
            __smtx_typeof_bv_op_1_ret (__smtx_typeof (__eo_to_smt x)) SmtType.Int by
          rw [theory1, theory0, __smtx_typeof.eq_def], hArg]
      simp [__smtx_typeof_bv_op_1_ret, native_ite, native_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_sbv_to_int_of_bitvec x w hxEo).symm
  all_goals
    sorry

end TranslationProofs
