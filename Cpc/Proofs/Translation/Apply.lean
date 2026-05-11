import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Quantifiers
import Cpc.Proofs.Translation.Special
import Cpc.Proofs.Translation.Inversions
import Cpc.Proofs.Translation.Heads
import Cpc.Proofs.Translation.EoTypeof
import Cpc.Proofs.TypePreservationFull

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

private theorem smtx_type_wf_rec_of_type_wf
    {T : SmtType}
    (hNotReg : T ≠ SmtType.RegLan)
    (h : __smtx_type_wf T = true) :
    __smtx_type_wf_rec T native_reflist_nil = true := by
  cases T <;> simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h hNotReg ⊢
  all_goals exact h.2

private theorem smtx_type_wf_seq_component
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Seq A) = true) :
    __smtx_type_wf A = true := by
  exact seq_type_wf_component_of_wf h

private theorem smtx_type_wf_set_component
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    __smtx_type_wf A = true := by
  exact set_type_wf_component_of_wf h

private theorem smtx_type_wf_map_components
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  exact map_type_wf_components_of_wf h

private theorem smtx_type_wf_fun_components
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  exact fun_type_wf_components_of_wf h

private theorem native_inhabited_type_of_type_inhabited
    {T : SmtType}
    (h : type_inhabited T) :
    native_inhabited_type T = true :=
  (Smtm.smtx_inhabited_type_eq_true_iff T).2 h

@[simp] private theorem native_inhabited_type_bool_apply :
    native_inhabited_type SmtType.Bool = true :=
  native_inhabited_type_of_type_inhabited type_inhabited_bool

@[simp] private theorem native_inhabited_type_int_apply :
    native_inhabited_type SmtType.Int = true :=
  native_inhabited_type_of_type_inhabited type_inhabited_int

@[simp] private theorem native_inhabited_type_real_apply :
    native_inhabited_type SmtType.Real = true :=
  native_inhabited_type_of_type_inhabited type_inhabited_real

@[simp] private theorem native_inhabited_type_reglan_apply :
    native_inhabited_type SmtType.RegLan = true :=
  native_inhabited_type_of_type_inhabited type_inhabited_reglan

@[simp] private theorem native_inhabited_type_char_apply :
    native_inhabited_type SmtType.Char = true :=
  native_inhabited_type_of_type_inhabited type_inhabited_char

@[simp] private theorem native_inhabited_type_usort_apply
    (i : native_Nat) :
    native_inhabited_type (SmtType.USort i) = true :=
  native_inhabited_type_of_type_inhabited (type_inhabited_usort i)

@[simp] private theorem native_inhabited_type_seq_apply
    (T : SmtType) :
    native_inhabited_type (SmtType.Seq T) = true :=
  native_inhabited_type_of_type_inhabited (type_inhabited_seq T)

@[simp] private theorem native_inhabited_type_set_apply
    (T : SmtType) :
    native_inhabited_type (SmtType.Set T) = true :=
  native_inhabited_type_of_type_inhabited (type_inhabited_set T)

@[simp] private theorem native_inhabited_type_bitvec_apply
    (w : native_Nat) :
    native_inhabited_type (SmtType.BitVec w) = true := by
  apply native_inhabited_type_of_type_inhabited
  refine ⟨SmtValue.Binary (native_nat_to_int w) 0, ?_⟩
  have hWidth : native_zleq 0 (native_nat_to_int w) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hMod :
      native_zeq 0
        (native_mod_total 0 (native_int_pow2 (native_nat_to_int w))) = true := by
    simp [native_zeq, SmtEval.native_zeq, native_mod_total,
      SmtEval.native_mod_total]
  simpa [native_int_to_nat, SmtEval.native_int_to_nat, native_nat_to_int,
    SmtEval.native_nat_to_int] using
      typeof_value_binary_of_nonneg (native_nat_to_int w) 0 hWidth hMod

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_concat`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_concat
    (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x) =
        SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x))
    (hEo :
      ∀ w1 w2 : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w1 ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w2 ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
          SmtType.BitVec
            (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_concat_args_of_non_none hApplyNN with ⟨w1, w2, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
    rw [hTranslate]
    rw [typeof_concat_eq (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_concat, hy, hx]
  exact hSmt.trans (hEo w1 w2 hy hx).symm

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

/-- Simplifies comparison operators translated through an `ite` returning `(_ BitVec 1)`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bv_cmp_to_bv1
    (eoOp : Term) (smtCmp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply eoOp y) x) =
        SmtTerm.ite (smtCmp (__eo_to_smt y) (__eo_to_smt x))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
    (hTy :
      __smtx_typeof (smtCmp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x))
          SmtType.Bool)
    (hEo :
      ∀ w : native_Nat,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) =
          SmtType.BitVec 1)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) := by
  have hIteNN :
      term_has_non_none_type
        (SmtTerm.ite (smtCmp (__eo_to_smt y) (__eo_to_smt x))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
  have hCmpNN :
      term_has_non_none_type (smtCmp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hCond]
    simp
  rcases bv_binop_ret_args_of_non_none hTy hCmpNN with ⟨w, hy, hx⟩
  have hCmpTy :
      __smtx_typeof (smtCmp (__eo_to_smt y) (__eo_to_smt x)) = SmtType.Bool := by
    rw [hTy, hy, hx]
    simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, SmtEval.native_nateq]
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
        SmtType.BitVec 1 := by
    rw [hTranslate, typeof_ite_eq, hCmpTy]
    have hThen : __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
      have hWidth : native_zleq 0 1 = true := by native_decide
      have hMod : native_zeq 1 (native_mod_total 1 (native_int_pow2 1)) = true := by
        native_decide
      have hNat : native_int_to_nat 1 = 1 := by native_decide
      simp [__smtx_typeof, native_ite, native_and, hWidth, hMod, hNat]
    have hElse : __smtx_typeof (SmtTerm.Binary 1 0) = SmtType.BitVec 1 := by
      have hWidth : native_zleq 0 1 = true := by native_decide
      have hMod : native_zeq 0 (native_mod_total 0 (native_int_pow2 1)) = true := by
        native_decide
      have hNat : native_int_to_nat 1 = 1 := by native_decide
      simp [__smtx_typeof, native_ite, native_and, hWidth, hMod, hNat]
    rw [hThen, hElse]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
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

/-- Rewrites `generic_apply_type` for heads that are not datatype selectors/testers. -/
private theorem generic_apply_type_of_non_special_head
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  exact __smtx_typeof.eq_140 f x hSel hTester

private theorem eo_to_smt_distinct_ne_dt_sel
    (xs : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt_distinct xs ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> try cases h
  case Apply f x =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> cases h
    case Apply g y =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_distinct_ne_dt_tester
    (xs : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt_distinct xs ≠ SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f x =>
    cases f <;> try cases h
    case UOp op =>
      cases op <;> cases h
    case Apply g y =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> cases h

private theorem eo_to_smt_distinct_top_ne_dt_sel
    (xs : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) ≠ SmtTerm.DtSel s d i j := by
  intro h
  change
    native_ite (__eo_to_smt_type_is_tlist (__eo_typeof xs))
      (__eo_to_smt_distinct xs) SmtTerm.None =
      SmtTerm.DtSel s d i j at h
  cases hGuard : __eo_to_smt_type_is_tlist (__eo_typeof xs)
  · simp [native_ite, hGuard] at h
  · simp [native_ite, hGuard] at h
    exact eo_to_smt_distinct_ne_dt_sel xs s d i j h

private theorem eo_to_smt_distinct_top_ne_dt_tester
    (xs : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) ≠ SmtTerm.DtTester s d i := by
  intro h
  change
    native_ite (__eo_to_smt_type_is_tlist (__eo_typeof xs))
      (__eo_to_smt_distinct xs) SmtTerm.None =
      SmtTerm.DtTester s d i at h
  cases hGuard : __eo_to_smt_type_is_tlist (__eo_typeof xs)
  · simp [native_ite, hGuard] at h
  · simp [native_ite, hGuard] at h
    exact eo_to_smt_distinct_ne_dt_tester xs s d i h

private theorem eo_to_smt_at_bv_ne_dt_sel
    (a b : SmtTerm) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt__at_bv a b ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases a <;> try (change SmtTerm.None = SmtTerm.DtSel s d i j at h; cases h)
  case Numeral n =>
    cases b <;> try (change SmtTerm.None = SmtTerm.DtSel s d i j at h; cases h)
    case Numeral m =>
      simp [__eo_to_smt__at_bv] at h
      unfold native_ite at h
      split at h <;> cases h

private theorem eo_to_smt_at_bv_ne_dt_tester
    (a b : SmtTerm) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt__at_bv a b ≠ SmtTerm.DtTester s d i := by
  intro h
  cases a <;> try (change SmtTerm.None = SmtTerm.DtTester s d i at h; cases h)
  case Numeral n =>
    cases b <;> try (change SmtTerm.None = SmtTerm.DtTester s d i at h; cases h)
    case Numeral m =>
      simp [__eo_to_smt__at_bv] at h
      unfold native_ite at h
      split at h <;> cases h

private theorem eo_to_smt_tuple_select_ne_dt_sel
    (T : SmtType) (n t : SmtTerm) (s : native_String) (d : SmtDatatype)
    (i j : native_Nat) :
    __eo_to_smt_tuple_select T n t ≠ SmtTerm.DtSel s d i j := by
  intro h
  simp [__eo_to_smt_tuple_select] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h <;> cases h

private theorem eo_to_smt_tuple_select_ne_dt_tester
    (T : SmtType) (n t : SmtTerm) (s : native_String) (d : SmtDatatype)
    (i : native_Nat) :
    __eo_to_smt_tuple_select T n t ≠ SmtTerm.DtTester s d i := by
  intro h
  simp [__eo_to_smt_tuple_select] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h <;> cases h

private theorem eo_to_smt_updater_ne_dt_sel
    (sel t u : SmtTerm) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt_updater sel t u ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases sel <;> cases h

private theorem eo_to_smt_updater_ne_dt_tester
    (sel t u : SmtTerm) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt_updater sel t u ≠ SmtTerm.DtTester s d i := by
  intro h
  cases sel <;> cases h

private theorem eo_to_smt_tuple_update_ne_dt_sel
    (T : SmtType) (n t u : SmtTerm) (s : native_String) (d : SmtDatatype)
    (i j : native_Nat) :
    __eo_to_smt_tuple_update T n t u ≠ SmtTerm.DtSel s d i j := by
  intro h
  simp [__eo_to_smt_tuple_update] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h
    · exact eo_to_smt_updater_ne_dt_sel _ _ _ _ _ _ _ h
    · cases h

private theorem eo_to_smt_tuple_update_ne_dt_tester
    (T : SmtType) (n t u : SmtTerm) (s : native_String) (d : SmtDatatype)
    (i : native_Nat) :
    __eo_to_smt_tuple_update T n t u ≠ SmtTerm.DtTester s d i := by
  intro h
  simp [__eo_to_smt_tuple_update] at h
  split at h <;> try cases h
  case h_1 =>
    unfold native_ite at h
    split at h
    · exact eo_to_smt_updater_ne_dt_tester _ _ _ _ _ _ h
    · cases h

private theorem eo_to_smt_tuple_ne_dt_sel
    (x y : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  change
    SmtTerm.Apply
        (__eo_to_smt_tuple_app_extend (__eo_to_smt y) (__eo_to_smt_type (__eo_typeof x)))
        (__eo_to_smt x) =
      SmtTerm.DtSel s d i j at h
  cases h

private theorem eo_to_smt_tuple_ne_dt_tester
    (x y : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x) ≠
      SmtTerm.DtTester s d i := by
  intro h
  change
    SmtTerm.Apply
        (__eo_to_smt_tuple_app_extend (__eo_to_smt y) (__eo_to_smt_type (__eo_typeof x)))
        (__eo_to_smt x) =
      SmtTerm.DtTester s d i at h
  cases h

private theorem eo_to_smt_tuple_app_extend_ne_dt_sel
    (t : SmtTerm) (T : SmtType) (s : native_String) (d : SmtDatatype)
    (i j : native_Nat) :
    __eo_to_smt_tuple_app_extend t T ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases t <;> try cases h
  case DtCons s0 d0 i0 =>
    cases d0
    · simp [__eo_to_smt_tuple_app_extend] at h
    · rename_i c dTail
      cases dTail
      · cases i0
        · by_cases hs : s0 = "@Tuple"
          · subst hs
            simp [__eo_to_smt_tuple_app_extend] at h
          · simp [__eo_to_smt_tuple_app_extend, hs] at h
        · simp [__eo_to_smt_tuple_app_extend] at h
      · simp [__eo_to_smt_tuple_app_extend] at h

private theorem eo_to_smt_tuple_app_extend_ne_dt_tester
    (t : SmtTerm) (T : SmtType) (s : native_String) (d : SmtDatatype)
    (i : native_Nat) :
    __eo_to_smt_tuple_app_extend t T ≠ SmtTerm.DtTester s d i := by
  intro h
  cases t <;> try cases h
  case DtCons s0 d0 i0 =>
    cases d0
    · simp [__eo_to_smt_tuple_app_extend] at h
    · rename_i c dTail
      cases dTail
      · cases i0
        · by_cases hs : s0 = "@Tuple"
          · subst hs
            simp [__eo_to_smt_tuple_app_extend] at h
          · simp [__eo_to_smt_tuple_app_extend, hs] at h
        · simp [__eo_to_smt_tuple_app_extend] at h
      · simp [__eo_to_smt_tuple_app_extend] at h

private theorem eo_to_smt_re_unfold_ne_dt_sel
    (str re : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt_re_unfold_pos_component str re n ≠ SmtTerm.DtSel s d i j := by
  induction n generalizing str re with
  | zero =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ h

private theorem eo_to_smt_re_unfold_ne_dt_tester
    (str re : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt_re_unfold_pos_component str re n ≠ SmtTerm.DtTester s d i := by
  induction n generalizing str re with
  | zero =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
  | succ n ih =>
      intro h
      cases re <;> simp [__eo_to_smt_re_unfold_pos_component] at h
      case re_concat r1 r2 =>
        exact ih _ _ h

private theorem eo_to_smt_quant_skolemize_ne_dt_sel
    (body : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt_quantifiers_skolemize body n ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases body <;> cases h

private theorem eo_to_smt_quant_skolemize_ne_dt_tester
    (body : SmtTerm) (n : native_Nat)
    (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt_quantifiers_skolemize body n ≠ SmtTerm.DtTester s d i := by
  intro h
  cases body <;> cases h

private theorem eo_to_smt_set_insert_top_ne_dt_sel
    (xs x : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> try cases h
  case Apply f tail =>
    cases f <;> try cases h
    case Apply g head =>
      cases g <;> cases h

private theorem eo_to_smt_set_insert_top_ne_dt_tester
    (xs x : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) xs) x) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f tail =>
    cases f <;> try cases h
    case Apply g head =>
      cases g <;> cases h

private theorem eo_to_smt_exists_top_ne_dt_sel
    (xs body : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> try cases h
  case Apply f vs =>
    cases f <;> try cases h
    case Apply g v =>
      cases g <;> try cases h
      case __eo_List_cons =>
        cases v <;> try cases h
        case Var name T =>
          cases name <;> cases h

private theorem eo_to_smt_exists_top_ne_dt_tester
    (xs body : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) body) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> try cases h
  case Apply f vs =>
    cases f <;> try cases h
    case Apply g v =>
      cases g <;> try cases h
      case __eo_List_cons =>
        cases v <;> try cases h
        case Var name T =>
          cases name <;> cases h

private theorem eo_to_smt_forall_top_ne_dt_sel
    (xs body : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ≠
      SmtTerm.DtSel s d i j := by
  intro h
  cases xs <;> cases h

private theorem eo_to_smt_forall_top_ne_dt_tester
    (xs body : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) body) ≠
      SmtTerm.DtTester s d i := by
  intro h
  cases xs <;> cases h

private theorem eo_to_smt_quant_skolemize_top_ne_dt_sel
    (q idx : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt (Term._at_quantifiers_skolemize q idx) ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change native_ite (native_teq (__eo_is_z idx) (Term.Boolean true))
              (native_ite (native_teq (__eo_is_neg idx) (Term.Boolean false))
                (__eo_to_smt_quantifiers_skolemize
                  (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body))) (__eo_to_smt_nat idx))
                SmtTerm.None) SmtTerm.None =
            SmtTerm.DtSel s d i j at h
          unfold native_ite at h
          split at h <;> try cases h
          split at h <;> try cases h
          exact eo_to_smt_quant_skolemize_ne_dt_sel _ _ _ _ _ _ h

private theorem eo_to_smt_quant_skolemize_top_ne_dt_tester
    (q idx : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt (Term._at_quantifiers_skolemize q idx) ≠ SmtTerm.DtTester s d i := by
  intro h
  cases q <;> try cases h
  case Apply f body =>
    cases f <;> try cases h
    case Apply g xs =>
      cases g <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case «forall» =>
          change native_ite (native_teq (__eo_is_z idx) (Term.Boolean true))
              (native_ite (native_teq (__eo_is_neg idx) (Term.Boolean false))
                (__eo_to_smt_quantifiers_skolemize
                  (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body))) (__eo_to_smt_nat idx))
                SmtTerm.None) SmtTerm.None =
            SmtTerm.DtTester s d i at h
          unfold native_ite at h
          split at h <;> try cases h
          split at h <;> try cases h
          exact eo_to_smt_quant_skolemize_ne_dt_tester _ _ _ _ _ h

private theorem eo_to_smt_apply_ne_dt_sel
    (f x : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __eo_to_smt (Term.Apply f x) ≠ SmtTerm.DtSel s d i j := by
  intro h
  cases f <;> try cases h
  case UOp op =>
    cases op <;> try cases h
    case distinct =>
      exact eo_to_smt_distinct_top_ne_dt_sel x s d i j h
    case _at_bvsize =>
      change native_ite (native_zleq 0 (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
          (SmtTerm.plus
            (SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
            (SmtTerm.Numeral 0)) SmtTerm.None =
        SmtTerm.DtSel s d i j at h
      unfold native_ite at h
      split at h <;> cases h
  case Apply g y =>
    cases g <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at_bv =>
        exact eo_to_smt_at_bv_ne_dt_sel _ _ _ _ _ _ h
      case tuple_select =>
        exact eo_to_smt_tuple_select_ne_dt_sel _ _ _ _ _ _ _ h
      case set_insert =>
        exact eo_to_smt_set_insert_top_ne_dt_sel _ _ _ _ _ _ h
      case «forall» =>
        exact eo_to_smt_forall_top_ne_dt_sel _ _ _ _ _ _ h
      case «exists» =>
        exact eo_to_smt_exists_top_ne_dt_sel _ _ _ _ _ _ h
    case Apply k z =>
      cases k <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case _at_re_unfold_pos_component =>
          change native_ite (native_teq (__eo_is_z x) (Term.Boolean true))
              (native_ite (native_teq (__eo_is_neg x) (Term.Boolean false))
                (__eo_to_smt_re_unfold_pos_component (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt_nat x))
                SmtTerm.None) SmtTerm.None =
            SmtTerm.DtSel s d i j at h
          unfold native_ite at h
          split at h <;> try cases h
          split at h <;> try cases h
          exact eo_to_smt_re_unfold_ne_dt_sel _ _ _ _ _ _ _ h
        case _at_witness_string_length =>
          change native_ite (native_teq (__eo_typeof x) (Term.UOp UserOp.Int))
              (SmtTerm.choice_nth "@x" (__eo_to_smt_type z)
                (SmtTerm.eq
                  (SmtTerm.str_len (SmtTerm.Var "@x" (__eo_to_smt_type z)))
                  (__eo_to_smt y)) 0) SmtTerm.None =
            SmtTerm.DtSel s d i j at h
          unfold native_ite at h
          split at h <;> cases h
        case update =>
          exact eo_to_smt_updater_ne_dt_sel _ _ _ _ _ _ _ h
        case tuple_update =>
          exact eo_to_smt_tuple_update_ne_dt_sel _ _ _ _ _ _ _ _ h

private theorem eo_to_smt_apply_ne_dt_tester
    (f x : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt (Term.Apply f x) ≠ SmtTerm.DtTester s d i := by
  intro h
  cases f <;> try cases h
  case UOp op =>
    cases op <;> try cases h
    case distinct =>
      exact eo_to_smt_distinct_top_ne_dt_tester x s d i h
    case _at_bvsize =>
      change native_ite (native_zleq 0 (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
          (SmtTerm.plus
            (SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
            (SmtTerm.Numeral 0)) SmtTerm.None =
        SmtTerm.DtTester s d i at h
      unfold native_ite at h
      split at h <;> cases h
  case Apply g y =>
    cases g <;> try cases h
    case UOp op =>
      cases op <;> try cases h
      case _at_bv =>
        exact eo_to_smt_at_bv_ne_dt_tester _ _ _ _ _ h
      case tuple_select =>
        exact eo_to_smt_tuple_select_ne_dt_tester _ _ _ _ _ _ h
      case set_insert =>
        exact eo_to_smt_set_insert_top_ne_dt_tester _ _ _ _ _ h
      case «forall» =>
        exact eo_to_smt_forall_top_ne_dt_tester _ _ _ _ _ h
      case «exists» =>
        exact eo_to_smt_exists_top_ne_dt_tester _ _ _ _ _ h
    case Apply k z =>
      cases k <;> try cases h
      case UOp op =>
        cases op <;> try cases h
        case _at_re_unfold_pos_component =>
          change native_ite (native_teq (__eo_is_z x) (Term.Boolean true))
              (native_ite (native_teq (__eo_is_neg x) (Term.Boolean false))
                (__eo_to_smt_re_unfold_pos_component (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt_nat x))
                SmtTerm.None) SmtTerm.None =
            SmtTerm.DtTester s d i at h
          unfold native_ite at h
          split at h <;> try cases h
          split at h <;> try cases h
          exact eo_to_smt_re_unfold_ne_dt_tester _ _ _ _ _ _ h
        case _at_witness_string_length =>
          change native_ite (native_teq (__eo_typeof x) (Term.UOp UserOp.Int))
              (SmtTerm.choice_nth "@x" (__eo_to_smt_type z)
                (SmtTerm.eq
                  (SmtTerm.str_len (SmtTerm.Var "@x" (__eo_to_smt_type z)))
                  (__eo_to_smt y)) 0) SmtTerm.None =
            SmtTerm.DtTester s d i at h
          unfold native_ite at h
          split at h <;> cases h
        case update =>
          exact eo_to_smt_updater_ne_dt_tester _ _ _ _ _ _ h
        case tuple_update =>
          exact eo_to_smt_tuple_update_ne_dt_tester _ _ _ _ _ _ _ h

/-- Rewrites the typing equation for `bvnot`. -/
private theorem typeof_bvnot_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnot t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_37]

/-- Rewrites the typing equation for `bvcomp`. -/
private theorem typeof_bvcomp_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.bvcomp t1 t2) =
      __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) (SmtType.BitVec 1) := by
  rw [__smtx_typeof.eq_44]

/-- Rewrites the typing equation for `bvneg`. -/
private theorem typeof_bvneg_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvneg t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_45]

/-- Rewrites the typing equation for `bvnego`. -/
private theorem typeof_bvnego_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnego t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Bool := by
  rw [__smtx_typeof.eq_70]

/-- Rewrites the typing equation for `seq_unit`. -/
private theorem typeof_seq_unit_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_unit t) =
      __smtx_typeof_guard_wf (__smtx_typeof t)
        (SmtType.Seq (__smtx_typeof t)) := by
  rw [__smtx_typeof.eq_118]

/-- Rewrites the typing equation for `set_empty`. -/
private theorem typeof_set_empty_eq
    (T : SmtType) :
    __smtx_typeof (SmtTerm.set_empty T) =
      __smtx_typeof_guard_wf T (SmtType.Set T) := by
  rw [__smtx_typeof.eq_120]

/-- Rewrites the typing equation for `set_singleton`. -/
private theorem typeof_set_singleton_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.set_singleton t) =
      __smtx_typeof_guard_wf (__smtx_typeof t)
        (SmtType.Set (__smtx_typeof t)) := by
  rw [__smtx_typeof.eq_121]

/-- Rewrites the typing equation for `exists`. -/
private theorem typeof_exists_eq
    (s : native_String) (T : SmtType) (t : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None := by
  rw [__smtx_typeof.eq_134]

/-- Computes the type of applying `none`. -/
private theorem typeof_apply_none_eq
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, smtx_typeof_none]
  simp [__smtx_typeof_apply]

/-- Computes the type of applying a term whose head is itself `none`. -/
private theorem typeof_apply_apply_none_head_eq
    (y x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None y) x) = SmtType.None := by
  have hGeneric : generic_apply_type (SmtTerm.Apply SmtTerm.None y) x := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, typeof_apply_none_eq y]
  simp [__smtx_typeof_apply]

/-- Computes the type of applying a term whose binary head starts from `none`. -/
private theorem typeof_apply_apply_apply_none_head_eq
    (z y x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None z) y) x) =
      SmtType.None := by
  have hGeneric :
      generic_apply_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None z) y) x := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, typeof_apply_apply_none_head_eq z y]
  simp [__smtx_typeof_apply]

/-- Computes the type of a generic apply with a non-function head. -/
private theorem typeof_generic_apply_non_function_head_eq_none
    (f x : SmtTerm)
    (hGeneric : generic_apply_type f x)
    (hFun : ∀ A B, __smtx_typeof f ≠ SmtType.FunType A B)
    (hDtc : ∀ A B, __smtx_typeof f ≠ SmtType.DtcAppType A B) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  rw [hGeneric]
  cases hF : __smtx_typeof f <;> try rfl
  · exact False.elim (hFun _ _ hF)
  · exact False.elim (hDtc _ _ hF)

/-- Computes the type of applying a Boolean literal as a head. -/
private theorem typeof_apply_boolean_head_eq_none
    (b : native_Bool) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Boolean b) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by intro A B h; rw [__smtx_typeof.eq_1] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_1] at h; cases h)

/-- Computes the type of applying an integer literal as a head. -/
private theorem typeof_apply_numeral_head_eq_none
    (n : native_Int) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Numeral n) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by intro A B h; rw [__smtx_typeof.eq_2] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_2] at h; cases h)

/-- Computes the type of applying a rational literal as a head. -/
private theorem typeof_apply_rational_head_eq_none
    (r : native_Rat) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Rational r) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by intro A B h; rw [__smtx_typeof.eq_3] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_3] at h; cases h)

/-- Computes the type of applying a string literal as a head. -/
private theorem typeof_apply_string_head_eq_none
    (s : native_String) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.String s) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s' d i j h; cases h)
      (by intro s' d i h; cases h))
    (by intro A B h; rw [__smtx_typeof.eq_4] at h; cases h)
    (by intro A B h; rw [__smtx_typeof.eq_4] at h; cases h)

/-- Computes the type of applying a bit-vector literal as a head. -/
private theorem typeof_apply_binary_head_eq_none
    (w n : native_Int) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Binary w n) x) = SmtType.None := by
  exact typeof_generic_apply_non_function_head_eq_none _ _
    (generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h))
    (by
      intro A B h
      rw [__smtx_typeof.eq_5] at h
      cases hCond :
          native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hCond] at h)
    (by
      intro A B h
      rw [__smtx_typeof.eq_5] at h
      cases hCond :
          native_and (native_zleq 0 w) (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hCond] at h)

/-- Rewrites the typing equation for unary arithmetic negation. -/
private theorem typeof_uneg_eq
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.uneg t) =
      __smtx_typeof_arith_overload_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_22]

/-- Computes the type of applying a regular-language constant as a head. -/
private theorem typeof_apply_reglan_head_eq_none
    (f x : SmtTerm)
    (hF : __smtx_typeof f = SmtType.RegLan)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  have hGeneric : generic_apply_type f x :=
    generic_apply_type_of_non_special_head f x hSel hTester
  rw [hGeneric, hF]
  rfl

/-- Computes the type of applying the nullary tuple constructor as a head. -/
private theorem typeof_apply_tuple_unit_eq_none
    (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtCons "@Tuple"
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) 0) x) =
      SmtType.None := by
  have hGeneric :
      generic_apply_type
        (SmtTerm.DtCons "@Tuple"
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) 0) x :=
    generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, smtx_typeof_tuple_unit_translation]
  rfl

/-- Computes `__smtx_typeof_apply` for translated `seq_empty`. -/
private theorem smtx_typeof_apply_eo_to_smt_seq_empty_eq_none
    (T X : SmtType) :
    __smtx_typeof_apply (__smtx_typeof (__eo_to_smt_seq_empty T)) X = SmtType.None := by
  cases T with
  | None
  | Bool
  | Int
  | Real
  | RegLan
  | BitVec _
  | Set _
  | Char
  | Datatype _ _
  | TypeRef _
  | USort _
  | Map _ _
  | FunType _ _
  | DtcAppType _ _ =>
      simp [__eo_to_smt_seq_empty, __smtx_typeof_apply]
  | Seq U =>
      rw [show __smtx_typeof (__eo_to_smt_seq_empty (SmtType.Seq U)) =
          __smtx_typeof_guard_wf U (SmtType.Seq U) by
        simp [__eo_to_smt_seq_empty, __smtx_typeof]]
      cases hInh : native_inhabited_type U <;>
      cases hWf : __smtx_type_wf U <;>
        simp [__smtx_typeof_apply, __smtx_typeof_guard_wf, native_ite, hWf]

/-- Computes the type of applying a translated `seq_empty` as a head. -/
private theorem typeof_apply_eo_to_smt_seq_empty_eq_none
    (T : SmtType) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt_seq_empty T) x) = SmtType.None := by
  have hGeneric : generic_apply_type (__eo_to_smt_seq_empty T) x := by
    cases T <;> simp [__eo_to_smt_seq_empty]
    all_goals
      exact generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
  rw [hGeneric]
  exact smtx_typeof_apply_eo_to_smt_seq_empty_eq_none T (__smtx_typeof x)

/-- Closes branches whose SMT translation is already typed as `none`. -/
private theorem eo_to_smt_typeof_matches_translation_of_smt_none
    (t : Term)
    (hNone : __smtx_typeof (__eo_to_smt t) = SmtType.None) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) := by
  intro hNonNone
  exact False.elim (hNonNone hNone)

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

/--
Function-like SMT head types have non-`None` components.  This is the
bridge-free strengthening needed when turning the generic apply case from a
whole-term bridge argument into explicit IHs for the head and argument.
-/
private theorem function_like_head_components_non_none
    (f : SmtTerm) {A B : SmtType}
    (hHead :
      __smtx_typeof f = SmtType.FunType A B ∨
        __smtx_typeof f = SmtType.DtcAppType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  have hNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hNoNone := Smtm.term_type_has_no_none_components_of_non_none f hNN
  rcases hHead with hHead | hHead
  · have hFun : Smtm.type_has_no_none_components (SmtType.FunType A B) := by
      simpa [hHead] using hNoNone
    exact Smtm.type_has_no_none_components_fun_components_non_none hFun
  · have hDtc : Smtm.type_has_no_none_components (SmtType.DtcAppType A B) := by
      simpa [hHead] using hNoNone
    exact Smtm.type_has_no_none_components_dtc_app_components_non_none hDtc

/--
Bridge-free EO-side application typing for function-like SMT heads.

The key extra hypothesis is field well-formedness of the argument type.  That
is the bit needed to turn equality of translated SMT types into syntactic EO
type equality, avoiding the previous circular appeal to the whole translation
theorem.
-/
private theorem eo_to_smt_type_typeof_apply_from_ih_of_fun_like
    (f x : Term) (A B : SmtType)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hHead :
      __smtx_typeof (__eo_to_smt f) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt f) = SmtType.DtcAppType A B)
    (hX : __smtx_typeof (__eo_to_smt x) = A)
    (hEoApply :
      __eo_typeof (Term.Apply f x) =
        __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hArgWF : smtx_type_field_wf_rec A native_reflist_nil)
    (hA : A ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply f x)) = B := by
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
    eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hA
  rcases hHead with hHead | hHead
  · have hFTrans : __eo_to_smt_type (__eo_typeof f) = SmtType.FunType A B := by
      rw [← ihF hFNN]
      exact hHead
    rcases eo_to_smt_type_eq_fun hFTrans with ⟨U, V, hFEq, hU, hV⟩
    have hxEo : __eo_typeof x = U :=
      eo_to_smt_type_injective_of_field_wf_rec hXTrans hU hArgWF
    have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
      rw [hU]
      exact hA
    exact
      (eo_to_smt_type_typeof_apply_of_fun_like
        x f U V
        hEoApply
        (Or.inl hFEq)
        hxEo hUNonNone).trans hV
  · have hFTrans : __eo_to_smt_type (__eo_typeof f) = SmtType.DtcAppType A B := by
      rw [← ihF hFNN]
      exact hHead
    rcases eo_to_smt_type_eq_dtc_app hFTrans with ⟨U, V, hFEq, hU, hV⟩
    have hxEo : __eo_typeof x = U :=
      eo_to_smt_type_injective_of_field_wf_rec hXTrans hU hArgWF
    have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
      rw [hU]
      exact hA
    exact
      (eo_to_smt_type_typeof_apply_of_fun_like
        x f U V
        hEoApply
        (Or.inr hFEq)
        hxEo hUNonNone).trans hV

/-- Bridge-free generic application, once the head argument type is known well-formed. -/
private theorem eo_to_smt_typeof_matches_translation_apply_generic_of_field_wf
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply f x) =
        __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hArgWF :
      ∀ A B,
        (__smtx_typeof (__eo_to_smt f) = SmtType.FunType A B ∨
          __smtx_typeof (__eo_to_smt f) = SmtType.DtcAppType A B) ->
        smtx_type_field_wf_rec A native_reflist_nil)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate] using hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, _hB⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) = B := by
    rw [hTranslate]
    rw [hGeneric]
    exact smtx_typeof_apply_of_head_cases hHead hX hA
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) = B :=
    eo_to_smt_type_typeof_apply_from_ih_of_fun_like
      f x A B ihF ihX hHead hX hEoApply (hArgWF A B hHead) hA
  exact hSmt.trans hEo.symm

/-- A zero-index `choice_nth` function-like type has a well-formed argument field. -/
private theorem choice_nth_fun_like_arg_field_wf
    (s : native_String) (T : SmtType) (body : SmtTerm) {A B : SmtType}
    (hHead :
      __smtx_typeof (SmtTerm.choice_nth s T body 0) = SmtType.FunType A B ∨
        __smtx_typeof (SmtTerm.choice_nth s T body 0) = SmtType.DtcAppType A B) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  have hNN : term_has_non_none_type (SmtTerm.choice_nth s T body 0) := by
    unfold term_has_non_none_type
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hGuard :
      __smtx_typeof (SmtTerm.choice_nth s T body 0) =
        __smtx_typeof_guard_wf T T :=
    Smtm.choice_term_guard_type_of_non_none hNN
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    exact hNN (by rw [hGuard, hNone])
  have hTWF : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hChoiceTy : __smtx_typeof (SmtTerm.choice_nth s T body 0) = T :=
    Smtm.choice_term_typeof_of_non_none hNN
  rcases hHead with hHead | hHead
  · have hTFun : T = SmtType.FunType A B := hChoiceTy.symm.trans hHead
    have hFunWF :
        smtx_type_field_wf_rec (SmtType.FunType A B) native_reflist_nil := by
      exact smtx_type_field_wf_rec_of_type_wf_rec (by
        rw [← hTFun]
        exact smtx_type_wf_rec_of_type_wf (by rw [hTFun]; simp) hTWF)
    exact (fun_type_field_wf_rec_components_of_wf hFunWF).1
  · have hTDtc : T = SmtType.DtcAppType A B := hChoiceTy.symm.trans hHead
    have hBad := hTWF
    rw [hTDtc] at hBad
    simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hBad

/-- An arbitrary-index `choice_nth` function-like type has a well-formed argument field. -/
private theorem choice_nth_fun_like_arg_field_wf_any
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat) {A B : SmtType}
    (hHead :
      __smtx_typeof (SmtTerm.choice_nth s T body n) = SmtType.FunType A B ∨
        __smtx_typeof (SmtTerm.choice_nth s T body n) = SmtType.DtcAppType A B) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  induction n generalizing s T body with
  | zero =>
      exact choice_nth_fun_like_arg_field_wf s T body hHead
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof
                  (SmtTerm.choice_nth s T (SmtTerm.exists s' U body') (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_136, __smtx_typeof.eq_136]
            simp [__smtx_typeof_choice_nth]
          exact ih s' U body' (by simpa [hTyEq] using hHead)
      | _ =>
          exfalso
          rcases hHead with hHead | hHead
          · rw [__smtx_typeof.eq_136] at hHead
            simp [__smtx_typeof_choice_nth] at hHead
          · rw [__smtx_typeof.eq_136] at hHead
            simp [__smtx_typeof_choice_nth] at hHead

/-- Skolemization is either a `choice_nth` chain or `none`, so function-like results have well-formed arguments. -/
private theorem eo_to_smt_quantifiers_skolemize_fun_like_arg_field_wf
    (body : SmtTerm) (n : native_Nat) {A B : SmtType}
    (hHead :
      __smtx_typeof (__eo_to_smt_quantifiers_skolemize body n) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt_quantifiers_skolemize body n) = SmtType.DtcAppType A B) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  cases body with
  | «exists» s T body' =>
      exact choice_nth_fun_like_arg_field_wf_any s T body' n hHead
  | _ =>
      exfalso
      rcases hHead with hHead | hHead
      · simp [__eo_to_smt_quantifiers_skolemize] at hHead
      · simp [__eo_to_smt_quantifiers_skolemize] at hHead

/-- Simplifies EO-to-SMT translation for sequence binary operators returning a sequence. -/
private theorem eo_to_smt_typeof_matches_translation_apply_seq_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_seq_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Seq T)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases seq_binop_args_of_non_none (op := smtOp) hTy hApplyNN with ⟨T, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, hTy]
    simp [__smtx_typeof_seq_op_2, hY, hX, native_ite, native_Teq]
  exact hSmt.trans (hEo T hY hX).symm

/-- Simplifies EO-to-SMT translation for sequence binary operators returning a fixed type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_seq_ret_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_seq_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) ret)
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases seq_binop_args_of_non_none_ret (op := smtOp) hTy hApplyNN with ⟨T, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret := by
    rw [hTranslate, hTy]
    simp [__smtx_typeof_seq_op_2_ret, hY, hX, native_ite, native_Teq]
  exact hSmt.trans (hEo T hY hX).symm

/-- Simplifies EO-to-SMT translation for sequence-char binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_seq_char_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
            ret SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := seq_char_binop_args_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-- Simplifies EO-to-SMT translation for regular-language binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_reglan_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.RegLan)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := reglan_binop_args_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.RegLan := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-- Simplifies EO-to-SMT translation for sequence-char/regular-language binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_seq_char_reglan_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
            ret SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := seq_char_reglan_args_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

private theorem smtx_dt_wf_cons_of_sum_wf_apply
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases hC : __smtx_dt_cons_wf_rec c refs <;>
    cases d <;> simp [__smtx_dt_wf_rec, native_ite, hC] at h ⊢

private theorem smtx_dt_wf_tail_of_sum_wf_apply
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    {refs : RefList}
    (hTail : d ≠ SmtDatatype.null)
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_wf_rec d refs = true := by
  cases d with
  | null =>
      exact False.elim (hTail rfl)
  | sum cTail dTail =>
      cases hC : __smtx_dt_cons_wf_rec c refs <;>
        simp [__smtx_dt_wf_rec, native_ite, hC] at h ⊢
      exact h

private def reflist_subset_apply (xs ys : RefList) : Prop :=
  ∀ s, native_reflist_contains xs s = true -> native_reflist_contains ys s = true

private theorem reflist_subset_insert_same_apply
    {xs ys : RefList} {s : native_String}
    (h : reflist_subset_apply xs ys) :
    reflist_subset_apply (native_reflist_insert xs s) (native_reflist_insert ys s) := by
  intro t ht
  by_cases hts : t = s
  · subst t
    simp [native_reflist_contains, native_reflist_insert]
  · have htXs : native_reflist_contains xs t = true := by
      simpa [native_reflist_contains, native_reflist_insert, hts] using ht
    have htYs := h t htXs
    simpa [native_reflist_contains, native_reflist_insert, hts] using htYs

private theorem reflist_subset_insert_dup_apply
    (refs : RefList) (s : native_String) :
    reflist_subset_apply (native_reflist_insert (native_reflist_insert refs s) s)
      (native_reflist_insert refs s) := by
  intro t ht
  by_cases hts : t = s <;> by_cases htr : t ∈ refs <;>
    simp [native_reflist_contains, native_reflist_insert, hts, htr] at ht ⊢

private theorem reflist_subset_insert_middle_apply
    (refs : RefList) (s t : native_String) :
    reflist_subset_apply (native_reflist_insert refs s)
      (native_reflist_insert (native_reflist_insert refs t) s) := by
  intro u hu
  by_cases hus : u = s <;> by_cases hut : u = t <;> by_cases hur : u ∈ refs <;>
    simp [native_reflist_contains, native_reflist_insert, hus, hut, hur] at hu ⊢

private theorem reflist_subset_insert_swap_apply
    (refs : RefList) (s t : native_String) :
    reflist_subset_apply (native_reflist_insert (native_reflist_insert refs s) t)
      (native_reflist_insert (native_reflist_insert refs t) s) := by
  intro u hu
  by_cases hus : u = s <;> by_cases hut : u = t <;> by_cases hur : u ∈ refs <;>
    simp [native_reflist_contains, native_reflist_insert, hus, hut, hur] at hu ⊢

private def smtx_type_substitute_top_apply (sub : native_String) (d0 : SmtDatatype) :
    SmtType -> SmtType
  | SmtType.Datatype s2 d2 =>
      SmtType.Datatype s2
        (native_ite (native_streq sub s2) d2 (__smtx_dt_substitute sub d0 d2))
  | T => native_ite (native_Teq T (SmtType.TypeRef sub)) (SmtType.Datatype sub d0) T

mutual

private def smtx_type_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) : SmtType -> SmtType
  | SmtType.TypeRef r =>
      if doSub && native_streq r sub then
        SmtType.Datatype sub
          (if doRoot then __smtx_dt_substitute root newRoot base else base)
      else
        SmtType.TypeRef r
  | SmtType.Datatype r d =>
      if doRoot && native_streq r root && decide (d = oldRoot) then
        SmtType.Datatype r newRoot
      else
        SmtType.Datatype r
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
            (doSub && !native_streq r sub) (doRoot && !native_streq r root) d)
  | T => T

private def smtx_dtc_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) : SmtDatatypeCons -> SmtDatatypeCons
  | SmtDatatypeCons.cons T c =>
      SmtDatatypeCons.cons
        (smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T)
        (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot doSub doRoot c)
  | SmtDatatypeCons.unit => SmtDatatypeCons.unit

private def smtx_dt_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) : SmtDatatype -> SmtDatatype
  | SmtDatatype.sum c d =>
      SmtDatatype.sum
        (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot doSub doRoot c)
        (smtx_dt_context_substitute_apply sub base root oldRoot newRoot doSub doRoot d)
  | SmtDatatype.null => SmtDatatype.null

end

private def smtx_chain_type_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) : SmtType -> SmtType
  | SmtType.DtcAppType A B =>
      SmtType.DtcAppType
        (smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot A)
        (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot B)
  | T =>
      smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T

private def smtx_value_dt_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    SmtValue -> SmtValue
  | SmtValue.DtCons s d i =>
      if native_streq s root && decide (d = oldRoot) then
        SmtValue.DtCons s newRoot i
      else
        SmtValue.DtCons s
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
            (!native_streq s sub) (!native_streq s root) d) i
  | SmtValue.Apply f a =>
      SmtValue.Apply
        (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot f)
        (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot a)
  | v => v

private theorem smtx_value_dt_context_substitute_apply_num_args
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (v : SmtValue) ->
      vsm_num_apply_args
          (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v) =
        vsm_num_apply_args v
  | SmtValue.Apply f a => by
      simp [smtx_value_dt_context_substitute_apply, vsm_num_apply_args,
        smtx_value_dt_context_substitute_apply_num_args sub base root oldRoot newRoot f]
  | SmtValue.NotValue => rfl
  | SmtValue.Boolean _ => rfl
  | SmtValue.Numeral _ => rfl
  | SmtValue.Rational _ => rfl
  | SmtValue.Binary _ _ => rfl
  | SmtValue.Map _ => rfl
  | SmtValue.Fun _ => rfl
  | SmtValue.Set _ => rfl
  | SmtValue.Seq _ => rfl
  | SmtValue.Char _ => rfl
  | SmtValue.UValue _ _ => rfl
  | SmtValue.RegLan _ => rfl
  | SmtValue.DtCons sh dh ih => by
      by_cases h :
          native_streq sh root = true ∧ dh = oldRoot <;>
        simp [smtx_value_dt_context_substitute_apply, h, vsm_num_apply_args]

private theorem smtx_value_dt_context_substitute_apply_head_of_root
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (v : SmtValue) -> {i : native_Nat} ->
      __vsm_apply_head v = SmtValue.DtCons root oldRoot i ->
      __vsm_apply_head
          (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v) =
        SmtValue.DtCons root newRoot i
  | SmtValue.DtCons s d i', i, hHead => by
      simp [__vsm_apply_head] at hHead
      rcases hHead with ⟨rfl, hRest⟩
      rcases hRest with ⟨rfl, rfl⟩
      simp [smtx_value_dt_context_substitute_apply, __vsm_apply_head,
        native_streq]
  | SmtValue.Apply f a, i, hHead => by
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons root oldRoot i := by
        simpa [__vsm_apply_head] using hHead
      have hRec :=
        smtx_value_dt_context_substitute_apply_head_of_root
          sub base root oldRoot newRoot f hHeadF
      simpa [smtx_value_dt_context_substitute_apply, __vsm_apply_head] using hRec
  | SmtValue.NotValue, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary _ _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue _ _, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan _, i, hHead => by
      simp [__vsm_apply_head] at hHead

private theorem smtx_value_dt_context_substitute_apply_arg_nth
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (v : SmtValue) -> (j : native_Nat) ->
      __vsm_apply_arg_nth
          (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v) j
          (vsm_num_apply_args
            (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v)) =
        smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot
          (__vsm_apply_arg_nth v j (vsm_num_apply_args v))
  | SmtValue.Apply f a, j => by
      by_cases hEq : native_nateq j (vsm_num_apply_args f) = true
      · simp [smtx_value_dt_context_substitute_apply, __vsm_apply_arg_nth,
          vsm_num_apply_args,
          smtx_value_dt_context_substitute_apply_num_args sub base root oldRoot newRoot f,
          native_ite, hEq]
      · have hArg :=
          smtx_value_dt_context_substitute_apply_arg_nth
            sub base root oldRoot newRoot f j
        simp [smtx_value_dt_context_substitute_apply, __vsm_apply_arg_nth,
          vsm_num_apply_args,
          smtx_value_dt_context_substitute_apply_num_args sub base root oldRoot newRoot f,
          native_ite, hEq]
        simpa [smtx_value_dt_context_substitute_apply_num_args
          sub base root oldRoot newRoot f] using hArg
  | SmtValue.NotValue, _ => rfl
  | SmtValue.Boolean _, _ => rfl
  | SmtValue.Numeral _, _ => rfl
  | SmtValue.Rational _, _ => rfl
  | SmtValue.Binary _ _, _ => rfl
  | SmtValue.Map _, _ => rfl
  | SmtValue.Fun _, _ => rfl
  | SmtValue.Set _, _ => rfl
  | SmtValue.Seq _, _ => rfl
  | SmtValue.Char _, _ => rfl
  | SmtValue.UValue _ _, _ => rfl
  | SmtValue.RegLan _, _ => rfl
  | SmtValue.DtCons sh dh ih, _ => by
      by_cases h :
          native_streq sh root = true ∧ dh = oldRoot <;>
        simp [smtx_value_dt_context_substitute_apply, h, __vsm_apply_arg_nth]

private theorem smtx_dtc_context_substitute_num_sels_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (c : SmtDatatypeCons) ->
      __smtx_dtc_num_sels
          (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot doSub doRoot c) =
        __smtx_dtc_num_sels c
  | SmtDatatypeCons.unit => by
      simp [smtx_dtc_context_substitute_apply, __smtx_dtc_num_sels]
  | SmtDatatypeCons.cons T c => by
      simp [smtx_dtc_context_substitute_apply, __smtx_dtc_num_sels,
        smtx_dtc_context_substitute_num_sels_apply sub base root oldRoot newRoot
          doSub doRoot c]

private theorem smtx_dt_context_substitute_num_sels_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (d : SmtDatatype) -> (i : native_Nat) ->
      __smtx_dt_num_sels
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot doSub doRoot d) i =
        __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;>
        simp [smtx_dt_context_substitute_apply, __smtx_dt_num_sels]
  | SmtDatatype.sum c d, native_nat_zero => by
      simp [smtx_dt_context_substitute_apply, __smtx_dt_num_sels,
        smtx_dtc_context_substitute_num_sels_apply]
  | SmtDatatype.sum c d, native_nat_succ i => by
      simp [smtx_dt_context_substitute_apply, __smtx_dt_num_sels,
        smtx_dt_context_substitute_num_sels_apply sub base root oldRoot newRoot
          doSub doRoot d i]

private theorem smtx_ret_typeof_sel_rec_context_substitute_cons_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (c : SmtDatatypeCons) -> (d : SmtDatatype) -> (j : native_Nat) ->
      __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum
            (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot
              doSub doRoot c)
            (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
              doSub doRoot d))
          native_nat_zero j =
        smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot
          (__smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) native_nat_zero j)
  | SmtDatatypeCons.unit, d, j => by
      cases j <;>
        simp [smtx_dtc_context_substitute_apply, __smtx_ret_typeof_sel_rec,
          smtx_type_context_substitute_apply]
  | SmtDatatypeCons.cons T c, d, native_nat_zero => by
      cases T <;>
        simp [smtx_dtc_context_substitute_apply, __smtx_ret_typeof_sel_rec,
          smtx_type_context_substitute_apply]
  | SmtDatatypeCons.cons T c, d, native_nat_succ j => by
      cases T <;>
        simp [smtx_dtc_context_substitute_apply, __smtx_ret_typeof_sel_rec,
          smtx_ret_typeof_sel_rec_context_substitute_cons_apply
            sub base root oldRoot newRoot doSub doRoot c d j]

private theorem smtx_ret_typeof_sel_rec_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (d : SmtDatatype) -> (i j : native_Nat) ->
      __smtx_ret_typeof_sel_rec
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
            doSub doRoot d) i j =
        smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot
          (__smtx_ret_typeof_sel_rec d i j)
  | SmtDatatype.null, i, j => by
      cases i <;> cases j <;>
        simp [smtx_dt_context_substitute_apply, __smtx_ret_typeof_sel_rec,
          smtx_type_context_substitute_apply]
  | SmtDatatype.sum c d, native_nat_zero, j => by
      simpa [smtx_dt_context_substitute_apply] using
        smtx_ret_typeof_sel_rec_context_substitute_cons_apply
          sub base root oldRoot newRoot doSub doRoot c d j
  | SmtDatatype.sum c d, native_nat_succ i, j => by
      simpa [smtx_dt_context_substitute_apply, __smtx_ret_typeof_sel_rec] using
        smtx_ret_typeof_sel_rec_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot d i j

private theorem smtx_typeof_dt_cons_value_rec_context_substitute_cons_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool)
    (T : SmtType) :
    (c : SmtDatatypeCons) -> (d : SmtDatatype) ->
      __smtx_typeof_dt_cons_value_rec
          (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T)
          (SmtDatatype.sum
            (smtx_dtc_context_substitute_apply sub base root oldRoot newRoot
              doSub doRoot c)
            (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
              doSub doRoot d))
          native_nat_zero =
        smtx_chain_type_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot
          (__smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) native_nat_zero)
  | SmtDatatypeCons.unit, d => by
      simp [smtx_dtc_context_substitute_apply, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatypeCons.cons U c, d => by
      simp [smtx_dtc_context_substitute_apply, __smtx_typeof_dt_cons_value_rec,
        smtx_chain_type_context_substitute_apply,
        smtx_typeof_dt_cons_value_rec_context_substitute_cons_apply
          sub base root oldRoot newRoot doSub doRoot T c d]

private theorem smtx_typeof_dt_cons_value_rec_context_substitute_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool)
    (T : SmtType) :
    (d : SmtDatatype) -> (i : native_Nat) ->
      __smtx_typeof_dt_cons_value_rec
          (smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T)
          (smtx_dt_context_substitute_apply sub base root oldRoot newRoot doSub doRoot d)
          i =
        smtx_chain_type_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot
          (__smtx_typeof_dt_cons_value_rec T d i)
  | SmtDatatype.null, i => by
      cases i <;>
        simp [smtx_dt_context_substitute_apply, __smtx_typeof_dt_cons_value_rec,
          smtx_chain_type_context_substitute_apply, smtx_type_context_substitute_apply]
  | SmtDatatype.sum c d, native_nat_zero => by
      simpa [smtx_dt_context_substitute_apply] using
        smtx_typeof_dt_cons_value_rec_context_substitute_cons_apply
          sub base root oldRoot newRoot doSub doRoot T c d
  | SmtDatatype.sum c d, native_nat_succ i => by
      simpa [smtx_dt_context_substitute_apply, __smtx_typeof_dt_cons_value_rec] using
        smtx_typeof_dt_cons_value_rec_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot T d i

private theorem smtx_type_context_substitute_ne_none_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (T : SmtType) ->
      T ≠ SmtType.None ->
      smtx_type_context_substitute_apply sub base root oldRoot newRoot doSub doRoot T ≠
        SmtType.None
  | SmtType.None, h => by
      exact False.elim (h rfl)
  | SmtType.TypeRef r, _h => by
      by_cases hSub : doSub && native_streq r sub <;>
        simp [smtx_type_context_substitute_apply, hSub]
  | SmtType.Datatype r d, _h => by
      by_cases hRoot : doRoot && native_streq r root && decide (d = oldRoot) <;>
        simp [smtx_type_context_substitute_apply, hRoot]
  | SmtType.DtcAppType A B, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Bool, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Int, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Real, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.RegLan, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.BitVec w, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Map A B, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Set A, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Seq A, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.Char, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.USort i, _h => by
      simp [smtx_type_context_substitute_apply]
  | SmtType.FunType A B, _h => by
      simp [smtx_type_context_substitute_apply]

private theorem smtx_chain_type_context_substitute_ne_none_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool) :
    (T : SmtType) ->
      T ≠ SmtType.None ->
      smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot
          doSub doRoot T ≠
        SmtType.None
  | SmtType.DtcAppType A B, _h => by
      simp [smtx_chain_type_context_substitute_apply]
  | SmtType.None, h => by
      exact False.elim (h rfl)
  | SmtType.TypeRef r, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot (SmtType.TypeRef r) h
  | SmtType.Datatype r d, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot (SmtType.Datatype r d) h
  | SmtType.Bool, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot SmtType.Bool h
  | SmtType.Int, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot SmtType.Int h
  | SmtType.Real, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot SmtType.Real h
  | SmtType.RegLan, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot SmtType.RegLan h
  | SmtType.BitVec w, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot (SmtType.BitVec w) h
  | SmtType.Map A B, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot (SmtType.Map A B) h
  | SmtType.Set A, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot (SmtType.Set A) h
  | SmtType.Seq A, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot (SmtType.Seq A) h
  | SmtType.Char, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot SmtType.Char h
  | SmtType.USort i, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot (SmtType.USort i) h
  | SmtType.FunType A B, h => by
      simpa [smtx_chain_type_context_substitute_apply] using
        smtx_type_context_substitute_ne_none_apply
          sub base root oldRoot newRoot doSub doRoot (SmtType.FunType A B) h

private theorem smtx_ret_typeof_sel_rec_context_substitute_ne_none_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool)
    (d : SmtDatatype) (i j : native_Nat)
    (h :
      __smtx_ret_typeof_sel_rec d i j ≠ SmtType.None) :
    __smtx_ret_typeof_sel_rec
        (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
          doSub doRoot d) i j ≠ SmtType.None := by
  rw [smtx_ret_typeof_sel_rec_context_substitute_apply]
  exact smtx_type_context_substitute_ne_none_apply
    sub base root oldRoot newRoot doSub doRoot
    (__smtx_ret_typeof_sel_rec d i j) h

private theorem smtx_typeof_dt_cons_value_rec_context_substitute_ne_none_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (doSub doRoot : Bool)
    (T : SmtType) (d : SmtDatatype) (i : native_Nat)
    (h :
      __smtx_typeof_dt_cons_value_rec T d i ≠ SmtType.None) :
    __smtx_typeof_dt_cons_value_rec
        (smtx_chain_type_context_substitute_apply
          sub base root oldRoot newRoot doSub doRoot T)
        (smtx_dt_context_substitute_apply sub base root oldRoot newRoot
          doSub doRoot d)
        i ≠ SmtType.None := by
  rw [smtx_typeof_dt_cons_value_rec_context_substitute_apply]
  exact smtx_chain_type_context_substitute_ne_none_apply
    sub base root oldRoot newRoot doSub doRoot
    (__smtx_typeof_dt_cons_value_rec T d i) h

private theorem smtx_ret_typeof_sel_rec_substitute_cons_apply
    (sub : native_String) (base : SmtDatatype) :
    (c : SmtDatatypeCons) -> (d : SmtDatatype) -> (j : native_Nat) ->
      __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum (__smtx_dtc_substitute sub base c)
            (__smtx_dt_substitute sub base d)) native_nat_zero j =
        smtx_type_substitute_top_apply sub base
          (__smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) native_nat_zero j)
  | SmtDatatypeCons.unit, d, j => by
      cases j <;>
        simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
          smtx_type_substitute_top_apply, native_ite, native_Teq]
  | SmtDatatypeCons.cons T c, d, native_nat_zero => by
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
          smtx_type_substitute_top_apply, native_ite, native_Teq, native_streq]
  | SmtDatatypeCons.cons T c, d, native_nat_succ j => by
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
          smtx_ret_typeof_sel_rec_substitute_cons_apply sub base c d j]

private theorem smtx_ret_typeof_sel_rec_substitute_apply
    (sub : native_String) (base : SmtDatatype) :
    (d : SmtDatatype) -> (i j : native_Nat) ->
      __smtx_ret_typeof_sel_rec (__smtx_dt_substitute sub base d) i j =
        smtx_type_substitute_top_apply sub base
          (__smtx_ret_typeof_sel_rec d i j)
  | SmtDatatype.null, i, j => by
      cases i <;> cases j <;>
        simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec,
          smtx_type_substitute_top_apply, native_ite, native_Teq]
  | SmtDatatype.sum c d, native_nat_zero, j => by
      simpa [__smtx_dt_substitute] using
        smtx_ret_typeof_sel_rec_substitute_cons_apply sub base c d j
  | SmtDatatype.sum c d, native_nat_succ i, j => by
      simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using
        smtx_ret_typeof_sel_rec_substitute_apply sub base d i j

private theorem smtx_ret_typeof_sel_rec_field_wf_of_wf_apply :
    (d : SmtDatatype) -> (i j : native_Nat) -> {refs : RefList} ->
      __smtx_dt_wf_rec d refs = true ->
      j < __smtx_dt_num_sels d i ->
      smtx_type_field_wf_rec (__smtx_ret_typeof_sel_rec d i j) refs
  | SmtDatatype.null, i, j, refs, hWf, hj => by
      cases i <;> simp [__smtx_dt_wf_rec] at hWf hj
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, j, refs, hWf, hj => by
      cases j <;> simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hj
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, native_nat_zero,
      native_nat_zero, refs, hWf, _hj => by
      have hCons :
          __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      simpa [__smtx_ret_typeof_sel_rec] using
        smtx_type_field_wf_rec_of_cons_wf hCons
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, native_nat_zero,
      native_nat_succ j, refs, hWf, hj => by
      have hCons :
          __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      have hTailCons : __smtx_dt_cons_wf_rec c refs = true :=
        smtx_dt_cons_wf_rec_tail_of_true hCons
      have hTailWf : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true := by
        cases d with
        | null =>
            simpa [__smtx_dt_wf_rec] using hTailCons
        | sum cTail dTail =>
            have hDTail :
                __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true :=
              smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
            simp [__smtx_dt_wf_rec, native_ite, hTailCons, hDTail]
      have hj' : j < __smtx_dt_num_sels (SmtDatatype.sum c d) native_nat_zero := by
        simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using hj
      simpa [__smtx_ret_typeof_sel_rec] using
        smtx_ret_typeof_sel_rec_field_wf_of_wf_apply
          (SmtDatatype.sum c d) native_nat_zero j hTailWf hj'
  | SmtDatatype.sum c d, native_nat_succ i, j, refs, hWf, hj => by
      cases d with
      | null =>
          simp [__smtx_dt_num_sels] at hj
      | sum cTail dTail =>
          have hTailWf :
              __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true :=
            smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
          have hj' : j < __smtx_dt_num_sels (SmtDatatype.sum cTail dTail) i := by
            simpa [__smtx_dt_num_sels] using hj
          simpa [__smtx_ret_typeof_sel_rec] using
            smtx_ret_typeof_sel_rec_field_wf_of_wf_apply
              (SmtDatatype.sum cTail dTail) i j hTailWf hj'

private theorem smtx_dtc_substitute_cons_tail_lt_apply
    (sub : native_String) (base : SmtDatatype)
    (T : SmtType) (c : SmtDatatypeCons) {j : native_Nat}
    (hj :
      (native_nat_succ j) <
        __smtx_dtc_num_sels
          (__smtx_dtc_substitute sub base (SmtDatatypeCons.cons T c))) :
    j < __smtx_dtc_num_sels (__smtx_dtc_substitute sub base c) := by
  cases T <;>
    simpa [__smtx_dtc_substitute, __smtx_dtc_num_sels] using hj

private theorem smtx_ret_typeof_sel_rec_substitute_cons_succ_apply
    (sub : native_String) (base : SmtDatatype)
    (T : SmtType) (c : SmtDatatypeCons) (d : SmtDatatype)
    (j : native_Nat) :
    __smtx_ret_typeof_sel_rec
        (SmtDatatype.sum
          (__smtx_dtc_substitute sub base (SmtDatatypeCons.cons T c))
          (__smtx_dt_substitute sub base d))
        native_nat_zero (native_nat_succ j) =
      __smtx_ret_typeof_sel_rec
        (SmtDatatype.sum (__smtx_dtc_substitute sub base c)
          (__smtx_dt_substitute sub base d))
        native_nat_zero j := by
  cases T <;>
    simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec]

private theorem smtx_ret_typeof_sel_rec_substitute_non_chain_or_datatype_of_wf_apply
    (sub : native_String) (base : SmtDatatype) :
    (d : SmtDatatype) -> (i j : native_Nat) -> {refs : RefList} ->
      __smtx_dt_wf_rec d (native_reflist_insert refs sub) = true ->
      j < __smtx_dt_num_sels (__smtx_dt_substitute sub base d) i ->
      (¬ dt_cons_chain_result
          (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute sub base d) i j)) ∨
        ∃ s2 d2,
          __smtx_ret_typeof_sel_rec (__smtx_dt_substitute sub base d) i j =
            SmtType.Datatype s2 d2
  | SmtDatatype.null, i, j, refs, hWf, hj => by
      cases i <;> simp [__smtx_dt_wf_rec] at hWf hj
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, j, refs, hWf, hj => by
      cases j <;>
        simp [__smtx_dt_substitute, __smtx_dtc_substitute,
          __smtx_dt_num_sels, __smtx_dtc_num_sels] at hj
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, native_nat_zero,
      native_nat_zero, refs, hWf, _hj => by
      have hCons :
          __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c)
              (native_reflist_insert refs sub) = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      cases T with
      | TypeRef r =>
          by_cases hEq : r = sub
          · subst r
            exact Or.inr (by
              refine ⟨sub, base, ?_⟩
              simp [__smtx_dt_substitute, __smtx_dtc_substitute,
                __smtx_ret_typeof_sel_rec, native_ite, native_Teq])
          · exact Or.inl (by
              simp [__smtx_dt_substitute, __smtx_dtc_substitute,
                __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
                native_ite, native_Teq, hEq])
      | None =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hCons
      | DtcAppType A B =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hCons
      | Datatype s2 d2 =>
          exact Or.inr (by
            refine ⟨s2, native_ite (native_streq sub s2) d2
              (__smtx_dt_substitute sub base d2), ?_⟩
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec])
      | Bool =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | Int =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | Real =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | RegLan =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hCons
      | BitVec w =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | Map A B =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | Set A =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | Seq A =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | Char =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | USort i =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
      | FunType A B =>
          exact Or.inl (by
            simp [__smtx_dt_substitute, __smtx_dtc_substitute,
              __smtx_ret_typeof_sel_rec, dt_cons_chain_result,
              native_ite, native_Teq])
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, native_nat_zero,
      native_nat_succ j, refs, hWf, hj => by
      have hCons :
          __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c)
              (native_reflist_insert refs sub) = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      have hTailCons :
          __smtx_dt_cons_wf_rec c (native_reflist_insert refs sub) = true :=
        smtx_dt_cons_wf_rec_tail_of_true hCons
      have hTailWf :
          __smtx_dt_wf_rec (SmtDatatype.sum c d)
              (native_reflist_insert refs sub) = true := by
        cases d with
        | null =>
            simpa [__smtx_dt_wf_rec] using hTailCons
        | sum cTail dTail =>
            have hDTail :
                __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail)
                    (native_reflist_insert refs sub) = true :=
              smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
            simp [__smtx_dt_wf_rec, native_ite, hTailCons, hDTail]
      have hj' :
          j <
            __smtx_dt_num_sels
              (__smtx_dt_substitute sub base (SmtDatatype.sum c d))
              native_nat_zero := by
        simpa [__smtx_dt_substitute, __smtx_dt_num_sels] using
          smtx_dtc_substitute_cons_tail_lt_apply sub base T c hj
      have hRec :=
        smtx_ret_typeof_sel_rec_substitute_non_chain_or_datatype_of_wf_apply
          sub base (SmtDatatype.sum c d) native_nat_zero j hTailWf hj'
      have hRet :=
        smtx_ret_typeof_sel_rec_substitute_cons_succ_apply
          sub base T c d j
      simpa [__smtx_dt_substitute, hRet] using hRec
  | SmtDatatype.sum c d, native_nat_succ i, j, refs, hWf, hj => by
      cases d with
      | null =>
          simp [__smtx_dt_substitute, __smtx_dt_num_sels] at hj
      | sum cTail dTail =>
          have hTailWf :
              __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail)
                  (native_reflist_insert refs sub) = true :=
            smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
          have hj' :
              j <
                __smtx_dt_num_sels
                  (__smtx_dt_substitute sub base (SmtDatatype.sum cTail dTail))
                  i := by
            simpa [__smtx_dt_substitute, __smtx_dt_num_sels] using hj
          simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using
            smtx_ret_typeof_sel_rec_substitute_non_chain_or_datatype_of_wf_apply
              sub base (SmtDatatype.sum cTail dTail) i j hTailWf hj'

mutual

private theorem smtx_type_wf_rec_mono_apply :
    (T : SmtType) -> {refs refs' : RefList} ->
      reflist_subset_apply refs refs' ->
      __smtx_type_wf_rec T refs = true ->
      __smtx_type_wf_rec T refs' = true
  | SmtType.Datatype s d, refs, refs', hSub, hWf => by
      exact smtx_dt_wf_rec_mono_apply d
        (reflist_subset_insert_same_apply hSub) (by
          simpa [__smtx_type_wf_rec] using hWf)
  | SmtType.TypeRef _s, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType _A _B, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.None, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Bool, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec]
  | SmtType.Int, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec]
  | SmtType.Real, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec]
  | SmtType.RegLan, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.BitVec _w, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec]
  | SmtType.Map _A _B, refs, refs', hSub, hWf => by
      simpa [__smtx_type_wf_rec] using hWf
  | SmtType.Set _A, refs, refs', hSub, hWf => by
      simpa [__smtx_type_wf_rec] using hWf
  | SmtType.Seq _A, refs, refs', hSub, hWf => by
      simpa [__smtx_type_wf_rec] using hWf
  | SmtType.Char, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec]
  | SmtType.USort _i, refs, refs', hSub, hWf => by
      simp [__smtx_type_wf_rec]
  | SmtType.FunType _A _B, refs, refs', hSub, hWf => by
      simpa [__smtx_type_wf_rec] using hWf

private theorem smtx_dtc_wf_rec_mono_apply :
    (c : SmtDatatypeCons) -> {refs refs' : RefList} ->
      reflist_subset_apply refs refs' ->
      __smtx_dt_cons_wf_rec c refs = true ->
      __smtx_dt_cons_wf_rec c refs' = true
  | SmtDatatypeCons.unit, refs, refs', hSub, hWf => by
      simp [__smtx_dt_cons_wf_rec]
  | SmtDatatypeCons.cons T c, refs, refs', hSub, hWf => by
      cases T with
      | TypeRef s =>
          have hPair :
              native_reflist_contains refs s = true ∧
                __smtx_dt_cons_wf_rec c refs = true := by
            simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
          have hRef' : native_reflist_contains refs' s = true :=
            hSub s hPair.1
          have hTail' : __smtx_dt_cons_wf_rec c refs' = true :=
            smtx_dtc_wf_rec_mono_apply c hSub hPair.2
          simp [__smtx_dt_cons_wf_rec, native_ite, hRef', hTail']
      | None =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
      | DtcAppType A B =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
      | Datatype s d =>
          have hInh :
              native_inhabited_type (SmtType.Datatype s d) = true := by
            have hAll :
                native_inhabited_type (SmtType.Datatype s d) = true ∧
                  __smtx_type_wf_rec (SmtType.Datatype s d) refs = true ∧
                    __smtx_dt_cons_wf_rec c refs = true := by
              simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
            exact hAll.1
          have hField :
              __smtx_type_wf_rec (SmtType.Datatype s d) refs = true :=
            by
              have hField' :
                  smtx_type_field_wf_rec (SmtType.Datatype s d) refs :=
                smtx_type_field_wf_rec_of_cons_wf hWf
              simpa [smtx_type_field_wf_rec] using hField'
          have hTail : __smtx_dt_cons_wf_rec c refs = true :=
            smtx_dt_cons_wf_rec_tail_of_true hWf
          have hField' :
              __smtx_type_wf_rec (SmtType.Datatype s d) refs' = true :=
            smtx_type_wf_rec_mono_apply (SmtType.Datatype s d) hSub hField
          have hTail' : __smtx_dt_cons_wf_rec c refs' = true :=
            smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, native_ite, hInh, hField', hTail']
      | Bool =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, hTail']
      | Int =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, hTail']
      | Real =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, hTail']
      | RegLan =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
      | BitVec w =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, hTail']
      | Map A B =>
          have hInh :
              native_inhabited_type (SmtType.Map A B) = true := by
            have hAll :
                native_inhabited_type (SmtType.Map A B) = true ∧
                  __smtx_type_wf_rec (SmtType.Map A B) refs = true ∧
                    __smtx_dt_cons_wf_rec c refs = true := by
              simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
            exact hAll.1
          have hField :
              __smtx_type_wf_rec (SmtType.Map A B) refs = true := by
            have hField' : smtx_type_field_wf_rec (SmtType.Map A B) refs :=
              smtx_type_field_wf_rec_of_cons_wf hWf
            simpa [smtx_type_field_wf_rec] using hField'
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hField' :=
            smtx_type_wf_rec_mono_apply (SmtType.Map A B) hSub hField
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, native_ite, hInh, hField', hTail']
      | Set A =>
          have hField :
              __smtx_type_wf_rec (SmtType.Set A) refs = true := by
            have hField' : smtx_type_field_wf_rec (SmtType.Set A) refs :=
              smtx_type_field_wf_rec_of_cons_wf hWf
            simpa [smtx_type_field_wf_rec] using hField'
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hField' :=
            smtx_type_wf_rec_mono_apply (SmtType.Set A) hSub hField
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, native_ite, hField', hTail']
      | Seq A =>
          have hField :
              __smtx_type_wf_rec (SmtType.Seq A) refs = true := by
            have hField' : smtx_type_field_wf_rec (SmtType.Seq A) refs :=
              smtx_type_field_wf_rec_of_cons_wf hWf
            simpa [smtx_type_field_wf_rec] using hField'
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hField' :=
            smtx_type_wf_rec_mono_apply (SmtType.Seq A) hSub hField
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, native_ite, hField', hTail']
      | Char =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, hTail']
      | USort i =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, hTail']
      | FunType A B =>
          have hInh :
              native_inhabited_type (SmtType.FunType A B) = true := by
            have hAll :
                native_inhabited_type (SmtType.FunType A B) = true ∧
                  __smtx_type_wf_rec (SmtType.FunType A B) refs = true ∧
                    __smtx_dt_cons_wf_rec c refs = true := by
              simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
            exact hAll.1
          have hField :
              __smtx_type_wf_rec (SmtType.FunType A B) refs = true := by
            have hField' : smtx_type_field_wf_rec (SmtType.FunType A B) refs :=
              smtx_type_field_wf_rec_of_cons_wf hWf
            simpa [smtx_type_field_wf_rec] using hField'
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hField' :=
            smtx_type_wf_rec_mono_apply (SmtType.FunType A B) hSub hField
          have hTail' := smtx_dtc_wf_rec_mono_apply c hSub hTail
          simp [__smtx_dt_cons_wf_rec, native_ite, hInh, hField', hTail']

private theorem smtx_dt_wf_rec_mono_apply :
    (d : SmtDatatype) -> {refs refs' : RefList} ->
      reflist_subset_apply refs refs' ->
      __smtx_dt_wf_rec d refs = true ->
      __smtx_dt_wf_rec d refs' = true
  | SmtDatatype.null, refs, refs', hSub, hWf => by
      simp [__smtx_dt_wf_rec] at hWf
  | SmtDatatype.sum c SmtDatatype.null, refs, refs', hSub, hWf => by
      exact smtx_dtc_wf_rec_mono_apply c hSub (by
        simpa [__smtx_dt_wf_rec] using hWf)
  | SmtDatatype.sum c (SmtDatatype.sum cTail dTail), refs, refs', hSub, hWf => by
      have hCons : __smtx_dt_cons_wf_rec c refs = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      have hTail :
          __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true := by
        simpa [__smtx_dt_wf_rec, native_ite, hCons] using hWf
      have hCons' := smtx_dtc_wf_rec_mono_apply c hSub hCons
      have hTail' :=
        smtx_dt_wf_rec_mono_apply (SmtDatatype.sum cTail dTail) hSub hTail
      simp [__smtx_dt_wf_rec, native_ite, hCons', hTail']

end

/-
Substituting a fixed datatype for its recursive reference preserves datatype
well-formedness for a target datatype.

The remaining hard case is semantic rather than list-shaped: a nested datatype
field produces a fresh `native_inhabited_type` obligation for the substituted
datatype, so the proof needs inhabitance preservation for datatype substitution.
-/

private def smtx_value_dt_substitute_apply
    (sub : native_String) (base : SmtDatatype) : SmtValue -> SmtValue
  | SmtValue.DtCons s d i =>
      SmtValue.DtCons s
        (native_ite (native_streq sub s) d (__smtx_dt_substitute sub base d)) i
  | SmtValue.Apply f a =>
      match __vsm_apply_head f with
      | SmtValue.DtCons s _ _ =>
          native_ite (native_streq sub s) (SmtValue.Apply f a)
            (SmtValue.Apply (smtx_value_dt_substitute_apply sub base f)
              (smtx_value_dt_substitute_apply sub base a))
      | _ =>
          SmtValue.Apply (smtx_value_dt_substitute_apply sub base f)
            (smtx_value_dt_substitute_apply sub base a)
  | v => v

private theorem smtx_value_dt_substitute_apply_num_args
    (sub : native_String) (base : SmtDatatype) :
    (v : SmtValue) ->
      vsm_num_apply_args (smtx_value_dt_substitute_apply sub base v) =
        vsm_num_apply_args v
  | SmtValue.Apply f a => by
      cases hHead : __vsm_apply_head f
      case DtCons s d i =>
        cases hEq : native_streq sub s <;>
          simp [smtx_value_dt_substitute_apply, hHead, native_ite, hEq,
            vsm_num_apply_args, smtx_value_dt_substitute_apply_num_args sub base f]
      all_goals
        simp [smtx_value_dt_substitute_apply, hHead,
          vsm_num_apply_args, smtx_value_dt_substitute_apply_num_args sub base f]
  | SmtValue.NotValue => rfl
  | SmtValue.Boolean _ => rfl
  | SmtValue.Numeral _ => rfl
  | SmtValue.Rational _ => rfl
  | SmtValue.Binary _ _ => rfl
  | SmtValue.Map _ => rfl
  | SmtValue.Fun _ => rfl
  | SmtValue.Set _ => rfl
  | SmtValue.Seq _ => rfl
  | SmtValue.Char _ => rfl
  | SmtValue.UValue _ _ => rfl
  | SmtValue.RegLan _ => rfl
  | SmtValue.DtCons _ _ _ => rfl

private theorem smtx_value_dt_substitute_apply_head_of_dt_cons
    (sub : native_String) (base : SmtDatatype) :
    (v : SmtValue) -> {s : native_String} -> {d : SmtDatatype} -> {i : native_Nat} ->
      __vsm_apply_head v = SmtValue.DtCons s d i ->
      __vsm_apply_head (smtx_value_dt_substitute_apply sub base v) =
        SmtValue.DtCons s
          (native_ite (native_streq sub s) d (__smtx_dt_substitute sub base d)) i
  | SmtValue.DtCons s' d' i', s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
      rcases hHead with ⟨rfl, hRest⟩
      rcases hRest with ⟨rfl, rfl⟩
      simp [smtx_value_dt_substitute_apply, __vsm_apply_head]
  | SmtValue.Apply f a, s, d, i, hHead => by
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons s d i := by
        simpa [__vsm_apply_head] using hHead
      have hRec :=
        smtx_value_dt_substitute_apply_head_of_dt_cons sub base f hHeadF
      cases hEq : native_streq sub s <;>
        simp [smtx_value_dt_substitute_apply, __vsm_apply_head, hHeadF,
          native_ite, hEq, hRec]
  | SmtValue.NotValue, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary _ _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue _ _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan _, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead

private theorem smtx_value_dt_substitute_apply_of_shadowed_head
    (sub : native_String) (base : SmtDatatype) :
    (v : SmtValue) -> {d : SmtDatatype} -> {i : native_Nat} ->
      __vsm_apply_head v = SmtValue.DtCons sub d i ->
      smtx_value_dt_substitute_apply sub base v = v
  | SmtValue.DtCons s d i, d', i', hHead => by
      simp [__vsm_apply_head] at hHead
      rcases hHead with ⟨rfl, hRest⟩
      rcases hRest with ⟨rfl, rfl⟩
      simp [smtx_value_dt_substitute_apply, native_streq, native_ite]
  | SmtValue.Apply f a, d, i, hHead => by
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons sub d i := by
        simpa [__vsm_apply_head] using hHead
      simp [smtx_value_dt_substitute_apply, hHeadF, native_streq, native_ite]
  | SmtValue.NotValue, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary _ _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue _ _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan _, d, i, hHead => by
      simp [__vsm_apply_head] at hHead

private theorem smtx_value_dt_substitute_apply_arg_nth
    (sub : native_String) (base : SmtDatatype) :
    (v : SmtValue) -> (j : native_Nat) ->
      (∀ {s : native_String} {d : SmtDatatype} {i : native_Nat},
        __vsm_apply_head v = SmtValue.DtCons s d i -> s ≠ sub) ->
      __vsm_apply_arg_nth (smtx_value_dt_substitute_apply sub base v) j
          (vsm_num_apply_args (smtx_value_dt_substitute_apply sub base v)) =
        smtx_value_dt_substitute_apply sub base
          (__vsm_apply_arg_nth v j (vsm_num_apply_args v))
  | SmtValue.Apply f a, j, hNoShadow => by
      have hNoShadowF :
          ∀ {s : native_String} {d : SmtDatatype} {i : native_Nat},
            __vsm_apply_head f = SmtValue.DtCons s d i -> s ≠ sub := by
        intro s d i hHead
        exact hNoShadow (by simpa [__vsm_apply_head] using hHead)
      cases hHead : __vsm_apply_head f
      case DtCons s d i =>
        have hNe : s ≠ sub := hNoShadowF hHead
        have hStreq : native_streq sub s = false := by
          cases hEq : native_streq sub s <;> simp [native_streq] at hEq ⊢
          exact False.elim (hNe hEq.symm)
        by_cases hEq : native_nateq j (vsm_num_apply_args f) = true
        · simp [smtx_value_dt_substitute_apply, hHead, __vsm_apply_arg_nth,
            vsm_num_apply_args, native_ite, hStreq,
            smtx_value_dt_substitute_apply_num_args sub base f, hEq]
        · have hArg := smtx_value_dt_substitute_apply_arg_nth sub base f j hNoShadowF
          simp [smtx_value_dt_substitute_apply, hHead, __vsm_apply_arg_nth,
            vsm_num_apply_args, native_ite, hStreq,
            smtx_value_dt_substitute_apply_num_args sub base f, hEq]
          simpa [smtx_value_dt_substitute_apply_num_args sub base f] using hArg
      all_goals
        by_cases hEq : native_nateq j (vsm_num_apply_args f) = true
        · simp [smtx_value_dt_substitute_apply, hHead, __vsm_apply_arg_nth,
            vsm_num_apply_args, native_ite,
            smtx_value_dt_substitute_apply_num_args sub base f, hEq]
        · have hArg := smtx_value_dt_substitute_apply_arg_nth sub base f j hNoShadowF
          simp [smtx_value_dt_substitute_apply, hHead, __vsm_apply_arg_nth,
            vsm_num_apply_args, native_ite,
            smtx_value_dt_substitute_apply_num_args sub base f, hEq]
          simpa [smtx_value_dt_substitute_apply_num_args sub base f] using hArg
  | SmtValue.NotValue, _, _ => rfl
  | SmtValue.Boolean _, _, _ => rfl
  | SmtValue.Numeral _, _, _ => rfl
  | SmtValue.Rational _, _, _ => rfl
  | SmtValue.Binary _ _, _, _ => rfl
  | SmtValue.Map _, _, _ => rfl
  | SmtValue.Fun _, _, _ => rfl
  | SmtValue.Set _, _, _ => rfl
  | SmtValue.Seq _, _, _ => rfl
  | SmtValue.Char _, _, _ => rfl
  | SmtValue.UValue _ _, _, _ => rfl
  | SmtValue.RegLan _, _, _ => rfl
  | SmtValue.DtCons _ _ _, _, _ => rfl

private theorem smtx_value_dt_substitute_apply_arg_nth_of_head_ne
    (sub : native_String) (base : SmtDatatype)
    {v : SmtValue} {s2 : native_String} {d : SmtDatatype} {i : native_Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s2 d i)
    (hNe : sub ≠ s2)
    (j : native_Nat) :
    __vsm_apply_arg_nth (smtx_value_dt_substitute_apply sub base v) j
        (vsm_num_apply_args (smtx_value_dt_substitute_apply sub base v)) =
      smtx_value_dt_substitute_apply sub base
        (__vsm_apply_arg_nth v j (vsm_num_apply_args v)) := by
  apply smtx_value_dt_substitute_apply_arg_nth
  intro sh dh ih hHead'
  have hEq : SmtValue.DtCons sh dh ih = SmtValue.DtCons s2 d i := by
    exact hHead'.symm.trans hHead
  injection hEq with hName _ _
  intro hSub
  apply hNe
  exact hSub.symm.trans hName

private theorem smtx_value_dtc_app_type_head_exists_apply :
    (v : SmtValue) -> {A B : SmtType} ->
      __smtx_typeof_value v = SmtType.DtcAppType A B ->
      ∃ s d i, __vsm_apply_head v = SmtValue.DtCons s d i
  | SmtValue.NotValue, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Boolean _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Numeral _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Rational _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Binary w n, A, B, h => by
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | SmtValue.Map m, A, B, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Fun m, A, B, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
  | SmtValue.Set m, A, B, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          cases U <;>
            simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | SmtValue.Seq ss, A, B, h => by
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Char _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.UValue _ _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.RegLan _, A, B, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.DtCons s d i, A, B, h => by
      exact ⟨s, d, i, rfl⟩
  | SmtValue.Apply f a, A, B, h => by
      change
        __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value a) =
          SmtType.DtcAppType A B at h
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_apply_value, hf] at h
      case DtcAppType C D =>
        rcases smtx_value_dtc_app_type_head_exists_apply f hf with
          ⟨s, d, i, hHead⟩
        exact ⟨s, d, i, by simpa [__vsm_apply_head] using hHead⟩

private theorem smtx_value_datatype_type_head_base_apply
    {v : SmtValue}
    {s sh : native_String}
    {d dh : SmtDatatype}
    {i : native_Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons sh dh i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    sh = s ∧ dh = d := by
  have hNN : __smtx_typeof_value v ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hTy
    simp at hTy
  have hChain := dt_cons_chain_type_of_non_none hHead hNN
  have hRes :
      dt_cons_applied_type_rec sh dh (__smtx_dt_substitute sh dh dh) i
          (vsm_num_apply_args v) =
        SmtType.Datatype s d := by
    exact hChain.symm.trans hTy
  have hArgsZero :
      __smtx_dt_num_sels (__smtx_dt_substitute sh dh dh) i -
          vsm_num_apply_args v =
        0 := by
    have hArgs := congrArg dt_cons_type_num_args hRes
    rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
    simpa [dt_cons_type_num_args] using hArgs
  have hle :
      vsm_num_apply_args v ≤
        __smtx_dt_num_sels (__smtx_dt_substitute sh dh dh) i :=
    dt_cons_applied_type_rec_non_none_implies_le sh dh
      (__smtx_dt_substitute sh dh dh) i (vsm_num_apply_args v)
      (by rw [hRes]; simp)
  have hCount :
      vsm_num_apply_args v =
        __smtx_dt_num_sels (__smtx_dt_substitute sh dh dh) i := by
    have hge :
        __smtx_dt_num_sels (__smtx_dt_substitute sh dh dh) i ≤
          vsm_num_apply_args v :=
      (Nat.sub_eq_zero_iff_le).1 hArgsZero
    exact Nat.le_antisymm hle hge
  have hFull :
      dt_cons_applied_type_rec sh dh (__smtx_dt_substitute sh dh dh) i
          (__smtx_dt_num_sels (__smtx_dt_substitute sh dh dh) i) =
        SmtType.Datatype sh dh :=
    dt_cons_applied_type_rec_full_arity sh dh (__smtx_dt_substitute sh dh dh) i
      (by rw [← hCount, hRes]; simp)
  have hCmp : SmtType.Datatype sh dh = SmtType.Datatype s d := by
    calc
      SmtType.Datatype sh dh =
          dt_cons_applied_type_rec sh dh (__smtx_dt_substitute sh dh dh) i
            (__smtx_dt_num_sels (__smtx_dt_substitute sh dh dh) i) := by
        exact hFull.symm
      _ =
          dt_cons_applied_type_rec sh dh (__smtx_dt_substitute sh dh dh) i
            (vsm_num_apply_args v) := by
        rw [← hCount]
      _ = SmtType.Datatype s d := hRes
  injection hCmp with hs hd
  exact ⟨hs, hd⟩

private theorem smtx_value_datatype_type_head_exists_apply :
    (v : SmtValue) -> {s : native_String} -> {d : SmtDatatype} ->
      __smtx_typeof_value v = SmtType.Datatype s d ->
      ∃ i, __vsm_apply_head v = SmtValue.DtCons s d i
  | SmtValue.NotValue, s, d, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Boolean _, s, d, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Numeral _, s, d, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Rational _, s, d, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Binary w n, s, d, h => by
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at h
  | SmtValue.Map m, s, d, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Fun m, s, d, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at h
  | SmtValue.Set m, s, d, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          cases U <;>
            simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | SmtValue.Seq ss, s, d, h => by
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Char _, s, d, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.UValue _ _, s, d, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.RegLan _, s, d, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.DtCons sh dh i, s, d, h => by
      have hBase :
          sh = s ∧ dh = d :=
        typeof_dt_cons_value_rec_eq_base_datatype sh dh
          (__smtx_dt_substitute sh dh dh) i s d
          (by simpa [__smtx_typeof_value] using h)
      rcases hBase with ⟨rfl, rfl⟩
      exact ⟨i, rfl⟩
  | SmtValue.Apply f a, s, d, h => by
      have hNN :
          __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value a) ≠
            SmtType.None := by
        intro hNone
        simp [__smtx_typeof_value, hNone] at h
      rcases typeof_apply_value_non_none_cases hNN with
        ⟨A, B, hF, _hX, _hA, _hB⟩
      rcases smtx_value_dtc_app_type_head_exists_apply f hF with
        ⟨sh, dh, i, hHeadF⟩
      have hHeadApply :
          __vsm_apply_head (SmtValue.Apply f a) = SmtValue.DtCons sh dh i := by
        simpa [__vsm_apply_head] using hHeadF
      have hBase :
          sh = s ∧ dh = d :=
        smtx_value_datatype_type_head_base_apply hHeadApply h
      rcases hBase with ⟨rfl, rfl⟩
      exact ⟨i, hHeadApply⟩

private theorem smtx_value_dt_substitute_typeof_shadowed_datatype_apply
    (v : SmtValue)
    {base d : SmtDatatype} {s : native_String}
    (hv : __smtx_typeof_value v = SmtType.Datatype s d) :
    __smtx_typeof_value (smtx_value_dt_substitute_apply s base v) =
      SmtType.Datatype s d := by
  rcases smtx_value_datatype_type_head_exists_apply v hv with ⟨i, hHead⟩
  have hSame :=
    smtx_value_dt_substitute_apply_of_shadowed_head s base v hHead
  simpa [hSame] using hv

private theorem smtx_value_dt_substitute_apply_datatype_head
    (v : SmtValue)
    {base d : SmtDatatype} {s s2 : native_String}
    (hv : __smtx_typeof_value v = SmtType.Datatype s2 d)
    (hNe : s ≠ s2) :
    ∃ i,
      __vsm_apply_head (smtx_value_dt_substitute_apply s base v) =
        SmtValue.DtCons s2 (__smtx_dt_substitute s base d) i ∧
      vsm_num_apply_args (smtx_value_dt_substitute_apply s base v) =
        vsm_num_apply_args v := by
  rcases smtx_value_datatype_type_head_exists_apply v hv with ⟨i, hHead⟩
  have hHeadSub :=
    smtx_value_dt_substitute_apply_head_of_dt_cons s base v hHead
  have hArgs := smtx_value_dt_substitute_apply_num_args s base v
  refine ⟨i, ?_, hArgs⟩
  simpa [native_streq, native_ite, hNe] using hHeadSub

private theorem smtx_value_dt_substitute_apply_datatype_head_full_args
    (v : SmtValue)
    {base d : SmtDatatype} {s s2 : native_String}
    (hv : __smtx_typeof_value v = SmtType.Datatype s2 d)
    (hNe : s ≠ s2) :
    ∃ i,
      __vsm_apply_head (smtx_value_dt_substitute_apply s base v) =
        SmtValue.DtCons s2 (__smtx_dt_substitute s base d) i ∧
      vsm_num_apply_args (smtx_value_dt_substitute_apply s base v) =
        __smtx_dt_num_sels
          (__smtx_dt_substitute s2
            (__smtx_dt_substitute s base d) (__smtx_dt_substitute s base d)) i := by
  rcases smtx_value_datatype_type_head_exists_apply v hv with ⟨i, hHead⟩
  have hHeadSub :=
    smtx_value_dt_substitute_apply_head_of_dt_cons s base v hHead
  have hHeadSub' :
      __vsm_apply_head (smtx_value_dt_substitute_apply s base v) =
        SmtValue.DtCons s2 (__smtx_dt_substitute s base d) i := by
    simpa [native_streq, native_ite, hNe] using hHeadSub
  have hArgs := smtx_value_dt_substitute_apply_num_args s base v
  have hOrigCount :
      vsm_num_apply_args v =
        __smtx_dt_num_sels (__smtx_dt_substitute s2 d d) i :=
    vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hv
  refine ⟨i, hHeadSub', ?_⟩
  calc
    vsm_num_apply_args (smtx_value_dt_substitute_apply s base v) =
        vsm_num_apply_args v := hArgs
    _ = __smtx_dt_num_sels (__smtx_dt_substitute s2 d d) i := hOrigCount
    _ = __smtx_dt_num_sels d i := dt_num_sels_substitute s2 d d i
    _ = __smtx_dt_num_sels (__smtx_dt_substitute s base d) i := by
        exact (dt_num_sels_substitute s base d i).symm
    _ =
        __smtx_dt_num_sels
          (__smtx_dt_substitute s2
            (__smtx_dt_substitute s base d) (__smtx_dt_substitute s base d)) i := by
        exact (dt_num_sels_substitute s2
          (__smtx_dt_substitute s base d) (__smtx_dt_substitute s base d) i).symm

private theorem smtx_value_dt_context_substitute_apply_datatype_head_full_args
    (v : SmtValue)
    {base d : SmtDatatype} {s s2 : native_String}
    (hv : __smtx_typeof_value v = SmtType.Datatype s2 d) :
    ∃ i,
      __vsm_apply_head
          (smtx_value_dt_context_substitute_apply
            s base s2 d (__smtx_dt_substitute s base d) v) =
        SmtValue.DtCons s2 (__smtx_dt_substitute s base d) i ∧
      vsm_num_apply_args
          (smtx_value_dt_context_substitute_apply
            s base s2 d (__smtx_dt_substitute s base d) v) =
        __smtx_dt_num_sels
          (__smtx_dt_substitute s2
            (__smtx_dt_substitute s base d) (__smtx_dt_substitute s base d)) i := by
  rcases smtx_value_datatype_type_head_exists_apply v hv with ⟨i, hHead⟩
  have hHeadSub :=
    smtx_value_dt_context_substitute_apply_head_of_root
      s base s2 d (__smtx_dt_substitute s base d) v hHead
  have hArgs :=
    smtx_value_dt_context_substitute_apply_num_args
      s base s2 d (__smtx_dt_substitute s base d) v
  have hOrigCount :
      vsm_num_apply_args v =
        __smtx_dt_num_sels (__smtx_dt_substitute s2 d d) i :=
    vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hv
  refine ⟨i, hHeadSub, ?_⟩
  calc
    vsm_num_apply_args
        (smtx_value_dt_context_substitute_apply
          s base s2 d (__smtx_dt_substitute s base d) v) =
        vsm_num_apply_args v := hArgs
    _ = __smtx_dt_num_sels (__smtx_dt_substitute s2 d d) i := hOrigCount
    _ = __smtx_dt_num_sels d i := dt_num_sels_substitute s2 d d i
    _ = __smtx_dt_num_sels (__smtx_dt_substitute s base d) i := by
        exact (dt_num_sels_substitute s base d i).symm
    _ =
        __smtx_dt_num_sels
          (__smtx_dt_substitute s2
            (__smtx_dt_substitute s base d) (__smtx_dt_substitute s base d)) i := by
        exact (dt_num_sels_substitute s2
          (__smtx_dt_substitute s base d) (__smtx_dt_substitute s base d) i).symm

private theorem smtx_value_typeof_full_dt_cons_chain_apply
    {v : SmtValue}
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d i)
    (hCount :
      vsm_num_apply_args v = __smtx_dt_num_sels (__smtx_dt_substitute s d d) i)
    (hNN : __smtx_typeof_value v ≠ SmtType.None) :
    __smtx_typeof_value v = SmtType.Datatype s d := by
  have hChain := dt_cons_chain_type_of_non_none hHead hNN
  have hRecNN :
      dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (vsm_num_apply_args v) ≠
        SmtType.None := by
    intro hNone
    apply hNN
    rw [hChain, hNone]
  have hFull :
      dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (__smtx_dt_num_sels (__smtx_dt_substitute s d d) i) =
        SmtType.Datatype s d :=
    dt_cons_applied_type_rec_full_arity s d (__smtx_dt_substitute s d d) i
      (by simpa [hCount] using hRecNN)
  calc
    __smtx_typeof_value v =
        dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (vsm_num_apply_args v) := hChain
    _ =
        dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (__smtx_dt_num_sels (__smtx_dt_substitute s d d) i) := by
        rw [hCount]
    _ = SmtType.Datatype s d := hFull

private theorem smtx_ret_typeof_sel_rec_ne_type_ref_of_apply_arg
    {v : SmtValue}
    {s r : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d i)
    (hNN : __smtx_typeof_value v ≠ SmtType.None)
    (hj : j < vsm_num_apply_args v) :
    __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i j ≠
      SmtType.TypeRef r := by
  have hArgTy :
      __smtx_typeof_value (__vsm_apply_arg_nth v j (vsm_num_apply_args v)) =
        __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i j :=
    apply_arg_nth_type_of_non_none hHead hNN hj
  intro hTypeRef
  exact typeof_value_ne_type_ref r
    (__vsm_apply_arg_nth v j (vsm_num_apply_args v))
    (hArgTy.trans hTypeRef)

private theorem smtx_value_dt_substitute_typeof_of_non_chain_apply
    (sub : native_String) (base : SmtDatatype) :
    (v : SmtValue) -> {T : SmtType} ->
      ¬ dt_cons_chain_result T ->
      __smtx_typeof_value v = T ->
      __smtx_typeof_value (smtx_value_dt_substitute_apply sub base v) = T
  | SmtValue.NotValue, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Boolean b, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Numeral n, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Rational q, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Binary w n, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Map m, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Fun m, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Set m, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Seq ss, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.Char c, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.UValue k e, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.RegLan r, T, hT, hv => by
      simpa [smtx_value_dt_substitute_apply] using hv
  | SmtValue.DtCons s d i, T, hT, hv => by
      exact False.elim (hT (dt_cons_chain_result_of_dt_cons_value_type hv))
  | SmtValue.Apply f a, T, hT, hv => by
      exact False.elim (apply_value_non_chain_result_impossible hT hv)

private theorem smtx_value_dt_context_substitute_typeof_of_non_chain_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype) :
    (v : SmtValue) -> {T : SmtType} ->
      ¬ dt_cons_chain_result T ->
      __smtx_typeof_value v = T ->
      __smtx_typeof_value
          (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v) = T
  | SmtValue.NotValue, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Boolean b, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Numeral n, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Rational q, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Binary w n, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Map m, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Fun m, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Set m, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Seq ss, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.Char c, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.UValue k e, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.RegLan r, T, hT, hv => by
      simpa [smtx_value_dt_context_substitute_apply] using hv
  | SmtValue.DtCons s d i, T, hT, hv => by
      exact False.elim (hT (dt_cons_chain_result_of_dt_cons_value_type hv))
  | SmtValue.Apply f a, T, hT, hv => by
      exact False.elim (apply_value_non_chain_result_impossible hT hv)

private theorem smtx_chain_type_context_substitute_eq_self_of_value_non_chain_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (v : SmtValue) {T : SmtType}
    (hT : ¬ dt_cons_chain_result T)
    (hv : __smtx_typeof_value v = T) :
    smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot true true T = T := by
  cases T with
  | TypeRef r =>
      exact False.elim (typeof_value_ne_type_ref r v hv)
  | None =>
      exact False.elim (hT (by simp [dt_cons_chain_result]))
  | Datatype s d =>
      exact False.elim (hT (by simp [dt_cons_chain_result]))
  | DtcAppType A B =>
      rcases smtx_value_dtc_app_type_head_exists_apply v hv with
        ⟨s, d, i, hHead⟩
      exact False.elim
        (hT (typeof_value_dt_cons_head_chain_result v (SmtType.DtcAppType A B)
          ⟨s, d, i, hHead⟩ hv))
  | Bool =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | Int =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | Real =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | RegLan =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | BitVec w =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | Map A B =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | Set A =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | Seq A =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | Char =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | USort i =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]
  | FunType A B =>
      simp [smtx_chain_type_context_substitute_apply,
        smtx_type_context_substitute_apply]

private theorem smtx_value_dt_context_substitute_typeof_non_chain_top_apply
    (sub : native_String) (base : SmtDatatype)
    (root : native_String) (oldRoot newRoot : SmtDatatype)
    (v : SmtValue) {T : SmtType}
    (hT : ¬ dt_cons_chain_result T)
    (hv : __smtx_typeof_value v = T) :
    __smtx_typeof_value
        (smtx_value_dt_context_substitute_apply sub base root oldRoot newRoot v) =
      smtx_chain_type_context_substitute_apply sub base root oldRoot newRoot true true T := by
  have hPres :=
    smtx_value_dt_context_substitute_typeof_of_non_chain_apply
      sub base root oldRoot newRoot v hT hv
  have hCtx :=
    smtx_chain_type_context_substitute_eq_self_of_value_non_chain_apply
      sub base root oldRoot newRoot v hT hv
  simpa [hCtx] using hPres

private theorem smtx_value_dt_substitute_typeof_non_chain_top_apply
    (sub : native_String) (base : SmtDatatype)
    (v : SmtValue) {T : SmtType}
    (hT : ¬ dt_cons_chain_result T)
    (hv : __smtx_typeof_value v = T) :
    __smtx_typeof_value (smtx_value_dt_substitute_apply sub base v) =
      smtx_type_substitute_top_apply sub base T := by
  have hPres :=
    smtx_value_dt_substitute_typeof_of_non_chain_apply sub base v hT hv
  have hNoSubRef : T ≠ SmtType.TypeRef sub := by
    intro hRef
    exact typeof_value_ne_type_ref sub v (hv.trans hRef)
  cases T with
  | TypeRef r =>
      by_cases hEq : r = sub
      · subst r
        exact False.elim (hNoSubRef rfl)
      · simpa [smtx_type_substitute_top_apply, native_ite, native_Teq, hEq]
          using hPres
  | None =>
      exact False.elim (hT (by simp [dt_cons_chain_result]))
  | Datatype s d =>
      exact False.elim (hT (by simp [dt_cons_chain_result]))
  | DtcAppType A B =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | Bool =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | Int =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | Real =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | RegLan =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | BitVec w =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | Map A B =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | Set A =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | Seq A =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | Char =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | USort i =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres
  | FunType A B =>
      simpa [smtx_type_substitute_top_apply, native_ite, native_Teq] using hPres

private theorem smtx_value_typeof_field_non_chain_or_datatype_apply
    {v : SmtValue} {T : SmtType} {refs : RefList}
    (hField : smtx_type_field_wf_rec T refs)
    (hv : __smtx_typeof_value v = T) :
    (¬ dt_cons_chain_result T) ∨
      ∃ s d, T = SmtType.Datatype s d := by
  cases T with
  | None =>
      simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hField
  | Bool =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | Int =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | Real =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | RegLan =>
      simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hField
  | BitVec w =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | Map A B =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | Set A =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | Seq A =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | Char =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | Datatype s d =>
      exact Or.inr ⟨s, d, rfl⟩
  | TypeRef r =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | USort i =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | FunType A B =>
      exact Or.inl (by simp [dt_cons_chain_result])
  | DtcAppType A B =>
      simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hField

private theorem smtx_value_dt_context_substitute_typeof_apply
    (v : SmtValue)
    {base d : SmtDatatype} {s s2 : native_String} {refs : RefList}
    (hBaseInh : native_inhabited_type (SmtType.Datatype s base) = true)
    (hBaseWf :
      __smtx_dt_wf_rec base
        (native_reflist_insert (native_reflist_insert refs s2) s) = true)
    (hTargetWf :
      __smtx_dt_wf_rec d
        (native_reflist_insert (native_reflist_insert refs s2) s) = true)
    (hv : __smtx_typeof_value v = SmtType.Datatype s2 d)
    (hSubWf :
      __smtx_dt_wf_rec (__smtx_dt_substitute s base d)
        (native_reflist_insert refs s2) = true)
    (hNe : s ≠ s2) :
    __smtx_typeof_value
        (smtx_value_dt_context_substitute_apply
          s base s2 d (__smtx_dt_substitute s base d) v) =
      SmtType.Datatype s2 (__smtx_dt_substitute s base d) := by
  rcases smtx_value_dt_context_substitute_apply_datatype_head_full_args v hv with
    ⟨i, hHead, hCount⟩
  exact smtx_value_typeof_full_dt_cons_chain_apply hHead hCount (by
    sorry)

private theorem smtx_value_typeof_dt_substitute_apply
    (v : SmtValue)
    {base d : SmtDatatype} {s s2 : native_String} {refs : RefList}
    (hBaseInh : native_inhabited_type (SmtType.Datatype s base) = true)
    (hBaseWf :
      __smtx_dt_wf_rec base
        (native_reflist_insert (native_reflist_insert refs s2) s) = true)
    (hTargetWf :
      __smtx_dt_wf_rec d
        (native_reflist_insert (native_reflist_insert refs s2) s) = true)
    (hv : __smtx_typeof_value v = SmtType.Datatype s2 d)
    (hSubWf :
      __smtx_dt_wf_rec (__smtx_dt_substitute s base d)
        (native_reflist_insert refs s2) = true)
    (hNe : s ≠ s2) :
    type_inhabited (SmtType.Datatype s2 (__smtx_dt_substitute s base d)) :=
  ⟨smtx_value_dt_context_substitute_apply
      s base s2 d (__smtx_dt_substitute s base d) v,
    smtx_value_dt_context_substitute_typeof_apply
      v hBaseInh hBaseWf hTargetWf hv hSubWf hNe⟩

private theorem smtx_dt_substitute_type_inhabited_apply
    {base d : SmtDatatype} {s s2 : native_String} {refs : RefList}
    (hBaseInh : native_inhabited_type (SmtType.Datatype s base) = true)
    (hBaseWf :
      __smtx_dt_wf_rec base
        (native_reflist_insert (native_reflist_insert refs s2) s) = true)
    (hTargetWf :
      __smtx_dt_wf_rec d
        (native_reflist_insert (native_reflist_insert refs s2) s) = true)
    (hTargetInh : type_inhabited (SmtType.Datatype s2 d))
    (hSubWf :
      __smtx_dt_wf_rec (__smtx_dt_substitute s base d)
        (native_reflist_insert refs s2) = true)
    (hNe : s ≠ s2) :
    type_inhabited (SmtType.Datatype s2 (__smtx_dt_substitute s base d)) := by
  rcases hTargetInh with ⟨v, hv⟩
  exact smtx_value_typeof_dt_substitute_apply v hBaseInh hBaseWf hTargetWf hv hSubWf hNe

private theorem smtx_dt_substitute_inhabited_apply
    {base d : SmtDatatype} {s s2 : native_String} {refs : RefList}
    (hBaseInh : native_inhabited_type (SmtType.Datatype s base) = true)
    (hBaseWf :
      __smtx_dt_wf_rec base
        (native_reflist_insert (native_reflist_insert refs s2) s) = true)
    (hTargetWf :
      __smtx_dt_wf_rec d
        (native_reflist_insert (native_reflist_insert refs s2) s) = true)
    (hTargetInh : native_inhabited_type (SmtType.Datatype s2 d) = true)
    (hSubWf :
      __smtx_dt_wf_rec (__smtx_dt_substitute s base d)
        (native_reflist_insert refs s2) = true)
    (hNe : s ≠ s2) :
    native_inhabited_type
      (SmtType.Datatype s2 (__smtx_dt_substitute s base d)) = true := by
  apply native_inhabited_type_of_type_inhabited
  exact smtx_dt_substitute_type_inhabited_apply hBaseInh hBaseWf hTargetWf
    ((Smtm.smtx_inhabited_type_eq_true_iff (SmtType.Datatype s2 d)).1 hTargetInh)
    hSubWf hNe

mutual

private theorem smtx_dtc_substitute_wf_apply :
    (c : SmtDatatypeCons) -> {base : SmtDatatype} ->
      {s : native_String} -> {refs : RefList} ->
      native_inhabited_type (SmtType.Datatype s base) = true ->
      __smtx_dt_wf_rec base (native_reflist_insert refs s) = true ->
      __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true ->
      __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s base c) refs = true
  | SmtDatatypeCons.unit, base, s, refs, _hBaseInh, _hBaseWf, _hWf => by
      simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec]
  | SmtDatatypeCons.cons T c, base, s, refs, hBaseInh, hBaseWf, hWf => by
      cases T with
      | TypeRef r =>
          have hPair :
              native_reflist_contains (native_reflist_insert refs s) r = true ∧
                __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true := by
            simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
          have hTailSub :
              __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s base c) refs = true :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hPair.2
          by_cases hEq : r = s
          · subst r
            have hBaseTypeWf :
                __smtx_type_wf_rec (SmtType.Datatype s base) refs = true := by
              simpa [__smtx_type_wf_rec] using hBaseWf
            simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
              native_ite, native_Teq, hBaseInh, hBaseTypeWf, hTailSub]
          · have hRef : native_reflist_contains refs r = true := by
              have hMem : r = s ∨ r ∈ refs := by
                simpa [native_reflist_contains, native_reflist_insert] using hPair.1
              cases hMem with
              | inl hr => exact False.elim (hEq hr)
              | inr hr => simpa [native_reflist_contains] using hr
            simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
              native_ite, native_Teq, hEq, hRef, hTailSub]
      | None =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
      | DtcAppType A B =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
      | Datatype s2 d2 =>
          have hAll :
              native_inhabited_type (SmtType.Datatype s2 d2) = true ∧
                __smtx_type_wf_rec (SmtType.Datatype s2 d2)
                    (native_reflist_insert refs s) = true ∧
                  __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true := by
            simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
          have hTailSub :
              __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s base c) refs = true :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hAll.2.2
          by_cases hEq : s = s2
          · subst s2
            have hOrigD2 :
                __smtx_dt_wf_rec d2
                    (native_reflist_insert (native_reflist_insert refs s) s) = true := by
              simpa [__smtx_type_wf_rec] using hAll.2.1
            have hD2Wf :
                __smtx_dt_wf_rec d2 (native_reflist_insert refs s) = true :=
              smtx_dt_wf_rec_mono_apply d2
                (reflist_subset_insert_dup_apply refs s) hOrigD2
            simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
              __smtx_type_wf_rec, native_ite, native_streq, hAll.1, hD2Wf,
              hTailSub]
          · have hOrigD2 :
                __smtx_dt_wf_rec d2
                    (native_reflist_insert (native_reflist_insert refs s) s2) = true := by
              simpa [__smtx_type_wf_rec] using hAll.2.1
            have hD2Swapped :
                __smtx_dt_wf_rec d2
                    (native_reflist_insert (native_reflist_insert refs s2) s) = true :=
              smtx_dt_wf_rec_mono_apply d2
                (reflist_subset_insert_swap_apply refs s s2) hOrigD2
            have hBaseWfBig :
                __smtx_dt_wf_rec base
                    (native_reflist_insert (native_reflist_insert refs s2) s) = true :=
              smtx_dt_wf_rec_mono_apply base
                (reflist_subset_insert_middle_apply refs s s2) hBaseWf
            have hSubD2Wf :
                __smtx_dt_wf_rec (__smtx_dt_substitute s base d2)
                    (native_reflist_insert refs s2) = true :=
              smtx_dt_substitute_wf_apply d2 hBaseInh hBaseWfBig hD2Swapped
            have hSubD2Inh :
                native_inhabited_type
                    (SmtType.Datatype s2 (__smtx_dt_substitute s base d2)) = true := by
              exact smtx_dt_substitute_inhabited_apply hBaseInh hBaseWfBig
                hD2Swapped hAll.1 hSubD2Wf hEq
            simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
              __smtx_type_wf_rec, native_ite, native_streq, hEq, hSubD2Inh,
              hSubD2Wf, hTailSub]
      | Bool =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hTail
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            __smtx_type_wf_rec, native_ite, native_Teq, hTailSub]
      | Int =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hTail
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            __smtx_type_wf_rec, native_ite, native_Teq, hTailSub]
      | Real =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hTail
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            __smtx_type_wf_rec, native_ite, native_Teq, hTailSub]
      | RegLan =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hWf
      | BitVec w =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hTail
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            __smtx_type_wf_rec, native_ite, native_Teq, hTailSub]
      | Map A B =>
          have hAll :
              native_inhabited_type (SmtType.Map A B) = true ∧
                __smtx_type_wf_rec (SmtType.Map A B)
                    (native_reflist_insert refs s) = true ∧
                  __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true := by
            simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
          have hField :
              __smtx_type_wf_rec (SmtType.Map A B) refs = true := by
            simpa [__smtx_type_wf_rec] using hAll.2.1
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hAll.2.2
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            native_ite, native_Teq, hAll.1, hField, hTailSub]
      | Set A =>
          have hAll :
              native_inhabited_type (SmtType.Set A) = true ∧
                __smtx_type_wf_rec (SmtType.Set A)
                    (native_reflist_insert refs s) = true ∧
                  __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true := by
            simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
          have hField :
              __smtx_type_wf_rec (SmtType.Set A) refs = true := by
            simpa [__smtx_type_wf_rec] using hAll.2.1
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hAll.2.2
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            native_ite, native_Teq, hAll.1, hField, hTailSub]
      | Seq A =>
          have hAll :
              native_inhabited_type (SmtType.Seq A) = true ∧
                __smtx_type_wf_rec (SmtType.Seq A)
                    (native_reflist_insert refs s) = true ∧
                  __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true := by
            simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
          have hField :
              __smtx_type_wf_rec (SmtType.Seq A) refs = true := by
            simpa [__smtx_type_wf_rec] using hAll.2.1
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hAll.2.2
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            native_ite, native_Teq, hAll.1, hField, hTailSub]
      | Char =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hTail
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            __smtx_type_wf_rec, native_ite, native_Teq, hTailSub]
      | USort i =>
          have hTail := smtx_dt_cons_wf_rec_tail_of_true hWf
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hTail
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            __smtx_type_wf_rec, native_ite, native_Teq, hTailSub]
      | FunType A B =>
          have hAll :
              native_inhabited_type (SmtType.FunType A B) = true ∧
                __smtx_type_wf_rec (SmtType.FunType A B)
                    (native_reflist_insert refs s) = true ∧
                  __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true := by
            simpa [__smtx_dt_cons_wf_rec, native_ite] using hWf
          have hField :
              __smtx_type_wf_rec (SmtType.FunType A B) refs = true := by
            simpa [__smtx_type_wf_rec] using hAll.2.1
          have hTailSub :=
            smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hAll.2.2
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            native_ite, native_Teq, hAll.1, hField, hTailSub]

private theorem smtx_dt_substitute_wf_apply :
    (target : SmtDatatype) -> {base : SmtDatatype} ->
      {s : native_String} -> {refs : RefList} ->
      native_inhabited_type (SmtType.Datatype s base) = true ->
      __smtx_dt_wf_rec base (native_reflist_insert refs s) = true ->
      __smtx_dt_wf_rec target (native_reflist_insert refs s) = true ->
      __smtx_dt_wf_rec (__smtx_dt_substitute s base target) refs = true
  | SmtDatatype.null, base, s, refs, _hBaseInh, _hBaseWf, hWf => by
      simp [__smtx_dt_wf_rec] at hWf
  | SmtDatatype.sum c targetTail, base, s, refs, hBaseInh, hBaseWf, hWf => by
      have hCons :
          __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      have hConsSub :
          __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s base c) refs = true :=
        smtx_dtc_substitute_wf_apply c hBaseInh hBaseWf hCons
      cases targetTail with
      | null =>
          simpa [__smtx_dt_substitute, __smtx_dt_wf_rec] using hConsSub
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail)
                  (native_reflist_insert refs s) = true :=
            smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
          have hTailSub :
              __smtx_dt_wf_rec
                  (__smtx_dt_substitute s base (SmtDatatype.sum cTail dTail))
                  refs = true :=
            smtx_dt_substitute_wf_apply (SmtDatatype.sum cTail dTail)
              hBaseInh hBaseWf hTail
          simp [__smtx_dt_substitute, __smtx_dt_wf_rec, native_ite, hConsSub]
          simpa [__smtx_dt_substitute] using hTailSub

end

/-- Self-substitution preserves datatype well-formedness. -/
private theorem smtx_dt_substitute_self_wf_apply :
    (d : SmtDatatype) -> {s : native_String} -> {refs : RefList} ->
      native_inhabited_type (SmtType.Datatype s d) = true ->
      __smtx_dt_wf_rec d (native_reflist_insert refs s) = true ->
      __smtx_dt_wf_rec (__smtx_dt_substitute s d d) refs = true
  | d, s, refs, hInh, hWf =>
      smtx_dt_substitute_wf_apply d hInh hWf hWf

private def smtx_type_fun_like_domains_wf : SmtType -> Prop
  | SmtType.Seq A => smtx_type_fun_like_domains_wf A
  | SmtType.Set A => smtx_type_fun_like_domains_wf A
  | SmtType.Map A B =>
      smtx_type_fun_like_domains_wf A ∧ smtx_type_fun_like_domains_wf B
  | SmtType.FunType A B =>
      smtx_type_field_wf_rec A native_reflist_nil ∧
        smtx_type_fun_like_domains_wf A ∧ smtx_type_fun_like_domains_wf B
  | SmtType.DtcAppType A B =>
      smtx_type_field_wf_rec A native_reflist_nil ∧
        smtx_type_fun_like_domains_wf A ∧ smtx_type_fun_like_domains_wf B
  | _ => True

/--
SMT types whose shape is strong enough for EO type-translation injectivity.

This is like `smtx_type_field_wf_rec`, but treats `DtcAppType` as an
intermediate function-like type instead of rejecting it outright.
-/
private def smtx_type_translation_injective_wf : SmtType -> Prop
  | SmtType.Seq A => smtx_type_translation_injective_wf A
  | SmtType.Set A => smtx_type_translation_injective_wf A
  | SmtType.Map A B =>
      smtx_type_translation_injective_wf A ∧ smtx_type_translation_injective_wf B
  | SmtType.FunType A B =>
      smtx_type_field_wf_rec A native_reflist_nil ∧
        smtx_type_translation_injective_wf A ∧ smtx_type_translation_injective_wf B
  | SmtType.DtcAppType A B =>
      smtx_type_field_wf_rec A native_reflist_nil ∧
        smtx_type_translation_injective_wf A ∧ smtx_type_translation_injective_wf B
  | SmtType.RegLan => True
  | T => smtx_type_field_wf_rec T native_reflist_nil

private theorem smtx_type_translation_injective_wf_of_type_wf
    {T : SmtType} (h : __smtx_type_wf T = true) :
    smtx_type_translation_injective_wf T := by
  let rec go : (T : SmtType) -> __smtx_type_wf T = true ->
      smtx_type_translation_injective_wf T
    | SmtType.None, h => by
        simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h
    | SmtType.Bool, _h => by
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
    | SmtType.Int, _h => by
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
    | SmtType.Real, _h => by
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
    | SmtType.RegLan, _h => by
        simp [smtx_type_translation_injective_wf]
    | SmtType.BitVec _w, _h => by
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
    | SmtType.Map A B, h => by
        rcases smtx_type_wf_map_components h with ⟨hA, hB⟩
        exact ⟨go A hA, go B hB⟩
    | SmtType.Set A, h => by
        exact go A (smtx_type_wf_set_component h)
    | SmtType.Seq A, h => by
        exact go A (smtx_type_wf_seq_component h)
    | SmtType.Char, _h => by
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
    | SmtType.Datatype _s _d, h => by
        exact smtx_type_field_wf_rec_of_type_wf_rec
          (smtx_type_wf_rec_of_type_wf (by simp) h)
    | SmtType.TypeRef _s, h => by
        simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h
    | SmtType.USort _i, _h => by
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
    | SmtType.FunType A B, h => by
        have hRec : __smtx_type_wf_rec (SmtType.FunType A B) native_reflist_nil = true :=
          smtx_type_wf_rec_of_type_wf (by simp) h
        rcases fun_type_wf_rec_components_of_wf
            (A := A) (B := B) (refs := native_reflist_nil) hRec with ⟨hA, hB⟩
        rcases smtx_type_wf_fun_components h with ⟨hAWf, hBWf⟩
        exact ⟨smtx_type_field_wf_rec_of_type_wf_rec hA,
          go A hAWf,
          go B hBWf⟩
    | SmtType.DtcAppType _A _B, h => by
        simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h
  exact go T h

private theorem smtx_type_translation_injective_wf_of_field_wf_rec
    {T : SmtType}
    (h : smtx_type_field_wf_rec T native_reflist_nil) :
    smtx_type_translation_injective_wf T := by
  let rec go : (T : SmtType) ->
      smtx_type_field_wf_rec T native_reflist_nil ->
      smtx_type_translation_injective_wf T
    | SmtType.Seq A, h => by
        exact go A (seq_type_field_wf_rec_component_of_wf h)
    | SmtType.Set A, h => by
        exact go A (set_type_field_wf_rec_component_of_wf h)
    | SmtType.Map A B, h => by
        rcases map_type_field_wf_rec_components_of_wf h with ⟨hA, hB⟩
        exact ⟨go A hA, go B hB⟩
    | SmtType.FunType A B, h => by
        rcases fun_type_field_wf_rec_components_of_wf h with ⟨hA, hB⟩
        exact ⟨hA, go A hA, go B hB⟩
    | SmtType.DtcAppType _A _B, h => by
        simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at h
    | SmtType.TypeRef _s, h => by
        simp [smtx_type_field_wf_rec, native_reflist_contains] at h
        cases h
    | SmtType.None, h => by
        simpa [smtx_type_translation_injective_wf] using h
    | SmtType.Bool, h => by
        simpa [smtx_type_translation_injective_wf] using h
    | SmtType.Int, h => by
        simpa [smtx_type_translation_injective_wf] using h
    | SmtType.Real, h => by
        simpa [smtx_type_translation_injective_wf] using h
    | SmtType.RegLan, h => by
        simp [smtx_type_translation_injective_wf]
    | SmtType.BitVec _w, h => by
        simpa [smtx_type_translation_injective_wf] using h
    | SmtType.Char, h => by
        simpa [smtx_type_translation_injective_wf] using h
    | SmtType.Datatype _s _d, h => by
        simpa [smtx_type_translation_injective_wf] using h
    | SmtType.USort _i, h => by
        simpa [smtx_type_translation_injective_wf] using h
  exact go T h

private theorem eo_to_smt_type_injective_of_translation_injective_wf
    {T U : Term} {A : SmtType}
    (hT : __eo_to_smt_type T = A)
    (hU : __eo_to_smt_type U = A)
    (hWF : smtx_type_translation_injective_wf A) :
    T = U := by
  let rec go : (A : SmtType) -> {T U : Term} ->
      __eo_to_smt_type T = A ->
      __eo_to_smt_type U = A ->
      smtx_type_translation_injective_wf A -> T = U
    | SmtType.FunType A B, T, U, hT, hU, hWF => by
        rcases eo_to_smt_type_eq_fun hT with ⟨T1, T2, rfl, hT1, hT2⟩
        rcases eo_to_smt_type_eq_fun hU with ⟨U1, U2, rfl, hU1, hU2⟩
        have h1 : T1 = U1 := go A hT1 hU1 hWF.2.1
        have h2 : T2 = U2 := go B hT2 hU2 hWF.2.2
        subst U1
        subst U2
        rfl
    | SmtType.Map A B, T, U, hT, hU, hWF => by
        rcases eo_to_smt_type_eq_map hT with ⟨T1, T2, rfl, hT1, hT2⟩
        rcases eo_to_smt_type_eq_map hU with ⟨U1, U2, rfl, hU1, hU2⟩
        have h1 : T1 = U1 := go A hT1 hU1 hWF.1
        have h2 : T2 = U2 := go B hT2 hU2 hWF.2
        subst U1
        subst U2
        rfl
    | SmtType.Set A, T, U, hT, hU, hWF => by
        rcases eo_to_smt_type_eq_set hT with ⟨T0, rfl, hT0⟩
        rcases eo_to_smt_type_eq_set hU with ⟨U0, rfl, hU0⟩
        have h0 : T0 = U0 := go A hT0 hU0 hWF
        subst U0
        rfl
    | SmtType.Seq A, T, U, hT, hU, hWF => by
        rcases eo_to_smt_type_eq_seq hT with ⟨T0, rfl, hT0⟩
        rcases eo_to_smt_type_eq_seq hU with ⟨U0, rfl, hU0⟩
        have h0 : T0 = U0 := go A hT0 hU0 hWF
        subst U0
        rfl
    | SmtType.DtcAppType A B, T, U, hT, hU, hWF => by
        rcases eo_to_smt_type_eq_dtc_app hT with ⟨T1, T2, rfl, hT1, hT2⟩
        rcases eo_to_smt_type_eq_dtc_app hU with ⟨U1, U2, rfl, hU1, hU2⟩
        have h1 : T1 = U1 := go A hT1 hU1 hWF.2.1
        have h2 : T2 = U2 := go B hT2 hU2 hWF.2.2
        subst U1
        subst U2
        rfl
    | SmtType.None, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
    | SmtType.Bool, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
    | SmtType.Int, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
    | SmtType.Real, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
    | SmtType.RegLan, T, U, hT, hU, hWF => by
        rw [eo_to_smt_type_eq_reglan hT, eo_to_smt_type_eq_reglan hU]
    | SmtType.BitVec w, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
    | SmtType.Char, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
    | SmtType.Datatype s d, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
    | SmtType.TypeRef s, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
    | SmtType.USort i, T, U, hT, hU, hWF => by
        exact eo_to_smt_type_injective_of_field_wf_rec hT hU hWF
  exact go A hT hU hWF

private theorem smtx_type_fun_like_domains_wf_of_type_wf_rec :
    ∀ {T : SmtType} {refs : RefList},
      __smtx_type_wf_rec T refs = true -> smtx_type_fun_like_domains_wf T
  | SmtType.None, _refs, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.Bool, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.Int, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.Real, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.RegLan, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.BitVec _w, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.Map A B, _refs, h => by
      rcases map_type_wf_rec_components_of_wf h with ⟨hA, hB⟩
      exact ⟨smtx_type_fun_like_domains_wf_of_type_wf_rec (T := A)
          (refs := native_reflist_nil) hA,
        smtx_type_fun_like_domains_wf_of_type_wf_rec (T := B)
          (refs := native_reflist_nil) hB⟩
  | SmtType.Set A, _refs, h => by
      exact smtx_type_fun_like_domains_wf_of_type_wf_rec (T := A)
        (refs := native_reflist_nil) (set_type_wf_rec_component_of_wf h)
  | SmtType.Seq A, _refs, h => by
      exact smtx_type_fun_like_domains_wf_of_type_wf_rec (T := A)
        (refs := native_reflist_nil) (seq_type_wf_rec_component_of_wf h)
  | SmtType.Char, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.Datatype _s _d, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.TypeRef _s, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.USort _i, _refs, _h => by
      simp [smtx_type_fun_like_domains_wf]
  | SmtType.FunType A B, _refs, h => by
      rcases fun_type_wf_rec_components_of_wf h with ⟨hA, hB⟩
      exact ⟨smtx_type_field_wf_rec_of_type_wf_rec hA,
        smtx_type_fun_like_domains_wf_of_type_wf_rec (T := A)
          (refs := native_reflist_nil) hA,
        smtx_type_fun_like_domains_wf_of_type_wf_rec (T := B)
          (refs := native_reflist_nil) hB⟩
  | SmtType.DtcAppType _A _B, _refs, h => by
      simp [__smtx_type_wf_rec] at h
termination_by T refs h => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

private theorem smtx_type_fun_like_domains_wf_of_type_wf
    {T : SmtType} (h : __smtx_type_wf T = true) :
    smtx_type_fun_like_domains_wf T := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    simp [smtx_type_fun_like_domains_wf]
  · exact smtx_type_fun_like_domains_wf_of_type_wf_rec (T := T)
      (refs := native_reflist_nil) (smtx_type_wf_rec_of_type_wf hReg h)

private theorem smtx_type_fun_like_domains_wf_of_field_wf_rec
    {T : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec T refs) :
    smtx_type_fun_like_domains_wf T := by
  cases T
  case TypeRef _s => simp [smtx_type_fun_like_domains_wf]
  all_goals
    exact smtx_type_fun_like_domains_wf_of_type_wf_rec (refs := refs) (by
      simpa [smtx_type_field_wf_rec] using h)

private theorem smtx_type_fun_like_domains_wf_apply
    {F X : SmtType}
    (hF : smtx_type_fun_like_domains_wf F)
    (hNN : __smtx_typeof_apply F X ≠ SmtType.None) :
    smtx_type_fun_like_domains_wf (__smtx_typeof_apply F X) := by
  rcases typeof_apply_non_none_cases hNN with ⟨A, B, hHead, hX, hA, _hB⟩
  have hRes : __smtx_typeof_apply F X = B :=
    smtx_typeof_apply_of_head_cases hHead hX hA
  rw [hRes]
  rcases hHead with hHead | hHead
  · rw [hHead] at hF
    exact hF.2.2
  · rw [hHead] at hF
    exact hF.2.2

private theorem smtx_type_fun_like_arg_field_wf_of_domains_wf
    {T A B : SmtType}
    (hWF : smtx_type_fun_like_domains_wf T)
    (hHead : T = SmtType.FunType A B ∨ T = SmtType.DtcAppType A B) :
    smtx_type_field_wf_rec A native_reflist_nil := by
    rcases hHead with hHead | hHead
    · rw [hHead] at hWF
      exact hWF.1
    · rw [hHead] at hWF
      exact hWF.1

private theorem smtx_type_translation_injective_wf_non_none
    {T : SmtType}
    (h : smtx_type_translation_injective_wf T) :
    T ≠ SmtType.None := by
  cases T <;> simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
    __smtx_type_wf_rec] at h ⊢

private theorem smtx_type_translation_injective_wf_apply
    {F X : SmtType}
    (hF : smtx_type_translation_injective_wf F)
    (hNN : __smtx_typeof_apply F X ≠ SmtType.None) :
    smtx_type_translation_injective_wf (__smtx_typeof_apply F X) := by
  rcases typeof_apply_non_none_cases hNN with ⟨A, B, hHead, hX, hA, _hB⟩
  have hRes : __smtx_typeof_apply F X = B :=
    smtx_typeof_apply_of_head_cases hHead hX hA
  rw [hRes]
  rcases hHead with hHead | hHead
  · rw [hHead] at hF
    exact hF.2.2
  · rw [hHead] at hF
    exact hF.2.2

private theorem smtx_typeof_guard_wf_fun_like_domains_wf_of_non_none
    {T U : SmtType}
    (hU : smtx_type_fun_like_domains_wf U)
    (hNN : __smtx_typeof_guard_wf T U ≠ SmtType.None) :
    smtx_type_fun_like_domains_wf (__smtx_typeof_guard_wf T U) := by
  rw [smtx_typeof_guard_wf_of_non_none T U hNN]
  exact hU

private theorem smtx_typeof_var_domains_wf_of_non_none
    (s : native_String) (T : SmtType)
    (hNN : term_has_non_none_type (SmtTerm.Var s T)) :
    smtx_type_fun_like_domains_wf (__smtx_typeof (SmtTerm.Var s T)) := by
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T (by
      unfold term_has_non_none_type at hNN
      simpa [__smtx_typeof] using hNN)
  rw [smtx_typeof_var_of_non_none s T hNN]
  exact smtx_type_fun_like_domains_wf_of_type_wf hWf

private theorem smtx_typeof_uconst_domains_wf_of_non_none
    (s : native_String) (T : SmtType)
    (hNN : term_has_non_none_type (SmtTerm.UConst s T)) :
    smtx_type_fun_like_domains_wf (__smtx_typeof (SmtTerm.UConst s T)) := by
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T (by
      unfold term_has_non_none_type at hNN
      simpa [__smtx_typeof] using hNN)
  rw [smtx_typeof_uconst_of_non_none s T hNN]
  exact smtx_type_fun_like_domains_wf_of_type_wf hWf

private theorem smtx_typeof_seq_empty_domains_wf_of_non_none
    (T : SmtType)
    (hNN : term_has_non_none_type (SmtTerm.seq_empty T)) :
    smtx_type_fun_like_domains_wf (__smtx_typeof (SmtTerm.seq_empty T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T (SmtType.Seq T) ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [__smtx_typeof] using hNN
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T (SmtType.Seq T) hGuardNN
  rw [smtx_typeof_seq_empty_of_non_none T hNN]
  change smtx_type_fun_like_domains_wf T
  exact smtx_type_fun_like_domains_wf_of_type_wf hWf

private theorem smtx_typeof_set_empty_domains_wf_of_non_none
    (T : SmtType)
    (hNN : term_has_non_none_type (SmtTerm.set_empty T)) :
    smtx_type_fun_like_domains_wf (__smtx_typeof (SmtTerm.set_empty T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T (SmtType.Set T) ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [__smtx_typeof] using hNN
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T (SmtType.Set T) hGuardNN
  rw [smtx_typeof_set_empty_of_non_none T hNN]
  change smtx_type_fun_like_domains_wf T
  exact smtx_type_fun_like_domains_wf_of_type_wf hWf

/-- A well-typed `choice_nth` result preserves well-formed function-like domains. -/
private theorem choice_nth_fun_like_domains_wf_any
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat)
    (hNN : term_has_non_none_type (SmtTerm.choice_nth s T body n)) :
    smtx_type_fun_like_domains_wf (__smtx_typeof (SmtTerm.choice_nth s T body n)) := by
  induction n generalizing s T body with
  | zero =>
      have hGuardTy :
          __smtx_typeof (SmtTerm.choice_nth s T body 0) = __smtx_typeof_guard_wf T T :=
        Smtm.choice_term_guard_type_of_non_none hNN
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        intro hNone
        unfold term_has_non_none_type at hNN
        rw [hGuardTy, hNone] at hNN
        exact hNN rfl
      have hWf : __smtx_type_wf T = true :=
        Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      have hTy : __smtx_typeof (SmtTerm.choice_nth s T body 0) = T :=
        Smtm.choice_term_typeof_of_non_none hNN
      rw [hTy]
      exact smtx_type_fun_like_domains_wf_of_type_wf hWf
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof (SmtTerm.choice_nth s T (SmtTerm.exists s' U body') (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_136, __smtx_typeof.eq_136]
            simp [__smtx_typeof_choice_nth]
          have hNN' : term_has_non_none_type (SmtTerm.choice_nth s' U body' n) := by
            unfold term_has_non_none_type at hNN ⊢
            rw [← hTyEq]
            exact hNN
          simpa [hTyEq] using ih s' U body' hNN'
      | _ =>
          exfalso
          unfold term_has_non_none_type at hNN
          rw [__smtx_typeof.eq_136] at hNN
          simp [__smtx_typeof_choice_nth] at hNN

private theorem smtx_typeof_dt_cons_rec_datatype_ne_fun
    (s : native_String) (d0 : SmtDatatype) :
    ∀ (d : SmtDatatype) (i : native_Nat) (A B : SmtType),
      __smtx_typeof_dt_cons_rec (SmtType.Datatype s d0) d i ≠ SmtType.FunType A B
  | SmtDatatype.null, i, A, B => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, A, B => by
      simp [__smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero, A, B => by
      simp [__smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum c d, native_nat_succ i, A, B => by
      simpa [__smtx_typeof_dt_cons_rec] using
        smtx_typeof_dt_cons_rec_datatype_ne_fun s d0 d i A B

private theorem smtx_typeof_dt_cons_rec_datatype_arg_field_wf_of_wf
    (s : native_String) (d0 : SmtDatatype) :
    ∀ (d : SmtDatatype) (i : native_Nat) (refs : RefList) {A B : SmtType},
      __smtx_dt_wf_rec d refs = true ->
      __smtx_typeof_dt_cons_rec (SmtType.Datatype s d0) d i = SmtType.DtcAppType A B ->
      smtx_type_field_wf_rec A refs
  | SmtDatatype.null, i, refs, A, B, _hWf, hRaw => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec] at hRaw
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, refs, A, B, _hWf, hRaw => by
      simp [__smtx_typeof_dt_cons_rec] at hRaw
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero, refs, A, B, hWf, hRaw => by
      have hCons :
          __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons U c) refs = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      have hField : smtx_type_field_wf_rec U refs :=
        smtx_type_field_wf_rec_of_cons_wf hCons
      have hA : U = A := by
        have hRaw' :
            SmtType.DtcAppType U
                (__smtx_typeof_dt_cons_rec (SmtType.Datatype s d0) (SmtDatatype.sum c d)
                  native_nat_zero) =
              SmtType.DtcAppType A B := by
          simpa [__smtx_typeof_dt_cons_rec] using hRaw
        injection hRaw' with hU _
      subst A
      exact hField
  | SmtDatatype.sum c d, native_nat_succ i, refs, A, B, hWf, hRaw => by
      cases d with
      | null =>
          simp [__smtx_typeof_dt_cons_rec] at hRaw
      | sum cTail dTail =>
          have hTail : __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true :=
            smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
          have hRaw' :
              __smtx_typeof_dt_cons_rec (SmtType.Datatype s d0)
                  (SmtDatatype.sum cTail dTail) i =
                SmtType.DtcAppType A B := by
            simpa [__smtx_typeof_dt_cons_rec] using hRaw
          exact smtx_typeof_dt_cons_rec_datatype_arg_field_wf_of_wf
            s d0 (SmtDatatype.sum cTail dTail) i refs hTail hRaw'

private theorem smtx_typeof_dt_cons_rec_domains_wf_of_wf_nil
    (s : native_String) (d0 : SmtDatatype) :
    ∀ (d : SmtDatatype) (i : native_Nat),
      __smtx_dt_wf_rec d native_reflist_nil = true ->
      smtx_type_fun_like_domains_wf
        (__smtx_typeof_dt_cons_rec (SmtType.Datatype s d0) d i)
  | SmtDatatype.null, i, hWf => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec, smtx_type_fun_like_domains_wf] at hWf ⊢
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, _hWf => by
      simp [__smtx_typeof_dt_cons_rec, smtx_type_fun_like_domains_wf]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero, hWf => by
      have hCons :
          __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons U c) native_reflist_nil = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      have hField : smtx_type_field_wf_rec U native_reflist_nil :=
        smtx_type_field_wf_rec_of_cons_wf hCons
      have hConsTail :
          __smtx_dt_cons_wf_rec c native_reflist_nil = true :=
        smtx_dt_cons_wf_rec_tail_of_true hCons
      have hSumTail :
          __smtx_dt_wf_rec (SmtDatatype.sum c d) native_reflist_nil = true := by
        cases d with
        | null =>
            simpa [__smtx_dt_wf_rec] using hConsTail
        | sum cTail dTail =>
            have hDTail :
                __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) native_reflist_nil = true :=
              smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
            simp [__smtx_dt_wf_rec, native_ite, hConsTail, hDTail]
      simp [__smtx_typeof_dt_cons_rec, smtx_type_fun_like_domains_wf]
      exact
        ⟨hField, smtx_type_fun_like_domains_wf_of_field_wf_rec hField,
          smtx_typeof_dt_cons_rec_domains_wf_of_wf_nil s d0 (SmtDatatype.sum c d)
            native_nat_zero hSumTail⟩
  | SmtDatatype.sum c d, native_nat_succ i, hWf => by
      cases d with
      | null =>
          simp [__smtx_typeof_dt_cons_rec, smtx_type_fun_like_domains_wf]
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) native_reflist_nil = true :=
            smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
          simpa [__smtx_typeof_dt_cons_rec] using
            smtx_typeof_dt_cons_rec_domains_wf_of_wf_nil s d0
              (SmtDatatype.sum cTail dTail) i hTail

private theorem smtx_typeof_dt_cons_domains_wf_of_non_none
    (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (hNN : term_has_non_none_type (SmtTerm.DtCons s d i)) :
    smtx_type_fun_like_domains_wf (__smtx_typeof (SmtTerm.DtCons s d i)) := by
  let raw := __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Datatype s d) raw ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [Smtm.typeof_dt_cons_eq, raw] using hNN
  have hRawEq : __smtx_typeof (SmtTerm.DtCons s d i) = raw := by
    rw [Smtm.typeof_dt_cons_eq]
    exact smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
  have hBaseTypeWf : __smtx_type_wf (SmtType.Datatype s d) = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
  have hBaseInh : native_inhabited_type (SmtType.Datatype s d) = true := by
    have hPair :
        native_inhabited_type (SmtType.Datatype s d) = true ∧
          __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true := by
      simpa [__smtx_type_wf, native_and] using hBaseTypeWf
    exact hPair.1
  have hBaseWf : __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true := by
    exact datatype_wf_rec_of_type_wf hBaseTypeWf
  have hSubWf : __smtx_dt_wf_rec (__smtx_dt_substitute s d d) native_reflist_nil = true :=
    smtx_dt_substitute_self_wf_apply (s := s) (d := d) (refs := native_reflist_nil)
      hBaseInh hBaseWf
  rw [hRawEq]
  exact smtx_typeof_dt_cons_rec_domains_wf_of_wf_nil s d
    (__smtx_dt_substitute s d d) i hSubWf

private theorem smtx_term_has_non_none_of_type_eq
    {t : SmtTerm} {T : SmtType}
    (h : __smtx_typeof t = T)
    (hT : T ≠ SmtType.None) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type
  rw [h]
  exact hT

private theorem smtx_typeof_apply_dt_sel_domains_wf_of_non_none
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) (x : SmtTerm)
    (hNN : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    smtx_type_fun_like_domains_wf
      (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner :=
    __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    rw [typeof_dt_sel_apply_eq] at hNN
    simpa [R, inner] using hNN
  have hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) = R := by
    simpa [R] using dt_sel_term_typeof_of_non_none hNN
  have hWF : __smtx_type_wf R = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
  rw [hTy]
  exact smtx_type_fun_like_domains_wf_of_type_wf hWF

private theorem smtx_term_fun_like_domains_wf_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t ->
      smtx_type_fun_like_domains_wf (__smtx_typeof t) := by
  let rec go (t : SmtTerm) (hNN : term_has_non_none_type t) :
      smtx_type_fun_like_domains_wf (__smtx_typeof t) := by
    cases t
    case Apply f x =>
        by_cases hSel : ∃ s d i j, f = SmtTerm.DtSel s d i j
        · rcases hSel with ⟨s, d, i, j, rfl⟩
          exact smtx_typeof_apply_dt_sel_domains_wf_of_non_none s d i j x hNN
        · by_cases hTester : ∃ s d i, f = SmtTerm.DtTester s d i
          · rcases hTester with ⟨s, d, i, rfl⟩
            have hTy :
                __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) =
                  SmtType.Bool :=
              dt_tester_term_typeof_of_non_none hNN
            rw [hTy]
            simp [smtx_type_fun_like_domains_wf]
          · have hGeneric :
                generic_apply_type f x :=
              generic_apply_type_of_non_special_head f x
                (by
                  intro s d i j h
                  exact hSel ⟨s, d, i, j, h⟩)
                (by
                  intro s d i h
                  exact hTester ⟨s, d, i, h⟩)
            have hApplyNN :
                __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
              unfold term_has_non_none_type at hNN
              rw [hGeneric] at hNN
              exact hNN
            have hFNN : term_has_non_none_type f := by
              rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, _hX, _hA, _hB⟩
              unfold term_has_non_none_type
              exact smtx_head_non_none_of_apply_cases hHead
            rw [hGeneric]
            exact smtx_type_fun_like_domains_wf_apply (go f hFNN) hApplyNN
    case Var s T =>
        exact smtx_typeof_var_domains_wf_of_non_none s T hNN
    case UConst s T =>
        exact smtx_typeof_uconst_domains_wf_of_non_none s T hNN
    case seq_empty T =>
        exact smtx_typeof_seq_empty_domains_wf_of_non_none T hNN
    case set_empty T =>
        exact smtx_typeof_set_empty_domains_wf_of_non_none T hNN
    case choice_nth s T body n =>
        exact choice_nth_fun_like_domains_wf_any s T body n hNN
    case DtCons s d i =>
        exact smtx_typeof_dt_cons_domains_wf_of_non_none s d i hNN
    case ite c t1 t2 =>
        rcases ite_args_of_non_none hNN with ⟨T, hc, h1, h2, hT⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 hT
        have hTy : __smtx_typeof (SmtTerm.ite c t1 t2) = T := by
          rw [typeof_ite_eq]
          simp [__smtx_typeof_ite, native_ite, native_Teq, hc, h1, h2]
        rw [hTy, ← h1]
        exact go t1 ht1
    case select t1 t2 =>
        rcases select_args_of_non_none hNN with ⟨A, B, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.select t1 t2) = B := by
          rw [typeof_select_eq]
          simp [__smtx_typeof_select, native_ite, native_Teq, h1, h2]
        have hWFMap := go t1 ht1
        rw [hTy]
        rw [h1] at hWFMap
        exact hWFMap.2
    case store t1 t2 t3 =>
        rcases store_args_of_non_none hNN with ⟨A, B, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.store t1 t2 t3) = SmtType.Map A B := by
          rw [typeof_store_eq]
          simp [__smtx_typeof_store, native_ite, native_Teq, h1, h2, h3]
        have hWFMap := go t1 ht1
        rw [hTy]
        rw [h1] at hWFMap
        exact hWFMap
    case seq_unit t =>
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type at hNN ⊢
          rw [__smtx_typeof.eq_118] at hNN
          by_cases hTy : __smtx_typeof t = SmtType.None
          · simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
              native_and, native_ite, hTy] at hNN
          · exact hTy
        have hTy :
            __smtx_typeof (SmtTerm.seq_unit t) = SmtType.Seq (__smtx_typeof t) := by
          rw [__smtx_typeof.eq_118]
          exact smtx_typeof_guard_wf_of_non_none (__smtx_typeof t)
            (SmtType.Seq (__smtx_typeof t)) (by
              unfold term_has_non_none_type at hNN
              rw [__smtx_typeof.eq_118] at hNN
              exact hNN)
        rw [hTy]
        exact go t hArgNN
    case set_singleton t =>
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type at hNN ⊢
          rw [__smtx_typeof.eq_121] at hNN
          by_cases hTy : __smtx_typeof t = SmtType.None
          · simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
              native_and, native_ite, hTy] at hNN
          · exact hTy
        have hTy :
            __smtx_typeof (SmtTerm.set_singleton t) = SmtType.Set (__smtx_typeof t) := by
          rw [__smtx_typeof.eq_121]
          exact smtx_typeof_guard_wf_of_non_none (__smtx_typeof t)
            (SmtType.Set (__smtx_typeof t)) (by
              unfold term_has_non_none_type at hNN
              rw [__smtx_typeof.eq_121] at hNN
              exact hNN)
        rw [hTy]
        exact go t hArgNN
    case seq_nth t1 t2 =>
        rcases seq_nth_args_of_non_none hNN with ⟨T, h1, h2⟩
        have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          unfold term_has_non_none_type at hNN
          rw [typeof_seq_nth_eq, h1, h2] at hNN
          simpa [__smtx_typeof_seq_nth] using hNN
        have hTy : __smtx_typeof (SmtTerm.seq_nth t1 t2) = T := by
          rw [typeof_seq_nth_eq, h1, h2]
          simpa [__smtx_typeof_seq_nth] using
            smtx_typeof_guard_wf_of_non_none T T hGuardNN
        have hWF : __smtx_type_wf T = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
        rw [hTy]
        exact smtx_type_fun_like_domains_wf_of_type_wf hWF
    case str_rev t =>
        rcases seq_arg_of_non_none (op := SmtTerm.str_rev) (t := t)
            (typeof_str_rev_eq t) hNN with ⟨T, h1⟩
        have ht : term_has_non_none_type t :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_rev t) = SmtType.Seq T := by
          rw [typeof_str_rev_eq, h1]
          simp [__smtx_typeof_seq_op_1]
        rw [hTy]
        simpa [h1] using go t ht
    case str_concat t1 t2 =>
        rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat)
            (typeof_str_concat_eq t1 t2) hNN with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_concat t1 t2) = SmtType.Seq T := by
          rw [typeof_str_concat_eq, h1, h2]
          simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_substr t1 t2 t3 =>
        rcases str_substr_args_of_non_none hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_substr t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_substr_eq, h1, h2, h3]
          simp [__smtx_typeof_str_substr]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_at t1 t2 =>
        rcases str_at_args_of_non_none hNN with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_at t1 t2) = SmtType.Seq T := by
          rw [typeof_str_at_eq, h1, h2]
          simp [__smtx_typeof_str_at]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_update t1 t2 t3 =>
        rcases str_update_args_of_non_none hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_update t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_update_eq, h1, h2, h3]
          simp [__smtx_typeof_str_update, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_replace t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
            (typeof_str_replace_eq t1 t2 t3) hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_replace t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_replace_eq, h1, h2, h3]
          simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_replace_all t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
            (typeof_str_replace_all_eq t1 t2 t3) hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_replace_all t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_replace_all_eq, h1, h2, h3]
          simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_union t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
            (typeof_set_union_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_union t1 t2) = SmtType.Set A := by
          rw [typeof_set_union_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_inter t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_inter)
            (typeof_set_inter_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_inter t1 t2) = SmtType.Set A := by
          rw [typeof_set_inter_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_minus t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_minus)
            (typeof_set_minus_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_minus t1 t2) = SmtType.Set A := by
          rw [typeof_set_minus_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    all_goals
      simp only [__smtx_typeof, native_ite,
        __smtx_typeof_bv_op_1, __smtx_typeof_bv_op_1_ret,
        __smtx_typeof_bv_op_2, __smtx_typeof_bv_op_2_ret,
        __smtx_typeof_eq, __smtx_typeof_guard,
        __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2,
        __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_seq_op_1_ret,
        __smtx_typeof_seq_op_2_ret, __smtx_typeof_str_indexof,
        __smtx_typeof_re_exp, __smtx_typeof_re_loop, __smtx_typeof_set_member,
        __smtx_typeof_sets_op_2_ret, __smtx_typeof_int_to_bv,
        __smtx_typeof_concat, __smtx_typeof_extract, __smtx_typeof_repeat,
        __smtx_typeof_zero_extend, __smtx_typeof_sign_extend,
        __smtx_typeof_rotate_left, __smtx_typeof_rotate_right]
      (repeat split) <;> try simp [smtx_type_fun_like_domains_wf]
      all_goals
        split <;> simp [smtx_type_fun_like_domains_wf]
  exact go

private theorem smtx_typeof_guard_wf_translation_injective_wf_of_non_none
    {T U : SmtType}
    (hU : smtx_type_translation_injective_wf U)
    (hNN : __smtx_typeof_guard_wf T U ≠ SmtType.None) :
    smtx_type_translation_injective_wf (__smtx_typeof_guard_wf T U) := by
  rw [smtx_typeof_guard_wf_of_non_none T U hNN]
  exact hU

private theorem smtx_typeof_var_translation_injective_wf_of_non_none
    (s : native_String) (T : SmtType)
    (hNN : term_has_non_none_type (SmtTerm.Var s T)) :
    smtx_type_translation_injective_wf (__smtx_typeof (SmtTerm.Var s T)) := by
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T (by
      unfold term_has_non_none_type at hNN
      simpa [__smtx_typeof] using hNN)
  rw [smtx_typeof_var_of_non_none s T hNN]
  exact smtx_type_translation_injective_wf_of_type_wf hWf

private theorem smtx_typeof_uconst_translation_injective_wf_of_non_none
    (s : native_String) (T : SmtType)
    (hNN : term_has_non_none_type (SmtTerm.UConst s T)) :
    smtx_type_translation_injective_wf (__smtx_typeof (SmtTerm.UConst s T)) := by
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T (by
      unfold term_has_non_none_type at hNN
      simpa [__smtx_typeof] using hNN)
  rw [smtx_typeof_uconst_of_non_none s T hNN]
  exact smtx_type_translation_injective_wf_of_type_wf hWf

private theorem smtx_typeof_seq_empty_translation_injective_wf_of_non_none
    (T : SmtType)
    (hNN : term_has_non_none_type (SmtTerm.seq_empty T)) :
    smtx_type_translation_injective_wf (__smtx_typeof (SmtTerm.seq_empty T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T (SmtType.Seq T) ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [__smtx_typeof] using hNN
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T (SmtType.Seq T) hGuardNN
  rw [smtx_typeof_seq_empty_of_non_none T hNN]
  change smtx_type_translation_injective_wf T
  exact smtx_type_translation_injective_wf_of_type_wf hWf

private theorem smtx_typeof_set_empty_translation_injective_wf_of_non_none
    (T : SmtType)
    (hNN : term_has_non_none_type (SmtTerm.set_empty T)) :
    smtx_type_translation_injective_wf (__smtx_typeof (SmtTerm.set_empty T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T (SmtType.Set T) ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [__smtx_typeof] using hNN
  have hWf : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T (SmtType.Set T) hGuardNN
  rw [smtx_typeof_set_empty_of_non_none T hNN]
  change smtx_type_translation_injective_wf T
  exact smtx_type_translation_injective_wf_of_type_wf hWf

private theorem choice_nth_translation_injective_wf_any
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat)
    (hNN : term_has_non_none_type (SmtTerm.choice_nth s T body n)) :
    smtx_type_translation_injective_wf (__smtx_typeof (SmtTerm.choice_nth s T body n)) := by
  induction n generalizing s T body with
  | zero =>
      have hGuardTy :
          __smtx_typeof (SmtTerm.choice_nth s T body 0) = __smtx_typeof_guard_wf T T :=
        Smtm.choice_term_guard_type_of_non_none hNN
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        intro hNone
        unfold term_has_non_none_type at hNN
        rw [hGuardTy, hNone] at hNN
        exact hNN rfl
      have hWf : __smtx_type_wf T = true :=
        Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      have hTy : __smtx_typeof (SmtTerm.choice_nth s T body 0) = T :=
        Smtm.choice_term_typeof_of_non_none hNN
      rw [hTy]
      exact smtx_type_translation_injective_wf_of_type_wf hWf
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof (SmtTerm.choice_nth s T (SmtTerm.exists s' U body') (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_136, __smtx_typeof.eq_136]
            simp [__smtx_typeof_choice_nth]
          have hNN' : term_has_non_none_type (SmtTerm.choice_nth s' U body' n) := by
            unfold term_has_non_none_type at hNN ⊢
            rw [← hTyEq]
            exact hNN
          simpa [hTyEq] using ih s' U body' hNN'
      | _ =>
          exfalso
          unfold term_has_non_none_type at hNN
          rw [__smtx_typeof.eq_136] at hNN
          simp [__smtx_typeof_choice_nth] at hNN

private theorem smtx_typeof_dt_cons_rec_sum_zero_ne_none
    (s : native_String) (d0 : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (d : SmtDatatype),
      __smtx_typeof_dt_cons_rec (SmtType.Datatype s d0) (SmtDatatype.sum c d)
          native_nat_zero ≠ SmtType.None
  | SmtDatatypeCons.unit, d => by
      simp [__smtx_typeof_dt_cons_rec]
  | SmtDatatypeCons.cons U c, d => by
      simp [__smtx_typeof_dt_cons_rec]

private theorem smtx_typeof_dt_cons_rec_translation_injective_wf_of_wf_nil
    (s : native_String) (d0 : SmtDatatype)
    (hBaseWf : __smtx_dt_wf_rec d0 (native_reflist_insert native_reflist_nil s) = true) :
    ∀ (d : SmtDatatype) (i : native_Nat),
      __smtx_dt_wf_rec d native_reflist_nil = true ->
      __smtx_typeof_dt_cons_rec (SmtType.Datatype s d0) d i ≠ SmtType.None ->
      smtx_type_translation_injective_wf
        (__smtx_typeof_dt_cons_rec (SmtType.Datatype s d0) d i)
  | SmtDatatype.null, i, hWf, hNN => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec] at hNN
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, _hWf, _hNN => by
      simp [__smtx_typeof_dt_cons_rec, smtx_type_translation_injective_wf,
        smtx_type_field_wf_rec, __smtx_type_wf_rec, hBaseWf]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero, hWf, _hNN => by
      have hCons :
          __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons U c) native_reflist_nil = true :=
        smtx_dt_wf_cons_of_sum_wf_apply hWf
      have hField : smtx_type_field_wf_rec U native_reflist_nil :=
        smtx_type_field_wf_rec_of_cons_wf hCons
      have hConsTail :
          __smtx_dt_cons_wf_rec c native_reflist_nil = true :=
        smtx_dt_cons_wf_rec_tail_of_true hCons
      have hSumTail :
          __smtx_dt_wf_rec (SmtDatatype.sum c d) native_reflist_nil = true := by
        cases d with
        | null =>
            simpa [__smtx_dt_wf_rec] using hConsTail
        | sum cTail dTail =>
            have hDTail :
                __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) native_reflist_nil = true :=
              smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
            simp [__smtx_dt_wf_rec, native_ite, hConsTail, hDTail]
      simp [__smtx_typeof_dt_cons_rec, smtx_type_translation_injective_wf]
      exact
        ⟨hField, smtx_type_translation_injective_wf_of_field_wf_rec hField,
          smtx_typeof_dt_cons_rec_translation_injective_wf_of_wf_nil s d0 hBaseWf
            (SmtDatatype.sum c d) native_nat_zero hSumTail
            (smtx_typeof_dt_cons_rec_sum_zero_ne_none s d0 c d)⟩
  | SmtDatatype.sum c d, native_nat_succ i, hWf, hNN => by
      cases d with
      | null =>
          simp [__smtx_typeof_dt_cons_rec] at hNN
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) native_reflist_nil = true :=
            smtx_dt_wf_tail_of_sum_wf_apply (by simp) hWf
          have hTailNN :
              __smtx_typeof_dt_cons_rec (SmtType.Datatype s d0)
                  (SmtDatatype.sum cTail dTail) i ≠ SmtType.None := by
            simpa [__smtx_typeof_dt_cons_rec] using hNN
          simpa [__smtx_typeof_dt_cons_rec] using
            smtx_typeof_dt_cons_rec_translation_injective_wf_of_wf_nil s d0 hBaseWf
              (SmtDatatype.sum cTail dTail) i hTail hTailNN

private theorem smtx_typeof_dt_cons_translation_injective_wf_of_non_none
    (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (hNN : term_has_non_none_type (SmtTerm.DtCons s d i)) :
    smtx_type_translation_injective_wf (__smtx_typeof (SmtTerm.DtCons s d i)) := by
  let raw := __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Datatype s d) raw ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [Smtm.typeof_dt_cons_eq, raw] using hNN
  have hRawEq : __smtx_typeof (SmtTerm.DtCons s d i) = raw := by
    rw [Smtm.typeof_dt_cons_eq]
    exact smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
  have hBaseTypeWf : __smtx_type_wf (SmtType.Datatype s d) = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
  have hBaseInh : native_inhabited_type (SmtType.Datatype s d) = true := by
    have hPair :
        native_inhabited_type (SmtType.Datatype s d) = true ∧
          __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true := by
      simpa [__smtx_type_wf, native_and] using hBaseTypeWf
    exact hPair.1
  have hBaseWf : __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true := by
    exact datatype_wf_rec_of_type_wf hBaseTypeWf
  have hSubWf : __smtx_dt_wf_rec (__smtx_dt_substitute s d d) native_reflist_nil = true :=
    smtx_dt_substitute_self_wf_apply (s := s) (d := d) (refs := native_reflist_nil)
      hBaseInh hBaseWf
  have hRawNN : raw ≠ SmtType.None := by
    rw [← hRawEq]
    simpa [term_has_non_none_type] using hNN
  rw [hRawEq]
  exact smtx_typeof_dt_cons_rec_translation_injective_wf_of_wf_nil s d hBaseWf
    (__smtx_dt_substitute s d d) i hSubWf hRawNN

private theorem smtx_typeof_apply_dt_sel_translation_injective_wf_of_non_none
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) (x : SmtTerm)
    (hNN : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    smtx_type_translation_injective_wf
      (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner :=
    __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    rw [typeof_dt_sel_apply_eq] at hNN
    simpa [R, inner] using hNN
  have hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) = R := by
    simpa [R] using dt_sel_term_typeof_of_non_none hNN
  have hWF : __smtx_type_wf R = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
  rw [hTy]
  exact smtx_type_translation_injective_wf_of_type_wf hWF

private theorem smtx_term_translation_injective_wf_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t ->
      smtx_type_translation_injective_wf (__smtx_typeof t) := by
  let rec go (t : SmtTerm) (hNN : term_has_non_none_type t) :
      smtx_type_translation_injective_wf (__smtx_typeof t) := by
    cases t
    case Apply f x =>
        by_cases hSel : ∃ s d i j, f = SmtTerm.DtSel s d i j
        · rcases hSel with ⟨s, d, i, j, rfl⟩
          exact smtx_typeof_apply_dt_sel_translation_injective_wf_of_non_none s d i j x hNN
        · by_cases hTester : ∃ s d i, f = SmtTerm.DtTester s d i
          · rcases hTester with ⟨s, d, i, rfl⟩
            have hTy :
                __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) =
                  SmtType.Bool :=
              dt_tester_term_typeof_of_non_none hNN
            rw [hTy]
            simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
              __smtx_type_wf_rec]
          · have hGeneric :
                generic_apply_type f x :=
              generic_apply_type_of_non_special_head f x
                (by
                  intro s d i j h
                  exact hSel ⟨s, d, i, j, h⟩)
                (by
                  intro s d i h
                  exact hTester ⟨s, d, i, h⟩)
            have hApplyNN :
                __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
              unfold term_has_non_none_type at hNN
              rw [hGeneric] at hNN
              exact hNN
            have hFNN : term_has_non_none_type f := by
              rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, _hX, _hA, _hB⟩
              unfold term_has_non_none_type
              exact smtx_head_non_none_of_apply_cases hHead
            rw [hGeneric]
            exact smtx_type_translation_injective_wf_apply (go f hFNN) hApplyNN
    case Var s T =>
        exact smtx_typeof_var_translation_injective_wf_of_non_none s T hNN
    case UConst s T =>
        exact smtx_typeof_uconst_translation_injective_wf_of_non_none s T hNN
    case seq_empty T =>
        exact smtx_typeof_seq_empty_translation_injective_wf_of_non_none T hNN
    case set_empty T =>
        exact smtx_typeof_set_empty_translation_injective_wf_of_non_none T hNN
    case choice_nth s T body n =>
        exact choice_nth_translation_injective_wf_any s T body n hNN
    case DtCons s d i =>
        exact smtx_typeof_dt_cons_translation_injective_wf_of_non_none s d i hNN
    case eq t1 t2 =>
        rw [eq_term_typeof_of_non_none hNN]
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
    case to_real t =>
        have hTy : __smtx_typeof (SmtTerm.to_real t) = SmtType.Real := by
          rcases to_real_arg_of_non_none hNN with hArg | hArg
          · rw [typeof_to_real_eq, hArg]
            simp [native_ite, native_Teq]
          · rw [typeof_to_real_eq, hArg]
            simp [native_ite, native_Teq]
        rw [hTy]
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
    case ite c t1 t2 =>
        rcases ite_args_of_non_none hNN with ⟨T, hc, h1, h2, hT⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 hT
        have hTy : __smtx_typeof (SmtTerm.ite c t1 t2) = T := by
          rw [typeof_ite_eq]
          simp [__smtx_typeof_ite, native_ite, native_Teq, hc, h1, h2]
        rw [hTy, ← h1]
        exact go t1 ht1
    case select t1 t2 =>
        rcases select_args_of_non_none hNN with ⟨A, B, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.select t1 t2) = B := by
          rw [typeof_select_eq]
          simp [__smtx_typeof_select, native_ite, native_Teq, h1, h2]
        have hWFMap := go t1 ht1
        rw [hTy]
        rw [h1] at hWFMap
        exact hWFMap.2
    case store t1 t2 t3 =>
        rcases store_args_of_non_none hNN with ⟨A, B, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.store t1 t2 t3) = SmtType.Map A B := by
          rw [typeof_store_eq]
          simp [__smtx_typeof_store, native_ite, native_Teq, h1, h2, h3]
        have hWFMap := go t1 ht1
        rw [hTy]
        rw [h1] at hWFMap
        exact hWFMap
    case seq_unit t =>
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type at hNN ⊢
          rw [__smtx_typeof.eq_118] at hNN
          by_cases hTy : __smtx_typeof t = SmtType.None
          · simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
              native_and, native_ite, hTy] at hNN
          · exact hTy
        have hTy :
            __smtx_typeof (SmtTerm.seq_unit t) = SmtType.Seq (__smtx_typeof t) := by
          rw [__smtx_typeof.eq_118]
          exact smtx_typeof_guard_wf_of_non_none (__smtx_typeof t)
            (SmtType.Seq (__smtx_typeof t)) (by
              unfold term_has_non_none_type at hNN
              rw [__smtx_typeof.eq_118] at hNN
              exact hNN)
        rw [hTy]
        exact go t hArgNN
    case set_singleton t =>
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type at hNN ⊢
          rw [__smtx_typeof.eq_121] at hNN
          by_cases hTy : __smtx_typeof t = SmtType.None
          · simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
              native_and, native_ite, hTy] at hNN
          · exact hTy
        have hTy :
            __smtx_typeof (SmtTerm.set_singleton t) = SmtType.Set (__smtx_typeof t) := by
          rw [__smtx_typeof.eq_121]
          exact smtx_typeof_guard_wf_of_non_none (__smtx_typeof t)
            (SmtType.Set (__smtx_typeof t)) (by
              unfold term_has_non_none_type at hNN
              rw [__smtx_typeof.eq_121] at hNN
              exact hNN)
        rw [hTy]
        exact go t hArgNN
    case seq_nth t1 t2 =>
        rcases seq_nth_args_of_non_none hNN with ⟨T, h1, h2⟩
        have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          unfold term_has_non_none_type at hNN
          rw [typeof_seq_nth_eq, h1, h2] at hNN
          simpa [__smtx_typeof_seq_nth] using hNN
        have hTy : __smtx_typeof (SmtTerm.seq_nth t1 t2) = T := by
          rw [typeof_seq_nth_eq, h1, h2]
          simpa [__smtx_typeof_seq_nth] using
            smtx_typeof_guard_wf_of_non_none T T hGuardNN
        have hWF : __smtx_type_wf T = true :=
          Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
        rw [hTy]
        exact smtx_type_translation_injective_wf_of_type_wf hWF
    case str_rev t =>
        rcases seq_arg_of_non_none (op := SmtTerm.str_rev) (t := t)
            (typeof_str_rev_eq t) hNN with ⟨T, h1⟩
        have ht : term_has_non_none_type t :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_rev t) = SmtType.Seq T := by
          rw [typeof_str_rev_eq, h1]
          simp [__smtx_typeof_seq_op_1]
        rw [hTy]
        simpa [h1] using go t ht
    case str_concat t1 t2 =>
        rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat)
            (typeof_str_concat_eq t1 t2) hNN with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_concat t1 t2) = SmtType.Seq T := by
          rw [typeof_str_concat_eq, h1, h2]
          simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_substr t1 t2 t3 =>
        rcases str_substr_args_of_non_none hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_substr t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_substr_eq, h1, h2, h3]
          simp [__smtx_typeof_str_substr]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_at t1 t2 =>
        rcases str_at_args_of_non_none hNN with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_at t1 t2) = SmtType.Seq T := by
          rw [typeof_str_at_eq, h1, h2]
          simp [__smtx_typeof_str_at]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_update t1 t2 t3 =>
        rcases str_update_args_of_non_none hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_update t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_update_eq, h1, h2, h3]
          simp [__smtx_typeof_str_update, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_replace t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
            (typeof_str_replace_eq t1 t2 t3) hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_replace t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_replace_eq, h1, h2, h3]
          simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case str_replace_all t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
            (typeof_str_replace_all_eq t1 t2 t3) hNN with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.str_replace_all t1 t2 t3) = SmtType.Seq T := by
          rw [typeof_str_replace_all_eq, h1, h2, h3]
          simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_union t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
            (typeof_set_union_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_union t1 t2) = SmtType.Set A := by
          rw [typeof_set_union_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_inter t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_inter)
            (typeof_set_inter_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_inter t1 t2) = SmtType.Set A := by
          rw [typeof_set_inter_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    case set_minus t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_minus)
            (typeof_set_minus_eq t1 t2) hNN with ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 :=
          smtx_term_has_non_none_of_type_eq h1 (by simp)
        have hTy : __smtx_typeof (SmtTerm.set_minus t1 t2) = SmtType.Set A := by
          rw [typeof_set_minus_eq, h1, h2]
          simp [__smtx_typeof_sets_op_2, native_ite, native_Teq]
        rw [hTy]
        simpa [h1] using go t1 ht1
    all_goals
      simp only [__smtx_typeof, native_ite,
        __smtx_typeof_bv_op_1, __smtx_typeof_bv_op_1_ret,
        __smtx_typeof_bv_op_2, __smtx_typeof_bv_op_2_ret,
        __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2,
        __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_seq_op_1_ret,
        __smtx_typeof_seq_op_2_ret, __smtx_typeof_str_indexof,
        __smtx_typeof_re_exp, __smtx_typeof_re_loop, __smtx_typeof_set_member,
        __smtx_typeof_sets_op_2_ret, __smtx_typeof_int_to_bv,
        __smtx_typeof_concat, __smtx_typeof_extract, __smtx_typeof_repeat,
        __smtx_typeof_zero_extend, __smtx_typeof_sign_extend,
        __smtx_typeof_rotate_left, __smtx_typeof_rotate_right]
      (repeat split) <;> try
        simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
          __smtx_type_wf_rec]
      all_goals
        first
        | split <;>
            simp [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
              __smtx_type_wf_rec]
        | exfalso
          unfold term_has_non_none_type at hNN
          simp only [__smtx_typeof, native_ite,
            __smtx_typeof_bv_op_1, __smtx_typeof_bv_op_1_ret,
            __smtx_typeof_bv_op_2, __smtx_typeof_bv_op_2_ret,
            __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2,
            __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_seq_op_1_ret,
            __smtx_typeof_seq_op_2_ret, __smtx_typeof_str_indexof,
            __smtx_typeof_re_exp, __smtx_typeof_re_loop, __smtx_typeof_set_member,
            __smtx_typeof_sets_op_2_ret, __smtx_typeof_int_to_bv,
            __smtx_typeof_concat, __smtx_typeof_extract, __smtx_typeof_repeat,
            __smtx_typeof_zero_extend, __smtx_typeof_sign_extend,
            __smtx_typeof_rotate_left, __smtx_typeof_rotate_right] at hNN
          (repeat split at hNN) <;> simp_all
  exact go

/-- Bridge-free selector application typing, using the local IH for the selector argument. -/
private theorem eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype_from_ih
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hReserved : __eo_reserved_datatype_name s = false)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype d)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hx]
    simp
  have hXType :
      __eo_to_smt_type (__eo_typeof x) =
        SmtType.Datatype s (__eo_to_smt_datatype d) :=
    eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hx (by simp)
  have hName : s ≠ "@Tuple" :=
    eo_unreserved_datatype_name_ne_tuple hReserved
  rcases eo_to_smt_type_eq_datatype_non_tuple hName hXType with ⟨d0, hxEo, hd0⟩
  have hDWF :
      __smtx_dt_wf_rec (__eo_to_smt_datatype d)
        (native_reflist_insert native_reflist_nil s) = true := by
    have hWF :=
      smtx_term_translation_injective_wf_of_non_none (__eo_to_smt x) (by
        simpa [term_has_non_none_type] using hxNN)
    rw [hx] at hWF
    simpa [smtx_type_translation_injective_wf, smtx_type_field_wf_rec,
      __smtx_type_wf_rec] using hWF
  have hdEq : d0 = d :=
    eo_to_smt_datatype_injective_of_wf_rec hd0 rfl hDWF
  subst d0
  exact eo_to_smt_type_typeof_apply_dt_sel_of_datatype_type_smt_ret x s d i j hxEo

private theorem smtx_set_elem_translation_injective_wf_of_type_eq
    {t : SmtTerm} {T : SmtType}
    (h : __smtx_typeof t = SmtType.Set T) :
    smtx_type_translation_injective_wf T := by
  have hNN : term_has_non_none_type t :=
    smtx_term_has_non_none_of_type_eq h (by simp)
  have hWF := smtx_term_translation_injective_wf_of_non_none t hNN
  rw [h] at hWF
  exact hWF

private theorem smtx_seq_elem_translation_injective_wf_of_type_eq
    {t : SmtTerm} {T : SmtType}
    (h : __smtx_typeof t = SmtType.Seq T) :
    smtx_type_translation_injective_wf T := by
  have hNN : term_has_non_none_type t :=
    smtx_term_has_non_none_of_type_eq h (by simp)
  have hWF := smtx_term_translation_injective_wf_of_non_none t hNN
  rw [h] at hWF
  exact hWF

private theorem eo_to_smt_type_seq_of_elem_eq
    {U : Term} {T : SmtType}
    (hU : __eo_to_smt_type U = T)
    (hTNN : T ≠ SmtType.None) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) = SmtType.Seq T := by
  change __smtx_typeof_guard (__eo_to_smt_type U) (SmtType.Seq (__eo_to_smt_type U)) =
    SmtType.Seq T
  rw [hU]
  exact smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN

private theorem eo_to_smt_type_typeof_set_union_like_of_smt_set_from_ih
    (x y : Term) (T : SmtType)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Set T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Set T) :
    __eo_to_smt_type (__eo_typeof_set_union (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Set T := by
  rcases eo_typeof_eq_set_of_smt_set_from_ih y ihY hy with ⟨U, hYSet, hU⟩
  rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX hx with ⟨V, hXSet, hV⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_set_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt y) hy
  have hUV : U = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
  subst V
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hSetTrans :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) U) = SmtType.Set T := by
    change __smtx_typeof_guard (__eo_to_smt_type U)
        (SmtType.Set (__eo_to_smt_type U)) = SmtType.Set T
    rw [hU]
    exact smtx_typeof_guard_of_non_none T (SmtType.Set T) hTNN
  rw [hYSet, hXSet]
  rw [show
      __eo_typeof_set_union (Term.Apply (Term.UOp UserOp.Set) U)
          (Term.Apply (Term.UOp UserOp.Set) U) =
        Term.Apply (Term.UOp UserOp.Set) U by
    cases U <;> simp [__eo_typeof_set_union, __eo_eq, __eo_requires, native_teq,
      native_ite, native_not, __eo_to_smt_type] at hU ⊢
    exact hTNN hU.symm]
  exact hSetTrans

private theorem eo_to_smt_type_typeof_apply_apply_set_union_of_smt_set_from_ih
    (x y : Term) (T : SmtType)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Set T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Set T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_union) y) x)) =
      SmtType.Set T := by
  change __eo_to_smt_type (__eo_typeof_set_union (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Set T
  exact eo_to_smt_type_typeof_set_union_like_of_smt_set_from_ih x y T ihY ihX hy hx

private theorem eo_to_smt_type_typeof_apply_apply_set_inter_of_smt_set_from_ih
    (x y : Term) (T : SmtType)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Set T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Set T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_inter) y) x)) =
      SmtType.Set T := by
  change __eo_to_smt_type (__eo_typeof_set_union (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Set T
  exact eo_to_smt_type_typeof_set_union_like_of_smt_set_from_ih x y T ihY ihX hy hx

private theorem eo_to_smt_type_typeof_apply_apply_set_minus_of_smt_set_from_ih
    (x y : Term) (T : SmtType)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Set T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Set T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_minus) y) x)) =
      SmtType.Set T := by
  change __eo_to_smt_type (__eo_typeof_set_union (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Set T
  exact eo_to_smt_type_typeof_set_union_like_of_smt_set_from_ih x y T ihY ihX hy hx

private theorem eo_to_smt_type_typeof_apply_apply_set_subset_of_smt_set_from_ih
    (x y : Term) (T : SmtType)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Set T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Set T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) y) x)) =
      SmtType.Bool := by
  rcases eo_typeof_eq_set_of_smt_set_from_ih y ihY hy with ⟨U, hYSet, hU⟩
  rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX hx with ⟨V, hXSet, hV⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_set_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt y) hy
  have hUV : U = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
  subst V
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  change __eo_to_smt_type (__eo_typeof_set_subset (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Bool
  rw [hYSet, hXSet]
  rw [show
      __eo_typeof_set_subset (Term.Apply (Term.UOp UserOp.Set) U)
          (Term.Apply (Term.UOp UserOp.Set) U) =
        Term.Bool by
    cases U <;> simp [__eo_typeof_set_subset, __eo_eq, __eo_requires, native_teq,
      native_ite, native_not, __eo_to_smt_type] at hU ⊢
    exact hTNN hU.symm]
  rfl

private theorem eo_to_smt_type_typeof_apply_apply_str_contains_of_smt_seq_from_ih
    (x y : Term) (T : SmtType)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) y) x)) =
      SmtType.Bool := by
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hy with ⟨U, hYSeq, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hx with ⟨V, hXSeq, hV⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_seq_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt y) hy
  have hUV : U = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
  subst V
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  exact eo_to_smt_type_typeof_apply_apply_str_contains_of_seq x y U hYSeq hXSeq
    (by rw [hU]; exact hTNN)

private theorem eo_to_smt_type_typeof_apply_apply_str_concat_of_smt_seq_from_ih
    (x y : Term) (T : SmtType)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x)) =
      SmtType.Seq T := by
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hy with ⟨U, hYSeq, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hx with ⟨V, hXSeq, hV⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_seq_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt y) hy
  have hUV : U = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
  subst V
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hEo :=
    eo_to_smt_type_typeof_apply_apply_str_concat_of_seq x y U hYSeq hXSeq
      (by rw [hU]; exact hTNN)
  have hSeq :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) = SmtType.Seq T := by
    change __smtx_typeof_guard (__eo_to_smt_type U) (SmtType.Seq (__eo_to_smt_type U)) =
      SmtType.Seq T
    rw [hU]
    exact smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN
  exact hEo.trans hSeq

private theorem eo_to_smt_typeof_matches_translation_apply_set_member_from_ih
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x) =
        SmtTerm.set_member (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.set_member (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases set_member_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_set_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt x) hX
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = T :=
    eo_to_smt_type_typeof_of_smt_type_from_ih y ihY hY hTNN
  rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX hX with ⟨U, hXSet, hU⟩
  have hYEq : __eo_typeof y = U :=
    eo_to_smt_type_injective_of_translation_injective_wf hYTrans hU hWF
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, typeof_set_member_eq]
    simp [__smtx_typeof_set_member, hY, hX, native_ite, native_Teq]
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) y) x)) =
        SmtType.Bool := by
    change __eo_to_smt_type (__eo_typeof_set_member (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Bool
    rw [hYEq, hXSet]
    rw [show
        __eo_typeof_set_member U (Term.Apply (Term.UOp UserOp.Set) U) =
          Term.Bool by
      cases U <;> simp [__eo_typeof_set_member, __eo_eq, __eo_requires, native_teq,
        native_ite, native_not, __eo_to_smt_type] at hU ⊢
      exact hTNN hU.symm]
    rfl
  exact hSmt.trans hEo.symm

/--
Bridge-free nested generic application once the translated head is known to be
ordinary SMT application. This is the version needed by `Full.lean`: it threads
the explicit IH for the outer argument instead of reaching through
the global type-recovery bridge.
-/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_generic_from_ih
    (g y x : Term)
    (ihHead :
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply g y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply g y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply g y)) (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g y) x)) := by
  intro hNonNone
  have hArgWF :
      ∀ A B,
        (__smtx_typeof (__eo_to_smt (Term.Apply g y)) = SmtType.FunType A B ∨
          __smtx_typeof (__eo_to_smt (Term.Apply g y)) = SmtType.DtcAppType A B) ->
        smtx_type_field_wf_rec A native_reflist_nil := by
    intro A B hHead
    have hHeadNN : term_has_non_none_type (__eo_to_smt (Term.Apply g y)) := by
      unfold term_has_non_none_type
      exact smtx_head_non_none_of_apply_cases hHead
    exact smtx_type_fun_like_arg_field_wf_of_domains_wf
      (smtx_term_fun_like_domains_wf_of_non_none _ hHeadNN) hHead
  exact eo_to_smt_typeof_matches_translation_apply_generic_of_field_wf
    (Term.Apply g y) x ihHead ihX hGeneric hTranslate hEoApply hArgWF hNonNone

/--
Bridge-free ternary nested generic application. This mirrors the older generic
helper but receives the final argument IH explicitly.
-/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_from_ih
    (g z y x : Term)
    (ihHead :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.Apply g z) y)) (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x)) := by
  intro hNonNone
  have hArgWF :
      ∀ A B,
        (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) = SmtType.FunType A B ∨
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) = SmtType.DtcAppType A B) ->
        smtx_type_field_wf_rec A native_reflist_nil := by
    intro A B hHead
    have hHeadNN :
        term_has_non_none_type (__eo_to_smt (Term.Apply (Term.Apply g z) y)) := by
      unfold term_has_non_none_type
      exact smtx_head_non_none_of_apply_cases hHead
    exact smtx_type_fun_like_arg_field_wf_of_domains_wf
      (smtx_term_fun_like_domains_wf_of_non_none _ hHeadNN) hHead
  exact eo_to_smt_typeof_matches_translation_apply_generic_of_field_wf
    (Term.Apply (Term.Apply g z) y) x ihHead ihX hGeneric hTranslate hEoApply hArgWF hNonNone

/-- Bridge-free variant for exposed non-special heads shaped as `(UOp op) y`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
    (op : UserOp) (y x : Term) (head : SmtTerm)
    (ihHead :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp op) y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.UOp op) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.UOp op) y)) (__eo_typeof x))
    (hSel : ∀ s d i j, head ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, head ≠ SmtTerm.DtTester s d i) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x)) := by
  intro hNonNone
  have hGeneric :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.UOp op) y)) (__eo_to_smt x) := by
    simpa [hHeadTranslate] using
      (generic_apply_type_of_non_special_head head (__eo_to_smt x) hSel hTester)
  exact eo_to_smt_typeof_matches_translation_apply_apply_generic_from_ih
    (Term.UOp op) y x ihHead ihX hGeneric hOuterTranslate hEoApply hNonNone

private theorem eo_to_smt_type_typeof_apply_dt_cons_of_smt_apply_from_ih
    (x : Term) (s : native_String) (d : Datatype) (i : native_Nat) (A B : SmtType)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hReserved : __eo_reserved_datatype_name s = false)
    (hHead :
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) = SmtType.FunType A B ∨
        __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hA : A ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtCons s d i) x)) = B := by
  have hHeadNN :
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) ≠ SmtType.None := by
    intro hNone
    rcases hHead with hHead | hHead <;> rw [hNone] at hHead <;> cases hHead
  let dSmt := __eo_to_smt_datatype d
  let raw := __smtx_typeof_dt_cons_rec (SmtType.Datatype s dSmt)
    (__smtx_dt_substitute s dSmt dSmt) i
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Datatype s dSmt) raw ≠ SmtType.None := by
    simpa [dSmt, raw, Smtm.typeof_dt_cons_eq] using hHeadNN
  have hTypeofEq : __smtx_typeof (SmtTerm.DtCons s dSmt i) = raw := by
    rw [Smtm.typeof_dt_cons_eq]
    exact smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s dSmt) raw hGuardNN
  have hBaseWf : __smtx_dt_wf_rec dSmt (native_reflist_insert native_reflist_nil s) = true := by
    have hWf := Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s dSmt) raw hGuardNN
    exact datatype_wf_rec_of_type_wf hWf
  have hBaseInh : native_inhabited_type (SmtType.Datatype s dSmt) = true := by
    have hWf := Smtm.smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s dSmt) raw hGuardNN
    have hPair :
        native_inhabited_type (SmtType.Datatype s dSmt) = true ∧
          __smtx_type_wf_rec (SmtType.Datatype s dSmt) native_reflist_nil = true := by
      simpa [__smtx_type_wf, native_and] using hWf
    exact hPair.1
  have hHeadTy :
      __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
        __smtx_typeof (SmtTerm.DtCons s dSmt i) :=
    eo_to_smt_type_typeof_dt_cons s d i hReserved (by simpa [dSmt] using hHeadNN)
  rcases hHead with hHeadFun | hHeadDtc
  · have hRawFun : raw = SmtType.FunType A B := hTypeofEq.symm.trans hHeadFun
    exact False.elim
      ((smtx_typeof_dt_cons_rec_datatype_ne_fun s dSmt
        (__smtx_dt_substitute s dSmt dSmt) i A B) hRawFun)
  · have hRawDtc : raw = SmtType.DtcAppType A B := hTypeofEq.symm.trans hHeadDtc
    have hSubWf :
        __smtx_dt_wf_rec (__smtx_dt_substitute s dSmt dSmt) native_reflist_nil = true :=
      smtx_dt_substitute_self_wf_apply (s := s) (d := dSmt) (refs := native_reflist_nil)
        hBaseInh hBaseWf
    have hArgWF : smtx_type_field_wf_rec A native_reflist_nil :=
      smtx_typeof_dt_cons_rec_datatype_arg_field_wf_of_wf s dSmt
        (__smtx_dt_substitute s dSmt dSmt) i native_reflist_nil hSubWf hRawDtc
    have hFTrans :
        __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = SmtType.DtcAppType A B := by
      exact hHeadTy.trans (by simpa [dSmt] using hHeadDtc)
    rcases eo_to_smt_type_eq_dtc_app hFTrans with ⟨U, V, hFEq, hU, hV⟩
    have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
      eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hx hA
    have hxEo : __eo_typeof x = U :=
      eo_to_smt_type_injective_of_field_wf_rec hXTrans hU hArgWF
    have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
      rw [hU]
      exact hA
    exact
      (eo_to_smt_type_typeof_apply_dt_cons_of_fun_like
        x U V s d i (Or.inr hFEq) hxEo hUNonNone).trans hV

/-- Computes the type of a non-`None` `re_exp` term. -/
private theorem re_exp_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.re_exp t1 t2)) :
    __smtx_typeof (SmtTerm.re_exp t1 t2) = SmtType.RegLan := by
  rw [typeof_re_exp_eq]
  unfold term_has_non_none_type at ht
  rw [typeof_re_exp_eq] at ht
  cases t1 <;> simp [__smtx_typeof_re_exp] at ht ⊢
  case Numeral n =>
    cases h2 : __smtx_typeof t2 <;> simp [h2] at ht ⊢
    by_cases hn : native_zleq 0 n <;> simp [hn, native_ite] at ht ⊢

/-- Extracts the argument types of a non-`None` `re_exp` term. -/
private theorem re_exp_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.re_exp t1 t2)) :
    (∃ n : native_Int, t1 = SmtTerm.Numeral n ∧ native_zleq 0 n = true) ∧
      __smtx_typeof t2 = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  rw [typeof_re_exp_eq] at ht
  cases t1 <;> simp [__smtx_typeof_re_exp] at ht
  case Numeral n =>
    cases h2 : __smtx_typeof t2 <;> simp [h2] at ht
    by_cases hn : native_zleq 0 n = true
    · exact ⟨⟨n, rfl, hn⟩, rfl⟩
    · exfalso
      cases hz : native_zleq 0 n <;> simp [hz] at hn ht
      exact ht rfl

/-- Simplifies EO-to-SMT translation for `re_exp`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_re_exp
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_exp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_exp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_exp) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_exp) y) x) =
        SmtTerm.re_exp (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (SmtTerm.re_exp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_exp) y) x)) =
        SmtType.RegLan := by
    rw [hTranslate]
    exact re_exp_typeof_of_non_none hApplyNN
  rcases re_exp_args_of_non_none hApplyNN with ⟨⟨n, hYNum, _hn⟩, hXRegLan⟩
  have hYInt : __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
    rw [hYNum]
    unfold __smtx_typeof
    rfl
  have hYEo : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hYInt
  have hXEo : __eo_typeof x = Term.UOp UserOp.RegLan :=
    eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hXRegLan
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_exp) y) x)) =
        SmtType.RegLan := by
    change __eo_to_smt_type (__eo_typeof_re_exp (__eo_typeof y) (__eo_typeof x)) =
      SmtType.RegLan
    rw [hYEo, hXEo]
    rfl
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `_at_strings_itos_result`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_strings_itos_result
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) y) x)) := by
  let rhs := SmtTerm.mod (__eo_to_smt y)
    (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x))
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) y) x) =
        rhs := by
    rfl
  have hApplyNN : term_has_non_none_type rhs := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod) (R := SmtType.Int)
    (typeof_mod_eq (__eo_to_smt y)
      (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x))) hApplyNN
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) y) x)) =
        SmtType.Int := by
    rw [hTranslate]
    change __smtx_typeof
        (SmtTerm.mod (__eo_to_smt y)
          (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x))) = SmtType.Int
    rw [typeof_mod_eq (__eo_to_smt y)
      (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x))]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  have hMulNN :
      term_has_non_none_type
        (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hArgs.2]
    simp
  have hMulArgs := int_binop_args_of_non_none (op := SmtTerm.multmult) (R := SmtType.Int)
    (typeof_multmult_eq (SmtTerm.Numeral 10) (__eo_to_smt x)) hMulNN
  have hYEo : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hArgs.1
  have hXEo : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hMulArgs.2
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) y) x)) =
        SmtType.Int := by
    change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
    rw [hYEo, hXEo]
    rfl
  exact hSmt.trans hEo.symm

/-- Computes the type of a non-`None` `_at_bv` translation. -/
private theorem at_bv_typeof_of_non_none
    {a b : SmtTerm}
    (hNN : term_has_non_none_type (__eo_to_smt__at_bv a b)) :
    ∃ w : native_Nat, __smtx_typeof (__eo_to_smt__at_bv a b) = SmtType.BitVec w := by
  cases a <;> simp [__eo_to_smt__at_bv, term_has_non_none_type] at hNN
  case Numeral n =>
    cases b <;> simp at hNN
    case Numeral w =>
      cases hWidth : native_zleq 0 w <;>
        simp [__eo_to_smt__at_bv, hWidth, native_ite] at hNN ⊢
      have hBinaryNN :
          __smtx_typeof (SmtTerm.Binary w (native_mod_total n (native_int_pow2 w))) ≠
            SmtType.None := by
        simpa [__eo_to_smt__at_bv, hWidth, native_ite] using hNN
      exact ⟨native_int_to_nat w, by
        simpa [__eo_to_smt__at_bv, hWidth, native_ite] using
          smtx_typeof_binary_of_non_none w (native_mod_total n (native_int_pow2 w)) hBinaryNN⟩

/-- Simplifies EO-to-SMT translation for `_at_bit`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_bit
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_bit) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_bit) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_bit) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_bit) y) x) =
        SmtTerm.eq
          (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x))
          (SmtTerm.Binary 1 1) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.eq
          (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x))
          (SmtTerm.Binary 1 1)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)))
          (SmtType.BitVec 1) ≠
        SmtType.None := by
    unfold term_has_non_none_type at hApplyNN
    rw [typeof_eq_eq, typeof_binary_one_eq] at hApplyNN
    exact hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_bit) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, typeof_eq_eq, typeof_binary_one_eq]
    cases hExt : __smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) <;>
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, hExt] at hEqNN ⊢
    exact hEqNN
  have hExtTy :
      __smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec 1 :=
    by
      by_cases hNone :
          __smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) =
            SmtType.None
      · exfalso
        exact hEqNN (by
          rw [hNone]
          simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq])
      · by_cases hEq :
          __smtx_typeof (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) =
            SmtType.BitVec 1
        · exact hEq
        · exfalso
          exact hEqNN (by
            simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, hNone, hEq])
  have hExtNN :
      term_has_non_none_type (SmtTerm.extract (__eo_to_smt y) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hExtTy]
    simp
  rcases extract_args_of_non_none hExtNN with ⟨i, _j, w, hYNum, _hYNum', hX, _hj0, _hji, _hiw⟩
  have hYSmt : __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
    rw [hYNum]
    unfold __smtx_typeof
    rfl
  have hYEo : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hYSmt
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hX
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_bit) y) x)) =
        SmtType.Bool := by
    change __eo_to_smt_type (__eo_typeof__at_bit (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Bool
    rw [hYEo, hXEo]
    rfl
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `_at_from_bools`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_from_bools
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) := by
  let bit :=
    SmtTerm.ite (__eo_to_smt y) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x) =
        SmtTerm.concat bit (__eo_to_smt x) := by
    rfl
  have hApplyNN : term_has_non_none_type (SmtTerm.concat bit (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_concat_args_of_non_none hApplyNN with ⟨w1, w2, hBit, hX⟩
  have hBitNN : term_has_non_none_type bit := by
    unfold term_has_non_none_type
    rw [hBit]
    simp
  rcases ite_args_of_non_none hBitNN with ⟨T, hY, hThen, hElse, hT⟩
  have hBitTy : __smtx_typeof bit = T := by
    rw [show bit =
        SmtTerm.ite (__eo_to_smt y) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0) by rfl]
    rw [typeof_ite_eq, hY, hThen, hElse]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hThenNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    rw [hThen]
    exact hT
  have hTBitVec1 : T = SmtType.BitVec 1 :=
    hThen.symm.trans (smtx_typeof_binary_of_non_none 1 1 hThenNN)
  have hW1 : w1 = 1 := by
    have hEq : SmtType.BitVec w1 = SmtType.BitVec 1 :=
      hBit.symm.trans (hBitTy.trans hTBitVec1)
    cases hEq
    rfl
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
    rw [hTranslate, typeof_concat_eq bit (__eo_to_smt x)]
    simp [__smtx_typeof_concat, hBit, hX]
  have hYEo : __eo_typeof y = Term.Bool :=
    eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hY
  have hXEo :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w2)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w2 hX
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
    change
      __eo_to_smt_type (__eo_typeof__at_from_bools (__eo_typeof y) (__eo_typeof x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2)))
    rw [hYEo, hXEo, hW1]
    have hNonnegProp : (0 : Int) ≤ native_zplus 1 (native_nat_to_int w2) := by
      unfold native_zplus native_nat_to_int
      exact Int.add_nonneg (by decide) (Int.natCast_nonneg w2)
    have hNonneg : native_zleq 0 (native_zplus 1 (native_nat_to_int w2)) = true := by
      unfold native_zleq
      simp [hNonnegProp]
    change
      native_ite (native_zleq 0 (native_zplus 1 (native_nat_to_int w2)))
        (SmtType.BitVec (native_int_to_nat (native_zplus 1 (native_nat_to_int w2))))
        SmtType.None =
      SmtType.BitVec
        (native_int_to_nat (native_zplus (native_nat_to_int 1) (native_nat_to_int w2)))
    rw [hNonneg]
    rfl
  exact hSmt.trans hEo.symm

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

/-- Recovers Boolean typing of a zero-index `choice_nth` body from `non_none`. -/
private theorem choice_nth_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body 0)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
  · simpa [native_Teq] using hEq
  · have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
      cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
    exfalso
    apply ht
    unfold __smtx_typeof
    simp [__smtx_typeof_choice_nth, hEqFalse, native_ite]

/-- Simplifies EO-to-SMT translation for `_at_bv`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_bv
    (x y : Term)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_bv) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_bv) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_bv) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_bv) y) x) =
        __eo_to_smt__at_bv (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type (__eo_to_smt__at_bv (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases at_bv_typeof_of_non_none hApplyNN with ⟨w, hSmt'⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_bv) y) x)) =
        SmtType.BitVec w := by
    rw [hTranslate]
    exact hSmt'
  exact hSmt.trans
    (eo_to_smt_type_typeof_of_smt_type
      (Term.Apply (Term.Apply (Term.UOp UserOp._at_bv) y) x) hSmt (by simp)).symm

/-- Simplifies EO-to-SMT translation for `_at_strings_deq_diff`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_strings_deq_diff
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) y) x)) := by
  let body :=
    SmtTerm.not
      (SmtTerm.eq
        (SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Var "@x" SmtType.Int) (SmtTerm.Numeral 1))
        (SmtTerm.str_substr (__eo_to_smt x) (SmtTerm.Var "@x" SmtType.Int) (SmtTerm.Numeral 1)))
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) y) x) =
        SmtTerm.choice_nth "@x" SmtType.Int body native_nat_zero := by
    rfl
  have hChoiceNN : term_has_non_none_type (SmtTerm.choice_nth "@x" SmtType.Int body 0) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) y) x)) =
        SmtType.Int := by
    rw [hTranslate]
    exact choice_term_typeof_of_non_none hChoiceNN
  let subY :=
    SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Var "@x" SmtType.Int)
      (SmtTerm.Numeral 1)
  let subX :=
    SmtTerm.str_substr (__eo_to_smt x) (SmtTerm.Var "@x" SmtType.Int)
      (SmtTerm.Numeral 1)
  let eqBody := SmtTerm.eq subY subX
  have hBodyBool : __smtx_typeof body = SmtType.Bool :=
    choice_nth_body_bool_of_non_none hChoiceNN
  have hEqBodyBool : __smtx_typeof eqBody = SmtType.Bool := by
    have hNotNN : __smtx_typeof (SmtTerm.not eqBody) ≠ SmtType.None := by
      have hNotTy : __smtx_typeof (SmtTerm.not eqBody) = SmtType.Bool := by
        simpa [body, eqBody, subY, subX] using hBodyBool
      rw [hNotTy]
      simp
    rw [typeof_not_eq] at hNotNN
    cases hEqTy : __smtx_typeof eqBody <;>
      simp [hEqTy, native_ite, native_Teq] at hNotNN ⊢
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof subY) (__smtx_typeof subX) ≠ SmtType.None := by
    have hEqBodyNN : __smtx_typeof eqBody ≠ SmtType.None := by
      rw [hEqBodyBool]
      simp
    simpa [eqBody, typeof_eq_eq] using hEqBodyNN
  have hEqArgs := smtx_typeof_eq_non_none hEqNN
  have hSubYNN : term_has_non_none_type subY := by
    unfold term_has_non_none_type
    exact hEqArgs.2
  have hSubXNN : term_has_non_none_type subX := by
    unfold term_has_non_none_type
    rw [← hEqArgs.1]
    exact hEqArgs.2
  rcases str_substr_args_of_non_none hSubYNN with ⟨T, hYSeq, hYIdx, hYLen⟩
  rcases str_substr_args_of_non_none hSubXNN with ⟨U, hXSeq, hXIdx, hXLen⟩
  have hSubYTy : __smtx_typeof subY = SmtType.Seq T := by
    rw [show subY =
        SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Var "@x" SmtType.Int)
          (SmtTerm.Numeral 1) by rfl]
    rw [typeof_str_substr_eq (__eo_to_smt y) (SmtTerm.Var "@x" SmtType.Int)
      (SmtTerm.Numeral 1), hYSeq, hYIdx, hYLen]
    simp [__smtx_typeof_str_substr]
  have hSubXTy : __smtx_typeof subX = SmtType.Seq U := by
    rw [show subX =
        SmtTerm.str_substr (__eo_to_smt x) (SmtTerm.Var "@x" SmtType.Int)
          (SmtTerm.Numeral 1) by rfl]
    rw [typeof_str_substr_eq (__eo_to_smt x) (SmtTerm.Var "@x" SmtType.Int)
      (SmtTerm.Numeral 1), hXSeq, hXIdx, hXLen]
    simp [__smtx_typeof_str_substr]
  have hTU : T = U := by
    have hSeqEq : SmtType.Seq T = SmtType.Seq U :=
      hSubYTy.symm.trans (hEqArgs.1.trans hSubXTy)
    cases hSeqEq
    rfl
  subst U
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hYSeq with ⟨V, hYSeqEo, hV⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hXSeq with ⟨W, hXSeqEo, hW⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_seq_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt y) hYSeq
  have hVW : V = W :=
    eo_to_smt_type_injective_of_translation_injective_wf hV hW hWF
  subst W
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hVNN : __eo_to_smt_type V ≠ SmtType.None := by
    rw [hV]
    exact hTNN
  have hVNS : V ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none V hVNN
  have hReq :
      __eo_requires (__eo_eq V V) (Term.Boolean true) (Term.UOp UserOp.Int) =
        Term.UOp UserOp.Int :=
    eo_requires_eo_eq_self_of_non_stuck V (Term.UOp UserOp.Int) hVNS
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) y) x)) =
        SmtType.Int := by
    change
      __eo_to_smt_type
          (__eo_typeof__at_strings_deq_diff (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Int
    rw [hYSeqEo, hXSeqEo]
    simpa [__eo_typeof__at_strings_deq_diff] using congrArg __eo_to_smt_type hReq
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for `_at_strings_num_occur`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_at_strings_num_occur
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) := by
  let pattern := __eo_to_smt x
  let source := __eo_to_smt y
  let numerator :=
    SmtTerm.neg (SmtTerm.str_len source)
      (SmtTerm.str_len
        (SmtTerm.str_replace_all source pattern (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))))
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x) =
        SmtTerm.div numerator (SmtTerm.str_len pattern) := by
    rfl
  have hApplyNN : term_has_non_none_type (SmtTerm.div numerator (SmtTerm.str_len pattern)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.div) (R := SmtType.Int)
    (typeof_div_eq numerator (SmtTerm.str_len pattern)) hApplyNN
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) =
        SmtType.Int := by
    rw [hTranslate, typeof_div_eq numerator (SmtTerm.str_len pattern)]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  have hEo :
      __eo_to_smt_type
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) =
        SmtType.Int := by
      let replacement :=
        SmtTerm.str_replace_all source pattern
          (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))
      have hNumeratorNN : term_has_non_none_type numerator := by
        unfold term_has_non_none_type
        rw [hArgs.1]
        simp
      rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
          (typeof_neg_eq (SmtTerm.str_len source) (SmtTerm.str_len replacement))
          (by
            simpa [numerator, replacement] using hNumeratorNN) with hNegArgs | hRealArgs
      · have hReplaceLenNN : term_has_non_none_type (SmtTerm.str_len replacement) := by
          unfold term_has_non_none_type
          rw [hNegArgs.2]
          simp
        rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
            (typeof_str_len_eq replacement) hReplaceLenNN with ⟨T, hReplacementSeq⟩
        have hReplacementNN : term_has_non_none_type replacement := by
          unfold term_has_non_none_type
          rw [hReplacementSeq]
          simp
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all)
            (typeof_str_replace_all_eq source pattern
              (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))
            (by simpa [replacement] using hReplacementNN) with
          ⟨A, hSourceSeq, hPatternSeq, _hEmptySeq⟩
        rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hSourceSeq with
          ⟨U, hYSeq, hU⟩
        rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hPatternSeq with
          ⟨V, hXSeq, hV⟩
        have hWF : smtx_type_translation_injective_wf A :=
          smtx_seq_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt y) hSourceSeq
        have hUV : U = V :=
          eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
        subst V
        have hANN : A ≠ SmtType.None :=
          smtx_type_translation_injective_wf_non_none hWF
        have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
          rw [hU]
          exact hANN
        have hUNS : U ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none U hUNN
        have hReq :
            __eo_requires (__eo_eq U U) (Term.Boolean true) (Term.UOp UserOp.Int) =
              Term.UOp UserOp.Int :=
          eo_requires_eo_eq_self_of_non_stuck U (Term.UOp UserOp.Int) hUNS
        have hEo :
            __eo_to_smt_type
                (__eo_typeof
                  (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) y) x)) =
              SmtType.Int := by
          change
            __eo_to_smt_type
                (__eo_typeof__at_strings_num_occur (__eo_typeof y) (__eo_typeof x)) =
              SmtType.Int
          rw [hYSeq, hXSeq]
          simpa [__eo_typeof__at_strings_num_occur] using congrArg __eo_to_smt_type hReq
        exact hEo
      · have hNumeratorReal : __smtx_typeof numerator = SmtType.Real := by
          rw [show numerator =
              SmtTerm.neg (SmtTerm.str_len source) (SmtTerm.str_len replacement) by rfl]
          rw [typeof_neg_eq, hRealArgs.1, hRealArgs.2]
          simp [__smtx_typeof_arith_overload_op_2]
        have hBad : SmtType.Int = SmtType.Real := hArgs.1.symm.trans hNumeratorReal
        cases hBad
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for datatype testers. -/
private theorem eo_to_smt_typeof_matches_translation_apply_is
    (x y : Term)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.is) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.is) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.is) y) x)) := by
  cases hCons : __eo_to_smt y with
  | DtCons s d i =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.is) y) x) =
            SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x) := by
        change SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt y)) (__eo_to_smt x) =
          SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x)
        rw [hCons]
        simp [__eo_to_smt_tester]
      have hApplyNN :
          term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.is) y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        exact dt_tester_term_typeof_of_non_none hApplyNN
      exact hSmt.trans
        (eo_to_smt_type_typeof_of_smt_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.is) y) x) hSmt (by simp)).symm
  | _ =>
      exact eo_to_smt_typeof_matches_translation_of_smt_none
        (Term.Apply (Term.Apply (Term.UOp UserOp.is) y) x)
        (by
          change __smtx_typeof (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt y)) (__eo_to_smt x)) =
            SmtType.None
          rw [hCons]
          simp [__eo_to_smt_tester, typeof_apply_none_eq])
        hNonNone

/-- Simplifies EO-to-SMT translation for unary `set_choose`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_set_choose
    (x : Term)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) x)) := by
  let T := __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) x))
  let body := SmtTerm.set_member (SmtTerm.Var "@x" T) (__eo_to_smt x)
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x) =
        SmtTerm.choice_nth "@x" T body native_nat_zero := by
    rfl
  have hChoiceNN : term_has_non_none_type (SmtTerm.choice_nth "@x" T body 0) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_choose) x)) =
        T := by
    rw [hTranslate]
    exact choice_term_typeof_of_non_none hChoiceNN
  simpa [T] using hSmt

/-- A non-empty, well-typed translated `set_insert` chain returns a set type. -/
private theorem smtx_typeof_eo_to_smt_set_insert_non_nil_of_non_none
    (xs : Term) (s : SmtTerm)
    (hNotNil : xs ≠ Term.__eo_List_nil)
    (hNonNone : __smtx_typeof (__eo_to_smt_set_insert xs s) ≠ SmtType.None) :
    ∃ T : SmtType, __smtx_typeof (__eo_to_smt_set_insert xs s) = SmtType.Set T := by
  cases xs
  case __eo_List_nil =>
    exact False.elim (hNotNil rfl)
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail s)) := by
          unfold term_has_non_none_type
          change
            __smtx_typeof
                (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail s)) ≠ SmtType.None
          simpa [__eo_to_smt_set_insert] using hNonNone
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
            (typeof_set_union_eq (SmtTerm.set_singleton (__eo_to_smt head))
              (__eo_to_smt_set_insert tail s))
            hApplyNN with
          ⟨T, hHead, hTail⟩
        refine ⟨T, ?_⟩
        change
          __smtx_typeof
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail s)) = SmtType.Set T
        rw [typeof_set_union_eq]
        simp [__smtx_typeof_sets_op_2, hHead, hTail, native_ite, native_Teq]
      all_goals
        exact False.elim (hNonNone (by simp [__eo_to_smt_set_insert, smtx_typeof_none]))
    all_goals
      exact False.elim (hNonNone (by simp [__eo_to_smt_set_insert, smtx_typeof_none]))
  all_goals
    exact False.elim (hNonNone (by simp [__eo_to_smt_set_insert, smtx_typeof_none]))

/-- A well-typed top-level `set_insert` translation returns a set type. -/
private theorem smtx_typeof_eo_to_smt_set_insert_top_of_non_none
    (x y : Term)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) ≠
        SmtType.None) :
    ∃ T : SmtType,
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) =
        SmtType.Set T := by
  cases y
  case __eo_List_nil =>
    exact False.elim (hNonNone (by
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact smtx_typeof_none))
  all_goals
    change ∃ T : SmtType, __smtx_typeof (__eo_to_smt_set_insert _ (__eo_to_smt x)) = SmtType.Set T
    apply smtx_typeof_eo_to_smt_set_insert_non_nil_of_non_none
    · intro h
      cases h
    · change __smtx_typeof (__eo_to_smt_set_insert _ (__eo_to_smt x)) ≠ SmtType.None at hNonNone
      exact hNonNone

/-- Computes the EO type of an untyped list cons once the tail is a list. -/
private theorem eo_typeof_list_cons
    (head tail : Term)
    (hTail : __eo_typeof tail = Term.__eo_List) :
    __eo_typeof (Term.Apply (Term.Apply Term.__eo_List_cons head) tail) =
      Term.__eo_List := by
  change
    __eo_typeof_apply
      (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
      (__eo_typeof tail) = Term.__eo_List
  rw [hTail]
  rfl

/-- A set-typed `set_insert` translation must come from an EO list. -/
private theorem eo_typeof_list_of_set_insert_set
    (xs : Term) (s : SmtTerm) {T : SmtType} :
    __smtx_typeof (__eo_to_smt_set_insert xs s) = SmtType.Set T ->
    __eo_typeof xs = Term.__eo_List := by
  intro hTy
  cases xs
  case __eo_List_nil =>
    rfl
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        have hUnionTy :
            __smtx_typeof
                (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail s)) =
              SmtType.Set T := by
          simpa [__eo_to_smt_set_insert] using hTy
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail s)) := by
          unfold term_has_non_none_type
          change
            __smtx_typeof
                (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail s)) ≠ SmtType.None
          rw [hUnionTy]
          simp
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
            (typeof_set_union_eq (SmtTerm.set_singleton (__eo_to_smt head))
              (__eo_to_smt_set_insert tail s))
            hApplyNN with
          ⟨A, _hHead, hTail⟩
        exact eo_typeof_list_cons head tail
          (eo_typeof_list_of_set_insert_set tail s hTail)
      all_goals
        have hBad := hTy
        simp [__eo_to_smt_set_insert, smtx_typeof_none] at hBad
    all_goals
      have hBad := hTy
      simp [__eo_to_smt_set_insert, smtx_typeof_none] at hBad
  all_goals
    have hBad := hTy
    simp [__eo_to_smt_set_insert, smtx_typeof_none] at hBad

/-- A set-typed `set_insert` translation has a base set of the same type. -/
private theorem smtx_typeof_set_insert_base_of_set
    (xs : Term) (s : SmtTerm) {T : SmtType} :
    __smtx_typeof (__eo_to_smt_set_insert xs s) = SmtType.Set T ->
    __smtx_typeof s = SmtType.Set T := by
  intro hTy
  cases xs
  case __eo_List_nil =>
    simpa [__eo_to_smt_set_insert] using hTy
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        have hUnionTy :
            __smtx_typeof
                (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail s)) =
              SmtType.Set T := by
          simpa [__eo_to_smt_set_insert] using hTy
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail s)) := by
          unfold term_has_non_none_type
          change
            __smtx_typeof
                (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail s)) ≠ SmtType.None
          rw [hUnionTy]
          simp
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union)
            (typeof_set_union_eq (SmtTerm.set_singleton (__eo_to_smt head))
              (__eo_to_smt_set_insert tail s))
            hApplyNN with
          ⟨A, hHead, hTail⟩
        have hResultA :
            __smtx_typeof
                (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
                  (__eo_to_smt_set_insert tail s)) =
              SmtType.Set A := by
          rw [typeof_set_union_eq]
          simp [__smtx_typeof_sets_op_2, hHead, hTail, native_ite, native_Teq]
        have hTA : T = A := by
          have hSetEq : SmtType.Set T = SmtType.Set A := hUnionTy.symm.trans hResultA
          cases hSetEq
          rfl
        have hTailT : __smtx_typeof (__eo_to_smt_set_insert tail s) = SmtType.Set T := by
          rw [hTA]
          exact hTail
        exact smtx_typeof_set_insert_base_of_set tail s hTailT
      all_goals
        have hBad := hTy
        simp [__eo_to_smt_set_insert, smtx_typeof_none] at hBad
    all_goals
      have hBad := hTy
      simp [__eo_to_smt_set_insert, smtx_typeof_none] at hBad
  all_goals
    have hBad := hTy
    simp [__eo_to_smt_set_insert, smtx_typeof_none] at hBad

/-- Simplifies EO-to-SMT translation for `set_insert`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_set_insert
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) := by
  rcases smtx_typeof_eo_to_smt_set_insert_top_of_non_none x y hNonNone with
    ⟨T, hSmt⟩
  have hChain :
      __smtx_typeof (__eo_to_smt_set_insert y (__eo_to_smt x)) = SmtType.Set T := by
    cases y
    case __eo_List_nil =>
      exact False.elim (hNonNone (by
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact smtx_typeof_none))
    all_goals
      change
        __smtx_typeof (__eo_to_smt_set_insert _ (__eo_to_smt x)) =
          SmtType.Set T at hSmt
      exact hSmt
  have hList : __eo_typeof y = Term.__eo_List :=
    eo_typeof_list_of_set_insert_set y (__eo_to_smt x) hChain
  have hXSetSmt : __smtx_typeof (__eo_to_smt x) = SmtType.Set T :=
    smtx_typeof_set_insert_base_of_set y (__eo_to_smt x) hChain
  rcases eo_typeof_eq_set_of_smt_set_from_ih x ihX hXSetSmt with
    ⟨U, hXSet, hU⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_set_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt x) hXSetSmt
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) =
        SmtType.Set T := by
    change __eo_to_smt_type (__eo_typeof_set_insert (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Set T
    rw [hList, hXSet]
    change __smtx_typeof_guard (__eo_to_smt_type U) (SmtType.Set (__eo_to_smt_type U)) =
      SmtType.Set T
    rw [hU]
    exact smtx_typeof_guard_of_non_none T (SmtType.Set T) hTNN
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for set binary operators returning a set. -/
private theorem eo_to_smt_typeof_matches_translation_apply_set_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_sets_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = SmtType.Set T ->
        __smtx_typeof (__eo_to_smt x) = SmtType.Set T ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Set T)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases set_binop_args_of_non_none (op := smtOp) hTy hApplyNN with ⟨T, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Set T := by
    rw [hTranslate, hTy]
    simp [__smtx_typeof_sets_op_2, hY, hX, native_ite, native_Teq]
  exact hSmt.trans (hEo T hY hX).symm

/-- Simplifies EO-to-SMT translation for set binary predicates. -/
private theorem eo_to_smt_typeof_matches_translation_apply_set_pred_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_sets_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = SmtType.Set T ->
        __smtx_typeof (__eo_to_smt x) = SmtType.Set T ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Bool)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases set_binop_ret_args_of_non_none (op := smtOp) (T := SmtType.Bool) hTy hApplyNN with
    ⟨T, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, hTy]
    simp [__smtx_typeof_sets_op_2_ret, hY, hX, native_ite, native_Teq]
  exact hSmt.trans (hEo T hY hX).symm

/-- Simplifies EO-to-SMT translation for Boolean binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bool_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
            SmtType.Bool SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.Bool ->
      __smtx_typeof (__eo_to_smt x) = SmtType.Bool ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Bool)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-- Simplifies EO-to-SMT translation for arithmetic binary operators returning their input type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_arith_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_arith_overload_op_2
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = T ->
        __smtx_typeof (__eo_to_smt x) = T ->
        (T = SmtType.Int ∨ T = SmtType.Real) ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) = T)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases arith_binop_args_of_non_none (op := smtOp) hTy hApplyNN with hArgs | hArgs
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Int := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Real := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm

/-- Simplifies EO-to-SMT translation for arithmetic comparisons returning Boolean. -/
private theorem eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = T ->
        __smtx_typeof (__eo_to_smt x) = T ->
        (T = SmtType.Int ∨ T = SmtType.Real) ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Bool)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases arith_binop_ret_bool_args_of_non_none (op := smtOp) hTy hApplyNN with hArgs | hArgs
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Bool := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          SmtType.Bool := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm

/-- Simplifies EO-to-SMT translation for arithmetic binary operators returning a fixed type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_arith_ret_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) ret)
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt y) = T ->
        __smtx_typeof (__eo_to_smt x) = T ->
        (T = SmtType.Int ∨ T = SmtType.Real) ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases arith_binop_ret_args_of_non_none (op := smtOp) hTy hApplyNN with hArgs | hArgs
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          ret := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
  · have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
          ret := by
      rw [hTranslate, hTy]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
    exact hSmt.trans (hEo SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm

/-- Simplifies EO-to-SMT translation for integer-only binary operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_int_binop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x) =
        smtOp (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Int)
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
            ret SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt y) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt x) = SmtType.Int ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := int_binop_args_of_non_none (op := smtOp) (R := ret) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y) x)) =
        ret := by
    rw [hTranslate, hTy]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  exact hSmt.trans (hEo hArgs.1 hArgs.2).symm

/-- Purified selector heads keep the selector result EO type. -/
private theorem eo_to_smt_eq_dt_sel_cases
    (y : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.DtSel s d i j) :
    (∃ d0, d = __eo_to_smt_datatype d0 ∧ y = Term.DtSel s d0 i j ∧
      __eo_reserved_datatype_name s = false) ∨
      (∃ z, y = Term._at_purify z ∧ __eo_to_smt z = SmtTerm.DtSel s d i j) := by
  cases y
  case DtSel s0 d0 i0 j0 =>
    cases hReserved : __eo_reserved_datatype_name s0
    · simp [eo_to_smt_term_dt_sel, native_ite, hReserved] at hy
      rcases hy with ⟨hs, hd, hi, hj⟩
      cases hs
      cases hd
      cases hi
      cases hj
      exact Or.inl ⟨d0, rfl, rfl, hReserved⟩
    · simp [eo_to_smt_term_dt_sel, native_ite, hReserved] at hy
  case DtCons s0 d0 i0 =>
    exfalso
    cases hReserved : __eo_reserved_datatype_name s0 <;>
      simp [eo_to_smt_term_dt_cons, native_ite, hReserved] at hy
  case _at_purify z =>
    have hz : __eo_to_smt z = SmtTerm.DtSel s d i j := hy
    exact Or.inr ⟨z, rfl, hz⟩
  case Apply f x =>
    exact (eo_to_smt_apply_ne_dt_sel f x s d i j hy).elim
  case UOp op =>
    exfalso
    cases op <;> cases hy
  case Var name T =>
    exfalso
    cases name <;> cases hy
  case seq_empty T =>
    exfalso
    change __eo_to_smt_seq_empty (__eo_to_smt_type T) = SmtTerm.DtSel s d i j at hy
    cases hTy : __eo_to_smt_type T <;> simp [__eo_to_smt_seq_empty, hTy] at hy
  case set_empty T =>
    exfalso
    change __eo_to_smt_set_empty (__eo_to_smt_type T) = SmtTerm.DtSel s d i j at hy
    cases hTy : __eo_to_smt_type T <;> simp [__eo_to_smt_set_empty, hTy] at hy
  case _at_quantifiers_skolemize q idx =>
    exact (eo_to_smt_quant_skolemize_top_ne_dt_sel q idx s d i j hy).elim
  all_goals
    exfalso
    cases hy

/-- EO translation never produces a bare datatype tester. -/
private theorem eo_to_smt_ne_dt_tester
    (y : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    __eo_to_smt y ≠ SmtTerm.DtTester s d i := by
  intro hy
  cases y
  case _at_purify z =>
    exact eo_to_smt_ne_dt_tester z s d i hy
  case Apply f x =>
    exact (eo_to_smt_apply_ne_dt_tester f x s d i hy).elim
  case DtCons s0 d0 i0 =>
    exfalso
    cases hReserved : __eo_reserved_datatype_name s0 <;>
      simp [eo_to_smt_term_dt_cons, native_ite, hReserved] at hy
  case DtSel s0 d0 i0 j0 =>
    exfalso
    cases hReserved : __eo_reserved_datatype_name s0 <;>
      simp [eo_to_smt_term_dt_sel, native_ite, hReserved] at hy
  case UOp op =>
    exfalso
    cases op <;> cases hy
  case Var name T =>
    exfalso
    cases name <;> cases hy
  case seq_empty T =>
    exfalso
    change __eo_to_smt_seq_empty (__eo_to_smt_type T) = SmtTerm.DtTester s d i at hy
    cases hTy : __eo_to_smt_type T <;> simp [__eo_to_smt_seq_empty, hTy] at hy
  case set_empty T =>
    exfalso
    change __eo_to_smt_set_empty (__eo_to_smt_type T) = SmtTerm.DtTester s d i at hy
    cases hTy : __eo_to_smt_type T <;> simp [__eo_to_smt_set_empty, hTy] at hy
  case _at_quantifiers_skolemize q idx =>
    exact (eo_to_smt_quant_skolemize_top_ne_dt_tester q idx s d i hy).elim
  all_goals
    exfalso
    cases hy
termination_by y
decreasing_by
  simp_wf
  simp_all

/-- Purified selector heads keep the selector result EO type. -/
private theorem eo_to_smt_type_typeof_apply_purify_of_dt_sel_translation
    (x y : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hy : __eo_to_smt y = SmtTerm.DtSel s d i j)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s d)
    (hApplyNN : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) (__eo_to_smt x))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_purify y) x)) =
      __smtx_ret_typeof_sel s d i j := by
  rcases eo_to_smt_eq_dt_sel_cases y s d i j hy with hSel | hPurify
  · rcases hSel with ⟨d0, hd, rfl, hReserved⟩
    have hx' : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype d0) := by
      simpa [hd] using hx
    have hApplyNN' :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d0) i j) (__eo_to_smt x)) := by
      simpa [hd] using hApplyNN
    have hHeadEq :
        __eo_typeof (Term._at_purify (Term.DtSel s d0 i j)) =
          __eo_typeof (Term.DtSel s d0 i j) := by
      rfl
    have hApplyEq :
        __eo_typeof (Term.Apply (Term._at_purify (Term.DtSel s d0 i j)) x) =
          __eo_typeof (Term.Apply (Term.DtSel s d0 i j) x) := by
      change
        __eo_typeof_apply (__eo_typeof (Term._at_purify (Term.DtSel s d0 i j))) (__eo_typeof x) =
          __eo_typeof_apply (__eo_typeof (Term.DtSel s d0 i j)) (__eo_typeof x)
      rw [hHeadEq]
    rw [hApplyEq]
    simpa [hd] using
      (eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype_from_ih
        x s d0 i j ihX hReserved hx')
  · rcases hPurify with ⟨z, rfl, hz⟩
    have hHeadEq :
        __eo_typeof (Term._at_purify (Term._at_purify z)) =
          __eo_typeof (Term._at_purify z) := by
      change
        __eo_typeof__at_purify (__eo_typeof (Term._at_purify z)) =
          __eo_typeof (Term._at_purify z)
      cases hTy : __eo_typeof (Term._at_purify z) <;> rfl
    have hApplyEq :
        __eo_typeof (Term.Apply (Term._at_purify (Term._at_purify z)) x) =
          __eo_typeof (Term.Apply (Term._at_purify z) x) := by
      change
        __eo_typeof_apply (__eo_typeof (Term._at_purify (Term._at_purify z))) (__eo_typeof x) =
          __eo_typeof_apply (__eo_typeof (Term._at_purify z)) (__eo_typeof x)
      rw [hHeadEq]
    rw [hApplyEq]
    exact eo_to_smt_type_typeof_apply_purify_of_dt_sel_translation x z s d i j ihX hz hx hApplyNN

/-- Purified tester heads still have stuck EO application type. -/
private theorem eo_to_smt_type_typeof_apply_purify_of_dt_tester_translation
    (x y : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.DtTester s d i) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_purify y) x)) = SmtType.None := by
  exact (eo_to_smt_ne_dt_tester y s d i hy).elim

/-- A non-`None` regex-unfold component always returns a string. -/
private theorem smtx_typeof_re_unfold_pos_component_of_non_none
    (s r : SmtTerm)
    (n : native_Nat)
    (hNN : __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_re_unfold_pos_component s r n) = SmtType.Seq SmtType.Char := by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN ⊢
      case re_concat r1 r2 =>
        exact choice_term_typeof_of_non_none (by
          unfold term_has_non_none_type
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN)
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN ⊢
      case re_concat r1 r2 =>
        exact ih _ r2 hNN

/-- Extracts the top-level string and regex types from the base regex-unfold component. -/
private theorem re_unfold_pos_component_zero_args_of_non_none
    (s r1 r2 : SmtTerm)
    (hNN :
      term_has_non_none_type
        (__eo_to_smt_re_unfold_pos_component s (SmtTerm.re_concat r1 r2) native_nat_zero)) :
    __smtx_typeof s = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
  let v0 := SmtType.Seq SmtType.Char
  let v2 := SmtTerm.Var "@x" v0
  let v3 := SmtTerm.str_len v2
  let v4 := SmtTerm.str_substr s v3 (SmtTerm.neg (SmtTerm.str_len s) v3)
  let in1 := SmtTerm.str_in_re v2 r1
  let in2 := SmtTerm.str_in_re v4 r2
  let body := SmtTerm.and (SmtTerm.eq s (SmtTerm.str_concat v2 v4)) (SmtTerm.and in1 in2)
  have hChoiceNN : term_has_non_none_type (SmtTerm.choice_nth "@x" v0 body native_nat_zero) := by
    simpa [__eo_to_smt_re_unfold_pos_component, v0, v2, v3, v4, in1, in2, body] using hNN
  have hBody : __smtx_typeof body = SmtType.Bool :=
    choice_nth_body_bool_of_non_none hChoiceNN
  have hBodyNN : term_has_non_none_type body := by
    unfold term_has_non_none_type
    rw [hBody]
    simp
  have hOuter :=
    bool_binop_args_bool_of_non_none (op := SmtTerm.and)
      (typeof_and_eq (SmtTerm.eq s (SmtTerm.str_concat v2 v4)) (SmtTerm.and in1 in2)) hBodyNN
  have hInnerNN : term_has_non_none_type (SmtTerm.and in1 in2) := by
    unfold term_has_non_none_type
    rw [hOuter.2]
    simp
  have hInner :=
    bool_binop_args_bool_of_non_none (op := SmtTerm.and) (typeof_and_eq in1 in2) hInnerNN
  have hIn1NN : term_has_non_none_type in1 := by
    unfold term_has_non_none_type
    rw [hInner.1]
    simp
  have hIn2NN : term_has_non_none_type in2 := by
    unfold term_has_non_none_type
    rw [hInner.2]
    simp
  have hR1 :=
    seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re) (typeof_str_in_re_eq v2 r1)
      hIn1NN
  have hR2 :=
    seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re) (typeof_str_in_re_eq v4 r2)
      hIn2NN
  have hV4 : __smtx_typeof v4 = SmtType.Seq SmtType.Char := hR2.1
  have hConcatTy : __smtx_typeof (SmtTerm.str_concat v2 v4) = SmtType.Seq SmtType.Char := by
    rw [typeof_str_concat_eq]
    simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, hR1.1, hV4]
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof s) (__smtx_typeof (SmtTerm.str_concat v2 v4)) ≠
        SmtType.None := by
    have hEqTermNN : term_has_non_none_type (SmtTerm.eq s (SmtTerm.str_concat v2 v4)) := by
      unfold term_has_non_none_type
      rw [hOuter.1]
      simp
    rw [← typeof_eq_eq]
    exact hEqTermNN
  have hEqArgs := smtx_typeof_eq_non_none hEqNN
  have hS : __smtx_typeof s = SmtType.Seq SmtType.Char := by
    rw [hEqArgs.1, hConcatTy]
  have hR : __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
    rw [typeof_re_concat_eq]
    simp [hR1.2, hR2.2, native_ite, native_Teq]
  exact ⟨hS, hR⟩

/-- Extracts the top-level string and regex types from a regex-unfold component. -/
private theorem re_unfold_pos_component_args_of_non_none
    (s r : SmtTerm)
    (n : native_Nat)
    (hNN : term_has_non_none_type (__eo_to_smt_re_unfold_pos_component s r n)) :
    __smtx_typeof s = SmtType.Seq SmtType.Char ∧
      __smtx_typeof r = SmtType.RegLan := by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        exact re_unfold_pos_component_zero_args_of_non_none s r1 r2 (by
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN)
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN smtx_typeof_none
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        let zeroComp :=
          __eo_to_smt_re_unfold_pos_component s (SmtTerm.re_concat r1 r2) native_nat_zero
        let v0 := SmtTerm.str_len zeroComp
        let newS := SmtTerm.str_substr s v0 (SmtTerm.neg (SmtTerm.str_len s) v0)
        have hRecArgs :
            __smtx_typeof newS = SmtType.Seq SmtType.Char ∧
              __smtx_typeof r2 = SmtType.RegLan := by
          exact ih newS r2 (by
            simpa [newS, v0, zeroComp, __eo_to_smt_re_unfold_pos_component] using hNN)
        have hNewSNN : term_has_non_none_type newS := by
          unfold term_has_non_none_type
          rw [hRecArgs.1]
          simp
        rcases str_substr_args_of_non_none hNewSNN with ⟨T, hSRaw, hV0, hLen⟩
        have hV0NN : term_has_non_none_type v0 := by
          unfold term_has_non_none_type
          rw [hV0]
          simp
        rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len) (typeof_str_len_eq zeroComp) hV0NN with
          ⟨U, hZeroSeq⟩
        have hZeroNN : term_has_non_none_type zeroComp := by
          unfold term_has_non_none_type
          rw [hZeroSeq]
          simp
        exact re_unfold_pos_component_zero_args_of_non_none s r1 r2 hZeroNN
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN smtx_typeof_none

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
  by_cases hWf : __smtx_type_wf T = true
  · have hSet : T = SmtType.Set T := by
      simpa [__smtx_typeof_guard_wf, hWf, native_ite] using h
    exact smt_type_ne_set_self T hSet
  · have hNone : T = SmtType.None := by
      simpa [__smtx_typeof_guard_wf, hWf, native_ite] using h
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
      simp [__eo_to_smt_set_empty, __smtx_typeof_apply]
  | Set U =>
      rw [show __smtx_typeof (__eo_to_smt_set_empty (SmtType.Set U)) =
          __smtx_typeof_guard_wf U (SmtType.Set U) by
        simp [__eo_to_smt_set_empty]
        rw [__smtx_typeof.eq_120]]
      cases hInh : native_inhabited_type U <;>
      cases hWf : __smtx_type_wf U <;>
        simp [__smtx_typeof_apply, __smtx_typeof_guard_wf, native_ite, hWf]

/-- Computes `__smtx_typeof` for `not` terms. -/
private theorem smtx_typeof_not_bool_or_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.not t) = SmtType.None := by
  cases hT : __smtx_typeof t <;>
    (rw [typeof_not_eq]; simp [hT, native_ite, native_Teq])

/-- Computes `__smtx_typeof` for `exists` terms. -/
private theorem smtx_typeof_exists_bool_or_none
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.exists s T body) = SmtType.None := by
  cases hBody : __smtx_typeof body <;>
    (rw [typeof_exists_eq]; simp [hBody, native_ite, native_Teq])

/-- `None` is not Boolean-typed. -/
private theorem smtx_typeof_none_ne_bool :
    __smtx_typeof SmtTerm.None ≠ SmtType.Bool := by
  simp [smtx_typeof_none]

/-- A Boolean `not` term has a Boolean argument. -/
private theorem smtx_typeof_not_arg_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  by_cases hArg : __smtx_typeof t = SmtType.Bool
  · exact hArg
  · cases hTest : native_Teq (__smtx_typeof t) SmtType.Bool <;>
      simp [hTest, native_ite] at hTy
    simpa [native_Teq] using hTest

/-- Computes the EO type of a variable-headed list cons once the tail is a list. -/
private theorem eo_typeof_list_cons_var
    (s : native_String) (T xs : Term)
    (hTail : __eo_typeof xs = Term.__eo_List) :
    __eo_typeof (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs) =
      Term.__eo_List := by
  change
    __eo_typeof_apply
      (Term.Apply (Term.Apply Term.FunType Term.__eo_List) Term.__eo_List)
      (__eo_typeof xs) = Term.__eo_List
  rw [hTail]
  rfl

/-- Pulls the body Boolean fact back through nested `__eo_to_smt_exists`. -/
private theorem eo_to_smt_exists_body_bool_of_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body = SmtType.Bool := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    simpa [__eo_to_smt_exists] using hTy
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            exact eo_to_smt_exists_body_bool_of_bool a body hSub
          all_goals
            subst hname
            have hNone := hTy
            simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
        all_goals
          subst hy
          have hNone := hTy
          simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
      all_goals
        subst hg
        have hNone := hTy
        simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
    all_goals
      subst hf
      have hNone := hTy
      simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
  all_goals
    subst hxs
    have hNone := hTy
    simp [smtx_typeof_none, __eo_to_smt_exists] at hNone

/-- Recovers EO list typing from a Boolean SMT existential chain. -/
private theorem eo_typeof_var_list_of_exists_bool
    (xs : Term) (body : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __eo_typeof xs = Term.__eo_List := by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    rfl
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type (SmtTerm.exists s (__eo_to_smt_type T) (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            have hTail : __eo_typeof a = Term.__eo_List :=
              eo_typeof_var_list_of_exists_bool a body hSub
            exact eo_typeof_list_cons_var s T a hTail
          all_goals
            subst hname
            have hNone := hTy
            simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
        all_goals
          subst hy
          have hNone := hTy
          simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
      all_goals
        subst hg
        have hNone := hTy
        simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
    all_goals
      subst hf
      have hNone := hTy
      simp [smtx_typeof_none, __eo_to_smt_exists] at hNone
  all_goals
    subst hxs
    have hNone := hTy
    simp [smtx_typeof_none, __eo_to_smt_exists] at hNone

/-- Computes `__smtx_typeof` for top-level translated `exists`. -/
private theorem smtx_typeof_eo_to_smt_exists_top_bool_or_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) =
        SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) =
        SmtType.None := by
  cases y
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            change
              __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt x))) =
                  SmtType.Bool ∨
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt x))) =
                  SmtType.None
            exact smtx_typeof_exists_bool_or_none s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail (__eo_to_smt x))
          all_goals
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact smtx_typeof_none
        all_goals
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none

/-- Computes `__smtx_typeof` for top-level translated `forall`. -/
private theorem smtx_typeof_eo_to_smt_forall_top_bool_or_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) =
        SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) =
        SmtType.None := by
  cases y
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none
  all_goals
    change
      __smtx_typeof
          (SmtTerm.not (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt x)))) =
          SmtType.Bool ∨
        __smtx_typeof
          (SmtTerm.not (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt x)))) =
          SmtType.None
    exact smtx_typeof_not_bool_or_none
      (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt x)))

/-- Bridge-free proof for `exists`, using the body IH and quantifier-list inversion. -/
private theorem eo_to_smt_typeof_matches_translation_apply_exists_from_ih
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) := by
  rcases smtx_typeof_eo_to_smt_exists_top_bool_or_none x y with hBool | hNone
  · have hChain : __smtx_typeof (__eo_to_smt_exists y (__eo_to_smt x)) = SmtType.Bool := by
      cases y
      case __eo_List_nil =>
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
      all_goals
        change __smtx_typeof (__eo_to_smt_exists _ (__eo_to_smt x)) = SmtType.Bool at hBool
        exact hBool
    have hList : __eo_typeof y = Term.__eo_List :=
      eo_typeof_var_list_of_exists_bool y (__eo_to_smt x) hChain
    have hXBoolSmt : __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      eo_to_smt_exists_body_bool_of_bool y (__eo_to_smt x) hChain
    have hXBool : __eo_typeof x = Term.Bool :=
      eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hXBoolSmt
    have hEo :
        __eo_to_smt_type
            (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.exists) y) x)) =
          SmtType.Bool := by
      change __eo_to_smt_type (__eo_typeof_forall (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Bool
      rw [hList, hXBool]
      rfl
    exact hBool.trans hEo.symm
  · exact False.elim (hNonNone hNone)

/-- Bridge-free proof for `forall`, using the body IH and quantifier-list inversion. -/
private theorem eo_to_smt_typeof_matches_translation_apply_forall_from_ih
    (x y : Term)
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) := by
  rcases smtx_typeof_eo_to_smt_forall_top_bool_or_none x y with hBool | hNone
  · have hChain :
        __smtx_typeof (__eo_to_smt_exists y (SmtTerm.not (__eo_to_smt x))) =
          SmtType.Bool := by
      cases y
      case __eo_List_nil =>
        exact False.elim (hNonNone (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none))
      all_goals
        refine smtx_typeof_not_arg_bool _ ?_
        exact hBool
    have hList : __eo_typeof y = Term.__eo_List :=
      eo_typeof_var_list_of_exists_bool y (SmtTerm.not (__eo_to_smt x)) hChain
    have hNotBoolSmt : __smtx_typeof (SmtTerm.not (__eo_to_smt x)) = SmtType.Bool :=
      eo_to_smt_exists_body_bool_of_bool y (SmtTerm.not (__eo_to_smt x)) hChain
    have hXBoolSmt : __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      smtx_typeof_not_arg_bool (__eo_to_smt x) hNotBoolSmt
    have hXBool : __eo_typeof x = Term.Bool :=
      eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hXBoolSmt
    have hEo :
        __eo_to_smt_type
            (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.forall) y) x)) =
          SmtType.Bool := by
      change __eo_to_smt_type (__eo_typeof_forall (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Bool
      rw [hList, hXBool]
      rfl
    exact hBool.trans hEo.symm
  · exact False.elim (hNonNone hNone)

/-- Computes `__smtx_typeof` for `and` terms. -/
private theorem smtx_typeof_and_bool_or_none
    (s t : SmtTerm) :
    __smtx_typeof (SmtTerm.and s t) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.and s t) = SmtType.None := by
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
    case UOp op =>
      cases op with
      | _at__at_TypedList_nil =>
          left
          change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
          rw [__smtx_typeof.eq_1]
      | _ =>
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none
    case Apply g b =>
      cases g
      case UOp op =>
        cases op with
        | _at__at_TypedList_cons =>
            change
              __smtx_typeof
                  (SmtTerm.and (SmtTerm.not (SmtTerm.eq s (__eo_to_smt b)))
                    (__eo_to_smt_distinct_pairs s a)) =
                SmtType.Bool ∨
              __smtx_typeof
                  (SmtTerm.and (SmtTerm.not (SmtTerm.eq s (__eo_to_smt b)))
                    (__eo_to_smt_distinct_pairs s a)) =
                SmtType.None
            exact smtx_typeof_and_bool_or_none
              (SmtTerm.not (SmtTerm.eq s (__eo_to_smt b)))
              (__eo_to_smt_distinct_pairs s a)
        | _ =>
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none

/-- Computes `__smtx_typeof` for `__eo_to_smt_distinct`. -/
private theorem smtx_typeof_eo_to_smt_distinct_bool_or_none
    (xs : Term) :
    __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.None := by
  cases xs
  case Apply f a =>
    cases f
    case UOp op =>
      cases op with
      | _at__at_TypedList_nil =>
          left
          change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
          rw [__smtx_typeof.eq_1]
      | _ =>
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact smtx_typeof_none
    case Apply g b =>
      cases g
      case UOp op =>
        cases op with
        | _at__at_TypedList_cons =>
            change
              __smtx_typeof
                  (SmtTerm.and (__eo_to_smt_distinct_pairs (__eo_to_smt b) a)
                    (__eo_to_smt_distinct a)) = SmtType.Bool ∨
                __smtx_typeof
                  (SmtTerm.and (__eo_to_smt_distinct_pairs (__eo_to_smt b) a)
                    (__eo_to_smt_distinct a)) = SmtType.None
            exact smtx_typeof_and_bool_or_none
              (__eo_to_smt_distinct_pairs (__eo_to_smt b) a)
              (__eo_to_smt_distinct a)
        | _ =>
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact smtx_typeof_none

/-- A non-`none` translated `distinct` has Boolean SMT type. -/
private theorem smtx_typeof_eo_to_smt_distinct_of_non_none
    (xs : Term)
    (hNonNone : __smtx_typeof (__eo_to_smt_distinct xs) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.Bool := by
  rcases smtx_typeof_eo_to_smt_distinct_bool_or_none xs with hBool | hNone
  · exact hBool
  · exact False.elim (hNonNone hNone)

/-- Inverts the top-level typed-list guard used by guarded `distinct`. -/
private theorem eo_to_smt_type_is_tlist_true_eq
    {T : Term} (hGuard : __eo_to_smt_type_is_tlist T = true) :
    ∃ U, T = Term.Apply (Term.UOp UserOp._at__at_TypedList) U := by
  cases T <;> try (change false = true at hGuard; cases hGuard)
  case Apply f U =>
    cases f <;> try (change false = true at hGuard; cases hGuard)
    case UOp op =>
      cases op <;> try (change false = true at hGuard; cases hGuard)
      case _at__at_TypedList =>
        exact ⟨U, rfl⟩

/-- The guarded top-level `distinct` translation has Boolean EO result type. -/
private theorem eo_to_smt_type_typeof_distinct_of_guard
    (xs : Term)
    (hGuard : __eo_to_smt_type_is_tlist (__eo_typeof xs) = true) :
    __eo_to_smt_type (__eo_typeof_distinct (__eo_typeof xs)) = SmtType.Bool := by
  rcases eo_to_smt_type_is_tlist_true_eq hGuard with ⟨T, hTy⟩
  rw [hTy]
  rfl

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
  have hGeneric : generic_apply_type (__eo_to_smt_distinct xs) x :=
    generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; exact eo_to_smt_distinct_ne_dt_sel xs s d i j h)
      (by intro s d i h; exact eo_to_smt_distinct_ne_dt_tester xs s d i h)
  rw [hGeneric]
  exact smtx_typeof_apply_eo_to_smt_distinct_eq_none xs (__smtx_typeof x)

/-- Applying a top-level translated `distinct` as a function is ill-typed. -/
private theorem smtx_typeof_eo_to_smt_distinct_top_apply_eq_none
    (xs : Term) (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) x) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (__eo_to_smt_type_is_tlist (__eo_typeof xs))
            (__eo_to_smt_distinct xs) SmtTerm.None) x) =
      SmtType.None
  cases hGuard : __eo_to_smt_type_is_tlist (__eo_typeof xs)
  · simp [native_ite]
    exact typeof_apply_none_eq x
  · simp [native_ite]
    exact smtx_typeof_eo_to_smt_distinct_apply_eq_none xs x

/-- Simplifies EO-to-SMT translation for `tuple_select`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_tuple_select
    (x y : Term)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)) := by
  cases hTy : __eo_to_smt_type (__eo_typeof x) with
  | Datatype s d =>
      by_cases hTuple : s = "@Tuple"
      · subst s
        cases hIdx : __eo_to_smt y with
        | Numeral n =>
            cases hNonneg : native_zleq 0 n
            · exact eo_to_smt_typeof_matches_translation_of_smt_none
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)
                (by
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_select
                          (__eo_to_smt_type (__eo_typeof x)) (__eo_to_smt y) (__eo_to_smt x)) =
                      SmtType.None
                  rw [hTy, hIdx]
                  simp [__eo_to_smt_tuple_select, hNonneg, native_ite])
                hNonNone
            · have hTranslate :
                  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x) =
                    SmtTerm.Apply
                      (SmtTerm.DtSel "@Tuple" d native_nat_zero (native_int_to_nat n))
                      (__eo_to_smt x) := by
                change
                  __eo_to_smt_tuple_select
                      (__eo_to_smt_type (__eo_typeof x)) (__eo_to_smt y) (__eo_to_smt x) =
                    SmtTerm.Apply
                      (SmtTerm.DtSel "@Tuple" d native_nat_zero (native_int_to_nat n))
                      (__eo_to_smt x)
                rw [hTy, hIdx]
                simp [__eo_to_smt_tuple_select, hNonneg, native_ite]
              have hApplyNN :
                  term_has_non_none_type
                    (SmtTerm.Apply
                      (SmtTerm.DtSel "@Tuple" d native_nat_zero (native_int_to_nat n))
                      (__eo_to_smt x)) := by
                unfold term_has_non_none_type
                rw [← hTranslate]
                exact hNonNone
              have hSmt :
                  __smtx_typeof
                      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)) =
                    __smtx_ret_typeof_sel "@Tuple" d native_nat_zero (native_int_to_nat n) := by
                rw [hTranslate]
                exact dt_sel_term_typeof_of_non_none hApplyNN
              have hTNonNone :
                  __smtx_ret_typeof_sel "@Tuple" d native_nat_zero (native_int_to_nat n) ≠
                    SmtType.None := by
                rw [← hSmt]
                exact hNonNone
              exact hSmt.trans
                (eo_to_smt_type_typeof_of_smt_type
                  (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)
                  hSmt hTNonNone).symm
        | _ =>
            exact eo_to_smt_typeof_matches_translation_of_smt_none
              (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)
              (by
                change
                  __smtx_typeof
                      (__eo_to_smt_tuple_select
                        (__eo_to_smt_type (__eo_typeof x)) (__eo_to_smt y) (__eo_to_smt x)) =
                    SmtType.None
                rw [hTy, hIdx]
                simp [__eo_to_smt_tuple_select])
              hNonNone
      · exact eo_to_smt_typeof_matches_translation_of_smt_none
          (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)
          (by
            change
              __smtx_typeof
                  (__eo_to_smt_tuple_select
                    (__eo_to_smt_type (__eo_typeof x)) (__eo_to_smt y) (__eo_to_smt x)) =
                SmtType.None
            rw [hTy]
            simp [__eo_to_smt_tuple_select, hTuple])
          hNonNone
  | _ =>
      exact eo_to_smt_typeof_matches_translation_of_smt_none
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) y) x)
        (by
          change
            __smtx_typeof
                (__eo_to_smt_tuple_select
                  (__eo_to_smt_type (__eo_typeof x)) (__eo_to_smt y) (__eo_to_smt x)) =
              SmtType.None
          rw [hTy]
          simp [__eo_to_smt_tuple_select])
        hNonNone

/-- Localizes the remaining tuple-constructor recovery obligation. -/
private theorem eo_to_smt_typeof_matches_translation_apply_tuple
    (x y : Term)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x)) := by
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.tuple) y) x
  exact (eo_to_smt_type_typeof_of_smt_type t rfl hNonNone).symm

/-- Simplifies EO-to-SMT translation for map `select`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_select
    (x y : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x) =
        SmtTerm.select (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN : term_has_non_none_type (SmtTerm.select (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases select_args_of_non_none hApplyNN with ⟨A, B, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) =
        B := by
    rw [hTranslate, typeof_select_eq (__eo_to_smt y) (__eo_to_smt x), hY, hX]
    simp [__smtx_typeof_select, native_ite, native_Teq]
  have hYTrans :
      __eo_to_smt_type (__eo_typeof y) = SmtType.Map A B :=
    eo_to_smt_type_typeof_of_smt_type_from_ih y ihY hY (by simp)
  rcases eo_to_smt_type_eq_map hYTrans with ⟨U, V, hYArray, hU, hV⟩
  have hMapWF : smtx_type_translation_injective_wf (SmtType.Map A B) := by
    have hYNN : term_has_non_none_type (__eo_to_smt y) :=
      smtx_term_has_non_none_of_type_eq hY (by simp)
    simpa [hY] using
      smtx_term_translation_injective_wf_of_non_none (__eo_to_smt y) hYNN
  have hAWF : smtx_type_translation_injective_wf A := hMapWF.1
  have hANN : A ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hAWF
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
    eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hANN
  have hXEq : __eo_typeof x = U :=
    eo_to_smt_type_injective_of_translation_injective_wf hXTrans hU hAWF
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hUNS : U ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hReq : __eo_requires (__eo_eq U U) (Term.Boolean true) V = V :=
    eo_requires_eo_eq_self_of_non_stuck U V hUNS
  have hEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) =
        B := by
    change __eo_to_smt_type (__eo_typeof_select (__eo_typeof y) (__eo_typeof x)) = B
    rw [hYArray, hXEq]
    simpa [__eo_typeof_select, hUNS, hV] using congrArg __eo_to_smt_type hReq
  exact hSmt.trans hEo.symm

/-- Bridge-free `eq` application, using the operand SMT type injectivity invariant. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_eq_from_ih_field_wf
    (y x : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) := by
  intro hNonNone
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) =
        SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    simpa [hTranslate, typeof_eq_eq] using hNonNone
  have hArgs := smtx_typeof_eq_non_none hEqNN
  have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := hArgs.2
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [← hArgs.1]
    exact hArgs.2
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
        SmtType.Bool := by
    rw [hTranslate, typeof_eq_eq]
    rw [hArgs.1]
    cases hT : __smtx_typeof (__eo_to_smt x) <;>
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
        hT] at hArgs ⊢
  have hYTrans :
      __eo_to_smt_type (__eo_typeof y) = __smtx_typeof (__eo_to_smt y) :=
    eo_to_smt_type_typeof_of_smt_type_from_ih y ihY rfl hYNN
  have hXTrans :
      __eo_to_smt_type (__eo_typeof x) = __smtx_typeof (__eo_to_smt x) :=
    eo_to_smt_type_typeof_of_smt_type_from_ih x ihX rfl hXNN
  have hYTransX :
      __eo_to_smt_type (__eo_typeof y) = __smtx_typeof (__eo_to_smt x) :=
    hYTrans.trans hArgs.1
  have hXTermNN : term_has_non_none_type (__eo_to_smt x) :=
    smtx_term_has_non_none_of_type_eq rfl hXNN
  have hWF : smtx_type_translation_injective_wf (__smtx_typeof (__eo_to_smt x)) :=
    smtx_term_translation_injective_wf_of_non_none (__eo_to_smt x) hXTermNN
  have hTypeEq : __eo_typeof y = __eo_typeof x :=
    eo_to_smt_type_injective_of_translation_injective_wf hYTransX hXTrans hWF
  have hXTypeNN : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
    rw [hXTrans]
    exact hXNN
  exact hSmt.trans
    (eo_to_smt_type_typeof_apply_apply_eq_of_same_type
      x y (__eo_typeof x) hTypeEq rfl hXTypeNN).symm

/-- Closes binary `UOp` branches whose translated head is `none`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_none_head
    (op : UserOp) (y x : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x) =
        SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y)) (__eo_to_smt x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply (Term.Apply (Term.UOp op) y) x)
    (by
      rw [hTranslate]
      exact typeof_apply_apply_none_head_eq (__eo_to_smt y) (__eo_to_smt x))

/-- Closes ternary `UOp` branches whose translated head starts from `none`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_none_head
    (op : UserOp) (z y x : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt z)) (__eo_to_smt y))
          (__eo_to_smt x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)
    (by
      rw [hTranslate]
      exact typeof_apply_apply_apply_none_head_eq
        (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))

private theorem bv_width_term_nonstuck (w : native_Nat) :
    Term.Numeral (native_nat_to_int w) ≠ Term.Stuck := by
  intro h
  cases h

/-- Dispatches direct-special binary heads shaped as `(UOp op) y`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_uop_application_head_obligation
    (op : UserOp) (y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp op) y)))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x)) := by
  intro hNonNone
  cases op
  case eq =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_eq_from_ih_field_wf
      y x ihY ihX hNonNone
  case distinct =>
    exfalso
    apply hNonNone
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.distinct) y) x) =
          SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) y)) (__eo_to_smt x) := by
      rfl
    rw [hTranslate]
    exact smtx_typeof_eo_to_smt_distinct_top_apply_eq_none y (__eo_to_smt x)
  case not =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.not y x (SmtTerm.not (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case to_real =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.to_real y x (SmtTerm.to_real (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case to_int =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.to_int y x (SmtTerm.to_int (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case is_int =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.is_int y x (SmtTerm.is_int (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case abs =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.abs y x (SmtTerm.abs (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case str_to_re =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.str_to_re y x (SmtTerm.str_to_re (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case re_mult =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.re_mult y x (SmtTerm.re_mult (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case re_plus =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.re_plus y x (SmtTerm.re_plus (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case re_opt =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.re_opt y x (SmtTerm.re_opt (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case re_comp =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.re_comp y x (SmtTerm.re_comp (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case set_singleton =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.set_singleton y x (SmtTerm.set_singleton (__eo_to_smt y)) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case set_is_empty =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.set_is_empty y x
      (let _v0 := __eo_to_smt y
       SmtTerm.eq _v0 (SmtTerm.set_empty (__smtx_typeof _v0))) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case set_is_singleton =>
    let T := __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) y))
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_of_head_from_ih
      UserOp.set_is_singleton y x
      (SmtTerm.exists "@x" T
        (SmtTerm.eq (__eo_to_smt y)
          (SmtTerm.set_singleton (SmtTerm.Var "@x" T)))) ihF ihX (by rfl)
      (by rfl) (by rfl)
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
      hNonNone
  case str_contains =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_ret_binop
      UserOp.str_contains SmtTerm.str_contains SmtType.Bool x y (by rfl)
      (typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun T hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_contains_of_smt_seq_from_ih
          x y T ihY ihX hy hx)
      hNonNone
  case str_prefixof =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_binop
      UserOp.str_prefixof SmtTerm.str_prefixof SmtType.Bool x y (by rfl)
      (typeof_str_prefixof_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_prefixof_of_seq x y (Term.UOp UserOp.Char)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hx)
          (by simp [__eo_to_smt_type]))
      hNonNone
  case str_suffixof =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_binop
      UserOp.str_suffixof SmtTerm.str_suffixof SmtType.Bool x y (by rfl)
      (typeof_str_suffixof_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_suffixof_of_seq x y (Term.UOp UserOp.Char)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hx)
          (by simp [__eo_to_smt_type]))
      hNonNone
  case str_lt =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_binop
      UserOp.str_lt SmtTerm.str_lt SmtType.Bool x y (by rfl)
      (typeof_str_lt_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_lt_of_seq_char x y
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hx))
      hNonNone
  case str_leq =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_binop
      UserOp.str_leq SmtTerm.str_leq SmtType.Bool x y (by rfl)
      (typeof_str_leq_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_leq_of_seq_char x y
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hx))
      hNonNone
  case str_concat =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_binop
      UserOp.str_concat SmtTerm.str_concat x y (by rfl)
      (typeof_str_concat_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun T hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_concat_of_smt_seq_from_ih
          x y T ihY ihX hy hx)
      hNonNone
  case re_range =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_binop
      UserOp.re_range SmtTerm.re_range SmtType.RegLan x y (by rfl)
      (typeof_re_range_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_range_of_seq_char x y
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hx))
      hNonNone
  case re_concat =>
    exact eo_to_smt_typeof_matches_translation_apply_reglan_binop
      UserOp.re_concat SmtTerm.re_concat x y (by rfl)
      (typeof_re_concat_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_concat_of_reglan x y
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case re_inter =>
    exact eo_to_smt_typeof_matches_translation_apply_reglan_binop
      UserOp.re_inter SmtTerm.re_inter x y (by rfl)
      (typeof_re_inter_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_inter_of_reglan x y
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case re_union =>
    exact eo_to_smt_typeof_matches_translation_apply_reglan_binop
      UserOp.re_union SmtTerm.re_union x y (by rfl)
      (typeof_re_union_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_union_of_reglan x y
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case re_diff =>
    exact eo_to_smt_typeof_matches_translation_apply_reglan_binop
      UserOp.re_diff SmtTerm.re_diff x y (by rfl)
      (typeof_re_diff_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_re_diff_of_reglan x y
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case str_in_re =>
    exact eo_to_smt_typeof_matches_translation_apply_seq_char_reglan_binop
      UserOp.str_in_re SmtTerm.str_in_re SmtType.Bool x y (by rfl)
      (typeof_str_in_re_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun hy hx =>
        eo_to_smt_type_typeof_apply_apply_str_in_re_of_seq_char_reglan x y
          (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hy)
          (eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hx))
      hNonNone
  case seq_nth =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x) =
          SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases seq_nth_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
    have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
      unfold term_has_non_none_type at hApplyNN
      rw [typeof_seq_nth_eq (__eo_to_smt y) (__eo_to_smt x)] at hApplyNN
      simpa [__smtx_typeof_seq_nth, hY, hX] using hApplyNN
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x)) =
          T := by
      rw [hTranslate]
      have hTy' : __smtx_typeof_guard_wf T T = T :=
        smtx_typeof_guard_wf_of_non_none T T hGuardNN
      rw [typeof_seq_nth_eq (__eo_to_smt y) (__eo_to_smt x)]
      simpa [__smtx_typeof_seq_nth, hY, hX] using hTy'
    rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with
      ⟨U, hYU, hU⟩
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x)) =
          T := by
      simpa [hU] using
        (eo_to_smt_type_typeof_apply_apply_seq_nth_of_seq_int x y U hYU
          (eo_typeof_eq_int_of_smt_int_from_ih x ihX hX))
    exact hSmt.trans
      hEo.symm
  case or =>
    exact eo_to_smt_typeof_matches_translation_apply_bool_binop
        UserOp.or SmtTerm.or x y (by rfl)
        (typeof_or_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_or_of_bool x y
            (eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hy)
            (eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hx))
        hNonNone
  case and =>
    exact eo_to_smt_typeof_matches_translation_apply_bool_binop
        UserOp.and SmtTerm.and x y (by rfl)
        (typeof_and_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_and_of_bool x y
            (eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hy)
            (eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hx))
        hNonNone
  case imp =>
    exact eo_to_smt_typeof_matches_translation_apply_bool_binop
        UserOp.imp SmtTerm.imp x y (by rfl)
        (typeof_imp_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_imp_of_bool x y
            (eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hy)
            (eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hx))
        hNonNone
  case xor =>
    exact eo_to_smt_typeof_matches_translation_apply_bool_binop
        UserOp.xor SmtTerm.xor x y (by rfl)
        (typeof_xor_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_xor_of_bool x y
            (eo_typeof_eq_bool_of_smt_bool_from_ih y ihY hy)
            (eo_typeof_eq_bool_of_smt_bool_from_ih x ihX hx))
        hNonNone
  case plus =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_binop
      UserOp.plus SmtTerm.plus x y (by rfl)
      (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · simpa using
              eo_to_smt_type_typeof_apply_apply_plus_of_arith_type x y
                (Term.UOp UserOp.Int)
                (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
                (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
                (Or.inl rfl)
          · simpa using
              eo_to_smt_type_typeof_apply_apply_plus_of_arith_type x y
                (Term.UOp UserOp.Real)
                (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
                (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
                (Or.inr rfl))
        hNonNone
  case neg =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_binop
      UserOp.neg SmtTerm.neg x y (by rfl)
      (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · simpa using
              eo_to_smt_type_typeof_apply_apply_neg_of_arith_type x y
                (Term.UOp UserOp.Int)
                (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
                (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
                (Or.inl rfl)
          · simpa using
              eo_to_smt_type_typeof_apply_apply_neg_of_arith_type x y
                (Term.UOp UserOp.Real)
                (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
                (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
                (Or.inr rfl))
        hNonNone
  case mult =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_binop
      UserOp.mult SmtTerm.mult x y (by rfl)
      (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · simpa using
              eo_to_smt_type_typeof_apply_apply_mult_of_arith_type x y
                (Term.UOp UserOp.Int)
                (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
                (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
                (Or.inl rfl)
          · simpa using
              eo_to_smt_type_typeof_apply_apply_mult_of_arith_type x y
                (Term.UOp UserOp.Real)
                (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
                (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
                (Or.inr rfl))
        hNonNone
  case lt =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
      UserOp.lt SmtTerm.lt x y (by rfl)
      (typeof_lt_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_lt_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_lt_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case leq =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
      UserOp.leq SmtTerm.leq x y (by rfl)
      (typeof_leq_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_leq_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_leq_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case gt =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
      UserOp.gt SmtTerm.gt x y (by rfl)
      (typeof_gt_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_gt_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_gt_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case geq =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_bool_binop
      UserOp.geq SmtTerm.geq x y (by rfl)
      (typeof_geq_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_geq_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_geq_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case div =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.div SmtTerm.div SmtType.Int x y (by rfl)
        (typeof_div_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_div_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case mod =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.mod SmtTerm.mod SmtType.Int x y (by rfl)
        (typeof_mod_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_mod_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case multmult =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.multmult SmtTerm.multmult SmtType.Int x y (by rfl)
        (typeof_multmult_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_multmult_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case divisible =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.divisible SmtTerm.divisible SmtType.Bool x y (by rfl)
        (typeof_divisible_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_divisible_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case div_total =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.div_total SmtTerm.div_total SmtType.Int x y (by rfl)
        (typeof_div_total_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_div_total_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case mod_total =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.mod_total SmtTerm.mod_total SmtType.Int x y (by rfl)
        (typeof_mod_total_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_mod_total_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case multmult_total =>
    exact eo_to_smt_typeof_matches_translation_apply_int_binop
        UserOp.multmult_total SmtTerm.multmult_total SmtType.Int x y (by rfl)
        (typeof_multmult_total_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun hy hx =>
          eo_to_smt_type_typeof_apply_apply_multmult_total_of_int x y
            (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
            (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx))
        hNonNone
  case qdiv =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_ret_binop
      UserOp.qdiv SmtTerm.qdiv SmtType.Real x y (by rfl)
      (typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_qdiv_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_qdiv_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case qdiv_total =>
    exact eo_to_smt_typeof_matches_translation_apply_arith_ret_binop
      UserOp.qdiv_total SmtTerm.qdiv_total SmtType.Real x y (by rfl)
      (typeof_qdiv_total_eq (__eo_to_smt y) (__eo_to_smt x))
        (fun T hy hx hT => by
          rcases hT with rfl | rfl
          · exact eo_to_smt_type_typeof_apply_apply_qdiv_total_of_arith_type x y
              (Term.UOp UserOp.Int)
              (eo_typeof_eq_int_of_smt_int_from_ih y ihY hy)
              (eo_typeof_eq_int_of_smt_int_from_ih x ihX hx)
              (Or.inl rfl)
          · exact eo_to_smt_type_typeof_apply_apply_qdiv_total_of_arith_type x y
              (Term.UOp UserOp.Real)
              (eo_typeof_eq_real_of_smt_real_from_ih y ihY hy)
              (eo_typeof_eq_real_of_smt_real_from_ih x ihX hx)
              (Or.inr rfl))
        hNonNone
  case select =>
    exact eo_to_smt_typeof_matches_translation_apply_select x y ihY ihX hNonNone
  case concat =>
    exact eo_to_smt_typeof_matches_translation_apply_concat x y
      (by rfl)
      (fun w1 w2 hy hx => by
        simpa [__eo_to_smt_type, __eo_mk_apply, __eo_add, native_ite, native_zleq] using
          eo_to_smt_type_typeof_apply_apply_concat_of_bitvec_types x y
            (Term.Numeral (native_nat_to_int w1))
            (Term.Numeral (native_nat_to_int w2))
            (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w1 hy)
            (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w2 hx))
      hNonNone
  case bvand =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvand) SmtTerm.bvand x y
      (by rfl)
      (by rw [__smtx_typeof.eq_38])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvand_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvor =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvor) SmtTerm.bvor x y
      (by rfl)
      (by rw [__smtx_typeof.eq_39])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvor_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvnand =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvnand) SmtTerm.bvnand x y
      (by rfl)
      (by rw [__smtx_typeof.eq_40])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvnand_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvnor =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvnor) SmtTerm.bvnor x y
      (by rfl)
      (by rw [__smtx_typeof.eq_41])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvnor_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvxor =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvxor) SmtTerm.bvxor x y
      (by rfl)
      (by rw [__smtx_typeof.eq_42])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvxor_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvxnor =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvxnor) SmtTerm.bvxnor x y
      (by rfl)
      (by rw [__smtx_typeof.eq_43])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvxnor_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvcomp =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvcomp) SmtTerm.bvcomp (SmtType.BitVec 1) x y
      (by rfl)
      (by rw [__smtx_typeof.eq_44])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvcomp_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvadd =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvadd) SmtTerm.bvadd x y
      (by rfl)
      (by rw [__smtx_typeof.eq_46])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvadd_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvmul =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvmul) SmtTerm.bvmul x y
      (by rfl)
      (by rw [__smtx_typeof.eq_47])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvmul_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvudiv =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvudiv) SmtTerm.bvudiv x y
      (by rfl)
      (by rw [__smtx_typeof.eq_48])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvudiv_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvurem =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvurem) SmtTerm.bvurem x y
      (by rfl)
      (by rw [__smtx_typeof.eq_49])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvurem_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsub =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvsub) SmtTerm.bvsub x y
      (by rfl)
      (by rw [__smtx_typeof.eq_50])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsub_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsdiv =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvsdiv) SmtTerm.bvsdiv x y
      (by rfl)
      (by rw [__smtx_typeof.eq_51])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsdiv_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsrem =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvsrem) SmtTerm.bvsrem x y
      (by rfl)
      (by rw [__smtx_typeof.eq_52])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsrem_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsmod =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvsmod) SmtTerm.bvsmod x y
      (by rfl)
      (by rw [__smtx_typeof.eq_53])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsmod_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvult =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvult) SmtTerm.bvult SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_54])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvult_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvule =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvule) SmtTerm.bvule SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_55])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvule_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvugt =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvugt) SmtTerm.bvugt SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_56])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvugt_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvuge =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvuge) SmtTerm.bvuge SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_57])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvuge_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvslt =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvslt) SmtTerm.bvslt SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_58])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvslt_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsle =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsle) SmtTerm.bvsle SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_59])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsle_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsgt =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsgt) SmtTerm.bvsgt SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_60])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsgt_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsge =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsge) SmtTerm.bvsge SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_61])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsge_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvshl =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvshl) SmtTerm.bvshl x y
      (by rfl)
      (by rw [__smtx_typeof.eq_62])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvshl_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvlshr =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvlshr) SmtTerm.bvlshr x y
      (by rfl)
      (by rw [__smtx_typeof.eq_63])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvlshr_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvashr =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop
      (Term.UOp UserOp.bvashr) SmtTerm.bvashr x y
      (by rfl)
      (by rw [__smtx_typeof.eq_64])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvashr_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvuaddo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvuaddo) SmtTerm.bvuaddo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_69])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvuaddo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsaddo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsaddo) SmtTerm.bvsaddo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_71])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsaddo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvumulo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvumulo) SmtTerm.bvumulo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_72])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvumulo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsmulo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsmulo) SmtTerm.bvsmulo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_73])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsmulo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvusubo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvusubo) SmtTerm.bvusubo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_74])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvusubo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvssubo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvssubo) SmtTerm.bvssubo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_75])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvssubo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsdivo =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
      (Term.UOp UserOp.bvsdivo) SmtTerm.bvsdivo SmtType.Bool x y
      (by rfl)
      (by rw [__smtx_typeof.eq_76])
      (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsdivo_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvultbv =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_cmp_to_bv1
      (Term.UOp UserOp.bvultbv) SmtTerm.bvult x y
      (by rfl)
      (by rw [__smtx_typeof.eq_54])
      (fun w hy hx => by
        simpa using eo_to_smt_type_typeof_apply_apply_bvcomp_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case bvsltbv =>
    exact eo_to_smt_typeof_matches_translation_apply_bv_cmp_to_bv1
      (Term.UOp UserOp.bvsltbv) SmtTerm.bvslt x y
      (by rfl)
      (by rw [__smtx_typeof.eq_58])
      (fun w hy hx => by
        simpa using eo_to_smt_type_typeof_apply_apply_bvcomp_of_bitvec_type x y (Term.Numeral (native_nat_to_int w))
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih y ihY w hy)
          (eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx)
          (bv_width_term_nonstuck w))
      hNonNone
  case «repeat» =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.repeat) y) x) =
          SmtTerm.repeat (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.repeat (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases repeat_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.repeat) y) x)) =
          SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w))) := by
      rw [hTranslate, typeof_repeat_eq, hy, hx]
      simp [__smtx_typeof_repeat, native_ite, hi]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_apply_repeat_of_smt_numeral_bitvec
        x y i w hy hx hi).symm
  case zero_extend =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.zero_extend) y) x) =
          SmtTerm.zero_extend (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.zero_extend (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases zero_extend_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.zero_extend) y) x)) =
          SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
      rw [hTranslate, typeof_zero_extend_eq, hy, hx]
      simp [__smtx_typeof_zero_extend, native_ite, hi]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_apply_zero_extend_of_smt_numeral_bitvec
        x y i w hy hx hi).symm
  case sign_extend =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.sign_extend) y) x) =
          SmtTerm.sign_extend (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.sign_extend (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases sign_extend_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.sign_extend) y) x)) =
          SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
      rw [hTranslate, typeof_sign_extend_eq, hy, hx]
      simp [__smtx_typeof_sign_extend, native_ite, hi]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_apply_sign_extend_of_smt_numeral_bitvec
        x y i w hy hx hi).symm
  case rotate_left =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_left) y) x) =
          SmtTerm.rotate_left (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.rotate_left (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases rotate_left_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_left) y) x)) =
          SmtType.BitVec w := by
      rw [hTranslate, typeof_rotate_left_eq, hy, hx]
      simp [__smtx_typeof_rotate_left, native_ite, hi]
    have hYInt : __eo_typeof y = Term.UOp UserOp.Int :=
      eo_typeof_eq_int_of_smt_int_from_ih y ihY (by
        rw [hy]
        unfold __smtx_typeof
        rfl)
    have hXBitVec :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
      eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_left) y) x)) =
          SmtType.BitVec w := by
      simpa [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
        native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
        SmtEval.native_int_to_nat] using
        eo_to_smt_type_typeof_apply_apply_rotate_left_of_int_bitvec_type
          x y (Term.Numeral (native_nat_to_int w)) hYInt hXBitVec
    exact hSmt.trans hEo.symm
  case rotate_right =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_right) y) x) =
          SmtTerm.rotate_right (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.rotate_right (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases rotate_right_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_right) y) x)) =
          SmtType.BitVec w := by
      rw [hTranslate, typeof_rotate_right_eq, hy, hx]
      simp [__smtx_typeof_rotate_right, native_ite, hi]
    have hYInt : __eo_typeof y = Term.UOp UserOp.Int :=
      eo_typeof_eq_int_of_smt_int_from_ih y ihY (by
        rw [hy]
        unfold __smtx_typeof
        rfl)
    have hXBitVec :
        __eo_typeof x =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
      eo_typeof_eq_bitvec_of_smt_bitvec_from_ih x ihX w hx
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_right) y) x)) =
          SmtType.BitVec w := by
      simpa [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
        native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
        SmtEval.native_int_to_nat] using
        eo_to_smt_type_typeof_apply_apply_rotate_right_of_int_bitvec_type
          x y (Term.Numeral (native_nat_to_int w)) hYInt hXBitVec
    exact hSmt.trans hEo.symm
  case int_to_bv =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.int_to_bv) y) x) =
          SmtTerm.int_to_bv (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.int_to_bv (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases int_to_bv_args_of_non_none hApplyNN with ⟨i, hy, hx, hi⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.int_to_bv) y) x)) =
          SmtType.BitVec (native_int_to_nat i) := by
      rw [hTranslate, typeof_int_to_bv_eq, hy, hx]
      simp [__smtx_typeof_int_to_bv, native_ite, hi]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_apply_int_to_bv_of_smt_numeral_int
        x y i hy hx hi).symm
  case str_at =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x) =
          SmtTerm.str_at (__eo_to_smt y) (__eo_to_smt x) := by
      rfl
    have hApplyNN :
        term_has_non_none_type (SmtTerm.str_at (__eo_to_smt y) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases str_at_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x)) =
          SmtType.Seq T := by
      rw [hTranslate, typeof_str_at_eq (__eo_to_smt y) (__eo_to_smt x), hY, hX]
      simp [__smtx_typeof_str_at]
    have hYTrans :
        __eo_to_smt_type (__eo_typeof y) = SmtType.Seq T := by
      have hTyped := ihY (by rw [hY]; simp)
      rw [hY] at hTyped
      exact hTyped.symm
    rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨U, hYSeq, hU⟩
    have hTGuard :
        __smtx_typeof_guard T (SmtType.Seq T) = SmtType.Seq T := by
      simpa [hYSeq, hU, __eo_to_smt_type] using hYTrans
    have hTNN : T ≠ SmtType.None := by
      intro hNone
      rw [hNone] at hTGuard
      simp [__smtx_typeof_guard, native_ite, native_Teq] at hTGuard
    have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
      eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x)) =
          SmtType.Seq T := by
      simpa [__eo_to_smt_type, hU, smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN] using
        eo_to_smt_type_typeof_apply_apply_str_at_of_seq_int x y U hYSeq hXInt
    exact hSmt.trans hEo.symm
  case _at_strings_stoi_result =>
    let subTerm :=
      SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0) (__eo_to_smt x)
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) y) x) =
          SmtTerm.str_to_int subTerm := by
      rfl
    have hApplyNN : term_has_non_none_type (SmtTerm.str_to_int subTerm) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hSubTy : __smtx_typeof subTerm = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_int) (typeof_str_to_int_eq subTerm) hApplyNN
    have hSubNN : term_has_non_none_type subTerm := by
      unfold term_has_non_none_type
      rw [hSubTy]
      simp
    rcases str_substr_args_of_non_none hSubNN with ⟨T, hY, hZero, hX⟩
    have hSubTy' : __smtx_typeof subTerm = SmtType.Seq T := by
      rw [show subTerm = SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0) (__eo_to_smt x)
        by rfl]
      rw [typeof_str_substr_eq (__eo_to_smt y) (SmtTerm.Numeral 0) (__eo_to_smt x), hY, hZero, hX]
      simp [__smtx_typeof_str_substr]
    have hTChar : T = SmtType.Char := by
      have hEq : SmtType.Seq SmtType.Char = SmtType.Seq T := hSubTy.symm.trans hSubTy'
      injection hEq with hT
      exact hT.symm
    have hYChar : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char := by
      simpa [hTChar] using hY
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) y) x)) =
          SmtType.Int := by
      rw [hTranslate, typeof_str_to_int_eq subTerm, hSubTy]
      simp [native_ite, native_Teq]
    have hYSeqChar :
        __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) :=
      eo_typeof_eq_seq_char_of_smt_seq_char_from_ih y ihY hYChar
    have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
      eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
    have hEo :
        __eo_to_smt_type
            (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) y) x)) =
          SmtType.Int := by
      change
        __eo_to_smt_type (__eo_typeof__at_strings_stoi_result (__eo_typeof y) (__eo_typeof x)) =
          SmtType.Int
      rw [hYSeqChar, hXInt]
      rfl
    exact hSmt.trans hEo.symm
  case _at_bit =>
    exact eo_to_smt_typeof_matches_translation_apply_at_bit x y ihY ihX hNonNone
  case _at_from_bools =>
    exact eo_to_smt_typeof_matches_translation_apply_at_from_bools x y ihY ihX hNonNone
  case _at_bv =>
    exact eo_to_smt_typeof_matches_translation_apply_at_bv x y hNonNone
  case re_exp =>
    exact eo_to_smt_typeof_matches_translation_apply_re_exp x y ihY ihX hNonNone
  case _at_strings_deq_diff =>
    exact eo_to_smt_typeof_matches_translation_apply_at_strings_deq_diff
      x y ihY ihX hNonNone
  case _at_strings_itos_result =>
    exact eo_to_smt_typeof_matches_translation_apply_at_strings_itos_result
      x y ihY ihX hNonNone
  case _at_strings_num_occur =>
    exact eo_to_smt_typeof_matches_translation_apply_at_strings_num_occur
      x y ihY ihX hNonNone
  case is =>
    exact eo_to_smt_typeof_matches_translation_apply_is x y hNonNone
  case tuple =>
    exact eo_to_smt_typeof_matches_translation_apply_tuple x y hNonNone
  case tuple_select =>
    exact eo_to_smt_typeof_matches_translation_apply_tuple_select x y hNonNone
  case set_union =>
    exact eo_to_smt_typeof_matches_translation_apply_set_binop
      UserOp.set_union SmtTerm.set_union x y (by rfl)
      (typeof_set_union_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun T hy hx =>
        eo_to_smt_type_typeof_apply_apply_set_union_of_smt_set_from_ih
          x y T ihY ihX hy hx)
      hNonNone
  case set_inter =>
    exact eo_to_smt_typeof_matches_translation_apply_set_binop
      UserOp.set_inter SmtTerm.set_inter x y (by rfl)
      (typeof_set_inter_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun T hy hx =>
        eo_to_smt_type_typeof_apply_apply_set_inter_of_smt_set_from_ih
          x y T ihY ihX hy hx)
      hNonNone
  case set_minus =>
    exact eo_to_smt_typeof_matches_translation_apply_set_binop
      UserOp.set_minus SmtTerm.set_minus x y (by rfl)
      (typeof_set_minus_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun T hy hx =>
        eo_to_smt_type_typeof_apply_apply_set_minus_of_smt_set_from_ih
          x y T ihY ihX hy hx)
      hNonNone
  case set_member =>
    exact eo_to_smt_typeof_matches_translation_apply_set_member_from_ih
      x y ihY ihX hNonNone
  case set_subset =>
    exact eo_to_smt_typeof_matches_translation_apply_set_pred_binop
      UserOp.set_subset SmtTerm.set_subset x y (by rfl)
      (typeof_set_subset_eq (__eo_to_smt y) (__eo_to_smt x))
      (fun T hy hx =>
        eo_to_smt_type_typeof_apply_apply_set_subset_of_smt_set_from_ih
          x y T ihY ihX hy hx)
      hNonNone
  case set_choose =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_from_ih
      (Term.UOp UserOp.set_choose) y x ihF
      ihX
      (generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h))
      (by rfl) (by rfl) hNonNone
  case set_insert =>
    exact eo_to_smt_typeof_matches_translation_apply_set_insert
      x y ihX hNonNone
  case «forall» =>
    exact eo_to_smt_typeof_matches_translation_apply_forall_from_ih
      x y ihX hNonNone
  case «exists» =>
    exact eo_to_smt_typeof_matches_translation_apply_exists_from_ih
      x y ihX hNonNone
  case _at__at_Pair =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_Pair y x (by rfl) hNonNone
  case _at__at_pair =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_pair y x (by rfl) hNonNone
  case _at__at_TypedList_cons =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_TypedList_cons y x (by rfl) hNonNone
  case Array =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp.Array y x (by rfl) hNonNone
  case _at_strings_num_occur_re =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at_strings_num_occur_re y x (by rfl) hNonNone
  case Tuple =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp.Tuple y x (by rfl) hNonNone
  case _at__at_mon =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_mon y x (by rfl) hNonNone
  case _at__at_poly =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_poly y x (by rfl) hNonNone
  case _at__at_aci_sorted =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_none_head
      UserOp._at__at_aci_sorted y x (by rfl) hNonNone
  all_goals
    exact eo_to_smt_typeof_matches_translation_apply_apply_generic_from_ih
      _ y x ihF ihX
      (generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; exact (eo_to_smt_apply_ne_dt_sel _ y s d i j h).elim)
        (by intro s d i h; exact (eo_to_smt_apply_ne_dt_tester _ y s d i h).elim))
      (by rfl) (by rfl) hNonNone

/-- Handles `(UOp op) y` heads in the nested-application apply proof. -/
private theorem eo_to_smt_typeof_matches_translation_apply_uop_application_head
    (op : UserOp) (y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp op) y)))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) y) x)) := by
  intro hNonNone
  exact eo_to_smt_typeof_matches_translation_apply_uop_application_head_obligation
    op y x ihF ihY ihX hNonNone

/-- Simplifies EO-to-SMT translation for ternary `bvite`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bvite
    (x y z : Term)
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x) =
        SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
          (__eo_to_smt y)
          (__eo_to_smt x) := by
    rfl
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
  have hZ : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec 1 :=
    (smtx_typeof_eq_non_none hEqNN).1
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
        T := by
    rw [hTranslate]
    rw [typeof_ite_eq]
    rw [hCond, hY, hX]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    exact hNonNone (by rw [hSmt, hNone])
  exact hSmt.trans
    (eo_to_smt_type_typeof_apply_apply_apply_bvite_of_smt_bitvec1_same_non_none
      x y z T hZ hY hX hTNN).symm

/-- Bridge-free ternary `ite`, using local IHs to align branch EO types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_ite_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x) =
        SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases ite_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX, hT⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
        T := by
    rw [hTranslate, typeof_ite_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    rw [hZ, hY, hX]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hZBool : __eo_typeof z = Term.Bool :=
    eo_typeof_eq_bool_of_smt_bool_from_ih z ihZ hZ
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = T :=
    eo_to_smt_type_typeof_of_smt_type_from_ih y ihY hY hT
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = T :=
    eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hT
  have hWF : smtx_type_translation_injective_wf T := by
    have hXNN : term_has_non_none_type (__eo_to_smt x) :=
      smtx_term_has_non_none_of_type_eq hX hT
    have hWFx := smtx_term_translation_injective_wf_of_non_none (__eo_to_smt x) hXNN
    simpa [hX] using hWFx
  have hYX : __eo_typeof y = __eo_typeof x :=
    eo_to_smt_type_injective_of_translation_injective_wf hYTrans hXTrans hWF
  have hXTypeNN : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
    rw [hXTrans]
    exact hT
  have hEoRaw :=
    eo_to_smt_type_typeof_apply_apply_apply_ite_of_bool_same_type
      x y z (__eo_typeof x) hZBool hYX rfl hXTypeNN
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
        T :=
    hEoRaw.trans hXTrans
  exact hSmt.trans hEo.symm

/-- Bridge-free ternary `bvite`, using local IHs to align branch EO types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bvite_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x) =
        SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
          (__eo_to_smt y)
          (__eo_to_smt x) := by
    rfl
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
  have hZ : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec 1 :=
    (smtx_typeof_eq_non_none hEqNN).1
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
        T := by
    rw [hTranslate, typeof_ite_eq]
    rw [hCond, hY, hX]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hZBitVec :
      __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int 1)) :=
    eo_typeof_eq_bitvec_of_smt_bitvec_from_ih z ihZ 1 hZ
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = T :=
    eo_to_smt_type_typeof_of_smt_type_from_ih y ihY hY hT
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = T :=
    eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hT
  have hWF : smtx_type_translation_injective_wf T := by
    have hXNN : term_has_non_none_type (__eo_to_smt x) :=
      smtx_term_has_non_none_of_type_eq hX hT
    have hWFx := smtx_term_translation_injective_wf_of_non_none (__eo_to_smt x) hXNN
    simpa [hX] using hWFx
  have hYX : __eo_typeof y = __eo_typeof x :=
    eo_to_smt_type_injective_of_translation_injective_wf hYTrans hXTrans hWF
  have hXTypeNN : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
    rw [hXTrans]
    exact hT
  have hEoRaw :=
    eo_to_smt_type_typeof_apply_apply_apply_bvite_of_bitvec1_same_type
      x y z (__eo_typeof x) hZBitVec hYX rfl hXTypeNN
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
        T :=
    hEoRaw.trans hXTrans
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for ternary bitvector `extract`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_extract
    (x y z : Term)
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.extract) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.extract) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.extract) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.extract) z) y) x) =
        SmtTerm.extract (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases extract_args_of_non_none hApplyNN with ⟨i, j, w, hZ, hY, hX, hj0, hji, hiw⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.extract) z) y) x)) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus (native_zplus i (native_zneg j)) 1)) := by
    rw [hTranslate, typeof_extract_eq, hZ, hY, hX]
    simp [__smtx_typeof_extract, native_ite, hj0, hji, hiw]
  exact hSmt.trans
    (eo_to_smt_type_typeof_apply_apply_apply_extract_of_smt_numeral_numeral_bitvec
      x y z i j w hZ hY hX hj0 hji hiw).symm

/-- Bridge-free proof for `_at_witness_string_length`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_at_witness_string_length
    (x y z : Term)
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_witness_string_length) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_witness_string_length) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_witness_string_length) z) y) x)) := by
  let T := __eo_to_smt_type z
  let body :=
    SmtTerm.eq
      (SmtTerm.str_len (SmtTerm.Var "@x" T))
      (__eo_to_smt y)
  have hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_witness_string_length) z) y) x) =
        native_ite (native_teq (__eo_typeof x) (Term.UOp UserOp.Int))
          (SmtTerm.choice_nth "@x" T body native_nat_zero) SmtTerm.None := by
    rfl
  have hXInt : __eo_typeof x = Term.UOp UserOp.Int := by
    cases hTest : native_teq (__eo_typeof x) (Term.UOp UserOp.Int)
    · exfalso
      apply hNonNone
      rw [hTranslate]
      simp [hTest, native_ite]
    · simpa [native_teq] using hTest
  have hChoiceNN : term_has_non_none_type (SmtTerm.choice_nth "@x" T body 0) := by
    unfold term_has_non_none_type
    have hTermNN := hNonNone
    rw [hTranslate] at hTermNN
    simpa [hXInt, native_teq, native_ite] using hTermNN
  have hBodyBool : __smtx_typeof body = SmtType.Bool :=
    choice_nth_body_bool_of_non_none hChoiceNN
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof (SmtTerm.str_len (SmtTerm.Var "@x" T)))
          (__smtx_typeof (__eo_to_smt y)) ≠
        SmtType.None := by
    have hBodyNN : __smtx_typeof body ≠ SmtType.None := by
      rw [hBodyBool]
      simp
    simpa [body, typeof_eq_eq] using hBodyNN
  have hEqArgs := smtx_typeof_eq_non_none hEqNN
  have hStrLenNN : term_has_non_none_type (SmtTerm.str_len (SmtTerm.Var "@x" T)) := by
    unfold term_has_non_none_type
    exact hEqArgs.2
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (SmtTerm.Var "@x" T)) hStrLenNN with
    ⟨A, hVarSeq⟩
  have hStrLenTy :
      __smtx_typeof (SmtTerm.str_len (SmtTerm.Var "@x" T)) = SmtType.Int := by
    rw [typeof_str_len_eq (SmtTerm.Var "@x" T), hVarSeq]
    simp [__smtx_typeof_seq_op_1_ret]
  have hYIntSmt : __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
    rw [← hEqArgs.1]
    exact hStrLenTy
  have hYInt : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hYIntSmt
  have hChoiceTy :
      __smtx_typeof (SmtTerm.choice_nth "@x" T body 0) = T :=
    choice_term_typeof_of_non_none hChoiceNN
  have hSmt :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_witness_string_length) z) y) x)) =
        T := by
    rw [hTranslate]
    simpa [hXInt, native_teq, native_ite] using hChoiceTy
  have hChoiceGuard :
      __smtx_typeof (SmtTerm.choice_nth "@x" T body 0) =
        __smtx_typeof_guard_wf T T :=
    choice_term_guard_type_of_non_none hChoiceNN
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    unfold term_has_non_none_type at hChoiceNN
    exact hChoiceNN (by rw [hChoiceGuard, hNone])
  have hTWF : __smtx_type_wf T = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hZType : __eo_typeof z = Term.Type :=
    eo_typeof_type_of_smt_type_wf z (by simpa [T] using hTWF)
  have hEo :
      __eo_to_smt_type
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_witness_string_length) z) y) x)) =
        T := by
    simpa [T] using
      eo_to_smt_type_typeof_apply_apply_apply_at_witness_string_length_of_type_int_int
        x y z hZType hYInt hXInt
  exact hSmt.trans hEo.symm

/-- Bridge-free `str_substr`, using the local IHs to recover EO argument types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_substr_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x) =
        SmtTerm.str_substr (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.str_substr (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases str_substr_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, typeof_str_substr_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_str_substr, hZ, hY, hX]
  have hZTrans :
      __eo_to_smt_type (__eo_typeof z) = SmtType.Seq T := by
    have hTyped := ihZ (by rw [hZ]; simp)
    rw [hZ] at hTyped
    exact hTyped.symm
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZSeq, hU⟩
  have hTGuard :
      __smtx_typeof_guard T (SmtType.Seq T) = SmtType.Seq T := by
    simpa [hZSeq, hU, __eo_to_smt_type] using hZTrans
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hTGuard
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hTGuard
  have hYInt : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hY
  have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
        SmtType.Seq T := by
    simpa [__eo_to_smt_type, hU, smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN] using
      eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_seq_int_int
        x y z U hZSeq hYInt hXInt
  exact hSmt.trans hEo.symm

/-- Bridge-free `str_indexof`, using local IHs to recover EO argument types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_indexof_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x) =
        SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases str_indexof_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
        SmtType.Int := by
    rw [hTranslate, typeof_str_indexof_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_str_indexof, native_ite, native_Teq, hZ, hY, hX]
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZSeq, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨V, hYSeq, hV⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_seq_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt z) hZ
  have hUV : U = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
  subst V
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hXInt : __eo_typeof x = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih x ihX hX
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
        SmtType.Int :=
    eo_to_smt_type_typeof_apply_apply_apply_str_indexof_of_seq_seq_int
      x y z U hZSeq hYSeq hXInt (by rw [hU]; exact hTNN)
  exact hSmt.trans hEo.symm

/-- Bridge-free `str_update`, using local IHs to recover EO argument types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_update_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x) =
        SmtTerm.str_update (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.str_update (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases str_update_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, typeof_str_update_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_str_update, native_ite, native_Teq, hZ, hY, hX]
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZSeq, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hX with ⟨V, hXSeq, hV⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_seq_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt z) hZ
  have hUV : U = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
  subst V
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hYInt : __eo_typeof y = Term.UOp UserOp.Int :=
    eo_typeof_eq_int_of_smt_int_from_ih y ihY hY
  have hEoRaw :=
    eo_to_smt_type_typeof_apply_apply_apply_str_update_of_seq_int_seq
      x y z U hZSeq hYInt hXSeq (by rw [hU]; exact hTNN)
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
        SmtType.Seq T :=
    hEoRaw.trans (eo_to_smt_type_seq_of_elem_eq hU hTNN)
  exact hSmt.trans hEo.symm

private theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_smt_seq_from_ih
    (x y z : Term) (T : SmtType)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hZ : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) z) y) x)) =
      SmtType.Seq T := by
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZSeq, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨V, hYSeq, hV⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hX with ⟨W, hXSeq, hW⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_seq_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt z) hZ
  have hUV : U = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
  have hUW : U = W :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hW hWF
  subst V
  subst W
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hEoRaw :=
    eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_seq
      x y z U hZSeq hYSeq hXSeq (by rw [hU]; exact hTNN)
  exact hEoRaw.trans (eo_to_smt_type_seq_of_elem_eq hU hTNN)

private theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_smt_seq_from_ih
    (x y z : Term) (T : SmtType)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hZ : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hY : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hX : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) z) y) x)) =
      SmtType.Seq T := by
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih z ihZ hZ with ⟨U, hZSeq, hU⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih y ihY hY with ⟨V, hYSeq, hV⟩
  rcases eo_typeof_eq_seq_of_smt_seq_from_ih x ihX hX with ⟨W, hXSeq, hW⟩
  have hWF : smtx_type_translation_injective_wf T :=
    smtx_seq_elem_translation_injective_wf_of_type_eq (t := __eo_to_smt z) hZ
  have hUV : U = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hV hWF
  have hUW : U = W :=
    eo_to_smt_type_injective_of_translation_injective_wf hU hW hWF
  subst V
  subst W
  have hTNN : T ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hWF
  have hEoRaw :=
    eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_seq
      x y z U hZSeq hYSeq hXSeq (by rw [hU]; exact hTNN)
  exact hEoRaw.trans (eo_to_smt_type_seq_of_elem_eq hU hTNN)

/-- Simplifies EO-to-SMT translation for sequence ternary operators returning a sequence. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_seq_triop
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (x y z : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x) =
        smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_seq_op_3
          (__smtx_typeof (__eo_to_smt z))
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ T : SmtType,
        __smtx_typeof (__eo_to_smt z) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
          SmtType.Seq T)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases seq_triop_args_of_non_none (op := smtOp) hTy hApplyNN with
    ⟨T, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
        SmtType.Seq T := by
    rw [hTranslate, hTy]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq, hZ, hY, hX]
  exact hSmt.trans (hEo T hZ hY hX).symm

/-- Simplifies EO-to-SMT translation for regex-replacement ternary string operators. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_replace_re_like
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (x y z : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x) =
        smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt z)) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (hEo :
      __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ->
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char ->
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
        SmtType.Seq SmtType.Char)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) := by
  have hApplyNN :
      term_has_non_none_type (smtOp (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := str_replace_re_args_of_non_none (op := smtOp) hTy hApplyNN
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) z) y) x)) =
        SmtType.Seq SmtType.Char := by
    rw [hTranslate, hTy]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
  exact hSmt.trans (hEo hArgs.1 hArgs.2.1 hArgs.2.2).symm

/-- Bridge-free `str_indexof_re`, using local IHs to recover EO argument types. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_str_indexof_re_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x) =
        SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  have hArgs := str_indexof_re_args_of_non_none hApplyNN
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
        SmtType.Int := by
    rw [hTranslate, typeof_str_indexof_re_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
        SmtType.Int :=
    eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_seq_char_reglan
      x y z
      (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hArgs.1)
      (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hArgs.2.1)
      (eo_typeof_eq_int_of_smt_int_from_ih x ihX hArgs.2.2)
  exact hSmt.trans hEo.symm

/-- Bridge-free ternary `store`, using local IHs to recover the EO array shape. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_store_from_ih
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x) =
        SmtTerm.store (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.store (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases store_args_of_non_none hApplyNN with ⟨A, B, hZ, hY, hX⟩
  have hSmt :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
        SmtType.Map A B := by
    rw [hTranslate, typeof_store_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_store, native_ite, native_Teq, hZ, hY, hX]
  have hZTrans : __eo_to_smt_type (__eo_typeof z) = SmtType.Map A B :=
    eo_to_smt_type_typeof_of_smt_type_from_ih z ihZ hZ (by simp)
  rcases eo_to_smt_type_eq_map hZTrans with ⟨U, V, hZArray, hU, hV⟩
  have hMapWF : smtx_type_translation_injective_wf (SmtType.Map A B) := by
    have hZNN : term_has_non_none_type (__eo_to_smt z) :=
      smtx_term_has_non_none_of_type_eq hZ (by simp)
    simpa [hZ] using
      smtx_term_translation_injective_wf_of_non_none (__eo_to_smt z) hZNN
  have hAWF : smtx_type_translation_injective_wf A := hMapWF.1
  have hBWF : smtx_type_translation_injective_wf B := hMapWF.2
  have hANN : A ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hAWF
  have hBNN : B ≠ SmtType.None :=
    smtx_type_translation_injective_wf_non_none hBWF
  have hYTrans : __eo_to_smt_type (__eo_typeof y) = A :=
    eo_to_smt_type_typeof_of_smt_type_from_ih y ihY hY hANN
  have hXTrans : __eo_to_smt_type (__eo_typeof x) = B :=
    eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hBNN
  have hYEq : __eo_typeof y = U :=
    eo_to_smt_type_injective_of_translation_injective_wf hYTrans hU hAWF
  have hXEq : __eo_typeof x = V :=
    eo_to_smt_type_injective_of_translation_injective_wf hXTrans hV hBWF
  have hUNN : __eo_to_smt_type U ≠ SmtType.None := by
    rw [hU]
    exact hANN
  have hVNN : __eo_to_smt_type V ≠ SmtType.None := by
    rw [hV]
    exact hBNN
  have hUNS : U ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none U hUNN
  have hVNS : V ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none V hVNN
  have hReq :
      __eo_requires (__eo_and (__eo_eq U U) (__eo_eq V V)) (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) V) =
        Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) V :=
    eo_requires_eo_and_eq_self_of_non_stuck U V
      (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) V) hUNS hVNS
  have hArrayTy :
      __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) V) =
        SmtType.Map A B := by
    change
      __smtx_typeof_guard (__eo_to_smt_type U)
          (__smtx_typeof_guard (__eo_to_smt_type V)
            (SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type V))) =
        SmtType.Map A B
    rw [hU, hV]
    rw [smtx_typeof_guard_of_non_none B (SmtType.Map A B) hBNN]
    rw [smtx_typeof_guard_of_non_none A (SmtType.Map A B) hANN]
  have hEo :
      __eo_to_smt_type
          (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
        SmtType.Map A B := by
    change
      __eo_to_smt_type (__eo_typeof_store (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
        SmtType.Map A B
    rw [hZArray, hYEq, hXEq]
    simpa [__eo_typeof_store, hUNS, hVNS, hReq] using hArrayTy
  exact hSmt.trans hEo.symm

/-- Simplifies EO-to-SMT translation for ternary `re_loop`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_re_loop
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.re_loop) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.re_loop) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.re_loop) z) y) x)) := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.re_loop) z) y) x) =
        SmtTerm.re_loop (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) := by
    rfl
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.re_loop (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  cases hz : __eo_to_smt z with
  | Numeral n1 =>
      cases hy : __eo_to_smt y with
      | Numeral n2 =>
          have hLoopNN :
              term_has_non_none_type
                (SmtTerm.re_loop
                  (SmtTerm.Numeral n1)
                  (SmtTerm.Numeral n2)
                  (__eo_to_smt x)) := by
            simpa [hz, hy] using hApplyNN
          rcases re_loop_arg_of_non_none hLoopNN with ⟨hn1, hn2, hX⟩
          have hSmt :
              __smtx_typeof
                  (__eo_to_smt
                    (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.re_loop) z) y) x)) =
                SmtType.RegLan := by
            rw [hTranslate, hz, hy]
            rw [typeof_re_loop_eq (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) (__eo_to_smt x)]
            simp [__smtx_typeof_re_loop, hX, hn1, hn2, native_ite]
          have hZInt : __smtx_typeof (__eo_to_smt z) = SmtType.Int := by
            rw [hz]
            unfold __smtx_typeof
            rfl
          have hYInt : __smtx_typeof (__eo_to_smt y) = SmtType.Int := by
            rw [hy]
            unfold __smtx_typeof
            rfl
          have hZEo : __eo_typeof z = Term.UOp UserOp.Int :=
            eo_typeof_eq_int_of_smt_int_from_ih z ihZ hZInt
          have hYEo : __eo_typeof y = Term.UOp UserOp.Int :=
            eo_typeof_eq_int_of_smt_int_from_ih y ihY hYInt
          have hXEo : __eo_typeof x = Term.UOp UserOp.RegLan :=
            eo_typeof_eq_reglan_of_smt_reglan_from_ih x ihX hX
          have hEo :
              __eo_to_smt_type
                  (__eo_typeof
                    (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.re_loop) z) y) x)) =
                SmtType.RegLan := by
            change
              __eo_to_smt_type
                  (__eo_typeof_re_loop (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
                SmtType.RegLan
            rw [hZEo, hYEo, hXEo]
            rfl
          exact hSmt.trans hEo.symm
      | _ =>
          exfalso
          unfold term_has_non_none_type at hApplyNN
          rw [hz, hy, typeof_re_loop_eq] at hApplyNN
          simp [__smtx_typeof_re_loop] at hApplyNN
  | _ =>
      exfalso
      unfold term_has_non_none_type at hApplyNN
      rw [hz, typeof_re_loop_eq] at hApplyNN
      simp [__smtx_typeof_re_loop] at hApplyNN

/-- Handles ternary applications whose binary head translates to a non-special SMT term. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
    (op : UserOp) (z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) ≠
        SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) z) y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (head : SmtTerm)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) (__eo_to_smt x))
    (hSel : ∀ s d i j, head ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, head ≠ SmtTerm.DtTester s d i)
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x) := by
    rw [hHeadTranslate]
    exact generic_apply_type_of_non_special_head head (__eo_to_smt x) hSel hTester
  exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_from_ih
    (Term.UOp op) z y x ihF ihX hGeneric hOuterTranslate hEoApply hNonNone

/-- Handles ternary applications whose binary head is itself a generic application. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
    (g z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hEoApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        __eo_typeof_apply (__eo_typeof (Term.Apply (Term.Apply g z) y)) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x)) := by
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x) := by
    exact generic_apply_type_of_non_special_head
      (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x)
      (by intro s d i j; exact eo_to_smt_apply_ne_dt_sel (Term.Apply g z) y s d i j)
      (by intro s d i; exact eo_to_smt_apply_ne_dt_tester (Term.Apply g z) y s d i)
  exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_from_ih
    g z y x ihF ihX hGeneric hOuterTranslate hEoApply hNonNone

/-- Closes attempts to apply a one-bit bitvector comparison result as a function. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bv_cmp_to_bv1_applied
    (op : UserOp) (smtCmp : SmtTerm -> SmtTerm -> SmtTerm) (x y z : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply
          (SmtTerm.ite (smtCmp (__eo_to_smt z) (__eo_to_smt y))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
          (__eo_to_smt x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  let head :=
    SmtTerm.ite (smtCmp (__eo_to_smt z) (__eo_to_smt y))
      (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof head) (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hHeadGeneric : generic_apply_type head (__eo_to_smt x) := by
      exact generic_apply_type_of_non_special_head _ _
        (by intro s d i j h; simp [head] at h)
        (by intro s d i h; simp [head] at h)
    have hApplyNN' :
        __smtx_typeof (SmtTerm.Apply head (__eo_to_smt x)) ≠ SmtType.None := by
      simpa [head, hTranslate] using hNonNone
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
  have hBitVec1 : T = SmtType.BitVec 1 := by
    exact hThen.symm.trans (smtx_typeof_binary_of_non_none 1 1 hThenNN)
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

/-- Simplifies EO-to-SMT translation for `_at_re_unfold_pos_component`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_re_unfold_pos_component
    (x y z : Term)
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at_re_unfold_pos_component) z) y)
              x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_re_unfold_pos_component) z) y)
            x)) =
      __eo_to_smt_type
        (__eo_typeof
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at_re_unfold_pos_component) z) y)
            x)) := by
  cases x with
  | Numeral n =>
      have hTranslate :
          __eo_to_smt
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at_re_unfold_pos_component) z) y)
                (Term.Numeral n)) =
            native_ite (native_teq (__eo_is_z (Term.Numeral n)) (Term.Boolean true))
              (native_ite
                (native_teq (__eo_is_neg (Term.Numeral n)) (Term.Boolean false))
                (__eo_to_smt_re_unfold_pos_component
                  (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt_nat (Term.Numeral n)))
                SmtTerm.None)
              SmtTerm.None := by
        rfl
      by_cases hnNeg : native_zlt n 0 = true
      · exfalso
        rw [hTranslate] at hNonNone
        simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, hnNeg, native_ite,
          native_teq, native_and, native_not] at hNonNone
      · have hnNegFalse : native_zlt n 0 = false := by
          cases hTest : native_zlt n 0 <;> simp [hTest] at hnNeg ⊢
        have hTranslateComp :
            __eo_to_smt
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp._at_re_unfold_pos_component) z) y)
                  (Term.Numeral n)) =
              __eo_to_smt_re_unfold_pos_component
                (__eo_to_smt z) (__eo_to_smt y) (native_int_to_nat n) := by
          rw [hTranslate]
          simp [__eo_is_z, __eo_is_z_internal, __eo_is_neg, __eo_to_smt_nat,
            hnNegFalse, native_ite, native_teq, native_and, native_not]
        have hCompNN :
            term_has_non_none_type
              (__eo_to_smt_re_unfold_pos_component
                (__eo_to_smt z) (__eo_to_smt y) (native_int_to_nat n)) := by
          unfold term_has_non_none_type
          rw [← hTranslateComp]
          exact hNonNone
        have hArgs :=
          re_unfold_pos_component_args_of_non_none
            (__eo_to_smt z) (__eo_to_smt y) (native_int_to_nat n) hCompNN
        have hSmt :
            __smtx_typeof
                (__eo_to_smt
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_re_unfold_pos_component) z) y)
                    (Term.Numeral n))) =
              SmtType.Seq SmtType.Char := by
          rw [hTranslateComp]
          exact
            smtx_typeof_re_unfold_pos_component_of_non_none
              (__eo_to_smt z) (__eo_to_smt y) (native_int_to_nat n) hCompNN
        have hxSmt : __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
          unfold __smtx_typeof
          rfl
        have hEo :
            __eo_to_smt_type
                (__eo_typeof
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at_re_unfold_pos_component) z) y)
                    (Term.Numeral n))) =
              SmtType.Seq SmtType.Char :=
          eo_to_smt_type_typeof_apply_apply_apply_re_unfold_pos_component_of_seq_char_reglan_int
            (Term.Numeral n) y z
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hArgs.1)
            (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hArgs.2)
            (by rfl)
        exact hSmt.trans hEo.symm
  | _ =>
      exfalso
      apply hNonNone
      change
        __smtx_typeof
          (native_ite (native_teq (__eo_is_z _) (Term.Boolean true))
            (native_ite (native_teq (__eo_is_neg _) (Term.Boolean false))
              (__eo_to_smt_re_unfold_pos_component
                (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt_nat _))
              SmtTerm.None)
            SmtTerm.None) =
        SmtType.None
      simp [__eo_is_z, __eo_is_z_internal, native_ite, native_teq,
        native_and, native_not]

/-- Closes attempts to apply a binary head already known to have SMT type `Bool`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_head_applied
    (op : UserOp) (head : SmtTerm) (x y z : Term)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x))
    (hHeadBool :
      term_has_non_none_type head ->
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) =
          SmtType.Bool)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
              (__eo_to_smt x)) ≠
          SmtType.None := by
      rw [← hOuterTranslate]
      exact hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN : term_has_non_none_type head := by
    unfold term_has_non_none_type
    rw [← hHeadTranslate]
    cases hHead with
    | inl hHead =>
        rw [hHead]
        simp
    | inr hHead =>
        rw [hHead]
        simp
  have hHeadTy := hHeadBool hHeadNN
  cases hHead with
  | inl hHead =>
      cases (hHeadTy.symm.trans hHead)
  | inr hHead =>
      cases (hHeadTy.symm.trans hHead)

/-- Closes attempts to apply a non-special binary head known to have SMT type `Bool`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_non_special_head_applied
    (op : UserOp) (head : SmtTerm) (x y z : Term)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x))
    (hHeadType :
      term_has_non_none_type head ->
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) =
          SmtType.Bool)
    (hSel : ∀ s d i j, head ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, head ≠ SmtTerm.DtTester s d i)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x) := by
    rw [hHeadTranslate]
    exact generic_apply_type_of_non_special_head head (__eo_to_smt x) hSel hTester
  exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_head_applied
    op head x y z hHeadTranslate hOuterTranslate hGeneric hHeadType hNonNone

/-- Closes attempts to apply a binary head known to have a non-function SMT type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_head_applied
    (op : UserOp) (head : SmtTerm) (x y z : Term)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x))
    (hHeadType :
      term_has_non_none_type head ->
        ∃ T,
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) = T ∧
            (∀ A B, T ≠ SmtType.FunType A B) ∧
            (∀ A B, T ≠ SmtType.DtcAppType A B))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
              (__eo_to_smt x)) ≠
          SmtType.None := by
      rw [← hOuterTranslate]
      exact hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN : term_has_non_none_type head := by
    unfold term_has_non_none_type
    rw [← hHeadTranslate]
    cases hHead with
    | inl hHead =>
        rw [hHead]
        simp
    | inr hHead =>
        rw [hHead]
        simp
  rcases hHeadType hHeadNN with ⟨T, hHeadTy, hNotFun, hNotDtcApp⟩
  cases hHead with
  | inl hHead =>
      exact False.elim (hNotFun A B (hHeadTy.symm.trans hHead))
  | inr hHead =>
      exact False.elim (hNotDtcApp A B (hHeadTy.symm.trans hHead))

/-- Closes attempts to apply a non-special binary head with any non-function SMT type. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_non_special_head_applied
    (op : UserOp) (head : SmtTerm) (x y z : Term)
    (hHeadTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y) = head)
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
          (__eo_to_smt x))
    (hHeadType :
      term_has_non_none_type head ->
        ∃ T,
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y)) = T ∧
            (∀ A B, T ≠ SmtType.FunType A B) ∧
            (∀ A B, T ≠ SmtType.DtcAppType A B))
    (hSel : ∀ s d i j, head ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, head ≠ SmtTerm.DtTester s d i)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) := by
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) z) y))
        (__eo_to_smt x) := by
    rw [hHeadTranslate]
    exact generic_apply_type_of_non_special_head head (__eo_to_smt x) hSel hTester
  exact eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_head_applied
    op head x y z hHeadTranslate hOuterTranslate hGeneric hHeadType hNonNone

/-- Bridge-free `update`, reducing the selector head and reusing the EO-side update typing helper. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_update
    (x y z : Term)
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x)) := by
  cases hz : __eo_to_smt z
  case DtSel s d i j =>
    let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x
    have hTranslate :
        __eo_to_smt t =
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x) := by
      change
        __eo_to_smt_updater (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x) =
          __eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x)
      rw [hz]
    have hUpdaterNN :
        __smtx_typeof
            (__eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x)) ≠
          SmtType.None := by
      rw [← hTranslate]
      exact hNonNone
    have hIteNN :
        term_has_non_none_type
          (SmtTerm.ite
            (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt y))
            (__eo_to_smt_updater_rec
              (SmtTerm.DtSel s d i j) (__smtx_dt_num_sels d i) (__eo_to_smt y)
              (__eo_to_smt x) (SmtTerm.DtCons s d i))
            (__eo_to_smt y)) := by
      unfold term_has_non_none_type
      simpa [__eo_to_smt_updater] using hUpdaterNN
    rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, _hT⟩
    have hCondNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt y)) := by
      unfold term_has_non_none_type
      rw [hCond]
      simp
    have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype s d :=
      dt_tester_arg_datatype_of_non_none hCondNN
    have hTTy : T = SmtType.Datatype s d :=
      hElse.symm.trans hYTy
    have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Datatype s d := by
      rw [hTranslate, __eo_to_smt_updater]
      rw [typeof_ite_eq, hCond, hThen, hElse, hTTy]
      simp [__smtx_typeof_ite, native_ite, native_Teq]
    have hEo :=
      eo_to_smt_type_typeof_apply_apply_apply_update_of_smt_dt_sel
        x y z s d i j hz hNonNone
    exact hSmt.trans hEo.symm
  all_goals
    exact False.elim (hNonNone (by
      change
        __smtx_typeof
            (__eo_to_smt_updater (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)) =
          SmtType.None
      rw [hz]
      simp [__eo_to_smt_updater]))

/-- Bridge-free `tuple_update`, reducing the tuple datatype and numeral index cases locally. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_tuple_update
    (x y z : Term)
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x)) =
      __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x)) := by
  cases hTy : __eo_to_smt_type (__eo_typeof y)
  case Datatype s d =>
    cases hz : __eo_to_smt z
    case Numeral n =>
      by_cases hs : s = "@Tuple"
      · subst s
        let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x
        have hTranslate :
            __eo_to_smt t =
              __eo_to_smt_tuple_update (SmtType.Datatype "@Tuple" d)
                (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x) := by
          change
            __eo_to_smt_tuple_update (__eo_to_smt_type (__eo_typeof y)) (__eo_to_smt z)
                (__eo_to_smt y) (__eo_to_smt x) =
              __eo_to_smt_tuple_update (SmtType.Datatype "@Tuple" d)
                (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)
          rw [hTy, hz]
        have hTupleNN :
            __smtx_typeof
                (__eo_to_smt_tuple_update (SmtType.Datatype "@Tuple" d)
                  (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)) ≠
              SmtType.None := by
          rw [← hTranslate]
          exact hNonNone
        have hGe : native_zleq 0 n = true := by
          cases hTest : native_zleq 0 n
          · simp [__eo_to_smt_tuple_update, hTest, native_ite] at hTupleNN
          · rfl
        have hUpdaterNN :
            __smtx_typeof
                (__eo_to_smt_updater
                  (SmtTerm.DtSel "@Tuple" d native_nat_zero (native_int_to_nat n))
                  (__eo_to_smt y) (__eo_to_smt x)) ≠
              SmtType.None := by
          simpa [__eo_to_smt_tuple_update, hGe, native_ite] using hTupleNN
        have hIteNN :
            term_has_non_none_type
              (SmtTerm.ite
                (SmtTerm.Apply (SmtTerm.DtTester "@Tuple" d native_nat_zero) (__eo_to_smt y))
                (__eo_to_smt_updater_rec
                  (SmtTerm.DtSel "@Tuple" d native_nat_zero (native_int_to_nat n))
                  (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt y)
                  (__eo_to_smt x) (SmtTerm.DtCons "@Tuple" d native_nat_zero))
                (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          simpa [__eo_to_smt_updater] using hUpdaterNN
        rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, _hT⟩
        have hCondNN :
            term_has_non_none_type
              (SmtTerm.Apply (SmtTerm.DtTester "@Tuple" d native_nat_zero) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [hCond]
          simp
        have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype "@Tuple" d :=
          dt_tester_arg_datatype_of_non_none hCondNN
        have hTTy : T = SmtType.Datatype "@Tuple" d :=
          hElse.symm.trans hYTy
        have hInnerTy :
            __smtx_typeof
                (__eo_to_smt_updater
                  (SmtTerm.DtSel "@Tuple" d native_nat_zero (native_int_to_nat n))
                  (__eo_to_smt y) (__eo_to_smt x)) =
              SmtType.Datatype "@Tuple" d := by
          rw [__eo_to_smt_updater]
          rw [typeof_ite_eq, hCond, hThen, hElse, hTTy]
          simp [__smtx_typeof_ite, native_ite, native_Teq]
        have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Datatype "@Tuple" d := by
          rw [hTranslate]
          simpa [__eo_to_smt_tuple_update, hGe, native_ite] using hInnerTy
        have hEo :=
          eo_to_smt_type_typeof_apply_apply_apply_tuple_update_of_smt_numeral_tuple
            x y z d n hTy hz hNonNone
        exact hSmt.trans hEo.symm
      · exact False.elim (hNonNone (by
          change
            __smtx_typeof
                (__eo_to_smt_tuple_update (__eo_to_smt_type (__eo_typeof y)) (__eo_to_smt z)
                  (__eo_to_smt y) (__eo_to_smt x)) =
              SmtType.None
          rw [hTy, hz]
          simp [__eo_to_smt_tuple_update, hs]))
    all_goals
      exact False.elim (hNonNone (by
        change
          __smtx_typeof
              (__eo_to_smt_tuple_update (__eo_to_smt_type (__eo_typeof y)) (__eo_to_smt z)
                (__eo_to_smt y) (__eo_to_smt x)) =
            SmtType.None
        rw [hTy, hz]
        simp [__eo_to_smt_tuple_update]))
  all_goals
    exact False.elim (hNonNone (by
      change
        __smtx_typeof
            (__eo_to_smt_tuple_update (__eo_to_smt_type (__eo_typeof y)) (__eo_to_smt z)
              (__eo_to_smt y) (__eo_to_smt x)) =
          SmtType.None
      rw [hTy]
      simp [__eo_to_smt_tuple_update]))

/-- Dispatches special heads shaped as `(f z) y`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_binary_application_head_obligation
    (f z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply f z) y)))
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply f z) y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply f z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply f z) y) x)) := by
  intro hNonNone
  cases f
  case UOp op =>
    cases op
    case ite =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_ite_from_ih
        x y z ihZ ihY ihX hNonNone
    case bvite =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bvite_from_ih
        x y z ihZ ihY ihX hNonNone
    case extract =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_extract
        x y z hNonNone
    case str_substr =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_substr_from_ih
        x y z ihZ ihY ihX hNonNone
    case str_indexof =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_indexof_from_ih
        x y z ihZ ihY ihX hNonNone
    case str_update =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_update_from_ih
        x y z ihZ ihY ihX hNonNone
    case str_replace =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_seq_triop
        UserOp.str_replace SmtTerm.str_replace x y z (by rfl)
        (typeof_str_replace_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
        (fun T hZ hY hX =>
          eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_smt_seq_from_ih
            x y z T ihZ ihY ihX hZ hY hX)
        hNonNone
    case str_replace_all =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_seq_triop
        UserOp.str_replace_all SmtTerm.str_replace_all x y z (by rfl)
        (typeof_str_replace_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
        (fun T hZ hY hX =>
          eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_smt_seq_from_ih
            x y z T ihZ ihY ihX hZ hY hX)
        hNonNone
    case str_replace_re =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_replace_re_like
        UserOp.str_replace_re SmtTerm.str_replace_re x y z (by rfl)
        (typeof_str_replace_re_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
        (fun hZ hY hX =>
          eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_seq_char_reglan
            x y z
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hZ)
            (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hY)
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hX))
        hNonNone
    case str_replace_re_all =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_replace_re_like
        UserOp.str_replace_re_all SmtTerm.str_replace_re_all x y z (by rfl)
        (typeof_str_replace_re_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))
        (fun hZ hY hX =>
          eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_seq_char_reglan
            x y z
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih z ihZ hZ)
            (eo_typeof_eq_reglan_of_smt_reglan_from_ih y ihY hY)
            (eo_typeof_eq_seq_char_of_smt_seq_char_from_ih x ihX hX))
        hNonNone
    case str_indexof_re =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_str_indexof_re_from_ih
        x y z ihZ ihY ihX hNonNone
    case store =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_store_from_ih
        x y z ihZ ihY ihX hNonNone
    case re_loop =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_re_loop
        x y z ihZ ihY ihX hNonNone
    case re_exp =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_exp z y x ihF ihX
        (SmtTerm.re_exp (__eo_to_smt z) (__eo_to_smt y)) (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_strings_deq_diff =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_strings_deq_diff z y x ihF ihX
        (let _v0 := SmtTerm.Numeral 1
         let _v2 := SmtTerm.Var "@x" SmtType.Int
         SmtTerm.choice_nth "@x" SmtType.Int
           (SmtTerm.not
             (SmtTerm.eq
               (SmtTerm.str_substr (__eo_to_smt z) _v2 _v0)
               (SmtTerm.str_substr (__eo_to_smt y) _v2 _v0))) 0)
        (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_strings_itos_result =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_strings_itos_result z y x ihF ihX
        (SmtTerm.mod (__eo_to_smt z)
          (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt y))) (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_strings_num_occur =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_strings_num_occur z y x ihF ihX
        (let _v0 := __eo_to_smt y
         let _v1 := __eo_to_smt z
         SmtTerm.div
           (SmtTerm.neg
             (SmtTerm.str_len _v1)
             (SmtTerm.str_len
               (SmtTerm.str_replace_all
                 _v1
                 _v0
                 (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
           (SmtTerm.str_len _v0))
        (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case or =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.or z y x ihF ihX
        (SmtTerm.or (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case and =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.and z y x ihF ihX
        (SmtTerm.and (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case imp =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.imp z y x ihF ihX
        (SmtTerm.imp (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case xor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.xor z y x ihF ihX
        (SmtTerm.xor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case eq =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.eq z y x ihF ihX
        (SmtTerm.eq (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case plus =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.plus z y x ihF ihX
        (SmtTerm.plus (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case neg =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.neg z y x ihF ihX
        (SmtTerm.neg (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case mult =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.mult z y x ihF ihX
        (SmtTerm.mult (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case lt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.lt z y x ihF ihX
        (SmtTerm.lt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case leq =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.leq z y x ihF ihX
        (SmtTerm.leq (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case gt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.gt z y x ihF ihX
        (SmtTerm.gt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case geq =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.geq z y x ihF ihX
        (SmtTerm.geq (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case div =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.div z y x ihF ihX
        (SmtTerm.div (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case mod =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.mod z y x ihF ihX
        (SmtTerm.mod (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case multmult =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.multmult z y x ihF ihX
        (SmtTerm.multmult (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case divisible =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.divisible z y x ihF ihX
        (SmtTerm.divisible (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case div_total =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.div_total z y x ihF ihX
        (SmtTerm.div_total (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case mod_total =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.mod_total z y x ihF ihX
        (SmtTerm.mod_total (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case multmult_total =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.multmult_total z y x ihF ihX
        (SmtTerm.multmult_total (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case concat =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.concat z y x ihF ihX
        (SmtTerm.concat (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case «repeat» =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.repeat z y x ihF ihX
        (SmtTerm.repeat (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvand =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvand z y x ihF ihX
        (SmtTerm.bvand (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvor z y x ihF ihX
        (SmtTerm.bvor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvnand =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvnand z y x ihF ihX
        (SmtTerm.bvnand (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvnor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvnor z y x ihF ihX
        (SmtTerm.bvnor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvxor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvxor z y x ihF ihX
        (SmtTerm.bvxor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvxnor =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvxnor z y x ihF ihX
        (SmtTerm.bvxnor (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvcomp =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvcomp z y x ihF ihX
        (SmtTerm.bvcomp (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvadd =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvadd z y x ihF ihX
        (SmtTerm.bvadd (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvmul =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvmul z y x ihF ihX
        (SmtTerm.bvmul (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvudiv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvudiv z y x ihF ihX
        (SmtTerm.bvudiv (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvurem =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvurem z y x ihF ihX
        (SmtTerm.bvurem (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsub =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsub z y x ihF ihX
        (SmtTerm.bvsub (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsdiv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsdiv z y x ihF ihX
        (SmtTerm.bvsdiv (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsrem =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsrem z y x ihF ihX
        (SmtTerm.bvsrem (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsmod =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsmod z y x ihF ihX
        (SmtTerm.bvsmod (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvult =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvult z y x ihF ihX
        (SmtTerm.bvult (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvule =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvule z y x ihF ihX
        (SmtTerm.bvule (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvugt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvugt z y x ihF ihX
        (SmtTerm.bvugt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvuge =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvuge z y x ihF ihX
        (SmtTerm.bvuge (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvslt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvslt z y x ihF ihX
        (SmtTerm.bvslt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsle =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsle z y x ihF ihX
        (SmtTerm.bvsle (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsgt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsgt z y x ihF ihX
        (SmtTerm.bvsgt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsge =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsge z y x ihF ihX
        (SmtTerm.bvsge (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvshl =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvshl z y x ihF ihX
        (SmtTerm.bvshl (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvlshr =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvlshr z y x ihF ihX
        (SmtTerm.bvlshr (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvashr =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvashr z y x ihF ihX
        (SmtTerm.bvashr (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case zero_extend =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.zero_extend z y x ihF ihX
        (SmtTerm.zero_extend (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case sign_extend =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.sign_extend z y x ihF ihX
        (SmtTerm.sign_extend (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case rotate_left =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.rotate_left z y x ihF ihX
        (SmtTerm.rotate_left (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case rotate_right =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.rotate_right z y x ihF ihX
        (SmtTerm.rotate_right (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvuaddo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvuaddo z y x ihF ihX
        (SmtTerm.bvuaddo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsaddo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsaddo z y x ihF ihX
        (SmtTerm.bvsaddo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvumulo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvumulo z y x ihF ihX
        (SmtTerm.bvumulo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsmulo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsmulo z y x ihF ihX
        (SmtTerm.bvsmulo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvusubo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvusubo z y x ihF ihX
        (SmtTerm.bvusubo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvssubo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvssubo z y x ihF ihX
        (SmtTerm.bvssubo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case bvsdivo =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.bvsdivo z y x ihF ihX
        (SmtTerm.bvsdivo (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case select =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.select z y x ihF ihX
        (SmtTerm.select (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_concat =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_concat z y x ihF ihX
        (SmtTerm.str_concat (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_contains =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_contains z y x ihF ihX
        (SmtTerm.str_contains (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_at =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_at z y x ihF ihX
        (SmtTerm.str_at (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_prefixof =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_prefixof z y x ihF ihX
        (SmtTerm.str_prefixof (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_suffixof =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_suffixof z y x ihF ihX
        (SmtTerm.str_suffixof (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_lt =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_lt z y x ihF ihX
        (SmtTerm.str_lt (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_leq =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_leq z y x ihF ihX
        (SmtTerm.str_leq (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_range =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_range z y x ihF ihX
        (SmtTerm.re_range (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_concat =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_concat z y x ihF ihX
        (SmtTerm.re_concat (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_inter =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_inter z y x ihF ihX
        (SmtTerm.re_inter (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_union =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_union z y x ihF ihX
        (SmtTerm.re_union (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case re_diff =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.re_diff z y x ihF ihX
        (SmtTerm.re_diff (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case str_in_re =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.str_in_re z y x ihF ihX
        (SmtTerm.str_in_re (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case seq_nth =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.seq_nth z y x ihF ihX
        (SmtTerm.seq_nth (__eo_to_smt z) (__eo_to_smt y)) (by rfl) (by rfl)
        (by intro s d i j h; cases h) (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_strings_stoi_result =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_strings_stoi_result z y x ihF ihX
        (SmtTerm.str_to_int
          (SmtTerm.str_substr (__eo_to_smt z) (SmtTerm.Numeral 0) (__eo_to_smt y)))
        (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_bit =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_bit z y x ihF ihX
        (let _v1 := __eo_to_smt z
         SmtTerm.eq (SmtTerm.extract _v1 _v1 (__eo_to_smt y)) (SmtTerm.Binary 1 1))
        (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_from_bools =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_from_bools z y x ihF ihX
        (SmtTerm.concat
          (SmtTerm.ite (__eo_to_smt z) (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
          (__eo_to_smt y))
        (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case _at_bv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp._at_bv z y x ihF ihX
        (__eo_to_smt__at_bv (__eo_to_smt z) (__eo_to_smt y))
        (by rfl)
        (by rfl)
        (by intro s d i j h; exact eo_to_smt_at_bv_ne_dt_sel _ _ _ _ _ _ h)
        (by intro s d i h; exact eo_to_smt_at_bv_ne_dt_tester _ _ _ _ _ h)
        (by rfl)
        hNonNone
    case bvultbv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bv_cmp_to_bv1_applied
        UserOp.bvultbv SmtTerm.bvult x y z (by rfl) hNonNone
    case bvsltbv =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bv_cmp_to_bv1_applied
        UserOp.bvsltbv SmtTerm.bvslt x y z (by rfl) hNonNone
    case _at_re_unfold_pos_component =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_re_unfold_pos_component
        x y z ihZ ihY hNonNone
    case update =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_update x y z hNonNone
    case tuple_update =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_tuple_update x y z hNonNone
    case set_union =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.set_union z y x ihF ihX
        (SmtTerm.set_union (__eo_to_smt z) (__eo_to_smt y)) (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case set_inter =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.set_inter z y x ihF ihX
        (SmtTerm.set_inter (__eo_to_smt z) (__eo_to_smt y)) (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case set_minus =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_non_special_head
        UserOp.set_minus z y x ihF ihX
        (SmtTerm.set_minus (__eo_to_smt z) (__eo_to_smt y)) (by rfl)
        (by rfl)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        (by rfl)
        hNonNone
    case set_choose =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
        (Term.UOp UserOp.set_choose) z y x ihF ihX (by rfl) (by rfl) hNonNone
    case set_member =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) z) y) =
            SmtTerm.set_member (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_non_special_head_applied
        UserOp.set_member (SmtTerm.set_member (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases set_member_args_of_non_none hHeadNN with ⟨A, hzTy, hyTy⟩
          rw [hHeadTranslate, typeof_set_member_eq]
          simp [__smtx_typeof_set_member, hzTy, hyTy, native_ite, native_Teq])
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case set_subset =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) z) y) =
            SmtTerm.set_subset (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_bool_non_special_head_applied
        UserOp.set_subset (SmtTerm.set_subset (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases set_binop_ret_args_of_non_none
              (op := SmtTerm.set_subset) (T := SmtType.Bool)
              (typeof_set_subset_eq (__eo_to_smt z) (__eo_to_smt y)) hHeadNN with
            ⟨A, hzTy, hyTy⟩
          rw [hHeadTranslate, typeof_set_subset_eq (__eo_to_smt z) (__eo_to_smt y)]
          simp [__smtx_typeof_sets_op_2_ret, hzTy, hyTy, native_ite, native_Teq])
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case qdiv =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) z) y) =
            SmtTerm.qdiv (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_non_special_head_applied
        UserOp.qdiv (SmtTerm.qdiv (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases arith_binop_ret_args_of_non_none
              (op := SmtTerm.qdiv) (R := SmtType.Real)
              (typeof_qdiv_eq (__eo_to_smt z) (__eo_to_smt y)) hHeadNN with hArgs | hArgs
          · refine ⟨SmtType.Real, ?_, ?_, ?_⟩
            · rw [hHeadTranslate, typeof_qdiv_eq (__eo_to_smt z) (__eo_to_smt y)]
              simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
            · intro A B h
              cases h
            · intro A B h
              cases h
          · refine ⟨SmtType.Real, ?_, ?_, ?_⟩
            · rw [hHeadTranslate, typeof_qdiv_eq (__eo_to_smt z) (__eo_to_smt y)]
              simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
            · intro A B h
              cases h
            · intro A B h
              cases h)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case qdiv_total =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) z) y) =
            SmtTerm.qdiv_total (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_non_special_head_applied
        UserOp.qdiv_total (SmtTerm.qdiv_total (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases arith_binop_ret_args_of_non_none
              (op := SmtTerm.qdiv_total) (R := SmtType.Real)
              (typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)) hHeadNN with hArgs | hArgs
          · refine ⟨SmtType.Real, ?_, ?_, ?_⟩
            · rw [hHeadTranslate, typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)]
              simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
            · intro A B h
              cases h
            · intro A B h
              cases h
          · refine ⟨SmtType.Real, ?_, ?_, ?_⟩
            · rw [hHeadTranslate, typeof_qdiv_total_eq (__eo_to_smt z) (__eo_to_smt y)]
              simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
            · intro A B h
              cases h
            · intro A B h
              cases h)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case int_to_bv =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.int_to_bv) z) y) =
            SmtTerm.int_to_bv (__eo_to_smt z) (__eo_to_smt y) := by
        rfl
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_non_function_non_special_head_applied
        UserOp.int_to_bv (SmtTerm.int_to_bv (__eo_to_smt z) (__eo_to_smt y)) x y z
        hHeadTranslate
        (by rfl)
        (by
          intro hHeadNN
          rcases int_to_bv_args_of_non_none hHeadNN with ⟨i, hz', hy', hi⟩
          refine ⟨SmtType.BitVec (native_int_to_nat i), ?_, ?_, ?_⟩
          · rw [hHeadTranslate, typeof_int_to_bv_eq, hz', hy']
            simp [__smtx_typeof_int_to_bv, native_ite, hi]
          · intro A B h
            cases h
          · intro A B h
            cases h)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hNonNone
    case _at_witness_string_length =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_at_witness_string_length
        x y z ihY hNonNone
    case _at_strings_occur_index =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_none_head
        UserOp._at_strings_occur_index z y x (by rfl) hNonNone
    case _at_strings_occur_index_re =>
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_none_head
        UserOp._at_strings_occur_index_re z y x (by rfl) hNonNone
    all_goals
      exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
        _ z y x ihF ihX (by rfl) (by rfl) hNonNone
  all_goals
    exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic_application_head
      _ z y x ihF ihX (by rfl) (by rfl) hNonNone

/-- Handles `(f z) y` heads in the nested-application apply proof. -/
private theorem eo_to_smt_typeof_matches_translation_apply_binary_application_head
    (f z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply f z) y)))
    (ihZ :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply f z) y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply f z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply f z) y) x)) := by
  intro hNonNone
  exact eo_to_smt_typeof_matches_translation_apply_binary_application_head_obligation
    f z y x ihF ihZ ihY ihX hNonNone

private theorem eo_to_smt_typeof_matches_translation_apply_apply_head
    (f y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply f y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply f y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply f y)))
    (ihFArg :
      ∀ g z,
        f = Term.Apply g z ->
          __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z))
    (ihY :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply f y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply f y) x)) := by
  intro hNonNone
  have genericFallback :
      ∀ head : Term,
        (__smtx_typeof (__eo_to_smt head) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt head) =
            __eo_to_smt_type (__eo_typeof head)) ->
        (∀ s d i j, __eo_to_smt head ≠ SmtTerm.DtSel s d i j) ->
        (∀ s d i, __eo_to_smt head ≠ SmtTerm.DtTester s d i) ->
        __eo_to_smt (Term.Apply head x) =
          SmtTerm.Apply (__eo_to_smt head) (__eo_to_smt x) ->
        __eo_typeof (Term.Apply head x) =
          __eo_typeof_apply (__eo_typeof head) (__eo_typeof x) ->
        __smtx_typeof (__eo_to_smt (Term.Apply head x)) ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt (Term.Apply head x)) =
          __eo_to_smt_type (__eo_typeof (Term.Apply head x)) := by
    intro head ihHead hNonSel hNonTester hTranslate hEoApply hNN
    have hGeneric :
        generic_apply_type (__eo_to_smt head) (__eo_to_smt x) :=
      generic_apply_type_of_non_special_head _ _ hNonSel hNonTester
    have hArgWF :
        ∀ A B,
          (__smtx_typeof (__eo_to_smt head) = SmtType.FunType A B ∨
            __smtx_typeof (__eo_to_smt head) = SmtType.DtcAppType A B) ->
          smtx_type_field_wf_rec A native_reflist_nil := by
      intro A B hHead
      have hHeadNN : term_has_non_none_type (__eo_to_smt head) := by
        unfold term_has_non_none_type
        exact smtx_head_non_none_of_apply_cases hHead
      exact smtx_type_fun_like_arg_field_wf_of_domains_wf
        (smtx_term_fun_like_domains_wf_of_non_none _ hHeadNN) hHead
    exact eo_to_smt_typeof_matches_translation_apply_generic_of_field_wf
      head x ihHead ihX hGeneric hTranslate hEoApply hArgWF hNN
  cases f
  case UOp op =>
    exact eo_to_smt_typeof_matches_translation_apply_uop_application_head op y x ihF ihY ihX hNonNone
  case Apply f z =>
    exact eo_to_smt_typeof_matches_translation_apply_binary_application_head f z y x ihF
      (ihFArg f z rfl) ihY ihX hNonNone
  case FunType =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply Term.FunType y) x) =
          SmtTerm.Apply (__eo_to_smt (Term.Apply Term.FunType y)) (__eo_to_smt x) := by
      rfl
    have hHeadTerm :
        __eo_to_smt (Term.Apply Term.FunType y) =
          SmtTerm.Apply SmtTerm.None (__eo_to_smt y) := by
      rfl
    exfalso
    apply hNonNone
    rw [hTranslate, hHeadTerm]
    simp only [__smtx_typeof, __smtx_typeof_apply]
  all_goals
    exact genericFallback _ ihF
        (by intro s d i j h; exact (eo_to_smt_apply_ne_dt_sel _ y s d i j h).elim)
        (by intro s d i h; exact (eo_to_smt_apply_ne_dt_tester _ y s d i h).elim)
        (by rfl)
        (by rfl)
        hNonNone

/-- Closes direct `UOp` applications that are unreachable because their SMT type is `none`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_uop_remaining_obligation
    (op : UserOp) (x : Term)
    (hNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp op) x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply (Term.UOp op) x) hNone

/-- Handles direct `distinct` by reducing to its typed-list inversion. -/
private theorem eo_to_smt_typeof_matches_translation_apply_distinct_obligation
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.distinct) x)) := by
  intro hNonNone
  by_cases hGuard : __eo_to_smt_type_is_tlist (__eo_typeof x) = true
  · have hTranslate :
        __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) x) =
          __eo_to_smt_distinct x := by
      change
        native_ite (__eo_to_smt_type_is_tlist (__eo_typeof x))
          (__eo_to_smt_distinct x) SmtTerm.None =
          __eo_to_smt_distinct x
      simp [native_ite, hGuard]
    have hDistinctNonNone :
        __smtx_typeof (__eo_to_smt_distinct x) ≠ SmtType.None := by
      rw [← hTranslate]
      exact hNonNone
    rw [hTranslate]
    have hSmt := smtx_typeof_eo_to_smt_distinct_of_non_none x hDistinctNonNone
    rw [hSmt]
    exact (eo_to_smt_type_typeof_distinct_of_guard x hGuard).symm
  · have hTranslate :
        __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) x) = SmtTerm.None := by
      change
        native_ite (__eo_to_smt_type_is_tlist (__eo_typeof x))
          (__eo_to_smt_distinct x) SmtTerm.None =
          SmtTerm.None
      cases h : __eo_to_smt_type_is_tlist (__eo_typeof x) <;>
        simp [native_ite, h] at hGuard ⊢
    exact False.elim (hNonNone (by rw [hTranslate]; exact smtx_typeof_none))

/-- `_at_purify` cannot expose a bare tester, so this branch is unreachable. -/
private theorem eo_to_smt_typeof_matches_translation_apply_purify_tester_obligation
    (x y : Term) (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (hTester : __eo_to_smt y = SmtTerm.DtTester s d i)
    (hEoNone :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_purify y) x)) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term._at_purify y) x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term._at_purify y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_purify y) x)) := by
  intro hNonNone
  exact (eo_to_smt_ne_dt_tester y s d i hTester).elim

/-- Remaining constructor fallback obligation for heads not handled by specific cases. -/
private theorem eo_to_smt_typeof_matches_translation_apply_constructor_fallback_obligation
    (f x : Term)
    (hNone :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  exact eo_to_smt_typeof_matches_translation_of_smt_none
    (Term.Apply f x) hNone

theorem eo_to_smt_typeof_matches_translation_apply
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (ihApplyArg :
      ∀ g y,
        f = Term.Apply g y ->
          __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type (__eo_typeof y))
    (ihApplyApplyArg :
      ∀ g z y,
        f = Term.Apply (Term.Apply g z) y ->
          __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
          __smtx_typeof (__eo_to_smt z) = __eo_to_smt_type (__eo_typeof z)) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  cases f <;> intro hNonNone
  case Var name T =>
    have hGeneric :
        __eo_to_smt (Term.Apply (Term.Var name T) x) =
          SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt x) := by
      rfl
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
          exact generic_apply_type_of_non_special_head _ _
            (by intro s' d i j h; cases h)
            (by intro s' d i h; cases h)
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
          exact generic_apply_type_of_non_special_head _ _
            (by intro s' d i j h; cases h)
            (by intro s' d i h; cases h)
        rw [hTranslate, hGenericApply]
        exact smtx_typeof_apply_of_head_cases hHead hX hA
      have hTWF : __smtx_type_wf (__eo_to_smt_type T) = true :=
        Smtm.smtx_typeof_guard_wf_wf_of_non_none
          (__eo_to_smt_type T) (__eo_to_smt_type T) (by
            simpa [__smtx_typeof] using hVarNN)
      cases hT with
      | inl hTFun =>
          rcases eo_to_smt_type_eq_fun hTFun with ⟨U, V, hTEq, hU, hV⟩
          have hFunWF :
              smtx_type_field_wf_rec (SmtType.FunType A B) native_reflist_nil := by
            exact smtx_type_field_wf_rec_of_type_wf_rec (by
              have h := hTWF
              rw [hTFun] at h
              exact smtx_type_wf_rec_of_type_wf (by simp) h)
          have hArgWF := (fun_type_field_wf_rec_components_of_wf hFunWF).1
          have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
            eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hA
          have hxEo : __eo_typeof x = U :=
            eo_to_smt_type_injective_of_field_wf_rec hXTrans hU hArgWF
          have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
            rw [hU]
            exact hA
          have hEo :
              __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Var (Term.String s) T) x)) =
                B :=
            (eo_to_smt_type_typeof_apply_var_of_fun_like
              x T U V s (Or.inl hTEq) hxEo hUNonNone).trans hV
          exact hSmt.trans hEo.symm
      | inr hTDtc =>
          have hBad := hTWF
          rw [hTDtc] at hBad
          simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hBad
    all_goals
      have hVarNone : __eo_to_smt (Term.Var name T) = SmtTerm.None := by
        rw [hName]
        rfl
      apply False.elim
      apply hNonNone
      simpa [hGeneric, hVarNone] using typeof_apply_none_eq (__eo_to_smt x)
  case DtCons s d i =>
    have hReserved : __eo_reserved_datatype_name s = false := by
      cases hRes : __eo_reserved_datatype_name s
      · rfl
      · exfalso
        apply hNonNone
        have hTranslateNone :
            __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
              SmtTerm.Apply SmtTerm.None (__eo_to_smt x) := by
          change SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) =
            SmtTerm.Apply SmtTerm.None (__eo_to_smt x)
          simp [eo_to_smt_term_dt_cons, native_ite, hRes]
        rw [hTranslateNone]
        exact typeof_apply_none_eq (__eo_to_smt x)
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
          SmtTerm.Apply (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
            SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) := by
        rfl
      simpa [eo_to_smt_term_dt_cons, native_ite, hReserved] using hGeneric
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)
            (__eo_to_smt x) := by
        exact generic_apply_type_of_non_special_head _ _
          (by intro s' d' i' j h; cases h)
          (by intro s' d' i' h; cases h)
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGenericApply] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtCons s d i) x)) = B := by
      have hGenericApply :
          generic_apply_type
            (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)
            (__eo_to_smt x) := by
        exact generic_apply_type_of_non_special_head _ _
          (by intro s' d' i' j h; cases h)
          (by intro s' d' i' h; cases h)
      rw [hTranslate, hGenericApply]
      exact smtx_typeof_apply_of_head_cases hHead hX hA
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_dt_cons_of_smt_apply_from_ih
        x s d i A B ihX hReserved hHead hX hA).symm
  case DtSel s d i j =>
    have hReserved : __eo_reserved_datatype_name s = false := by
      cases hRes : __eo_reserved_datatype_name s
      · rfl
      · exfalso
        apply hNonNone
        have hTranslateNone :
            __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
              SmtTerm.Apply SmtTerm.None (__eo_to_smt x) := by
          change SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) =
            SmtTerm.Apply SmtTerm.None (__eo_to_smt x)
          simp [eo_to_smt_term_dt_sel, native_ite, hRes]
        rw [hTranslateNone]
        exact typeof_apply_none_eq (__eo_to_smt x)
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
          SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
            SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) := by
        rfl
      simpa [eo_to_smt_term_dt_sel, native_ite, hReserved] using hGeneric
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
      (eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype_from_ih
        x s d i j ihX hReserved hArg).symm
  case UConst i T =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.UConst i T) x) =
          SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.UConst i T) x) =
            SmtTerm.Apply (__eo_to_smt (Term.UConst i T)) (__eo_to_smt x) := by
        rfl
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
        exact generic_apply_type_of_non_special_head _ _
          (by intro s' d i' j h; cases h)
          (by intro s' d i' h; cases h)
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
        exact generic_apply_type_of_non_special_head _ _
          (by intro s' d i' j h; cases h)
          (by intro s' d i' h; cases h)
      rw [hTranslate, hGenericApply]
      exact smtx_typeof_apply_of_head_cases hHead hX hA
    have hTWF : __smtx_type_wf (__eo_to_smt_type T) = true :=
      Smtm.smtx_typeof_guard_wf_wf_of_non_none
        (__eo_to_smt_type T) (__eo_to_smt_type T) (by
          simpa [__smtx_typeof] using hUConstNN)
    cases hT with
    | inl hTFun =>
        rcases eo_to_smt_type_eq_fun hTFun with ⟨U, V, hTEq, hU, hV⟩
        have hFunWF :
            smtx_type_field_wf_rec (SmtType.FunType A B) native_reflist_nil := by
          exact smtx_type_field_wf_rec_of_type_wf_rec (by
            have h := hTWF
            rw [hTFun] at h
            exact smtx_type_wf_rec_of_type_wf (by simp) h)
        have hArgWF := (fun_type_field_wf_rec_components_of_wf hFunWF).1
        have hXTrans : __eo_to_smt_type (__eo_typeof x) = A :=
          eo_to_smt_type_typeof_of_smt_type_from_ih x ihX hX hA
        have hxEo : __eo_typeof x = U :=
          eo_to_smt_type_injective_of_field_wf_rec hXTrans hU hArgWF
        have hUNonNone : __eo_to_smt_type U ≠ SmtType.None := by
          rw [hU]
          exact hA
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UConst i T) x)) = B :=
          (eo_to_smt_type_typeof_apply_uconst_of_fun_like
            x T U V i (Or.inl hTEq) hxEo hUNonNone).trans hV
        exact hSmt.trans hEo.symm
    | inr hTDtc =>
        have hBad := hTWF
        rw [hTDtc] at hBad
        simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hBad
  case Apply f y =>
    exact eo_to_smt_typeof_matches_translation_apply_apply_head f y x ihF
      (fun g z h => ihApplyApplyArg g z y (by rw [h]))
      (ihApplyArg f y rfl) ihX hNonNone
  case UOp op =>
    cases op
    case distinct =>
      exact eo_to_smt_typeof_matches_translation_apply_distinct_obligation x hNonNone
    case not =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.not) x) =
            SmtTerm.not (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.not (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
        have hNotTy : __smtx_typeof (SmtTerm.not (__eo_to_smt x)) = SmtType.Bool := by
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
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_not_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_not_of_bool x hxEo).symm
    case to_real =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x) =
            SmtTerm.to_real (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.to_real (__eo_to_smt x)) := by
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
          have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
          have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x)) = SmtType.Real := by
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
          have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
          have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x)) = SmtType.Real := by
            rw [hTranslate, typeof_to_real_eq]
            simp [hArgReal, native_ite, native_Teq]
          exact hSmt.trans (eo_to_smt_type_typeof_apply_to_real_of_real x hxEo).symm
    case to_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.to_int) x) =
            SmtTerm.to_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
        real_arg_of_non_none (op := SmtTerm.to_int) (t := __eo_to_smt x)
          (typeof_to_int_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.to_int) x)) = SmtType.Int := by
        rw [hTranslate, typeof_to_int_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_to_int_of_real x hxEo).symm
    case is_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.is_int) x) =
            SmtTerm.is_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.is_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
        real_arg_of_non_none (op := SmtTerm.is_int) (t := __eo_to_smt x)
          (typeof_is_int_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.is_int) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_is_int_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_is_int_of_real x hxEo).symm
    case abs =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.abs) x) =
            SmtTerm.abs (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.abs (__eo_to_smt x)) := by
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
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.abs) x)) = SmtType.Int := by
        rw [hTranslate, typeof_abs_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_abs_of_int x hxEo).symm
    case __eoo_neg_2 =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) =
            SmtTerm.uneg (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.uneg (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg :
          __smtx_typeof (__eo_to_smt x) = SmtType.Int ∨
            __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
        unfold term_has_non_none_type at hApplyNN
        rw [typeof_uneg_eq] at hApplyNN
        cases hTy : __smtx_typeof (__eo_to_smt x) <;>
          simp [__smtx_typeof_arith_overload_op_1, hTy] at hApplyNN
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hArg with hArgInt | hArgReal
      · have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgInt]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
          rw [← hXTyped]
          exact hArgInt
        have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) =
              SmtType.Int := by
          rw [hTranslate, typeof_uneg_eq]
          simp [__smtx_typeof_arith_overload_op_1, hArgInt]
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) =
              SmtType.Int := by
          change __eo_to_smt_type (__eo_typeof_abs (__eo_typeof x)) = SmtType.Int
          rw [hxEo]
          simp [__eo_typeof_abs, __eo_requires, __is_arith_type,
            native_ite, native_teq, native_not]
        exact hSmt.trans hEo.symm
      · have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgReal]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
          rw [← hXTyped]
          exact hArgReal
        have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) =
              SmtType.Real := by
          rw [hTranslate, typeof_uneg_eq]
          simp [__smtx_typeof_arith_overload_op_1, hArgReal]
        have hEo :
            __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) =
              SmtType.Real := by
          change __eo_to_smt_type (__eo_typeof_abs (__eo_typeof x)) = SmtType.Real
          rw [hxEo]
          simp [__eo_typeof_abs, __eo_requires, __is_arith_type,
            native_ite, native_teq, native_not]
        exact hSmt.trans hEo.symm
    case int_pow2 =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.int_pow2) x) =
            SmtTerm.int_pow2 (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.int_pow2 (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.int_pow2)
          (typeof_int_pow2_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_pow2) x)) = SmtType.Int := by
        rw [hTranslate, typeof_int_pow2_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_int_pow2_of_int x hxEo).symm
    case int_log2 =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.int_log2) x) =
            SmtTerm.int_log2 (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.int_log2 (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.int_log2)
          (typeof_int_log2_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_log2) x)) = SmtType.Int := by
        rw [hTranslate, typeof_int_log2_eq]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_int_log2_of_int x hxEo).symm
    case int_ispow2 =>
      let geqTerm :=
        SmtTerm.geq (__eo_to_smt x) (SmtTerm.Numeral 0)
      let eqTerm :=
        SmtTerm.eq (__eo_to_smt x)
          (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt x)))
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.int_ispow2) x) =
            SmtTerm.and geqTerm eqTerm := by
        rfl
      have hApplyNN :
          term_has_non_none_type (SmtTerm.and geqTerm eqTerm) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :
          __smtx_typeof geqTerm = SmtType.Bool ∧
            __smtx_typeof eqTerm = SmtType.Bool :=
        bool_binop_args_bool_of_non_none (op := SmtTerm.and)
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
        arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
          (typeof_geq_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hGeqNN
        
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
        rcases hGeqArgs with hInt | hReal
        · exact hInt.1
        · have hZeroReal := hReal.2
          rw [__smtx_typeof.eq_2] at hZeroReal
          simp at hZeroReal
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.int_ispow2) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_and_eq geqTerm eqTerm]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_int_ispow2_of_int x hxEo).symm
    case _at_int_div_by_zero =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) =
            SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
          __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int :=
        int_binop_args_of_non_none (op := SmtTerm.div) (R := SmtType.Int)
          (typeof_div_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgs.1]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArgs.1
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x)) = SmtType.Int := by
        rw [hTranslate, typeof_div_eq (__eo_to_smt x) (SmtTerm.Numeral 0)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_at_int_div_by_zero_of_int x hxEo).symm
    case _at_mod_by_zero =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) =
            SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
          __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int :=
        int_binop_args_of_non_none (op := SmtTerm.mod) (R := SmtType.Int)
          (typeof_mod_eq (__eo_to_smt x) (SmtTerm.Numeral 0)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgs.1]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArgs.1
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x)) = SmtType.Int := by
        rw [hTranslate, typeof_mod_eq (__eo_to_smt x) (SmtTerm.Numeral 0)]
        simp [hArgs.1, hArgs.2, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_at_mod_by_zero_of_int x hxEo).symm
    case _at_bvsize =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x) =
            let _v0 := __smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))
            native_ite (native_zleq 0 _v0)
              (SmtTerm.plus (SmtTerm.Numeral _v0) (SmtTerm.Numeral 0))
              SmtTerm.None := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (let _v0 := __smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))
             native_ite (native_zleq 0 _v0)
               (SmtTerm.plus (SmtTerm.Numeral _v0) (SmtTerm.Numeral 0))
               SmtTerm.None) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgExists : ∃ w : native_Nat, __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
        apply smtx_bv_sizeof_term_non_none (t := __eo_to_smt x)
        unfold term_has_non_none_type at hApplyNN
        exact hApplyNN
      rcases hArgExists with ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) = SmtType.Int := by
        have hWNonneg : native_zleq 0 (native_nat_to_int w) = true := by
          simp [native_zleq, SmtEval.native_zleq, native_nat_to_int, SmtEval.native_nat_to_int]
        rw [hTranslate, hArg]
        simp [__smtx_bv_sizeof_type, __smtx_typeof, native_ite, hWNonneg,
          __smtx_typeof_arith_overload_op_2]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_at_bvsize_of_bitvec x w hxEo).symm
    case bvnot =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x) =
            SmtTerm.bvnot (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
          (typeof_bvnot_eq (__eo_to_smt x)) hApplyNN with ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x)) = SmtType.BitVec w := by
        rw [hTranslate, typeof_bvnot_eq (__eo_to_smt x), hArg]
        simp [__smtx_typeof_bv_op_1]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvnot_of_bitvec x w hxEo).symm
    case bvneg =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x) =
            SmtTerm.bvneg (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_arg_of_non_none (op := SmtTerm.bvneg)
          (typeof_bvneg_eq (__eo_to_smt x)) hApplyNN with ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) x)) = SmtType.BitVec w := by
        rw [hTranslate, typeof_bvneg_eq (__eo_to_smt x), hArg]
        simp [__smtx_typeof_bv_op_1]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvneg_of_bitvec x w hxEo).symm
    case bvnego =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvnego) x) =
            SmtTerm.bvnego (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.bvnego (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.bvnego) (ret := SmtType.Bool)
          (typeof_bvnego_eq (__eo_to_smt x)) hApplyNN with
        ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnego) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_bvnego_eq (__eo_to_smt x), hArg]
        simp [__smtx_typeof_bv_op_1_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvnego_of_bitvec x w hxEo).symm
    case bvredand =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvredand) x) =
            let _v0 := __eo_to_smt x
            SmtTerm.bvcomp _v0
              (SmtTerm.bvnot
                (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (let _v0 := __eo_to_smt x
             SmtTerm.bvcomp _v0
               (SmtTerm.bvnot
                 (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0))) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_binop_ret_args_of_non_none
          (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1)
          (typeof_bvcomp_eq
            (__eo_to_smt x)
            (SmtTerm.bvnot (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)))
          hApplyNN with
        ⟨w, hArgX, hArgY⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArgX]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArgX
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hArgY' :
          __smtx_typeof
              (SmtTerm.bvnot
                (SmtTerm.Binary (__smtx_bv_sizeof_type (SmtType.BitVec w)) 0)) =
            SmtType.BitVec w := by
        simpa [hArgX] using hArgY
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredand) x)) = SmtType.BitVec 1 := by
        rw [hTranslate]
        rw [typeof_bvcomp_eq]
        rw [hArgX, hArgY']
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, SmtEval.native_nateq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvredand_of_bitvec x w hxEo).symm
    case bvredor =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x) =
            let _v0 := __eo_to_smt x
            SmtTerm.bvnot
              (SmtTerm.bvcomp _v0
                (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (let _v0 := __eo_to_smt x
             SmtTerm.bvnot
               (SmtTerm.bvcomp _v0
                 (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0))) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hInner :
          ∃ w : native_Nat,
            __smtx_typeof
                (SmtTerm.bvcomp
                  (__eo_to_smt x)
                  (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) =
              SmtType.BitVec w := by
        rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
            (typeof_bvnot_eq
              (SmtTerm.bvcomp
                (__eo_to_smt x)
                (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)))
            hApplyNN with ⟨w, hInner⟩
        exact ⟨w, hInner⟩
      rcases hInner with ⟨_, hInnerTy⟩
      have hInnerNN :
          term_has_non_none_type
            (SmtTerm.bvcomp
              (__eo_to_smt x)
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) := by
        unfold term_has_non_none_type
        rw [hInnerTy]
        simp
      rcases bv_binop_ret_args_of_non_none
          (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1)
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
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hArgY' :
          __smtx_typeof (SmtTerm.Binary (__smtx_bv_sizeof_type (SmtType.BitVec w)) 0) =
            SmtType.BitVec w := by
        simpa [hArgX] using hArgY
      have hInnerOne :
          __smtx_typeof
              (SmtTerm.bvcomp
                (__eo_to_smt x)
                (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) =
            SmtType.BitVec 1 := by
        rw [typeof_bvcomp_eq]
        rw [hArgX, hArgY']
        simp [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, SmtEval.native_nateq]
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvredor) x)) = SmtType.BitVec 1 := by
        rw [hTranslate, typeof_bvnot_eq]
        rw [hInnerOne]
        simp [__smtx_typeof_bv_op_1]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_bvredor_of_bitvec x w hxEo).symm
    case str_len =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) x) =
            SmtTerm.str_len (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgExists : ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        exact seq_arg_of_non_none_ret (op := SmtTerm.str_len)
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
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) x)) = SmtType.Int := by
        rw [hTranslate, typeof_str_len_eq (__eo_to_smt x), hArg]
        simp [__smtx_typeof_seq_op_1_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_len_of_seq x V hxEo).symm
    case str_rev =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) x) =
            SmtTerm.str_rev (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
          (typeof_str_rev_eq (__eo_to_smt x)) hApplyNN with ⟨T, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
        rw [← hXTyped]
        exact hArg
      rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) x)) = SmtType.Seq T := by
        rw [hTranslate, typeof_str_rev_eq (__eo_to_smt x)]
        simp [__smtx_typeof_seq_op_1, hArg]
      have hEo :
          __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) x)) =
            SmtType.Seq (__eo_to_smt_type V) :=
        eo_to_smt_type_typeof_apply_str_rev_of_seq x V hxEo (by
          intro hNone
          rw [hxEo] at hxSmt
          simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hNone] at hxSmt)
      rw [hV] at hEo
      exact hSmt.trans hEo.symm
    case str_to_lower =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_lower) x) =
            SmtTerm.str_to_lower (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_lower (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
          (typeof_str_to_lower_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_lower) x)) =
            SmtType.Seq SmtType.Char := by
        rw [hTranslate, typeof_str_to_lower_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char x hxEo).symm
    case str_to_upper =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_upper) x) =
            SmtTerm.str_to_upper (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_upper (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
          (typeof_str_to_upper_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_upper) x)) =
            SmtType.Seq SmtType.Char := by
        rw [hTranslate, typeof_str_to_upper_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char x hxEo).symm
    case str_to_code =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_code) x) =
            SmtTerm.str_to_code (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_code (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
          (typeof_str_to_code_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_code) x)) = SmtType.Int := by
        rw [hTranslate, typeof_str_to_code_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_code_of_seq_char x hxEo).symm
    case str_from_code =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_code) x) =
            SmtTerm.str_from_code (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_from_code (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.str_from_code) (R := SmtType.Seq SmtType.Char)
          (typeof_str_from_code_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_code) x)) =
            SmtType.Seq SmtType.Char := by
        rw [hTranslate, typeof_str_from_code_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_code_of_int x hxEo).symm
    case str_is_digit =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_is_digit) x) =
            SmtTerm.str_is_digit (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_is_digit (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_is_digit)
          (typeof_str_is_digit_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_is_digit) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_str_is_digit_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char x hxEo).symm
    case str_to_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) x) =
            SmtTerm.str_to_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
          (typeof_str_to_int_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) x)) = SmtType.Int := by
        rw [hTranslate, typeof_str_to_int_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_int_of_seq_char x hxEo).symm
    case str_from_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_int) x) =
            SmtTerm.str_from_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_from_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
        int_ret_arg_of_non_none (op := SmtTerm.str_from_int) (R := SmtType.Seq SmtType.Char)
          (typeof_str_from_int_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Int) := eo_to_smt_type_eq_int hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_int) x)) =
            SmtType.Seq SmtType.Char := by
        rw [hTranslate, typeof_str_from_int_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_int_of_int x hxEo).symm
    case _at_strings_stoi_non_digit =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x) =
            SmtTerm.str_indexof_re
              (__eo_to_smt x)
              (SmtTerm.re_comp
                (SmtTerm.re_range (SmtTerm.String "0") (SmtTerm.String "9")))
              (SmtTerm.Numeral 0) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.str_indexof_re
              (__eo_to_smt x)
              (SmtTerm.re_comp
                (SmtTerm.re_range (SmtTerm.String "0") (SmtTerm.String "9")))
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
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x)) =
            SmtType.Int := by
        rw [hTranslate]
        rw [typeof_str_indexof_re_eq]
        rw [hArgs.1, hArgs.2.1, hArgs.2.2]
        simp [native_ite, native_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char x hxEo).symm
    case str_to_re =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) x) =
            SmtTerm.str_to_re (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.str_to_re (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
          (typeof_str_to_re_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := eo_to_smt_type_eq_seq_char hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_str_to_re_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_re_of_seq_char x hxEo).symm
    case re_mult =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) x) =
            SmtTerm.re_mult (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.re_mult (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
        reglan_arg_of_non_none (op := SmtTerm.re_mult)
          (typeof_re_mult_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.RegLan) := eo_to_smt_type_eq_reglan hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_re_mult_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_re_mult_of_reglan x hxEo).symm
    case re_plus =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.re_plus) x) =
            SmtTerm.re_plus (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.re_plus (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
        reglan_arg_of_non_none (op := SmtTerm.re_plus)
          (typeof_re_plus_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.RegLan) := eo_to_smt_type_eq_reglan hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_plus) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_re_plus_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_re_plus_of_reglan x hxEo).symm
    case re_opt =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.re_opt) x) =
            SmtTerm.re_opt (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.re_opt (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
        reglan_arg_of_non_none (op := SmtTerm.re_opt)
          (typeof_re_opt_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.RegLan) := eo_to_smt_type_eq_reglan hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_opt) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_re_opt_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_re_opt_of_reglan x hxEo).symm
    case re_comp =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.re_comp) x) =
            SmtTerm.re_comp (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.re_comp (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
        reglan_arg_of_non_none (op := SmtTerm.re_comp)
          (typeof_re_comp_eq (__eo_to_smt x)) hApplyNN
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = (Term.UOp UserOp.RegLan) := eo_to_smt_type_eq_reglan hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_comp) x)) = SmtType.RegLan := by
        rw [hTranslate, typeof_re_comp_eq (__eo_to_smt x)]
        simp [hArg, native_ite, native_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_re_comp_of_reglan x hxEo).symm
    case seq_unit =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) x) =
            SmtTerm.seq_unit (__eo_to_smt x) := by
        rfl
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        intro hXNone
        apply hNonNone
        rw [hTranslate, typeof_seq_unit_eq (__eo_to_smt x), hXNone]
        simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
          native_and, native_ite]
      have hXTyped := ihX hXNonNone
      have hxEoNonNone : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
        rw [← hXTyped]
        exact hXNonNone
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.seq_unit) x)) =
            SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
        have hGuardNN :
            __smtx_typeof_guard_wf (__smtx_typeof (__eo_to_smt x))
                (SmtType.Seq (__smtx_typeof (__eo_to_smt x))) ≠
              SmtType.None := by
          rw [hTranslate, typeof_seq_unit_eq (__eo_to_smt x)] at hNonNone
          exact hNonNone
        have hGuard :
            __smtx_typeof_guard_wf (__eo_to_smt_type (__eo_typeof x))
                (SmtType.Seq (__eo_to_smt_type (__eo_typeof x))) =
              SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
          rw [← hXTyped]
          exact smtx_typeof_guard_wf_of_non_none
            (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq (__smtx_typeof (__eo_to_smt x))) hGuardNN
        rw [hTranslate, typeof_seq_unit_eq (__eo_to_smt x), hXTyped]
        exact hGuard
      exact hSmt.trans (eo_to_smt_type_typeof_apply_seq_unit_of_non_none x hxEoNonNone).symm
    case is =>
      exfalso
      apply hNonNone
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.is) x) =
            SmtTerm.Apply (__eo_to_smt (Term.UOp UserOp.is)) (__eo_to_smt x) := by
        rfl
      have hHeadNone : __eo_to_smt (Term.UOp UserOp.is) = SmtTerm.None := by
        rfl
      rw [hTranslate, hHeadNone]
      exact typeof_apply_none_eq (__eo_to_smt x)
    case set_singleton =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) x) =
            SmtTerm.set_singleton (__eo_to_smt x) := by
        rfl
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        intro hXNone
        apply hNonNone
        rw [hTranslate, typeof_set_singleton_eq (__eo_to_smt x), hXNone]
        simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
          native_and, native_ite]
      have hXTyped := ihX hXNonNone
      have hxEoNonNone : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
        rw [← hXTyped]
        exact hXNonNone
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_singleton) x)) =
            SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
        have hGuardNN :
            __smtx_typeof_guard_wf (__smtx_typeof (__eo_to_smt x))
                (SmtType.Set (__smtx_typeof (__eo_to_smt x))) ≠
              SmtType.None := by
          rw [hTranslate, typeof_set_singleton_eq (__eo_to_smt x)] at hNonNone
          exact hNonNone
        have hGuard :
            __smtx_typeof_guard_wf (__eo_to_smt_type (__eo_typeof x))
                (SmtType.Set (__eo_to_smt_type (__eo_typeof x))) =
              SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
          rw [← hXTyped]
          exact smtx_typeof_guard_wf_of_non_none
            (__smtx_typeof (__eo_to_smt x))
            (SmtType.Set (__smtx_typeof (__eo_to_smt x))) hGuardNN
        rw [hTranslate, typeof_set_singleton_eq (__eo_to_smt x), hXTyped]
        exact hGuard
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_set_singleton_of_non_none x hxEoNonNone).symm
    case set_choose =>
      exact eo_to_smt_typeof_matches_translation_apply_set_choose x hNonNone
    case set_is_empty =>
      exfalso
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_empty) x) =
            let _v0 := __eo_to_smt x
            SmtTerm.eq _v0 (SmtTerm.set_empty (__smtx_typeof _v0)) := by
        rfl
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
      let T := __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) x))
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_singleton) x) =
            SmtTerm.exists "@x" T
              (SmtTerm.eq (__eo_to_smt x)
                (SmtTerm.set_singleton (SmtTerm.Var "@x" T))) := by
        rfl
      have hExistsNN :
          term_has_non_none_type
            (SmtTerm.exists "@x" T
              (SmtTerm.eq (__eo_to_smt x)
                (SmtTerm.set_singleton (SmtTerm.Var "@x" T)))) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hBodyNN :
          term_has_non_none_type
            (SmtTerm.eq (__eo_to_smt x)
              (SmtTerm.set_singleton (SmtTerm.Var "@x" T))) := by
        unfold term_has_non_none_type
        rw [exists_body_bool_of_non_none hExistsNN]
        simp
      have hEqNN :
          __smtx_typeof_eq
              (__smtx_typeof (__eo_to_smt x))
              (__smtx_typeof (SmtTerm.set_singleton (SmtTerm.Var "@x" T))) ≠
            SmtType.None := by
        unfold term_has_non_none_type at hBodyNN
        rw [typeof_eq_eq] at hBodyNN
        exact hBodyNN
      have hEqArgs := smtx_typeof_eq_non_none hEqNN
      have hSingletonNN :
          __smtx_typeof (SmtTerm.set_singleton (SmtTerm.Var "@x" T)) ≠
            SmtType.None := by
        rw [← hEqArgs.1]
        exact hEqArgs.2
      have hVarNN : __smtx_typeof (SmtTerm.Var "@x" T) ≠ SmtType.None := by
        intro hVarNone
        apply hSingletonNN
        rw [typeof_set_singleton_eq, hVarNone]
        simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_rec,
          native_and, native_ite]
      have hTNonNone : T ≠ SmtType.None := by
        intro hTNone
        have hVarTyNone := smtx_typeof_var_of_non_none "@x" T hVarNN
        exact hVarNN (hVarTyNone.trans hTNone)
      have hVarTy : __smtx_typeof (SmtTerm.Var "@x" T) = T := by
        simpa using smtx_typeof_var_of_non_none "@x" T hVarNN
      have hSingletonGuard :
          __smtx_typeof_guard_wf T (SmtType.Set T) = SmtType.Set T := by
        rw [← hVarTy]
        exact smtx_typeof_guard_wf_of_non_none
          (__smtx_typeof (SmtTerm.Var "@x" T))
          (SmtType.Set (__smtx_typeof (SmtTerm.Var "@x" T))) (by
            simpa [typeof_set_singleton_eq] using hSingletonNN)
      have hXTy :
          __smtx_typeof (__eo_to_smt x) = SmtType.Set T := by
        rw [hEqArgs.1, typeof_set_singleton_eq, hVarTy]
        exact hSingletonGuard
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hXTy]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Set T := by
        rw [← hXTyped]
        exact hXTy
      rcases TranslationProofs.eo_to_smt_type_eq_set hxSmt with ⟨U, hxEo, hU⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.set_is_singleton) x)) = SmtType.Bool := by
        rw [hTranslate, typeof_exists_eq]
        rw [typeof_eq_eq, typeof_set_singleton_eq, hVarTy]
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq,
          hXTy, hSingletonGuard]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_set_is_singleton_of_set x U hxEo).symm
    case _at_div_by_zero =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) =
            SmtTerm.qdiv (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1)) := by
        rfl
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.qdiv (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1))) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :
          (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
              __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) = SmtType.Int) ∨
            (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
              __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) = SmtType.Real) :=
        arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real)
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
      have hxEo : __eo_typeof x = (Term.UOp UserOp.Real) := eo_to_smt_type_eq_real hxSmt
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_div_by_zero) x)) = SmtType.Real := by
        rw [hTranslate, typeof_qdiv_eq (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1)),
          typeof_rational_eq, hArg]
        simp [__smtx_typeof_arith_overload_op_2_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_at_div_by_zero_of_real x hxEo).symm
    case ubv_to_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.ubv_to_int) x) =
            SmtTerm.ubv_to_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.ubv_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.ubv_to_int) (ret := SmtType.Int)
          (by rw [__smtx_typeof.eq_130]) hApplyNN with
        ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.ubv_to_int) x)) = SmtType.Int := by
        rw [hTranslate, __smtx_typeof.eq_130, hArg]
        simp [__smtx_typeof_bv_op_1_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_ubv_to_int_of_bitvec x w hxEo).symm
    case sbv_to_int =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.UOp UserOp.sbv_to_int) x) =
            SmtTerm.sbv_to_int (__eo_to_smt x) := by
        rfl
      have hApplyNN : term_has_non_none_type (SmtTerm.sbv_to_int (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.sbv_to_int) (ret := SmtType.Int)
          (by rw [__smtx_typeof.eq_131]) hApplyNN with
        ⟨w, hArg⟩
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hArg]
        simp
      have hXTyped := ihX hXNonNone
      have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
        rw [← hXTyped]
        exact hArg
      have hxEo : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) :=
        eo_to_smt_type_eq_bitvec hxSmt
      have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.sbv_to_int) x)) = SmtType.Int := by
        rw [hTranslate, __smtx_typeof.eq_131, hArg]
        simp [__smtx_typeof_bv_op_1_ret]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_sbv_to_int_of_bitvec x w hxEo).symm
    all_goals
      refine eo_to_smt_typeof_matches_translation_apply_uop_remaining_obligation _ x ?_ hNonNone
      first
      | change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) = SmtType.None
        exact typeof_apply_none_eq (__eo_to_smt x)
      | change __smtx_typeof (SmtTerm.Apply SmtTerm.re_allchar (__eo_to_smt x)) = SmtType.None
        exact typeof_apply_reglan_head_eq_none _ _
          (by unfold __smtx_typeof; rfl)
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
      | change __smtx_typeof (SmtTerm.Apply SmtTerm.re_none (__eo_to_smt x)) = SmtType.None
        exact typeof_apply_reglan_head_eq_none _ _
          (by unfold __smtx_typeof; rfl)
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
      | change __smtx_typeof (SmtTerm.Apply SmtTerm.re_all (__eo_to_smt x)) = SmtType.None
        exact typeof_apply_reglan_head_eq_none _ _
          (by unfold __smtx_typeof; rfl)
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
      | change
          __smtx_typeof
              (SmtTerm.Apply
                (SmtTerm.DtCons "@Tuple"
                  (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) 0)
                (__eo_to_smt x)) =
            SmtType.None
        exact typeof_apply_tuple_unit_eq_none (__eo_to_smt x)
  case _at_purify y =>
    by_cases hSelCase : ∃ s d i j, __eo_to_smt y = SmtTerm.DtSel s d i j
    · rcases hSelCase with ⟨s, d, i, j, hSel⟩
      have hHeadTranslate :
          __eo_to_smt (Term._at_purify y) = SmtTerm.DtSel s d i j := by
        have hPurify :
            __eo_to_smt (Term._at_purify y) = __eo_to_smt y := by
          rfl
        exact hPurify.trans hSel
      have hTranslate :
          __eo_to_smt (Term.Apply (Term._at_purify y) x) =
            SmtTerm.Apply (SmtTerm.DtSel s d i j) (__eo_to_smt x) := by
        have hGeneric :
            __eo_to_smt (Term.Apply (Term._at_purify y) x) =
              SmtTerm.Apply (__eo_to_smt (Term._at_purify y)) (__eo_to_smt x) := by
          rfl
        rw [hGeneric, hHeadTranslate]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.DtSel s d i j) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArg :
          __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s d :=
        dt_sel_arg_datatype_of_non_none hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term._at_purify y) x)) =
            __smtx_ret_typeof_sel s d i j := by
        rw [hTranslate]
        exact dt_sel_term_typeof_of_non_none hApplyNN
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_purify_of_dt_sel_translation
          x y s d i j ihX hSel hArg hApplyNN).symm
    · by_cases hTesterCase : ∃ s d i, __eo_to_smt y = SmtTerm.DtTester s d i
      · rcases hTesterCase with ⟨s, d, i, hTester⟩
        have hEoNone :
            __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_purify y) x)) = SmtType.None := by
          exact eo_to_smt_type_typeof_apply_purify_of_dt_tester_translation x y s d i hTester
        exact eo_to_smt_typeof_matches_translation_apply_purify_tester_obligation
          x y s d i hTester hEoNone hNonNone
      · have hPurifyHead : __eo_to_smt (Term._at_purify y) = __eo_to_smt y := by
          rfl
        have hNonSel :
            ∀ s d i j, __eo_to_smt (Term._at_purify y) ≠ SmtTerm.DtSel s d i j := by
          intro s d i j h
          apply hSelCase
          exact ⟨s, d, i, j, by rw [← hPurifyHead]; exact h⟩
        have hNonTester :
            ∀ s d i, __eo_to_smt (Term._at_purify y) ≠ SmtTerm.DtTester s d i := by
          intro s d i h
          apply hTesterCase
          exact ⟨s, d, i, by rw [← hPurifyHead]; exact h⟩
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term._at_purify y)) (__eo_to_smt x) := by
          exact generic_apply_type_of_non_special_head _ _ hNonSel hNonTester
        have hArgWF :
            ∀ A B,
              (__smtx_typeof (__eo_to_smt (Term._at_purify y)) = SmtType.FunType A B ∨
                __smtx_typeof (__eo_to_smt (Term._at_purify y)) = SmtType.DtcAppType A B) ->
              smtx_type_field_wf_rec A native_reflist_nil := by
          intro A B hHead
          have hHeadNN : term_has_non_none_type (__eo_to_smt (Term._at_purify y)) := by
            unfold term_has_non_none_type
            exact smtx_head_non_none_of_apply_cases hHead
          exact smtx_type_fun_like_arg_field_wf_of_domains_wf
            (smtx_term_fun_like_domains_wf_of_non_none _ hHeadNN) hHead
        exact eo_to_smt_typeof_matches_translation_apply_generic_of_field_wf
          (Term._at_purify y) x ihF ihX hGeneric (by rfl) (by rfl) hArgWF hNonNone
  case _at_array_deq_diff x1 x2 =>
    have hHeadTranslate :
        __eo_to_smt (Term._at_array_deq_diff x1 x2) =
      let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
      let _v2 := SmtTerm.Var "@x" _v0
      SmtTerm.choice_nth "@x" _v0
        (SmtTerm.not
          (SmtTerm.eq
            (SmtTerm.select (__eo_to_smt x1) _v2)
            (SmtTerm.select (__eo_to_smt x2) _v2))) 0 := by
      rfl
    have hTranslate :
        __eo_to_smt (Term.Apply (Term._at_array_deq_diff x1 x2) x) =
          SmtTerm.Apply (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x) := by
      rfl
    have hGeneric :
        generic_apply_type (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x) := by
      rw [hHeadTranslate]
      exact generic_apply_type_of_non_special_head _ _ (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
    have hArgWF :
        ∀ A B,
          (__smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) = SmtType.FunType A B ∨
            __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) = SmtType.DtcAppType A B) ->
          smtx_type_field_wf_rec A native_reflist_nil := by
      intro A B hHead
      rw [hHeadTranslate] at hHead
      simpa using choice_nth_fun_like_arg_field_wf
        "@x" (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
        (SmtTerm.not
          (SmtTerm.eq
            (SmtTerm.select (__eo_to_smt x1)
              (SmtTerm.Var "@x" (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))))
            )
            (SmtTerm.select (__eo_to_smt x2)
              (SmtTerm.Var "@x" (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))))
            )))
        hHead
    exact eo_to_smt_typeof_matches_translation_apply_generic_of_field_wf
      (Term._at_array_deq_diff x1 x2) x ihF ihX hGeneric hTranslate (by rfl) hArgWF hNonNone
  case set_empty T =>
    exfalso
    apply hNonNone
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.set_empty T) x) =
          SmtTerm.Apply (__eo_to_smt_set_empty (__eo_to_smt_type T)) (__eo_to_smt x) := by
      rfl
    have hGeneric :
        generic_apply_type (__eo_to_smt_set_empty (__eo_to_smt_type T)) (__eo_to_smt x) := by
      cases hT : __eo_to_smt_type T <;> simp [__eo_to_smt_set_empty]
      all_goals
        exact generic_apply_type_of_non_special_head _ _
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
    rw [hTranslate, hGeneric]
    exact smtx_typeof_apply_eo_to_smt_set_empty_eq_none
      (__eo_to_smt_type T) (__smtx_typeof (__eo_to_smt x))
  case _at_sets_deq_diff x1 x2 =>
    have hHeadTranslate :
        __eo_to_smt (Term._at_sets_deq_diff x1 x2) =
          let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))
          let _v2 := SmtTerm.Var "@x" _v0
          SmtTerm.choice_nth "@x" _v0
            (SmtTerm.not
              (SmtTerm.eq
                (SmtTerm.set_member _v2 (__eo_to_smt x1))
                (SmtTerm.set_member _v2 (__eo_to_smt x2)))) 0 := by
      rfl
    have hTranslate :
        __eo_to_smt (Term.Apply (Term._at_sets_deq_diff x1 x2) x) =
          SmtTerm.Apply (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x) := by
      rfl
    have hGeneric :
        generic_apply_type (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x) := by
      rw [hHeadTranslate]
      exact generic_apply_type_of_non_special_head _ _ (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
    have hArgWF :
        ∀ A B,
          (__smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) = SmtType.FunType A B ∨
            __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) = SmtType.DtcAppType A B) ->
          smtx_type_field_wf_rec A native_reflist_nil := by
      intro A B hHead
      rw [hHeadTranslate] at hHead
      simpa using choice_nth_fun_like_arg_field_wf
        "@x" (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
        (SmtTerm.not
          (SmtTerm.eq
            (SmtTerm.set_member
              (SmtTerm.Var "@x" (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))))
              (__eo_to_smt x1))
            (SmtTerm.set_member
              (SmtTerm.Var "@x" (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))))
              (__eo_to_smt x2))))
        hHead
    exact eo_to_smt_typeof_matches_translation_apply_generic_of_field_wf
      (Term._at_sets_deq_diff x1 x2) x ihF ihX hGeneric hTranslate (by rfl) hArgWF hNonNone
  case _at_quantifiers_skolemize x1 x2 =>
    have hNonSel :
        ∀ s d i j, __eo_to_smt (Term._at_quantifiers_skolemize x1 x2) ≠ SmtTerm.DtSel s d i j := by
      intro s d i j h
      exact eo_to_smt_quant_skolemize_top_ne_dt_sel x1 x2 s d i j h
    have hNonTester :
        ∀ s d i, __eo_to_smt (Term._at_quantifiers_skolemize x1 x2) ≠ SmtTerm.DtTester s d i := by
      intro s d i h
      exact eo_to_smt_quant_skolemize_top_ne_dt_tester x1 x2 s d i h
    have hGeneric :
        generic_apply_type (__eo_to_smt (Term._at_quantifiers_skolemize x1 x2)) (__eo_to_smt x) := by
      exact generic_apply_type_of_non_special_head _ _ hNonSel hNonTester
    have hArgWF :
        ∀ A B,
          (__smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize x1 x2)) = SmtType.FunType A B ∨
            __smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize x1 x2)) = SmtType.DtcAppType A B) ->
          smtx_type_field_wf_rec A native_reflist_nil := by
      intro A B hHead
      cases x1 <;> try
        (exfalso
         rcases hHead with hHead | hHead
         · change __smtx_typeof SmtTerm.None = SmtType.FunType A B at hHead
           simp [smtx_typeof_none] at hHead
         · change __smtx_typeof SmtTerm.None = SmtType.DtcAppType A B at hHead
           simp [smtx_typeof_none] at hHead)
      case Apply qf body =>
        cases qf <;> try
          (exfalso
           rcases hHead with hHead | hHead
           · change __smtx_typeof SmtTerm.None = SmtType.FunType A B at hHead
             simp [smtx_typeof_none] at hHead
           · change __smtx_typeof SmtTerm.None = SmtType.DtcAppType A B at hHead
             simp [smtx_typeof_none] at hHead)
        case Apply qff xs =>
          cases qff <;> try
            (exfalso
             rcases hHead with hHead | hHead
             · change __smtx_typeof SmtTerm.None = SmtType.FunType A B at hHead
               simp [smtx_typeof_none] at hHead
             · change __smtx_typeof SmtTerm.None = SmtType.DtcAppType A B at hHead
               simp [smtx_typeof_none] at hHead)
          case UOp op =>
            cases op <;> try
              (exfalso
               rcases hHead with hHead | hHead
               · change __smtx_typeof SmtTerm.None = SmtType.FunType A B at hHead
                 simp [smtx_typeof_none] at hHead
               · change __smtx_typeof SmtTerm.None = SmtType.DtcAppType A B at hHead
                 simp [smtx_typeof_none] at hHead)
            case «forall» =>
              change
                  __smtx_typeof
                      (native_ite (native_teq (__eo_is_z x2) (Term.Boolean true))
                        (native_ite (native_teq (__eo_is_neg x2) (Term.Boolean false))
                          (__eo_to_smt_quantifiers_skolemize
                            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                            (__eo_to_smt_nat x2))
                          SmtTerm.None)
                        SmtTerm.None) =
                      SmtType.FunType A B ∨
                    __smtx_typeof
                      (native_ite (native_teq (__eo_is_z x2) (Term.Boolean true))
                        (native_ite (native_teq (__eo_is_neg x2) (Term.Boolean false))
                          (__eo_to_smt_quantifiers_skolemize
                            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                            (__eo_to_smt_nat x2))
                          SmtTerm.None)
                        SmtTerm.None) =
                      SmtType.DtcAppType A B at hHead
              cases hIdxZ : native_teq (__eo_is_z x2) (Term.Boolean true)
              · exfalso
                rcases hHead with hHead | hHead
                · rw [hIdxZ] at hHead
                  simp [native_ite, smtx_typeof_none] at hHead
                · rw [hIdxZ] at hHead
                  simp [native_ite, smtx_typeof_none] at hHead
              · cases hIdxNeg : native_teq (__eo_is_neg x2) (Term.Boolean false)
                · exfalso
                  rcases hHead with hHead | hHead
                  · rw [hIdxZ, hIdxNeg] at hHead
                    simp [native_ite, smtx_typeof_none] at hHead
                  · rw [hIdxZ, hIdxNeg] at hHead
                    simp [native_ite, smtx_typeof_none] at hHead
                · have hSkHead :
                      __smtx_typeof
                          (__eo_to_smt_quantifiers_skolemize
                            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                            (__eo_to_smt_nat x2)) =
                          SmtType.FunType A B ∨
                        __smtx_typeof
                          (__eo_to_smt_quantifiers_skolemize
                            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                            (__eo_to_smt_nat x2)) =
                          SmtType.DtcAppType A B := by
                    simpa [native_ite, hIdxZ, hIdxNeg] using hHead
                  exact eo_to_smt_quantifiers_skolemize_fun_like_arg_field_wf
                    (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt body)))
                    (__eo_to_smt_nat x2) hSkHead
    exact eo_to_smt_typeof_matches_translation_apply_generic_of_field_wf
      (Term._at_quantifiers_skolemize x1 x2) x ihF ihX hGeneric (by rfl) (by rfl) hArgWF hNonNone
  all_goals
    refine eo_to_smt_typeof_matches_translation_apply_constructor_fallback_obligation
      _ x ?_ hNonNone
    first
    | change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_none_eq (__eo_to_smt x)
    | change
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt_seq_empty (__eo_to_smt_type _)) (__eo_to_smt x)) =
          SmtType.None
      exact typeof_apply_eo_to_smt_seq_empty_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.Boolean _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_boolean_head_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.Numeral _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_numeral_head_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.Rational _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_rational_head_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.String _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_string_head_eq_none _ (__eo_to_smt x)
    | change __smtx_typeof (SmtTerm.Apply (SmtTerm.Binary _ _) (__eo_to_smt x)) = SmtType.None
      exact typeof_apply_binary_head_eq_none _ _ (__eo_to_smt x)

end TranslationProofs
