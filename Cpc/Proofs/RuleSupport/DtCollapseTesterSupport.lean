module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.CongSupport
import all Cpc.Proofs.RuleSupport.CongSupport
public import Cpc.Proofs.RuleSupport.DatatypeSupport
import all Cpc.Proofs.RuleSupport.DatatypeSupport
public import Cpc.Proofs.Translation.Apply
import all Cpc.Proofs.Translation.Apply

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private inductive DtConsSpineRoot :
    Term -> native_String -> Datatype -> native_Nat -> Prop where
  | root (s : native_String) (d : Datatype) (i : native_Nat) :
      DtConsSpineRoot (Term.DtCons s d i) s d i
  | app {t : Term} {s : native_String} {d : Datatype} {i : native_Nat}
      (x : Term) :
      DtConsSpineRoot t s d i ->
      DtConsSpineRoot (Term.Apply t x) s d i

private inductive CtorSpineRoot : Term -> Term -> Prop where
  | tuple :
      CtorSpineRoot (Term.UOp UserOp.tuple) (Term.UOp UserOp.tuple)
  | tupleUnit :
      CtorSpineRoot (Term.UOp UserOp.tuple_unit) (Term.UOp UserOp.tuple_unit)
  | dtCons (s : native_String) (d : Datatype) (i : native_Nat) :
      CtorSpineRoot (Term.DtCons s d i) (Term.DtCons s d i)
  | app {t root : Term} (x : Term) :
      CtorSpineRoot t root ->
      CtorSpineRoot (Term.Apply t x) root

private theorem dtConsSpineRoot_of_ctor_dtCons_aux
    {t root : Term} :
    CtorSpineRoot t root ->
      ∀ {s : native_String} {d : Datatype} {i : native_Nat},
        root = Term.DtCons s d i -> DtConsSpineRoot t s d i := by
  intro h
  induction h with
  | tuple =>
      intro s d i hEq
      cases hEq
  | tupleUnit =>
      intro s d i hEq
      cases hEq
  | dtCons s' d' i' =>
      intro s d i hEq
      cases hEq
      exact DtConsSpineRoot.root s' d' i'
  | app x h ih =>
      intro s d i hEq
      exact DtConsSpineRoot.app x (ih hEq)

private theorem dtConsSpineRoot_of_ctor_dtCons
    {t : Term} {s : native_String} {d : Datatype} {i : native_Nat} :
    CtorSpineRoot t (Term.DtCons s d i) ->
      DtConsSpineRoot t s d i := by
  intro h
  exact dtConsSpineRoot_of_ctor_dtCons_aux h rfl

private theorem ctorSpineRoot_root_cases
    {t root : Term}
    (hSp : CtorSpineRoot t root) :
    root = Term.UOp UserOp.tuple ∨
      root = Term.UOp UserOp.tuple_unit ∨
        ∃ s d i, root = Term.DtCons s d i := by
  induction hSp with
  | tuple =>
      exact Or.inl rfl
  | tupleUnit =>
      exact Or.inr (Or.inl rfl)
  | dtCons s d i =>
      exact Or.inr (Or.inr ⟨s, d, i, rfl⟩)
  | app x hSp ih =>
      exact ih

private theorem ctorSpineRoot_apply_generic_of_not_tuple_one_arg
    {f root : Term}
    (hSp : CtorSpineRoot f root) (a : Term)
    (hNotTupleOne : ∀ x, f ≠ Term.Apply (Term.UOp UserOp.tuple) x) :
    __eo_to_smt (Term.Apply f a) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a) := by
  cases hSp with
  | tuple =>
      rfl
  | tupleUnit =>
      rfl
  | dtCons s d i =>
      rfl
  | app x hPrev =>
      cases hPrev with
      | tuple =>
          exact False.elim (hNotTupleOne x rfl)
      | tupleUnit =>
          rfl
      | dtCons s d i =>
          rfl
      | app y hPrev' =>
          cases hPrev' <;> rfl

private theorem ctorSpineRoot_to_smt_ne_dt_sel
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    ∀ s d i j, __eo_to_smt f ≠ SmtTerm.DtSel s d i j := by
  induction hSp with
  | tuple =>
      intro s d i j h
      cases h
  | tupleUnit =>
      intro s d i j h
      rw [TranslationProofs.eo_to_smt_term_tuple_unit] at h
      cases h
  | dtCons s d i =>
      intro s' d' i' j h
      rw [TranslationProofs.eo_to_smt_term_dt_cons] at h
      by_cases hRes : TranslationProofs.__eo_reserved_datatype_name s <;>
        simp [native_ite, hRes] at h
  | app x hPrev ih =>
      intro s d i j h
      cases hPrev with
      | tuple =>
          change
            SmtTerm.Apply SmtTerm.None (__eo_to_smt x) =
              SmtTerm.DtSel s d i j at h
          cases h
      | tupleUnit =>
          have hNotOne :
              ∀ z, Term.UOp UserOp.tuple_unit ≠
                Term.Apply (Term.UOp UserOp.tuple) z := by
            intro z hz
            cases hz
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              CtorSpineRoot.tupleUnit x hNotOne
          rw [hTo] at h
          cases h
      | dtCons s0 d0 i0 =>
          have hNotOne :
              ∀ z, Term.DtCons s0 d0 i0 ≠
                Term.Apply (Term.UOp UserOp.tuple) z := by
            intro z hz
            cases hz
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              (CtorSpineRoot.dtCons s0 d0 i0) x hNotOne
          rw [hTo] at h
          cases h
      | app y hPrev' =>
          cases hPrev' with
          | tuple =>
              exact
                TranslationProofs.eo_to_smt_tuple_ne_dt_sel x y s d i j h
          | tupleUnit =>
              have hNotOne :
                  ∀ z, Term.Apply (Term.UOp UserOp.tuple_unit) y ≠
                    Term.Apply (Term.UOp UserOp.tuple) z := by
                intro z hz
                cases hz
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  (CtorSpineRoot.app y CtorSpineRoot.tupleUnit) x hNotOne
              rw [hTo] at h
              cases h
          | dtCons s0 d0 i0 =>
              have hNotOne :
                  ∀ z, Term.Apply (Term.DtCons s0 d0 i0) y ≠
                    Term.Apply (Term.UOp UserOp.tuple) z := by
                intro z hz
                cases hz
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  (CtorSpineRoot.app y (CtorSpineRoot.dtCons s0 d0 i0))
                  x hNotOne
              rw [hTo] at h
              cases h
          | app z hPrev'' =>
              have hCurSp := CtorSpineRoot.app y (CtorSpineRoot.app z hPrev'')
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  hCurSp x (by intro w hw; cases hw)
              rw [hTo] at h
              cases h

private theorem ctorSpineRoot_to_smt_ne_dt_tester
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    ∀ s d i, __eo_to_smt f ≠ SmtTerm.DtTester s d i := by
  induction hSp with
  | tuple =>
      intro s d i h
      cases h
  | tupleUnit =>
      intro s d i h
      rw [TranslationProofs.eo_to_smt_term_tuple_unit] at h
      cases h
  | dtCons s d i =>
      intro s' d' i' h
      rw [TranslationProofs.eo_to_smt_term_dt_cons] at h
      by_cases hRes : TranslationProofs.__eo_reserved_datatype_name s <;>
        simp [native_ite, hRes] at h
  | app x hPrev ih =>
      intro s d i h
      cases hPrev with
      | tuple =>
          change
            SmtTerm.Apply SmtTerm.None (__eo_to_smt x) =
              SmtTerm.DtTester s d i at h
          cases h
      | tupleUnit =>
          have hNotOne :
              ∀ z, Term.UOp UserOp.tuple_unit ≠
                Term.Apply (Term.UOp UserOp.tuple) z := by
            intro z hz
            cases hz
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              CtorSpineRoot.tupleUnit x hNotOne
          rw [hTo] at h
          cases h
      | dtCons s0 d0 i0 =>
          have hNotOne :
              ∀ z, Term.DtCons s0 d0 i0 ≠
                Term.Apply (Term.UOp UserOp.tuple) z := by
            intro z hz
            cases hz
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              (CtorSpineRoot.dtCons s0 d0 i0) x hNotOne
          rw [hTo] at h
          cases h
      | app y hPrev' =>
          cases hPrev' with
          | tuple =>
              exact
                TranslationProofs.eo_to_smt_tuple_ne_dt_tester x y s d i h
          | tupleUnit =>
              have hNotOne :
                  ∀ z, Term.Apply (Term.UOp UserOp.tuple_unit) y ≠
                    Term.Apply (Term.UOp UserOp.tuple) z := by
                intro z hz
                cases hz
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  (CtorSpineRoot.app y CtorSpineRoot.tupleUnit) x hNotOne
              rw [hTo] at h
              cases h
          | dtCons s0 d0 i0 =>
              have hNotOne :
                  ∀ z, Term.Apply (Term.DtCons s0 d0 i0) y ≠
                    Term.Apply (Term.UOp UserOp.tuple) z := by
                intro z hz
                cases hz
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  (CtorSpineRoot.app y (CtorSpineRoot.dtCons s0 d0 i0))
                  x hNotOne
              rw [hTo] at h
              cases h
          | app z hPrev'' =>
              have hCurSp := CtorSpineRoot.app y (CtorSpineRoot.app z hPrev'')
              have hTo :=
                ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                  hCurSp x (by intro w hw; cases hw)
              rw [hTo] at h
              cases h

private theorem smtx_typeof_apply_tuple_prepend_eq_none
    (head tail arg : SmtTerm) (headTy : SmtType) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_tuple_prepend head headTy tail) arg) =
      SmtType.None := by
  have hGen :
      generic_apply_type (__eo_to_smt_tuple_prepend head headTy tail) arg :=
    generic_apply_type_of_non_datatype_head
      (TranslationProofs.eo_to_smt_tuple_prepend_ne_dt_sel head headTy tail)
      (TranslationProofs.eo_to_smt_tuple_prepend_ne_dt_tester head headTy tail)
  by_cases hNN :
      __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
        SmtType.None
  · rcases CongSupport.tuple_prepend_tail_type_of_non_none
      head headTy tail hNN with ⟨c, hTailTy⟩
    have hTy :=
      TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
        tail head headTy c hTailTy hNN
    unfold generic_apply_type at hGen
    rw [hGen, hTy]
    simp [__smtx_typeof_apply]
  · have hNone :
        __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
          SmtType.None := by
      cases hTy : __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) <;>
        simp [hTy] at hNN ⊢
    unfold generic_apply_type at hGen
    rw [hGen, hNone]
    simp [__smtx_typeof_apply]

private theorem ctorSpineRoot_tuple_apply_type_none_or_one_arg_aux
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    ∀ {a : Term}, root = Term.UOp UserOp.tuple ->
      __smtx_typeof (__eo_to_smt (Term.Apply f a)) = SmtType.None ∨
        ∃ x, f = Term.Apply (Term.UOp UserOp.tuple) x := by
  induction hSp with
  | tuple =>
      intro a _hRoot
      left
      change
        __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
      exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt a)
  | tupleUnit =>
      intro a hRoot
      cases hRoot
  | dtCons s d i =>
      intro a hRoot
      cases hRoot
  | app x hSp ih =>
      intro a hRoot
      cases hSp with
      | tuple =>
          right
          exact ⟨x, rfl⟩
      | tupleUnit =>
          cases hRoot
      | dtCons s d i =>
          cases hRoot
      | app x' hSp' =>
          left
          have hPrev := ih (a := x) hRoot
          rcases hPrev with hNone | hOne
          · have hCurSp := CtorSpineRoot.app x (CtorSpineRoot.app x' hSp')
            have hTo :=
              ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                hCurSp a (by intro z hz; cases hz)
            have hGen :=
              generic_apply_type_of_non_datatype_head
                (x := __eo_to_smt a)
                (ctorSpineRoot_to_smt_ne_dt_sel hCurSp)
                (ctorSpineRoot_to_smt_ne_dt_tester hCurSp)
            rw [hTo]
            unfold generic_apply_type at hGen
            rw [hGen, hNone]
            simp [__smtx_typeof_apply]
          · rcases hOne with ⟨z, hz⟩
            cases hz
            have hCurSp :=
              CtorSpineRoot.app x (CtorSpineRoot.app x' CtorSpineRoot.tuple)
            have hTo :=
              ctorSpineRoot_apply_generic_of_not_tuple_one_arg
                hCurSp a (by intro w hw; cases hw)
            rw [hTo]
            change
              __smtx_typeof
                  (SmtTerm.Apply
                    (__eo_to_smt_tuple_prepend (__eo_to_smt x')
                      (__smtx_typeof (__eo_to_smt x')) (__eo_to_smt x))
                    (__eo_to_smt a)) = SmtType.None
            exact smtx_typeof_apply_tuple_prepend_eq_none
              (__eo_to_smt x') (__eo_to_smt x) (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt x'))

private theorem ctorSpineRoot_tuple_apply_type_none_or_one_arg
    {f a : Term}
    (hSp : CtorSpineRoot f (Term.UOp UserOp.tuple)) :
    __smtx_typeof (__eo_to_smt (Term.Apply f a)) = SmtType.None ∨
      ∃ x, f = Term.Apply (Term.UOp UserOp.tuple) x :=
  ctorSpineRoot_tuple_apply_type_none_or_one_arg_aux hSp rfl

private theorem ctorSpineRoot_tupleUnit_apply_type_none_aux
    {f root : Term}
    (hSp : CtorSpineRoot f root) :
    ∀ {a : Term}, root = Term.UOp UserOp.tuple_unit ->
      __smtx_typeof (__eo_to_smt (Term.Apply f a)) = SmtType.None := by
  induction hSp with
  | tuple =>
      intro a hRoot
      cases hRoot
  | tupleUnit =>
      intro a _hRoot
      change
        __smtx_typeof
            (SmtTerm.Apply
              (SmtTerm.DtCons (native_string_lit "@Tuple")
                (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
                native_nat_zero)
              (__eo_to_smt a)) =
          SmtType.None
      have hGeneric :
          generic_apply_type
            (SmtTerm.DtCons (native_string_lit "@Tuple")
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
              native_nat_zero)
            (__eo_to_smt a) :=
        generic_apply_type_of_non_datatype_head
          (by intro s d i j h; cases h)
          (by intro s d i h; cases h)
      unfold generic_apply_type at hGeneric
      rw [hGeneric, TranslationProofs.smtx_typeof_tuple_unit_translation]
      rfl
  | dtCons s d i =>
      intro a hRoot
      cases hRoot
  | app x hSp ih =>
      intro a hRoot
      cases hSp with
      | tuple =>
          cases hRoot
      | tupleUnit =>
          have hPrev := ih (a := x) hRoot
          have hCurSp := CtorSpineRoot.app x CtorSpineRoot.tupleUnit
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              hCurSp a (by intro z hz; cases hz)
          have hGen :=
            generic_apply_type_of_non_datatype_head
              (x := __eo_to_smt a)
              (ctorSpineRoot_to_smt_ne_dt_sel hCurSp)
              (ctorSpineRoot_to_smt_ne_dt_tester hCurSp)
          rw [hTo]
          unfold generic_apply_type at hGen
          rw [hGen, hPrev]
          simp [__smtx_typeof_apply]
      | dtCons s d i =>
          cases hRoot
      | app x' hSp' =>
          have hPrev := ih (a := x) hRoot
          have hCurSp := CtorSpineRoot.app x (CtorSpineRoot.app x' hSp')
          have hTo :=
            ctorSpineRoot_apply_generic_of_not_tuple_one_arg
              hCurSp a (by intro z hz; cases hz)
          have hGen :=
            generic_apply_type_of_non_datatype_head
              (x := __eo_to_smt a)
              (ctorSpineRoot_to_smt_ne_dt_sel hCurSp)
              (ctorSpineRoot_to_smt_ne_dt_tester hCurSp)
          rw [hTo]
          unfold generic_apply_type at hGen
          rw [hGen, hPrev]
          simp [__smtx_typeof_apply]

private theorem ctorSpineRoot_tupleUnit_apply_type_none
    {f a : Term}
    (hSp : CtorSpineRoot f (Term.UOp UserOp.tuple_unit)) :
    __smtx_typeof (__eo_to_smt (Term.Apply f a)) = SmtType.None :=
  ctorSpineRoot_tupleUnit_apply_type_none_aux hSp rfl

private theorem ctorSpineRoot_tuple_typeof_tuple
    {t : Term}
    (hSp : CtorSpineRoot t (Term.UOp UserOp.tuple))
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    ∃ A c,
      __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null) := by
  cases hSp with
  | tuple =>
      exfalso
      apply hNN
      native_decide
  | app a hHead =>
      rcases ctorSpineRoot_tuple_apply_type_none_or_one_arg hHead with
        hNone | hOne
      · exfalso
        exact hNN hNone
      · rcases hOne with ⟨head, hHeadEq⟩
        subst hHeadEq
        let headTy := __smtx_typeof (__eo_to_smt head)
        have hPrependNN :
            __smtx_typeof
                (__eo_to_smt_tuple_prepend (__eo_to_smt head) headTy
                  (__eo_to_smt a)) ≠ SmtType.None := by
          change
            __smtx_typeof
                (__eo_to_smt_tuple_prepend (__eo_to_smt head) headTy
                  (__eo_to_smt a)) ≠ SmtType.None at hNN
          exact hNN
        rcases CongSupport.tuple_prepend_tail_type_of_non_none
            (__eo_to_smt head) headTy (__eo_to_smt a) hPrependNN with
          ⟨c, hTailTy⟩
        have hTy :=
          TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
            (__eo_to_smt a) (__eo_to_smt head) headTy c hTailTy
            hPrependNN
        exact ⟨headTy, c, by simpa [headTy] using hTy⟩

private theorem ctorSpineRoot_tupleUnit_typeof_unit
    {t : Term}
    (hSp : CtorSpineRoot t (Term.UOp UserOp.tuple_unit))
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt t) =
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) := by
  cases hSp with
  | tupleUnit =>
      exact TranslationProofs.smtx_typeof_tuple_unit_translation
  | app a hHead =>
      exfalso
      exact hNN (ctorSpineRoot_tupleUnit_apply_type_none hHead)

private theorem eo_to_smt_dtCons_eq
    (s : native_String) (d : Datatype) (i : native_Nat) :
    __eo_to_smt (Term.DtCons s d i) =
      native_ite (native_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) := by
  rfl

private theorem dtConsSpineRoot_apply_generic
    {t : Term} {s : native_String} {d : Datatype} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) (x : Term) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  induction hSp generalizing x with
  | root s d i =>
      rfl
  | app x' hSp ih =>
      cases hSp with
      | root s d i =>
          rfl
      | app x'' hSp' =>
          cases hSp' with
          | root s d i =>
              rfl
          | app x''' hSp'' =>
              rfl

private theorem dtConsSpineRoot_to_smt_ne_dt_sel
    {t : Term} {s : native_String} {d : Datatype} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) :
    ∀ s' d' i' j, __eo_to_smt t ≠ SmtTerm.DtSel s' d' i' j := by
  induction hSp with
  | root s d i =>
      intro s' d' i' j
      rw [eo_to_smt_dtCons_eq]
      by_cases hRes : native_reserved_datatype_name s <;>
        simp [native_ite, hRes]
  | app x hSp ih =>
      intro s' d' i' j hEq
      rw [dtConsSpineRoot_apply_generic hSp x] at hEq
      cases hEq

private theorem dtConsSpineRoot_to_smt_ne_dt_tester
    {t : Term} {s : native_String} {d : Datatype} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i) :
    ∀ s' d' i', __eo_to_smt t ≠ SmtTerm.DtTester s' d' i' := by
  induction hSp with
  | root s d i =>
      intro s' d' i'
      rw [eo_to_smt_dtCons_eq]
      by_cases hRes : native_reserved_datatype_name s <;>
        simp [native_ite, hRes]
  | app x hSp ih =>
      intro s' d' i' hEq
      rw [dtConsSpineRoot_apply_generic hSp x] at hEq
      cases hEq

private theorem smtx_model_eval_apply_eq_apply_of_not_dt_ops
    (M : SmtModel) (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x) := by
  cases f <;> simp [__smtx_model_eval]
  case DtSel s d i j => exact False.elim (hSel s d i j rfl)
  case DtTester s d i => exact False.elim (hTester s d i rfl)

private theorem smtx_model_eval_apply_of_dt_chain
    (M : SmtModel) (v x : SmtValue)
    (hHead : ∃ s d i, __vsm_apply_head v = SmtValue.DtCons s d i)
    (hx : x ≠ SmtValue.NotValue) :
    __smtx_model_eval_apply M v x = SmtValue.Apply v x := by
  cases x <;> simp [__smtx_model_eval_apply] at hx ⊢
  all_goals
    cases v <;> simp [__vsm_apply_head] at hHead ⊢

private theorem smt_model_eval_not_notvalue_of_non_none
    (M : SmtModel) (hM : model_total_typed M) (x : SmtTerm)
    (hNN : __smtx_typeof x ≠ SmtType.None) :
    __smtx_model_eval M x ≠ SmtValue.NotValue := by
  have hPres :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM x hNN
  intro hNot
  apply hNN
  rw [← hPres, hNot]
  simp [__smtx_typeof_value]

private theorem dtConsSpineRoot_eval_head
    (M : SmtModel) (hM : model_total_typed M)
    {t : Term} {s : native_String} {d : Datatype} {i : native_Nat}
    (hSp : DtConsSpineRoot t s d i)
    (hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
    __vsm_apply_head (__smtx_model_eval M (__eo_to_smt t)) =
      SmtValue.DtCons s (__eo_to_smt_datatype d) i := by
  induction hSp with
  | root s d i =>
      rw [eo_to_smt_dtCons_eq] at hNN
      by_cases hRes : native_reserved_datatype_name s
      · exfalso
        apply hNN
        simp [native_ite, hRes]
      · rw [eo_to_smt_dtCons_eq]
        simp [native_ite, hRes, __smtx_model_eval, __vsm_apply_head]
  | app x hSp ih =>
      rename_i t0 s0 d0 i0
      have hTo := dtConsSpineRoot_apply_generic hSp x
      have hGen : generic_apply_type (__eo_to_smt t0) (__eo_to_smt x) :=
        generic_apply_type_of_non_datatype_head
          (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
          (dtConsSpineRoot_to_smt_ne_dt_tester hSp)
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof (__eo_to_smt t0))
              (__smtx_typeof (__eo_to_smt x)) ≠ SmtType.None := by
        have hNN' := hNN
        rw [hTo] at hNN'
        unfold generic_apply_type at hGen
        rw [hGen] at hNN'
        exact hNN'
      rcases typeof_apply_non_none_cases hApplyNN with
        ⟨A, B, hHead, hX, hANN, _hBNN⟩
      have hHeadNN : __smtx_typeof (__eo_to_smt t0) ≠ SmtType.None := by
        rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
      have hEvalHead := ih hHeadNN
      have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [hX]
        exact hANN
      have hxNot :=
        smt_model_eval_not_notvalue_of_non_none M hM (__eo_to_smt x) hXNN
      rw [hTo]
      rw [smtx_model_eval_apply_eq_apply_of_not_dt_ops M
        _ _
        (dtConsSpineRoot_to_smt_ne_dt_sel hSp)
        (dtConsSpineRoot_to_smt_ne_dt_tester hSp)]
      rw [smtx_model_eval_apply_of_dt_chain M
        _ _
        ⟨s0, __eo_to_smt_datatype d0, i0, hEvalHead⟩ hxNot]
      simp [__vsm_apply_head, hEvalHead]

private theorem smt_datatype_dt_wf_rec_of_typeof
    (x : SmtTerm) (s : native_String) (d : SmtDatatype)
    (hxTy : __smtx_typeof x = SmtType.Datatype s d) :
    __smtx_dt_wf_rec (__smtx_dt_substitute s d d) d = true :=
  Smtm.datatype_wf_rec_of_type_wf
    (Smtm.smt_datatype_wf_of_non_none_type x s d hxTy)

private theorem dt_eq_cons_dtcons_true_spine
    (s : native_String) (d : Datatype) (i : native_Nat) :
  ∀ t : Term,
    __dt_eq_cons (Term.DtCons s d i) t = Term.Boolean true ->
    DtConsSpineRoot t s d i
  | Term.Apply f a, h => by
      exact DtConsSpineRoot.app a
        (dt_eq_cons_dtcons_true_spine s d i f (by
          simpa [__dt_eq_cons] using h))
  | Term.DtCons s' d' i', h => by
      by_cases hEq : Term.DtCons s d i = Term.DtCons s' d' i'
      · cases hEq
        exact DtConsSpineRoot.root s d i
      · exfalso
        have hRootNe : ¬(s' = s ∧ d' = d ∧ i' = i) := by
          intro hParts
          apply hEq
          rcases hParts with ⟨rfl, rfl, rfl⟩
          rfl
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_is_ok, native_ite, native_teq, native_and, hRootNe] at h
        by_cases hLeftStuck :
            __eo_dt_selectors (Term.DtCons s d i) = Term.Stuck
        · simp [hLeftStuck, SmtEval.native_not] at h
        · by_cases hRightStuck :
              __eo_dt_selectors (Term.DtCons s' d' i') = Term.Stuck
          · simp [hLeftStuck, hRightStuck, SmtEval.native_not] at h
          · simp [hLeftStuck, hRightStuck, SmtEval.native_not] at h
  | Term.Stuck, h => by
      simp [__dt_eq_cons] at h
  | Term.UOp op, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
      all_goals
        exfalso
        split at h <;> cases h
  | Term.UOp1 op a, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.UOp2 op a b, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.UOp3 op a b c, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List_nil, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List_cons, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.Bool, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.Boolean b, h => by
      cases b <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.Numeral n, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.Rational q, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.String str, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.Binary w n, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.Type, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.FunType, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.Var name T, h => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.DatatypeType name D, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.DatatypeTypeRef name, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.DtcAppType a b, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.DtSel name D i j, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.USort name, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.UConst name T, h => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h

private theorem dt_eq_cons_dtcons_bool_or_stuck
    (s : native_String) (d : Datatype) (i : native_Nat) :
  ∀ t : Term,
    (∃ b : Bool, __dt_eq_cons (Term.DtCons s d i) t = Term.Boolean b) ∨
      __dt_eq_cons (Term.DtCons s d i) t = Term.Stuck
  | Term.Apply f a => by
      simpa [__dt_eq_cons] using
        dt_eq_cons_dtcons_bool_or_stuck s d i f
  | Term.Stuck => by
      simp [__dt_eq_cons]
  | Term.UOp op => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not]
      all_goals
        by_cases hSel :
            __eo_datatype_cons_selectors_rec s d i d i 0 = Term.Stuck <;>
          simp [hSel]
  | Term.UOp1 op a => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not]
  | Term.UOp2 op a b => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not]
  | Term.UOp3 op a b c => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not]
  | Term.__eo_List => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.__eo_List_nil => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.__eo_List_cons => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.Bool => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.Boolean b => by
      cases b <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not]
  | Term.Numeral n => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.Rational q => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.String str => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.Binary w n => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.Type => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.FunType => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.Var name T => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not]
  | Term.DatatypeType name D => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.DatatypeTypeRef name => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.DtcAppType a b => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.DtCons s' d' i' => by
      by_cases hEq : Term.DtCons s d i = Term.DtCons s' d' i'
      · cases hEq
        by_cases hSel : __eo_dt_selectors (Term.DtCons s d i) = Term.Stuck
        · simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_is_eq,
            __eo_is_ok, native_ite, native_teq, native_and, hSel, SmtEval.native_not]
        · simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
            __eo_is_ok, native_ite, native_teq, native_and, hSel, SmtEval.native_not]
      · have hRootNe : ¬(s' = s ∧ d' = d ∧ i' = i) := by
          intro hParts
          apply hEq
          rcases hParts with ⟨rfl, rfl, rfl⟩
          rfl
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_is_ok, native_ite, native_teq, native_and, hRootNe, SmtEval.native_not]
        by_cases hLeftStuck :
            __eo_dt_selectors (Term.DtCons s d i) = Term.Stuck
        · simp [hLeftStuck]
        · by_cases hRightStuck :
              __eo_dt_selectors (Term.DtCons s' d' i') = Term.Stuck
          · simp [hLeftStuck, hRightStuck]
          · simp [hLeftStuck, hRightStuck]
  | Term.DtSel name D i j => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.USort name => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not]
  | Term.UConst name T => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not]

private theorem dt_eq_cons_dtcons_false_ctor_root
    (s : native_String) (d : Datatype) (i : native_Nat) :
  ∀ t : Term,
    __dt_eq_cons (Term.DtCons s d i) t = Term.Boolean false ->
    ∃ root, CtorSpineRoot t root ∧ root ≠ Term.DtCons s d i
  | Term.Apply f a, h => by
      rcases dt_eq_cons_dtcons_false_ctor_root s d i f
          (by simpa [__dt_eq_cons] using h) with
        ⟨root, hRoot, hNe⟩
      exact ⟨root, CtorSpineRoot.app a hRoot, hNe⟩
  | Term.DtCons s' d' i', h => by
      by_cases hEq : Term.DtCons s d i = Term.DtCons s' d' i'
      · cases hEq
        exfalso
        by_cases hSel : __eo_dt_selectors (Term.DtCons s d i) = Term.Stuck
        · simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_is_eq,
            __eo_is_ok, native_ite, native_teq, native_and, hSel,
            SmtEval.native_not] at h
        · have hEqBool :
              __eo_eq (Term.DtCons s d i) (Term.DtCons s d i) =
                Term.Boolean true := by
            simp [__eo_eq, native_teq]
          simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_is_eq,
            __eo_is_ok, native_ite, native_teq, native_and, hSel,
            hEqBool, SmtEval.native_not] at h
      · exact ⟨Term.DtCons s' d' i', CtorSpineRoot.dtCons s' d' i',
          by intro hRoot; exact hEq hRoot.symm⟩
  | Term.UOp op, h => by
      cases op
      all_goals
        first
        | exact ⟨Term.UOp UserOp.tuple_unit, CtorSpineRoot.tupleUnit,
            by intro hEq; cases hEq⟩
        | exact ⟨Term.UOp UserOp.tuple, CtorSpineRoot.tuple,
            by intro hEq; cases hEq⟩
        | (exfalso
           simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
             __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
             native_teq, native_not, native_and, SmtEval.native_not] at h
           try split at h <;> cases h)
  | Term.Stuck, h => by
      simp [__dt_eq_cons] at h
  | Term.UOp1 op a, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.UOp2 op a b, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.UOp3 op a b c, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List_nil, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List_cons, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.Bool, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.Boolean b, h => by
      cases b <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.Numeral n, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.Rational q, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.String str, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.Binary w n, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.Type, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.FunType, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.Var name T, h => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h
  | Term.DatatypeType name D, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.DatatypeTypeRef name, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.DtcAppType a b, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.DtSel name D i j, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.USort name, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
        native_not, native_and, SmtEval.native_not] at h
  | Term.UConst name T, h => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite, native_teq,
          native_not, native_and, SmtEval.native_not] at h

private theorem dt_eq_cons_tupleUnit_bool_or_stuck :
  ∀ t : Term,
    (∃ b : Bool,
      __dt_eq_cons (Term.UOp UserOp.tuple_unit) t = Term.Boolean b) ∨
      __dt_eq_cons (Term.UOp UserOp.tuple_unit) t = Term.Stuck
  | Term.Apply f a => by
      simpa [__dt_eq_cons] using dt_eq_cons_tupleUnit_bool_or_stuck f
  | Term.Stuck => by
      simp [__dt_eq_cons]
  | Term.UOp op => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not]
  | Term.DtCons s d i => by
      by_cases hSel : __eo_dt_selectors (Term.DtCons s d i) = Term.Stuck
      · simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_is_ok, native_ite, native_teq, native_not, native_and,
          hSel, SmtEval.native_not]
      · simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_is_ok, native_ite, native_teq, native_not, native_and,
          hSel, SmtEval.native_not]
  | Term.UOp1 op a => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not]
  | Term.UOp2 op a b => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not]
  | Term.UOp3 op a b c => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not]
  | Term.__eo_List => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.__eo_List_nil => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.__eo_List_cons => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.Bool => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.Boolean b => by
      cases b <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not]
  | Term.Numeral n => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.Rational q => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.String str => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.Binary w n => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.Type => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.FunType => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.Var name T => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not]
  | Term.DatatypeType name D => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.DatatypeTypeRef name => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.DtcAppType a b => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.DtSel name D i j => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.USort name => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not]
  | Term.UConst name T => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not]

private theorem dt_eq_cons_tupleUnit_false_ctor_root :
  ∀ t : Term,
    __dt_eq_cons (Term.UOp UserOp.tuple_unit) t = Term.Boolean false ->
    ∃ root, CtorSpineRoot t root ∧ root ≠ Term.UOp UserOp.tuple_unit
  | Term.Apply f a, h => by
      rcases dt_eq_cons_tupleUnit_false_ctor_root f
          (by simpa [__dt_eq_cons] using h) with
        ⟨root, hRoot, hNe⟩
      exact ⟨root, CtorSpineRoot.app a hRoot, hNe⟩
  | Term.UOp op, h => by
      cases op
      all_goals
        first
        | exact ⟨Term.UOp UserOp.tuple, CtorSpineRoot.tuple,
            by intro hEq; cases hEq⟩
        | (exfalso
           simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq,
             __eo_is_eq, __eo_dt_selectors, __eo_dt_selectors_main,
             __eo_is_ok, native_ite, native_teq, native_not, native_and,
             SmtEval.native_not] at h)
  | Term.DtCons s d i, h => by
      exact ⟨Term.DtCons s d i, CtorSpineRoot.dtCons s d i,
        by intro hEq; cases hEq⟩
  | Term.Stuck, h => by
      simp [__dt_eq_cons] at h
  | Term.UOp1 op a, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.UOp2 op a b, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.UOp3 op a b c, h => by
      cases op <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List_nil, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.__eo_List_cons, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.Bool, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.Boolean b, h => by
      cases b <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.Numeral n, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.Rational q, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.String str, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.Binary w n, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.Type, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.FunType, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.Var name T, h => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.DatatypeType name D, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.DatatypeTypeRef name, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.DtcAppType a b, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.DtSel name D i j, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.USort name, h => by
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
        __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
        native_teq, native_not, native_and, SmtEval.native_not] at h
  | Term.UConst name T, h => by
      cases name <;>
        simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_eq, __eo_is_eq,
          __eo_dt_selectors, __eo_dt_selectors_main, __eo_is_ok, native_ite,
          native_teq, native_not, native_and, SmtEval.native_not] at h

theorem dt_tester_eval_false_of_dt_eq_cons_dtcons_false
    (M : SmtModel) (hM : model_total_typed M)
    (cs : native_String) (d0 : Datatype) (ci : native_Nat) (t : Term) :
    TranslationProofs.__eo_reserved_datatype_name cs = false ->
    term_has_non_none_type
      (SmtTerm.Apply
        (SmtTerm.DtTester cs (__eo_to_smt_datatype d0) ci)
        (__eo_to_smt t)) ->
    __dt_eq_cons (Term.DtCons cs d0 ci) t = Term.Boolean false ->
    __smtx_model_eval M
        (SmtTerm.Apply
          (SmtTerm.DtTester cs (__eo_to_smt_datatype d0) ci)
          (__eo_to_smt t)) =
      SmtValue.Boolean false := by
  intro hReserved hLeftNN hGuardValue
  have hTType :
      __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype cs (__eo_to_smt_datatype d0) :=
    dt_tester_arg_datatype_of_non_none hLeftNN
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [hTType]
    simp
  rcases dt_eq_cons_dtcons_false_ctor_root cs d0 ci t hGuardValue with
    ⟨root, hRoot, hRootNe⟩
  have hHeadNe :
      __vsm_apply_head (__smtx_model_eval M (__eo_to_smt t)) ≠
        SmtValue.DtCons cs (__eo_to_smt_datatype d0) ci := by
    intro hEqHead
    rcases ctorSpineRoot_root_cases hRoot with hTuple | hRest
    · subst root
      rcases ctorSpineRoot_tuple_typeof_tuple hRoot hTNN with
        ⟨A, td, hTupleTy⟩
      rw [hTType] at hTupleTy
      injection hTupleTy with hName _hD
      exact (TranslationProofs.eo_unreserved_datatype_name_ne_tuple
        hReserved) hName
    · rcases hRest with hUnit | hDtRoot
      · subst root
        have hUnitTy :=
          ctorSpineRoot_tupleUnit_typeof_unit hRoot hTNN
        rw [hTType] at hUnitTy
        injection hUnitTy with hName _hD
        exact (TranslationProofs.eo_unreserved_datatype_name_ne_tuple
          hReserved) hName
      · rcases hDtRoot with ⟨s', d', i', hRootEq⟩
        subst root
        have hSpDt :
            DtConsSpineRoot t s' d' i' :=
          dtConsSpineRoot_of_ctor_dtCons hRoot
        have hHeadRoot :
            __vsm_apply_head
                (__smtx_model_eval M (__eo_to_smt t)) =
              SmtValue.DtCons s' (__eo_to_smt_datatype d') i' :=
          dtConsSpineRoot_eval_head M hM hSpDt hTNN
        rw [hHeadRoot] at hEqHead
        injection hEqHead with hs hD hi
        cases hs
        cases hi
        have hWF :
            __smtx_dt_wf_rec
                (__smtx_dt_substitute cs (__eo_to_smt_datatype d0)
                  (__eo_to_smt_datatype d0))
                (__eo_to_smt_datatype d0) =
              true :=
          smt_datatype_dt_wf_rec_of_typeof
            (__eo_to_smt t) cs (__eo_to_smt_datatype d0) hTType
        have hdEq : d' = d0 :=
          TranslationProofs.eo_to_smt_datatype_injective_of_wf_rec
            hD rfl hWF
        cases hdEq
        exact hRootNe rfl
  simp [__smtx_model_eval, __smtx_model_eval_dt_tester, hHeadNe,
    native_veq]
