import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

/--
The generated helper functions treat terms of the form `(q (cons x xs) body)`
as binder-shaped.  This predicate records the SMT heads for which that
syntactic treatment is intended.
-/
def IsQuantifierHead (q : Term) : Prop :=
  q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists

def eoBinderListCons (x xs : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons x) xs

def eoBinderShape (q x xs body : Term) : Term :=
  Term.Apply (Term.Apply q (eoBinderListCons x xs)) body

/--
Target statement for the common inversion lemma we want to discharge: if a
binder-shaped term has a meaningful SMT type, its head must be a real quantifier.
-/
def BinderShapeNonNoneForcesQuantifierHead : Prop :=
  ∀ q x xs body,
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) ≠
      SmtType.None ->
    IsQuantifierHead q

/-- The non-`None` inversion is stronger than the older Bool-only formulation. -/
def BinderShapeBoolForcesQuantifierHead : Prop :=
  ∀ q x xs body,
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.Bool ->
    IsQuantifierHead q

theorem binderShapeBoolForcesQuantifierHead_of_nonNone
    (h : BinderShapeNonNoneForcesQuantifierHead) :
    BinderShapeBoolForcesQuantifierHead := by
  intro q x xs body hBool
  exact h q x xs body (by
    intro hNone
    rw [hNone] at hBool
    cases hBool)

theorem isQuantifierHead_forall :
    IsQuantifierHead (Term.UOp UserOp.forall) :=
  Or.inl rfl

theorem isQuantifierHead_exists :
    IsQuantifierHead (Term.UOp UserOp.exists) :=
  Or.inr rfl

theorem eo_to_smt_binderListCons_eq (x xs : Term) :
    __eo_to_smt (eoBinderListCons x xs) =
      SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
        (__eo_to_smt xs) := by
  rfl

theorem smtx_typeof_eo_to_smt_binderListCons_none (x xs : Term) :
    __smtx_typeof (__eo_to_smt (eoBinderListCons x xs)) =
      SmtType.None := by
  rw [eo_to_smt_binderListCons_eq]
  simp [__smtx_typeof, __smtx_typeof_apply]

theorem eo_to_smt_binderShape_forall_eq
    (x xs body : Term) :
    __eo_to_smt (eoBinderShape (Term.UOp UserOp.forall) x xs body) =
      SmtTerm.not
        (__eo_to_smt_exists (eoBinderListCons x xs)
          (SmtTerm.not (__eo_to_smt body))) := by
  rfl

theorem eo_to_smt_binderShape_exists_eq
    (x xs body : Term) :
    __eo_to_smt (eoBinderShape (Term.UOp UserOp.exists) x xs body) =
      __eo_to_smt_exists (eoBinderListCons x xs) (__eo_to_smt body) := by
  rfl

theorem smtx_typeof_ite_term_eq
    (c t e : SmtTerm) :
    __smtx_typeof (SmtTerm.ite c t e) =
      __smtx_typeof_ite
        (__smtx_typeof c) (__smtx_typeof t) (__smtx_typeof e) := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smtx_typeof_apply_of_arg_none
    (f x : SmtTerm)
    (hx : __smtx_typeof x = SmtType.None) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  by_cases hNN : __smtx_typeof (SmtTerm.Apply f x) = SmtType.None
  · exact hNN
  · exfalso
    by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
    · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
      have hArg : __smtx_typeof x = SmtType.Datatype s d :=
        dt_sel_arg_datatype_of_non_none (s := s) (d := d) (i := i)
          (j := j) (x := x) hNN
      rw [hx] at hArg
      cases hArg
    · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
      · rcases hTesterWitness with ⟨s, d, i, rfl⟩
        have hArg : __smtx_typeof x = SmtType.Datatype s d :=
          dt_tester_arg_datatype_of_non_none (s := s) (d := d) (i := i)
            (x := x) hNN
        rw [hx] at hArg
        cases hArg
      · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
          intro s d i j hEq
          exact hSelWitness ⟨s, d, i, j, hEq⟩
        have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
          intro s d i hEq
          exact hTesterWitness ⟨s, d, i, hEq⟩
        have hGeneric : generic_apply_type f x :=
          generic_apply_type_of_non_datatype_head hSel hTester
        have hApply :
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
              SmtType.None := by
          unfold generic_apply_type at hGeneric
          rw [← hGeneric]
          exact hNN
        rcases typeof_apply_non_none_cases hApply with
          ⟨A, _B, _hHead, hArg, hA, _hB⟩
        rw [hx] at hArg
        exact hA hArg.symm

theorem smtx_typeof_apply_eo_to_smt_binderListCons_none
    (f : SmtTerm) (x xs : Term) :
    __smtx_typeof
        (SmtTerm.Apply f (__eo_to_smt (eoBinderListCons x xs))) =
      SmtType.None :=
  smtx_typeof_apply_of_arg_none f (__eo_to_smt (eoBinderListCons x xs))
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_apply_apply_eo_to_smt_binderListCons_none
    (f : SmtTerm) (x xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.Apply f (__eo_to_smt (eoBinderListCons x xs))) body) =
      SmtType.None :=
  by
    have hGeneric :
        generic_apply_type
          (SmtTerm.Apply f (__eo_to_smt (eoBinderListCons x xs))) body :=
      generic_apply_type_of_non_datatype_head
        (by intro s d i j hEq; cases hEq)
        (by intro s d i hEq; cases hEq)
    unfold generic_apply_type at hGeneric
    rw [hGeneric, smtx_typeof_apply_eo_to_smt_binderListCons_none]
    simp [__smtx_typeof_apply]

theorem smtx_typeof_eo_to_smt_binderShape_or_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.or) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.or (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  simp [__smtx_typeof, smtx_typeof_eo_to_smt_binderListCons_none,
    native_ite, native_Teq]

theorem smtx_typeof_eo_to_smt_binderShape_and_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.and) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.and (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  simp [__smtx_typeof, smtx_typeof_eo_to_smt_binderListCons_none,
    native_ite, native_Teq]

theorem smtx_typeof_eo_to_smt_binderShape_imp_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.imp) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.imp (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  simp [__smtx_typeof, smtx_typeof_eo_to_smt_binderListCons_none,
    native_ite, native_Teq]

theorem smtx_typeof_eo_to_smt_binderShape_xor_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.xor) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.xor (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  simp [__smtx_typeof, smtx_typeof_eo_to_smt_binderListCons_none,
    native_ite, native_Teq]

theorem smtx_typeof_eo_to_smt_binderShape_eq_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.eq) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.eq (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
    smtx_typeof_eo_to_smt_binderListCons_none, native_ite, native_Teq]

theorem smtx_typeof_eo_to_smt_binderShape_ite_none
    (c x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.ite) c) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  rw [smtx_typeof_ite_term_eq]
  rw [smtx_typeof_eo_to_smt_binderListCons_none]
  generalize __smtx_typeof (__eo_to_smt c) = cTy
  generalize __smtx_typeof (__eo_to_smt body) = bodyTy
  cases cTy <;> cases bodyTy <;>
    simp [__smtx_typeof_ite, native_ite, native_Teq]
