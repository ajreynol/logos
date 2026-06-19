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

theorem smtx_typeof_apply_of_head_none_of_non_datatype_head
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hf : __smtx_typeof f = SmtType.None) :
    __smtx_typeof (SmtTerm.Apply f x) = SmtType.None := by
  have hGeneric : generic_apply_type f x :=
    generic_apply_type_of_non_datatype_head hSel hTester
  unfold generic_apply_type at hGeneric
  rw [hGeneric, hf]
  simp [__smtx_typeof_apply]

theorem smt_bool_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hArg :
      __smtx_typeof (op a b) ≠ SmtType.None ->
        __smtx_typeof a = SmtType.Bool) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have haBool := hArg hNone
    rw [ha] at haBool
    cases haBool

theorem smt_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hArgs :
      ∀ a b,
        __smtx_typeof (op a b) ≠ SmtType.None ->
          ∃ A B,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    rcases hArgs a b hNone with
      ⟨A, _B, haTy, _hbTy, hANN, _hBNN, _hAReg, _hBReg⟩
    rw [ha] at haTy
    exact hANN haTy.symm

theorem smt_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hArgs :
      ∀ a b,
        __smtx_typeof (op a b) ≠ SmtType.None ->
          ∃ A B,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    rcases hArgs a b hNone with
      ⟨_A, B, _haTy, hbTy, _hANN, hBNN, _hAReg, _hBReg⟩
    rw [hb] at hbTy
    exact hBNN hbTy.symm

theorem smt_bool_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hArg :
      __smtx_typeof (op a b) ≠ SmtType.None ->
        __smtx_typeof b = SmtType.Bool) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have hbBool := hArg hNone
    rw [hb] at hbBool
    cases hbBool

theorem smt_reglan_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None)
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := reglan_binop_args_of_non_none (op := op) (hTy a b) hTerm
    rw [ha] at hArgs
    cases hArgs.1

theorem smt_reglan_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None)
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := reglan_binop_args_of_non_none (op := op) (hTy a b) hTerm
    rw [hb] at hArgs
    cases hArgs.2

theorem smt_seq_char_reglan_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.Bool SmtType.None)
            SmtType.None)
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := seq_char_reglan_args_of_non_none
      (op := op) (hTy a b) hTerm
    rw [ha] at hArgs
    cases hArgs.1

theorem smt_seq_char_reglan_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.Bool SmtType.None)
            SmtType.None)
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := seq_char_reglan_args_of_non_none
      (op := op) (hTy a b) hTerm
    rw [hb] at hArgs
    cases hArgs.2

theorem smt_eq_type_none_of_first_arg_none
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (SmtTerm.eq a b) = SmtType.None := by
  intro ha
  by_cases hNone : __smtx_typeof (SmtTerm.eq a b) = SmtType.None
  · exact hNone
  · exfalso
    rw [typeof_eq_eq, ha] at hNone
    cases __smtx_typeof b <;>
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
        native_Teq] at hNone

theorem smt_eq_type_none_of_second_arg_none
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.eq a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (SmtTerm.eq a b) = SmtType.None
  · exact hNone
  · exfalso
    rw [typeof_eq_eq, hb] at hNone
    cases __smtx_typeof a <;>
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
        native_Teq] at hNone

theorem smt_ite_type_none_of_then_arg_none
    (c t e : SmtTerm) :
    __smtx_typeof t = SmtType.None ->
    __smtx_typeof (SmtTerm.ite c t e) = SmtType.None := by
  intro ht
  by_cases hNone : __smtx_typeof (SmtTerm.ite c t e) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (SmtTerm.ite c t e) := by
      unfold term_has_non_none_type
      exact hNone
    rcases ite_args_of_non_none hTerm with ⟨T, _hc, htT, _heT, hTNN⟩
    rw [ht] at htT
    exact hTNN htT.symm

theorem smt_ite_type_none_of_else_arg_none
    (c t e : SmtTerm) :
    __smtx_typeof e = SmtType.None ->
    __smtx_typeof (SmtTerm.ite c t e) = SmtType.None := by
  intro he
  by_cases hNone : __smtx_typeof (SmtTerm.ite c t e) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (SmtTerm.ite c t e) := by
      unfold term_has_non_none_type
      exact hNone
    rcases ite_args_of_non_none hTerm with ⟨T, _hc, _htT, heT, hTNN⟩
    rw [he] at heT
    exact hTNN heT.symm

theorem smt_ternop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (a b c : SmtTerm)
    (hArgs :
      ∀ a b c,
        __smtx_typeof (op a b c) ≠ SmtType.None ->
          ∃ A B C,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              __smtx_typeof c = C ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
              C ≠ SmtType.RegLan) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b c) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b c) = SmtType.None
  · exact hNone
  · exfalso
    rcases hArgs a b c hNone with
      ⟨_A, B, _C, _haTy, hbTy, _hcTy, _hANN, hBNN, _hCNN,
        _hAReg, _hBReg, _hCReg⟩
    rw [hb] at hbTy
    exact hBNN hbTy.symm

theorem smt_ternop_type_none_of_third_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (a b c : SmtTerm)
    (hArgs :
      ∀ a b c,
        __smtx_typeof (op a b c) ≠ SmtType.None ->
          ∃ A B C,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              __smtx_typeof c = C ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
              C ≠ SmtType.RegLan) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (op a b c) = SmtType.None := by
  intro hc
  by_cases hNone : __smtx_typeof (op a b c) = SmtType.None
  · exact hNone
  · exfalso
    rcases hArgs a b c hNone with
      ⟨_A, _B, C, _haTy, _hbTy, hcTy, _hANN, _hBNN, hCNN,
        _hAReg, _hBReg, _hCReg⟩
    rw [hc] at hcTy
    exact hCNN hcTy.symm

theorem smt_str_replace_re_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b c,
        __smtx_typeof (op a b c) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              (native_ite
                (native_Teq (__smtx_typeof c) (SmtType.Seq SmtType.Char))
                (SmtType.Seq SmtType.Char) SmtType.None)
              SmtType.None)
            SmtType.None)
    (a b c : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b c) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (op a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_replace_re_args_of_non_none (op := op) (hTy a b c) hTerm
    rw [hb] at hArgs
    cases hArgs.2.1

theorem smt_str_replace_re_type_none_of_third_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b c,
        __smtx_typeof (op a b c) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              (native_ite
                (native_Teq (__smtx_typeof c) (SmtType.Seq SmtType.Char))
                (SmtType.Seq SmtType.Char) SmtType.None)
              SmtType.None)
            SmtType.None)
    (a b c : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (op a b c) = SmtType.None := by
  intro hc
  by_cases hNone : __smtx_typeof (op a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (op a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_replace_re_args_of_non_none (op := op) (hTy a b c) hTerm
    rw [hc] at hArgs
    cases hArgs.2.2

theorem smt_str_indexof_re_type_none_of_second_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re a b c) = SmtType.None := by
  intro hb
  by_cases hNone :
      __smtx_typeof (SmtTerm.str_indexof_re a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_indexof_re_args_of_non_none hTerm
    rw [hb] at hArgs
    cases hArgs.2.1

theorem smt_str_indexof_re_type_none_of_third_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re a b c) = SmtType.None := by
  intro hc
  by_cases hNone :
      __smtx_typeof (SmtTerm.str_indexof_re a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_indexof_re_args_of_non_none hTerm
    rw [hc] at hArgs
    cases hArgs.2.2

theorem smt_str_indexof_re_split_type_none_of_second_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re_split a b c) = SmtType.None := by
  intro hb
  by_cases hNone :
      __smtx_typeof (SmtTerm.str_indexof_re_split a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re_split a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_indexof_re_split_args_of_non_none hTerm
    rw [hb] at hArgs
    cases hArgs.2.1

theorem smt_str_indexof_re_split_type_none_of_third_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof_re_split a b c) = SmtType.None := by
  intro hc
  by_cases hNone :
      __smtx_typeof (SmtTerm.str_indexof_re_split a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm :
        term_has_non_none_type (SmtTerm.str_indexof_re_split a b c) := by
      unfold term_has_non_none_type
      exact hNone
    have hArgs := str_indexof_re_split_args_of_non_none hTerm
    rw [hc] at hArgs
    cases hArgs.2.2

theorem smtx_typeof_apply_eo_to_smt_binderListCons_none
    (f : SmtTerm) (x xs : Term) :
    __smtx_typeof
        (SmtTerm.Apply f (__eo_to_smt (eoBinderListCons x xs))) =
      SmtType.None :=
  smtx_typeof_apply_of_arg_none f (__eo_to_smt (eoBinderListCons x xs))
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_binderListCons_generic_none
    (q x xs : Term)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        SmtTerm.Apply (__eo_to_smt q)
          (__eo_to_smt (eoBinderListCons x xs))) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smtx_typeof_apply_eo_to_smt_binderListCons_none
    (__eo_to_smt q) x xs

theorem smtx_typeof_apply_apply_eo_to_smt_binderListCons_none
    (f : SmtTerm) (x xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.Apply f (__eo_to_smt (eoBinderListCons x xs))) body) =
      SmtType.None :=
  smtx_typeof_apply_of_head_none_of_non_datatype_head
    (SmtTerm.Apply f (__eo_to_smt (eoBinderListCons x xs))) body
    (by intro s d i j hEq; cases hEq)
    (by intro s d i hEq; cases hEq)
    (smtx_typeof_apply_eo_to_smt_binderListCons_none f x xs)

theorem smtx_typeof_eo_to_smt_binderShape_generic_none
    (q x xs body : Term)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        SmtTerm.Apply
          (SmtTerm.Apply (__eo_to_smt q)
            (__eo_to_smt (eoBinderListCons x xs)))
          (__eo_to_smt body)) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smtx_typeof_apply_apply_eo_to_smt_binderListCons_none
    (__eo_to_smt q) x xs (__eo_to_smt body)

theorem smtx_typeof_eo_to_smt_binderShape_outer_apply_none
    (q x xs body : Term)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply q (eoBinderListCons x xs)))
          (__eo_to_smt body))
    (hSel :
      ∀ s d i j,
        __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) ≠
          SmtTerm.DtSel s d i j)
    (hTester :
      ∀ s d i,
        __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) ≠
          SmtTerm.DtTester s d i)
    (hHead :
      __smtx_typeof
          (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smtx_typeof_apply_of_head_none_of_non_datatype_head
    (__eo_to_smt (Term.Apply q (eoBinderListCons x xs)))
    (__eo_to_smt body) hSel hTester hHead

theorem smtx_typeof_eo_to_smt_binderShape_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hArgs :
      ∀ a b,
        __smtx_typeof (op a b) ≠ SmtType.None ->
          ∃ A B,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_binop_type_none_of_first_arg_none op
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hArgs (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_bool_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hArg :
      __smtx_typeof
            (op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) ≠
          SmtType.None ->
        __smtx_typeof (__eo_to_smt (eoBinderListCons x xs)) =
          SmtType.Bool) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_bool_binop_type_none_of_first_arg_none op
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hArg (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_reglan_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_reglan_binop_type_none_of_first_arg_none op hTy
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_seq_char_reglan_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.Bool SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_seq_char_reglan_binop_type_none_of_first_arg_none op hTy
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_ternop_second_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (a : SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op a (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hArgs :
      ∀ a b c,
        __smtx_typeof (op a b c) ≠ SmtType.None ->
          ∃ A B C,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              __smtx_typeof c = C ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧ C ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
              C ≠ SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_ternop_type_none_of_second_arg_none op a
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hArgs (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_str_replace_re_second_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (a : SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op a (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b c,
        __smtx_typeof (op a b c) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              (native_ite
                (native_Teq (__smtx_typeof c) (SmtType.Seq SmtType.Char))
                (SmtType.Seq SmtType.Char) SmtType.None)
              SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_str_replace_re_type_none_of_second_arg_none op hTy a
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_not_binderListCons_none
    (x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.not) (eoBinderListCons x xs))) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.not (__eo_to_smt (eoBinderListCons x xs))) =
      SmtType.None
  rw [typeof_not_eq, smtx_typeof_eo_to_smt_binderListCons_none]
  rfl

theorem eo_to_smt_typed_list_elem_type_binderListCons_none
    (x xs : Term) :
    __eo_to_smt_typed_list_elem_type (eoBinderListCons x xs) =
      SmtType.None := by
  rfl

theorem smtx_typeof_eo_to_smt_apply_distinct_binderListCons_none
    (x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.distinct)
            (eoBinderListCons x xs))) =
      SmtType.None := by
  change
    __smtx_typeof
        (native_ite
          (native_Teq
            (__eo_to_smt_typed_list_elem_type (eoBinderListCons x xs))
            SmtType.None)
          SmtTerm.None
          (__eo_to_smt_distinct (eoBinderListCons x xs))) =
      SmtType.None
  rw [eo_to_smt_typed_list_elem_type_binderListCons_none]
  simp [native_ite, native_Teq]

theorem smtx_typeof_eo_to_smt_binderShape_not_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.not) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_outer_apply_none
    (Term.UOp UserOp.not) x xs body
    (by rfl)
    (by intro s d i j hEq; cases hEq)
    (by intro s d i hEq; cases hEq)
    (smtx_typeof_eo_to_smt_apply_not_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_distinct_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.distinct) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_outer_apply_none
    (Term.UOp UserOp.distinct) x xs body
    (by rfl)
    (by intro s d i j hEq; cases hEq)
    (by intro s d i hEq; cases hEq)
    (smtx_typeof_eo_to_smt_apply_distinct_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_or_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.or) x xs body)) =
      SmtType.None := by
  exact smtx_typeof_eo_to_smt_binderShape_bool_binop_first_none
    (Term.UOp UserOp.or) x xs body SmtTerm.or (by rfl)
    (fun h =>
      (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
        (typeof_or_eq (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body))
        (by
          unfold term_has_non_none_type
          exact h)).1)

theorem smtx_typeof_eo_to_smt_binderShape_and_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.and) x xs body)) =
      SmtType.None := by
  exact smtx_typeof_eo_to_smt_binderShape_bool_binop_first_none
    (Term.UOp UserOp.and) x xs body SmtTerm.and (by rfl)
    (fun h =>
      (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
        (typeof_and_eq (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body))
        (by
          unfold term_has_non_none_type
          exact h)).1)

theorem smtx_typeof_eo_to_smt_binderShape_imp_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.imp) x xs body)) =
      SmtType.None := by
  exact smtx_typeof_eo_to_smt_binderShape_bool_binop_first_none
    (Term.UOp UserOp.imp) x xs body SmtTerm.imp (by rfl)
    (fun h =>
      (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
        (typeof_imp_eq (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body))
        (by
          unfold term_has_non_none_type
          exact h)).1)

theorem smtx_typeof_eo_to_smt_binderShape_xor_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.xor) x xs body)) =
      SmtType.None := by
  exact smtx_typeof_eo_to_smt_binderShape_bool_binop_first_none
    (Term.UOp UserOp.xor) x xs body SmtTerm.xor (by rfl)
    (fun h =>
      (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
        (typeof_xor_eq (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body))
        (by
          unfold term_has_non_none_type
          exact h)).1)

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
  exact smt_eq_type_none_of_first_arg_none
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

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
  exact smt_ite_type_none_of_then_arg_none
    (__eo_to_smt c) (__eo_to_smt (eoBinderListCons x xs))
    (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)
