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

theorem native_ite_smt_type_ne_set_none
    (b : native_Bool) {T U : SmtType}
    (hT : T ≠ SmtType.Set SmtType.None)
    (hU : U ≠ SmtType.Set SmtType.None) :
    native_ite b T U ≠ SmtType.Set SmtType.None := by
  cases b
  · simpa [native_ite] using hU
  · simpa [native_ite] using hT

theorem smtx_typeof_guard_ne_set_none
    (T U : SmtType)
    (hU : U ≠ SmtType.Set SmtType.None) :
    __smtx_typeof_guard T U ≠ SmtType.Set SmtType.None := by
  exact native_ite_smt_type_ne_set_none
    (native_Teq T SmtType.None)
    (by intro h; cases h) hU

theorem smtx_typeof_guard_set_self_ne_set_none
    (T : SmtType) :
    __smtx_typeof_guard T (SmtType.Set T) ≠
      SmtType.Set SmtType.None := by
  cases T <;> simp [__smtx_typeof_guard, native_Teq, native_ite]

theorem eo_to_smt_type_tuple_ne_set_none
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Set SmtType.None := by
  cases V <;> simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d
    case null =>
      simp
    case sum c tail =>
      cases tail
      case null =>
        by_cases h :
            native_and (native_streq s (native_string_lit "@Tuple"))
              (__smtx_type_wf_component U) = true
        · simpa [__eo_to_smt_type_tuple, h] using
            native_ite_smt_type_ne_set_none true
              (by intro hEq; cases hEq) (by intro hEq; cases hEq)
        · simpa [__eo_to_smt_type_tuple, h] using
            native_ite_smt_type_ne_set_none false
              (by intro hEq; cases hEq) (by intro hEq; cases hEq)
      case sum c' tail' =>
        simp

theorem eo_to_smt_type_ne_set_none (T : Term) :
    __eo_to_smt_type T ≠ SmtType.Set SmtType.None := by
  cases T
  case UOp op =>
    cases op <;> simp [__eo_to_smt_type]
  case DatatypeType s d =>
    exact native_ite_smt_type_ne_set_none
      (native_reserved_datatype_name s)
      (by intro h; cases h) (by intro h; cases h)
  case DatatypeTypeRef s =>
    exact native_ite_smt_type_ne_set_none
      (native_reserved_datatype_name s)
      (by intro h; cases h) (by intro h; cases h)
  case DtcAppType T U =>
    exact smtx_typeof_guard_ne_set_none _ _
      (smtx_typeof_guard_ne_set_none _ _
        (by intro h; cases h))
  case Apply f x =>
    cases f <;> try (simp [__eo_to_smt_type])
    case UOp op =>
      cases op <;> try (simp [__eo_to_smt_type])
      case BitVec =>
        cases x
        case Numeral n =>
          exact native_ite_smt_type_ne_set_none
            (native_zleq 0 n)
            (by intro h; cases h) (by intro h; cases h)
        all_goals simp [__eo_to_smt_type]
      case Seq =>
        exact smtx_typeof_guard_ne_set_none _ _
          (by intro h; cases h)
      case Set =>
        exact smtx_typeof_guard_set_self_ne_set_none
          (__eo_to_smt_type x)
    case Apply f' y =>
      cases f' <;> try (simp [__eo_to_smt_type])
      case FunType =>
        exact smtx_typeof_guard_ne_set_none _ _
          (smtx_typeof_guard_ne_set_none _ _
            (by intro h; cases h))
      case UOp op =>
        cases op <;> try (simp [__eo_to_smt_type])
        case Array =>
          exact smtx_typeof_guard_ne_set_none _ _
            (smtx_typeof_guard_ne_set_none _ _
              (by intro h; cases h))
        case Tuple =>
          let tupleTy :=
            __eo_to_smt_type_tuple (__eo_to_smt_type y)
              (__eo_to_smt_type x)
          change native_ite (__smtx_type_wf tupleTy) tupleTy SmtType.None ≠
            SmtType.Set SmtType.None
          exact native_ite_smt_type_ne_set_none
            (__smtx_type_wf tupleTy)
            (eo_to_smt_type_tuple_ne_set_none
              (__eo_to_smt_type y) (__eo_to_smt_type x))
            (by intro h; cases h)
  all_goals simp [__eo_to_smt_type]

theorem smtx_typeof_eo_to_smt_ne_set_none (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.Set SmtType.None := by
  intro hSetNone
  have hNonNone :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hSetNone
    cases hSetNone
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hNonNone
  exact eo_to_smt_type_ne_set_none (__eo_typeof t)
    (hMatch.symm.trans hSetNone)

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

theorem smtx_typeof_eo_to_smt_exists_of_body_none :
    ∀ (vs : Term) (body : SmtTerm),
      __smtx_typeof body = SmtType.None ->
        __smtx_typeof (__eo_to_smt_exists vs body) = SmtType.None
  | Term.__eo_List_nil, body, hBody => by
      simpa [__eo_to_smt_exists] using hBody
  | Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String s) T)) tail, body, hBody => by
      change
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail body)) =
          SmtType.None
      rw [smtx_typeof_exists_term_eq,
        smtx_typeof_eo_to_smt_exists_of_body_none tail body hBody]
      rfl
  | vs, body, hBody => by
      cases vs
      case __eo_List_nil =>
        simpa [__eo_to_smt_exists] using hBody
      case Apply f tail =>
        cases f
        case Apply f' head =>
          cases f'
          case __eo_List_cons =>
            cases head
            case Var name T =>
              cases name
              case String s =>
                change
                  __smtx_typeof
                      (SmtTerm.exists s (__eo_to_smt_type T)
                        (__eo_to_smt_exists tail body)) =
                    SmtType.None
                rw [smtx_typeof_exists_term_eq,
                  smtx_typeof_eo_to_smt_exists_of_body_none tail body hBody]
                rfl
              all_goals
                change __smtx_typeof SmtTerm.None = SmtType.None
                exact TranslationProofs.smtx_typeof_none
            all_goals
              change __smtx_typeof SmtTerm.None = SmtType.None
              exact TranslationProofs.smtx_typeof_none
          all_goals
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none

theorem eo_to_smt_exists_binderListCons_ne_dt_sel :
    ∀ (vs x xs : Term) (s : native_String)
      (d : SmtDatatype) (i j : native_Nat),
      __eo_to_smt_exists vs (__eo_to_smt (eoBinderListCons x xs)) ≠
        SmtTerm.DtSel s d i j
  | Term.__eo_List_nil, x, xs, s, d, i, j => by
      change
        SmtTerm.Apply
            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
            (__eo_to_smt xs) ≠
          SmtTerm.DtSel s d i j
      intro h
      cases h
  | Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String v) T)) tail, x, xs, s, d, i, j => by
      change
        SmtTerm.exists v (__eo_to_smt_type T)
          (__eo_to_smt_exists tail (__eo_to_smt (eoBinderListCons x xs))) ≠
          SmtTerm.DtSel s d i j
      intro h
      cases h
  | vs, x, xs, s, d, i, j => by
      cases vs
      case __eo_List_nil =>
        change
          SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
              (__eo_to_smt xs) ≠
            SmtTerm.DtSel s d i j
        intro h
        cases h
      case Apply f tail =>
        cases f
        case Apply f' head =>
          cases f'
          case __eo_List_cons =>
            cases head
            case Var name T =>
              cases name
              case String v =>
                change
                  SmtTerm.exists v (__eo_to_smt_type T)
                    (__eo_to_smt_exists tail
                      (__eo_to_smt (eoBinderListCons x xs))) ≠
                    SmtTerm.DtSel s d i j
                intro h
                cases h
              all_goals
                change SmtTerm.None ≠ SmtTerm.DtSel s d i j
                intro h
                cases h
            all_goals
              change SmtTerm.None ≠ SmtTerm.DtSel s d i j
              intro h
              cases h
          all_goals
            change SmtTerm.None ≠ SmtTerm.DtSel s d i j
            intro h
            cases h
        all_goals
          change SmtTerm.None ≠ SmtTerm.DtSel s d i j
          intro h
          cases h
      all_goals
        change SmtTerm.None ≠ SmtTerm.DtSel s d i j
        intro h
        cases h

theorem eo_to_smt_exists_binderListCons_ne_dt_tester :
    ∀ (vs x xs : Term) (s : native_String)
      (d : SmtDatatype) (i : native_Nat),
      __eo_to_smt_exists vs (__eo_to_smt (eoBinderListCons x xs)) ≠
        SmtTerm.DtTester s d i
  | Term.__eo_List_nil, x, xs, s, d, i => by
      change
        SmtTerm.Apply
            (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
            (__eo_to_smt xs) ≠
          SmtTerm.DtTester s d i
      intro h
      cases h
  | Term.Apply (Term.Apply Term.__eo_List_cons
        (Term.Var (Term.String v) T)) tail, x, xs, s, d, i => by
      change
        SmtTerm.exists v (__eo_to_smt_type T)
          (__eo_to_smt_exists tail (__eo_to_smt (eoBinderListCons x xs))) ≠
          SmtTerm.DtTester s d i
      intro h
      cases h
  | vs, x, xs, s, d, i => by
      cases vs
      case __eo_List_nil =>
        change
          SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
              (__eo_to_smt xs) ≠
            SmtTerm.DtTester s d i
        intro h
        cases h
      case Apply f tail =>
        cases f
        case Apply f' head =>
          cases f'
          case __eo_List_cons =>
            cases head
            case Var name T =>
              cases name
              case String v =>
                change
                  SmtTerm.exists v (__eo_to_smt_type T)
                    (__eo_to_smt_exists tail
                      (__eo_to_smt (eoBinderListCons x xs))) ≠
                    SmtTerm.DtTester s d i
                intro h
                cases h
              all_goals
                change SmtTerm.None ≠ SmtTerm.DtTester s d i
                intro h
                cases h
            all_goals
              change SmtTerm.None ≠ SmtTerm.DtTester s d i
              intro h
              cases h
          all_goals
            change SmtTerm.None ≠ SmtTerm.DtTester s d i
            intro h
            cases h
        all_goals
          change SmtTerm.None ≠ SmtTerm.DtTester s d i
          intro h
          cases h
      all_goals
        change SmtTerm.None ≠ SmtTerm.DtTester s d i
        intro h
        cases h

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

theorem smt_arith_overload_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  cases __smtx_typeof b <;> rfl

theorem smt_arith_overload_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_arith_overload_ret_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  cases __smtx_typeof b <;> rfl

theorem smt_arith_overload_ret_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_int_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Int)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.Int)
              R SmtType.None)
            SmtType.None) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  rfl

theorem smt_int_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Int)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.Int)
              R SmtType.None)
            SmtType.None) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_bv_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  rfl

theorem smt_bv_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_bv_binop_ret_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  rfl

theorem smt_bv_binop_ret_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_concat_type_none_of_first_arg_none
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (SmtTerm.concat a b) = SmtType.None := by
  intro ha
  rw [typeof_concat_eq, ha]
  rfl

theorem smt_concat_type_none_of_second_arg_none
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.concat a b) = SmtType.None := by
  intro hb
  rw [typeof_concat_eq, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_seq_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  rfl

theorem smt_seq_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_seq_binop_ret_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  rfl

theorem smt_seq_binop_ret_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_seq_char_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
              R SmtType.None)
            SmtType.None) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  rfl

theorem smt_seq_char_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
              R SmtType.None)
            SmtType.None) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  by_cases hA :
      native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char)
  · simp [native_ite, native_Teq]
  · simp [native_ite, hA]

theorem smt_set_binop_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  rfl

theorem smt_set_binop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_set_binop_ret_type_none_of_first_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro ha
  rw [hTy a b, ha]
  rfl

theorem smt_set_binop_ret_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (a b : SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b) = SmtType.None := by
  intro hb
  rw [hTy a b, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_map_diff_type_none_of_first_arg_none
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (SmtTerm.map_diff a b) = SmtType.None := by
  intro ha
  rw [typeof_map_diff_eq, ha]
  rfl

theorem smt_map_diff_type_none_of_second_arg_none
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.map_diff a b) = SmtType.None := by
  intro hb
  rw [typeof_map_diff_eq, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_set_member_type_none_of_second_arg_none
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.set_member a b) = SmtType.None := by
  intro hb
  rw [typeof_set_member_eq, hb]
  rfl

theorem smt_set_member_type_none_of_first_arg_none_of_second_not_set_none
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof b ≠ SmtType.Set SmtType.None ->
    __smtx_typeof (SmtTerm.set_member a b) = SmtType.None := by
  intro ha hb
  rw [typeof_set_member_eq, ha]
  cases hbTy : __smtx_typeof b <;> try rfl
  case Set U =>
    cases U <;> try rfl
    case None =>
      exact False.elim (hb hbTy)

theorem smt_array_deq_diff_type_none_of_first_arg_none
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_array_deq_diff a (__smtx_typeof a) b
          (__smtx_typeof b)) =
      SmtType.None := by
  intro ha
  rw [ha]
  cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_array_deq_diff,
      TranslationProofs.smtx_typeof_none]

theorem smt_array_deq_diff_type_none_of_second_arg_none
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_array_deq_diff a (__smtx_typeof a) b
          (__smtx_typeof b)) =
      SmtType.None := by
  intro hb
  rw [hb]
  cases ha : __smtx_typeof a <;>
    simp [__eo_to_smt_array_deq_diff,
      TranslationProofs.smtx_typeof_none]

theorem smt_array_deq_diff_ne_dt_sel
    (a b : SmtTerm) :
    ∀ s d i j,
      __eo_to_smt_array_deq_diff a (__smtx_typeof a) b
          (__smtx_typeof b) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_array_deq_diff, ha, hb] at h

theorem smt_array_deq_diff_ne_dt_tester
    (a b : SmtTerm) :
    ∀ s d i,
      __eo_to_smt_array_deq_diff a (__smtx_typeof a) b
          (__smtx_typeof b) ≠
        SmtTerm.DtTester s d i := by
  intro s d i h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_array_deq_diff, ha, hb] at h

theorem smt_sets_deq_diff_type_none_of_first_arg_none
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_sets_deq_diff a (__smtx_typeof a) b
          (__smtx_typeof b)) =
      SmtType.None := by
  intro ha
  rw [ha]
  cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_sets_deq_diff,
      TranslationProofs.smtx_typeof_none]

theorem smt_sets_deq_diff_type_none_of_second_arg_none
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_sets_deq_diff a (__smtx_typeof a) b
          (__smtx_typeof b)) =
      SmtType.None := by
  intro hb
  rw [hb]
  cases ha : __smtx_typeof a <;>
    simp [__eo_to_smt_sets_deq_diff,
      TranslationProofs.smtx_typeof_none]

theorem smt_sets_deq_diff_ne_dt_sel
    (a b : SmtTerm) :
    ∀ s d i j,
      __eo_to_smt_sets_deq_diff a (__smtx_typeof a) b
          (__smtx_typeof b) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_sets_deq_diff, ha, hb] at h

theorem smt_sets_deq_diff_ne_dt_tester
    (a b : SmtTerm) :
    ∀ s d i,
      __eo_to_smt_sets_deq_diff a (__smtx_typeof a) b
          (__smtx_typeof b) ≠
        SmtTerm.DtTester s d i := by
  intro s d i h
  cases ha : __smtx_typeof a <;> cases hb : __smtx_typeof b <;>
    simp [__eo_to_smt_sets_deq_diff, ha, hb] at h

theorem eo_to_smt_set_insert_type_none_of_eo_list_cons
    (x xs : Term) (base : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_set_insert (eoBinderListCons x xs) base) =
      SmtType.None := by
  simp [eoBinderListCons, __eo_to_smt_set_insert,
    TranslationProofs.smtx_typeof_none]

theorem eo_to_smt_set_insert_type_none_of_base_none :
    ∀ (xs : Term) (base : SmtTerm),
      __smtx_typeof base = SmtType.None ->
        __smtx_typeof (__eo_to_smt_set_insert xs base) =
          SmtType.None
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
      tail, base, hBase => by
      change
        __smtx_typeof
            (SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
              (__eo_to_smt_set_insert tail base)) =
          SmtType.None
      exact smt_set_binop_type_none_of_second_arg_none
        SmtTerm.set_union
        (SmtTerm.set_singleton (__eo_to_smt head))
        (__eo_to_smt_set_insert tail base)
        (fun a b => typeof_set_union_eq a b)
        (eo_to_smt_set_insert_type_none_of_base_none tail base hBase)
  | Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T, base, hBase => by
      change
        __smtx_typeof
            (native_ite
              (native_Teq (__smtx_typeof base)
                (SmtType.Set (__eo_to_smt_type T)))
              base SmtTerm.None) =
          SmtType.None
      rw [hBase]
      simp [native_Teq, native_ite, TranslationProofs.smtx_typeof_none]
  | xs, base, hBase => by
      cases xs <;>
        try
          simp [__eo_to_smt_set_insert,
            TranslationProofs.smtx_typeof_none]
      case Apply f tail =>
        cases f <;>
          try
            simp [__eo_to_smt_set_insert,
              TranslationProofs.smtx_typeof_none]
        case UOp op =>
          cases op <;>
            try
              simp [__eo_to_smt_set_insert,
                TranslationProofs.smtx_typeof_none]
          case _at__at_TypedList_nil =>
            change
              __smtx_typeof
                  (native_ite
                    (native_Teq (__smtx_typeof base)
                      (SmtType.Set (__eo_to_smt_type tail)))
                    base SmtTerm.None) =
                SmtType.None
            rw [hBase]
            simp [native_Teq, native_ite,
              TranslationProofs.smtx_typeof_none]
        case Apply f' head =>
          cases f' <;>
            try
              simp [__eo_to_smt_set_insert,
                TranslationProofs.smtx_typeof_none]
          case UOp op =>
            cases op <;>
              try
                simp [__eo_to_smt_set_insert,
                  TranslationProofs.smtx_typeof_none]
            case _at__at_TypedList_cons =>
              change
                __smtx_typeof
                    (SmtTerm.set_union
                      (SmtTerm.set_singleton (__eo_to_smt head))
                      (__eo_to_smt_set_insert tail base)) =
                  SmtType.None
              exact smt_set_binop_type_none_of_second_arg_none
                SmtTerm.set_union
                (SmtTerm.set_singleton (__eo_to_smt head))
                (__eo_to_smt_set_insert tail base)
                (fun a b => typeof_set_union_eq a b)
                (eo_to_smt_set_insert_type_none_of_base_none
                  tail base hBase)

theorem eo_to_smt_set_insert_base_none_ne_dt_sel :
    ∀ (xs : Term) (base : SmtTerm),
      __smtx_typeof base = SmtType.None ->
        ∀ s d i j,
          __eo_to_smt_set_insert xs base ≠ SmtTerm.DtSel s d i j
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
      tail, base, _hBase, s, d, i, j => by
      change
        SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
            (__eo_to_smt_set_insert tail base) ≠
          SmtTerm.DtSel s d i j
      intro h
      cases h
  | Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T, base, hBase,
      s, d, i, j => by
      change
        native_ite
            (native_Teq (__smtx_typeof base)
              (SmtType.Set (__eo_to_smt_type T)))
            base SmtTerm.None ≠
          SmtTerm.DtSel s d i j
      rw [hBase]
      simp [native_Teq, native_ite]
  | xs, base, hBase, s, d, i, j => by
      cases xs
      all_goals
        try
          (change SmtTerm.None ≠ SmtTerm.DtSel s d i j
           intro h
           cases h)
      case Apply f tail =>
        cases f
        all_goals
          try
            (change SmtTerm.None ≠ SmtTerm.DtSel s d i j
             intro h
             cases h)
        case UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change
              native_ite
                  (native_Teq (__smtx_typeof base)
                    (SmtType.Set (__eo_to_smt_type tail)))
                  base SmtTerm.None ≠
                SmtTerm.DtSel s d i j
            rw [hBase]
            simp [native_Teq, native_ite]
          all_goals
            change SmtTerm.None ≠ SmtTerm.DtSel s d i j
            intro h
            cases h
        case Apply f' head =>
          cases f'
          all_goals
            try
              (change SmtTerm.None ≠ SmtTerm.DtSel s d i j
               intro h
               cases h)
          case UOp op =>
            cases op
            case _at__at_TypedList_cons =>
              change
                SmtTerm.set_union
                    (SmtTerm.set_singleton (__eo_to_smt head))
                    (__eo_to_smt_set_insert tail base) ≠
                  SmtTerm.DtSel s d i j
              intro h
              cases h
            all_goals
              change SmtTerm.None ≠ SmtTerm.DtSel s d i j
              intro h
              cases h

theorem eo_to_smt_set_insert_base_none_ne_dt_tester :
    ∀ (xs : Term) (base : SmtTerm),
      __smtx_typeof base = SmtType.None ->
        ∀ s d i,
          __eo_to_smt_set_insert xs base ≠ SmtTerm.DtTester s d i
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) head)
      tail, base, _hBase, s, d, i => by
      change
        SmtTerm.set_union (SmtTerm.set_singleton (__eo_to_smt head))
            (__eo_to_smt_set_insert tail base) ≠
          SmtTerm.DtTester s d i
      intro h
      cases h
  | Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T, base, hBase,
      s, d, i => by
      change
        native_ite
            (native_Teq (__smtx_typeof base)
              (SmtType.Set (__eo_to_smt_type T)))
            base SmtTerm.None ≠
          SmtTerm.DtTester s d i
      rw [hBase]
      simp [native_Teq, native_ite]
  | xs, base, hBase, s, d, i => by
      cases xs
      all_goals
        try
          (change SmtTerm.None ≠ SmtTerm.DtTester s d i
           intro h
           cases h)
      case Apply f tail =>
        cases f
        all_goals
          try
            (change SmtTerm.None ≠ SmtTerm.DtTester s d i
             intro h
             cases h)
        case UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change
              native_ite
                  (native_Teq (__smtx_typeof base)
                    (SmtType.Set (__eo_to_smt_type tail)))
                  base SmtTerm.None ≠
                SmtTerm.DtTester s d i
            rw [hBase]
            simp [native_Teq, native_ite]
          all_goals
            change SmtTerm.None ≠ SmtTerm.DtTester s d i
            intro h
            cases h
        case Apply f' head =>
          cases f'
          all_goals
            try
              (change SmtTerm.None ≠ SmtTerm.DtTester s d i
               intro h
               cases h)
          case UOp op =>
            cases op
            case _at__at_TypedList_cons =>
              change
                SmtTerm.set_union
                    (SmtTerm.set_singleton (__eo_to_smt head))
                    (__eo_to_smt_set_insert tail base) ≠
                  SmtTerm.DtTester s d i
              intro h
              cases h
            all_goals
              change SmtTerm.None ≠ SmtTerm.DtTester s d i
              intro h
              cases h

theorem tuple_prepend_tail_type_of_non_none
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm) :
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
      SmtType.None ->
    ∃ c,
      __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum c SmtDatatype.null) := by
  intro hNN
  unfold __eo_to_smt_tuple_prepend at hNN
  cases hTail : __smtx_typeof tail with
  | Datatype s d =>
      by_cases hs : s = native_string_lit "@Tuple"
      · subst s
        cases d with
        | null =>
            exact False.elim (hNN (by
              simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
        | sum c rest =>
            cases rest with
            | null =>
                exact ⟨c, rfl⟩
            | sum c' rest' =>
                exact False.elim (hNN (by
                  simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
      · exact False.elim (hNN (by
          cases d with
          | null =>
              simp [hTail, __eo_to_smt_tuple_prepend_of_type]
          | sum c rest =>
              cases rest <;>
                simp [hTail, __eo_to_smt_tuple_prepend_of_type,
                  native_streq, native_and, native_ite, hs]))
  | _ =>
      exact False.elim (hNN (by
        simp [hTail, __eo_to_smt_tuple_prepend_of_type]))

theorem smt_tuple_prepend_type_none_of_head_none
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm) :
    __smtx_typeof head = SmtType.None ->
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
      SmtType.None := by
  intro hHead
  by_cases hNone :
      __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
        SmtType.None
  · exact hNone
  · exfalso
    rcases tuple_prepend_tail_type_of_non_none head headTy tail hNone with
      ⟨c, hTail⟩
    have hHeadNN :=
      TranslationProofs.smtx_tuple_prepend_head_non_none_of_tail_tuple_type
        tail head headTy c hTail hNone
    exact hHeadNN hHead

theorem smt_tuple_prepend_type_none_of_tail_none
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm) :
    __smtx_typeof tail = SmtType.None ->
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
      SmtType.None := by
  intro hTail
  by_cases hNone :
      __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
        SmtType.None
  · exact hNone
  · exfalso
    rcases tuple_prepend_tail_type_of_non_none head headTy tail hNone with
      ⟨c, hTuple⟩
    rw [hTail] at hTuple
    cases hTuple

theorem smt_select_type_none_of_first_arg_none
    (a b : SmtTerm) :
    __smtx_typeof a = SmtType.None ->
    __smtx_typeof (SmtTerm.select a b) = SmtType.None := by
  intro ha
  rw [typeof_select_eq, ha]
  rfl

theorem smt_select_type_none_of_second_arg_none
    (a b : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.select a b) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (SmtTerm.select a b) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (SmtTerm.select a b) := by
      unfold term_has_non_none_type
      exact hNone
    rcases select_args_of_non_none hTerm with ⟨K, V, ha, hbK⟩
    have hKWf :
        __smtx_type_wf_rec K native_reflist_nil = true :=
      (smt_map_components_wf_rec_of_non_none_type a K V ha).1
    have hKNN : K ≠ SmtType.None := by
      intro hK
      rw [hK] at hKWf
      simp [__smtx_type_wf_rec] at hKWf
    rw [hb] at hbK
    exact hKNN hbK.symm

theorem smt_store_type_none_of_second_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.store a b c) = SmtType.None := by
  intro hb
  by_cases hNone : __smtx_typeof (SmtTerm.store a b c) = SmtType.None
  · exact hNone
  · exfalso
    have hTerm : term_has_non_none_type (SmtTerm.store a b c) := by
      unfold term_has_non_none_type
      exact hNone
    rcases store_args_of_non_none hTerm with ⟨K, V, ha, hbK, _hcV⟩
    have hKWf :
        __smtx_type_wf_rec K native_reflist_nil = true :=
      (smt_map_components_wf_rec_of_non_none_type a K V ha).1
    have hKNN : K ≠ SmtType.None := by
      intro hK
      rw [hK] at hKWf
      simp [__smtx_type_wf_rec] at hKWf
    rw [hb] at hbK
    exact hKNN hbK.symm

theorem smt_str_substr_type_none_of_second_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.str_substr a b c) = SmtType.None := by
  intro hb
  rw [typeof_str_substr_eq, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_str_substr_type_none_of_third_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (SmtTerm.str_substr a b c) = SmtType.None := by
  intro hc
  rw [typeof_str_substr_eq, hc]
  simp [__smtx_typeof_str_substr]

theorem smt_str_indexof_type_none_of_second_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.str_indexof a b c) = SmtType.None := by
  intro hb
  rw [typeof_str_indexof_eq, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_str_update_type_none_of_second_arg_none
    (a b c : SmtTerm) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (SmtTerm.str_update a b c) = SmtType.None := by
  intro hb
  rw [typeof_str_update_eq, hb]
  cases __smtx_typeof a <;> rfl

theorem smt_seq_triop_type_none_of_second_arg_none
    (op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (a b c : SmtTerm)
    (hTy :
      ∀ a b c,
        __smtx_typeof (op a b c) =
          __smtx_typeof_seq_op_3
            (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c)) :
    __smtx_typeof b = SmtType.None ->
    __smtx_typeof (op a b c) = SmtType.None := by
  intro hb
  rw [hTy a b c, hb]
  cases __smtx_typeof a <;> rfl

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

theorem smt_ite_type_none_of_cond_arg_none
    (c t e : SmtTerm) :
    __smtx_typeof c = SmtType.None ->
    __smtx_typeof (SmtTerm.ite c t e) = SmtType.None := by
  intro hc
  rw [smtx_typeof_ite_term_eq, hc]
  rfl

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

theorem smtx_typeof_eo_to_smt_apply_generic_none_of_arg_none
    (f x : Term)
    (hToSmt :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) = SmtType.None := by
  rw [hToSmt]
  exact smtx_typeof_apply_of_arg_none
    (__eo_to_smt f) (__eo_to_smt x) hx

theorem smtx_typeof_eo_to_smt_apply_uop1_none_of_arg_none
    (op : UserOp1) (idx x : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp1 op idx) x)) =
      SmtType.None := by
  cases op
  case «repeat» =>
    change
      __smtx_typeof
          (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_repeat_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case zero_extend =>
    change
      __smtx_typeof
          (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_zero_extend_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case sign_extend =>
    change
      __smtx_typeof
          (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_sign_extend_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case rotate_left =>
    change
      __smtx_typeof
          (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_rotate_left_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case rotate_right =>
    change
      __smtx_typeof
          (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_rotate_right_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case _at_bit =>
    change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x))
            (SmtTerm.Binary 1 1)) =
        SmtType.None
    have hExt :
        __smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)) =
          SmtType.None := by
      rw [typeof_extract_eq, hx]
      cases __eo_to_smt idx <;> rfl
    rw [typeof_eq_eq, hExt]
    rfl
  case re_exp =>
    change
      __smtx_typeof
          (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_re_exp_eq, hx]
    cases __eo_to_smt idx <;> rfl
  case is =>
    change
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx))
            (__eo_to_smt x)) =
        SmtType.None
    exact smtx_typeof_apply_of_arg_none
      (__eo_to_smt_tester (__eo_to_smt idx)) (__eo_to_smt x) hx
  case tuple_select =>
    change
      __smtx_typeof
          (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt x))
            (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [hx]
    simp [__eo_to_smt_tuple_select]
  case int_to_bv =>
    change
      __smtx_typeof
          (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_int_to_bv_eq, hx]
    cases __eo_to_smt idx <;> rfl
  all_goals
    exact smtx_typeof_eo_to_smt_apply_generic_none_of_arg_none
      _ _ (by rfl) hx

theorem smtx_typeof_eo_to_smt_apply_uop2_none_of_arg_none
    (op : UserOp2) (idx₁ idx₂ x : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.None) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp2 op idx₁ idx₂) x)) =
      SmtType.None := by
  cases op
  case extract =>
    change
      __smtx_typeof
          (SmtTerm.extract (__eo_to_smt idx₁) (__eo_to_smt idx₂)
            (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_extract_eq, hx]
    cases __eo_to_smt idx₁ <;> cases __eo_to_smt idx₂ <;> rfl
  case re_loop =>
    change
      __smtx_typeof
          (SmtTerm.re_loop (__eo_to_smt idx₁) (__eo_to_smt idx₂)
            (__eo_to_smt x)) =
        SmtType.None
    rw [typeof_re_loop_eq, hx]
    cases __eo_to_smt idx₁ <;> cases __eo_to_smt idx₂ <;> rfl
  all_goals
    exact smtx_typeof_eo_to_smt_apply_generic_none_of_arg_none
      _ _ (by rfl) hx

theorem smtx_typeof_eo_to_smt_apply_uop1_binderListCons_none
    (op : UserOp1) (idx x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 op idx) (eoBinderListCons x xs))) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_apply_uop1_none_of_arg_none op idx
    (eoBinderListCons x xs)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_uop2_binderListCons_none
    (op : UserOp2) (idx₁ idx₂ x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp2 op idx₁ idx₂)
            (eoBinderListCons x xs))) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_apply_uop2_none_of_arg_none op idx₁ idx₂
    (eoBinderListCons x xs)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_uop3_binderListCons_none
    (op : UserOp3) (idx₁ idx₂ idx₃ x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp3 op idx₁ idx₂ idx₃)
            (eoBinderListCons x xs))) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_apply_generic_none_of_arg_none
    (Term.UOp3 op idx₁ idx₂ idx₃) (eoBinderListCons x xs)
    (by rfl)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

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

theorem smtx_typeof_eo_to_smt_binderShape_uop2_none
    (op : UserOp2) (idx₁ idx₂ x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp2 op idx₁ idx₂) x xs body)) =
      SmtType.None := by
  exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
    (Term.UOp2 op idx₁ idx₂) x xs body
    (by rfl)
    (by
      intro s d i j hEq
      cases op <;>
        dsimp [__eo_to_smt, eoBinderListCons] at hEq <;>
        cases hEq)
    (by
      intro s d i hEq
      cases op <;>
        dsimp [__eo_to_smt, eoBinderListCons] at hEq <;>
        cases hEq)
    (smtx_typeof_eo_to_smt_apply_uop2_binderListCons_none
      op idx₁ idx₂ x xs)

theorem smtx_typeof_eo_to_smt_binderShape_uop3_none
    (op : UserOp3) (idx₁ idx₂ idx₃ x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp3 op idx₁ idx₂ idx₃) x xs body)) =
      SmtType.None := by
  exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
    (Term.UOp3 op idx₁ idx₂ idx₃) x xs body
    (by rfl)
    (by
      intro s d i j hEq
      change
        SmtTerm.Apply
            (__eo_to_smt (Term.UOp3 op idx₁ idx₂ idx₃))
            (__eo_to_smt (eoBinderListCons x xs)) ≠
          SmtTerm.DtSel s d i j at hEq
      cases hEq)
    (by
      intro s d i hEq
      change
        SmtTerm.Apply
            (__eo_to_smt (Term.UOp3 op idx₁ idx₂ idx₃))
            (__eo_to_smt (eoBinderListCons x xs)) ≠
          SmtTerm.DtTester s d i at hEq
      cases hEq)
    (smtx_typeof_eo_to_smt_apply_uop3_binderListCons_none
      op idx₁ idx₂ idx₃ x xs)

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

theorem smtx_typeof_eo_to_smt_binderShape_arith_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_arith_overload_binop_type_none_of_first_arg_none op
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_arith_ret_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_arith_overload_ret_binop_type_none_of_first_arg_none op R
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_int_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Int)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.Int)
              R SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_int_binop_type_none_of_first_arg_none op R
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_bv_binop_type_none_of_first_arg_none op
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_bv_binop_ret_type_none_of_first_arg_none op R
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_seq_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_seq_binop_type_none_of_first_arg_none op
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_seq_ret_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_seq_binop_ret_type_none_of_first_arg_none op R
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_seq_char_binop_first_none'
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
              R SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_seq_char_binop_type_none_of_first_arg_none op R
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_set_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_set_binop_type_none_of_first_arg_none op
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_set_ret_binop_first_none
    (q x xs body : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (eoBinderShape q x xs body) =
        op (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof (__eo_to_smt (eoBinderShape q x xs body)) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_set_binop_ret_type_none_of_first_arg_none op R
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

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

theorem smtx_typeof_eo_to_smt_apply_apply_bool_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hArg :
      __smtx_typeof
            (op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))) ≠
          SmtType.None ->
        __smtx_typeof (__eo_to_smt (eoBinderListCons x xs)) =
          SmtType.Bool) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_bool_binop_type_none_of_second_arg_none op
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hArg (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_arith_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_arith_overload_binop_type_none_of_second_arg_none op
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_arith_ret_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_arith_overload_ret_binop_type_none_of_second_arg_none op R
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_int_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Int)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.Int)
              R SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_int_binop_type_none_of_second_arg_none op R
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_bv_binop_type_none_of_second_arg_none op
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_bv_binop_ret_type_none_of_second_arg_none op R
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_seq_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_seq_binop_type_none_of_second_arg_none op
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_seq_ret_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_seq_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_seq_binop_ret_type_none_of_second_arg_none op R
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_seq_char_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite
            (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof b) (SmtType.Seq SmtType.Char))
              R SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_seq_char_binop_type_none_of_second_arg_none op R
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_set_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2
            (__smtx_typeof a) (__smtx_typeof b)) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_set_binop_type_none_of_second_arg_none op
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_set_ret_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm) (R : SmtType)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_sets_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_set_binop_ret_type_none_of_second_arg_none op R
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    hTy (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_reglan_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_reglan_binop_type_none_of_second_arg_none op hTy
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_apply_apply_seq_char_reglan_binop_second_none
    (q a x xs : Term)
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      __eo_to_smt (Term.Apply q (eoBinderListCons x xs)) =
        op (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs)))
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) (SmtType.Seq SmtType.Char))
            (native_ite (native_Teq (__smtx_typeof b) SmtType.RegLan)
              SmtType.Bool SmtType.None)
            SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply q (eoBinderListCons x xs))) =
      SmtType.None := by
  rw [hToSmt]
  exact smt_seq_char_reglan_binop_type_none_of_second_arg_none op hTy
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
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

theorem smtx_typeof_eo_to_smt_apply_uop_binderListCons_none
    (op : UserOp) (x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp op) (eoBinderListCons x xs))) =
      SmtType.None := by
  cases op
  case not =>
    exact smtx_typeof_eo_to_smt_apply_not_binderListCons_none x xs
  case distinct =>
    exact smtx_typeof_eo_to_smt_apply_distinct_binderListCons_none x xs
  case _at_purify =>
    change
      __smtx_typeof
          (SmtTerm._at_purify (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [__smtx_typeof.eq_def] <;> simp only
    exact smtx_typeof_eo_to_smt_binderListCons_none x xs
  case to_real =>
    change
      __smtx_typeof
          (SmtTerm.to_real (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_to_real_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case to_int =>
    change
      __smtx_typeof
          (SmtTerm.to_int (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_to_int_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case is_int =>
    change
      __smtx_typeof
          (SmtTerm.is_int (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_is_int_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case abs =>
    change
      __smtx_typeof
          (SmtTerm.abs (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_abs_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case __eoo_neg_2 =>
    change
      __smtx_typeof
          (SmtTerm.uneg (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_uneg_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case int_pow2 =>
    change
      __smtx_typeof
          (SmtTerm.int_pow2 (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_int_pow2_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case int_log2 =>
    change
      __smtx_typeof
          (SmtTerm.int_log2 (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_int_log2_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case int_ispow2 =>
    let t := __eo_to_smt (eoBinderListCons x xs)
    have ht : __smtx_typeof t = SmtType.None :=
      smtx_typeof_eo_to_smt_binderListCons_none x xs
    change
      __smtx_typeof
          (SmtTerm.and (SmtTerm.geq t (SmtTerm.Numeral 0))
            (SmtTerm.eq t
              (SmtTerm.int_pow2 (SmtTerm.int_log2 t)))) =
        SmtType.None
    have hGeq :
        __smtx_typeof (SmtTerm.geq t (SmtTerm.Numeral 0)) =
          SmtType.None := by
      rw [typeof_geq_eq, ht]
      rfl
    rw [typeof_and_eq, hGeq]
    rfl
  case _at_int_div_by_zero =>
    change
      __smtx_typeof
          (SmtTerm.div (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.Numeral 0)) =
        SmtType.None
    rw [typeof_div_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case _at_mod_by_zero =>
    change
      __smtx_typeof
          (SmtTerm.mod (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.Numeral 0)) =
        SmtType.None
    rw [typeof_mod_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case _at_bvsize =>
    change
      __smtx_typeof
          (native_ite
            (native_zleq 0
              (__smtx_bv_sizeof_type
                (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs)))))
            (SmtTerm._at_purify
              (SmtTerm.Numeral
                (__smtx_bv_sizeof_type
                  (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs))))))
            SmtTerm.None) =
        SmtType.None
    rw [smtx_typeof_eo_to_smt_binderListCons_none]
    have hLe :
        native_zleq 0 (__smtx_bv_sizeof_type SmtType.None) = false := by
      rfl
    rw [hLe]
    simp [native_ite]
  case bvnot =>
    change
      __smtx_typeof
          (SmtTerm.bvnot (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [__smtx_typeof.eq_def] <;> simp only
    rw [smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case bvneg =>
    change
      __smtx_typeof
          (SmtTerm.bvneg (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [__smtx_typeof.eq_def] <;> simp only
    rw [smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case bvnego =>
    change
      __smtx_typeof
          (SmtTerm.bvnego (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [__smtx_typeof.eq_def] <;> simp only
    rw [smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case bvredand =>
    let t := __eo_to_smt (eoBinderListCons x xs)
    have ht : __smtx_typeof t = SmtType.None :=
      smtx_typeof_eo_to_smt_binderListCons_none x xs
    change
      __smtx_typeof
          (SmtTerm.bvcomp t
            (SmtTerm.bvnot
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof t))
                0))) =
        SmtType.None
    rw [__smtx_typeof.eq_def] <;> simp only
    rw [ht]
    rfl
  case bvredor =>
    let t := __eo_to_smt (eoBinderListCons x xs)
    have ht : __smtx_typeof t = SmtType.None :=
      smtx_typeof_eo_to_smt_binderListCons_none x xs
    change
      __smtx_typeof
          (SmtTerm.bvnot
            (SmtTerm.bvcomp t
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof t))
                0))) =
        SmtType.None
    have hComp :
        __smtx_typeof
            (SmtTerm.bvcomp t
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof t))
                0)) =
          SmtType.None := by
      rw [__smtx_typeof.eq_def] <;> simp only
      rw [ht]
      rfl
    rw [__smtx_typeof.eq_def] <;> simp only
    rw [hComp]
    rfl
  case str_len =>
    change
      __smtx_typeof
          (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_len_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_rev =>
    change
      __smtx_typeof
          (SmtTerm.str_rev (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_rev_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_to_lower =>
    change
      __smtx_typeof
          (SmtTerm.str_to_lower (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_to_lower_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_to_upper =>
    change
      __smtx_typeof
          (SmtTerm.str_to_upper (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_to_upper_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_to_code =>
    change
      __smtx_typeof
          (SmtTerm.str_to_code (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_to_code_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_from_code =>
    change
      __smtx_typeof
          (SmtTerm.str_from_code (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_from_code_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_is_digit =>
    change
      __smtx_typeof
          (SmtTerm.str_is_digit (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_is_digit_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_to_int =>
    change
      __smtx_typeof
          (SmtTerm.str_to_int (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_to_int_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_from_int =>
    change
      __smtx_typeof
          (SmtTerm.str_from_int (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_from_int_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case str_to_re =>
    change
      __smtx_typeof
          (SmtTerm.str_to_re (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_to_re_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case re_mult =>
    change
      __smtx_typeof
          (SmtTerm.re_mult (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_re_mult_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case re_plus =>
    change
      __smtx_typeof
          (SmtTerm.re_plus (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_re_plus_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case re_opt =>
    change
      __smtx_typeof
          (SmtTerm.re_opt (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_re_opt_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case re_comp =>
    change
      __smtx_typeof
          (SmtTerm.re_comp (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_re_comp_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case seq_unit =>
    change
      __smtx_typeof
          (SmtTerm.seq_unit (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [smtx_typeof_seq_unit_term_eq,
      smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case _at_strings_stoi_non_digit =>
    change
      __smtx_typeof
          (SmtTerm.str_indexof_re (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.re_comp
              (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
                (SmtTerm.String (native_string_lit "9"))))
            (SmtTerm.Numeral 0)) =
        SmtType.None
    rw [typeof_str_indexof_re_eq,
      smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case set_singleton =>
    change
      __smtx_typeof
          (SmtTerm.set_singleton (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [smtx_typeof_set_singleton_term_eq,
      smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case set_choose =>
    let t := __eo_to_smt (eoBinderListCons x xs)
    have ht : __smtx_typeof t = SmtType.None :=
      smtx_typeof_eo_to_smt_binderListCons_none x xs
    change
      __smtx_typeof
          (SmtTerm.map_diff t
            (SmtTerm.set_empty
              (__eo_to_smt_set_elem_type (__smtx_typeof t)))) =
        SmtType.None
    rw [typeof_map_diff_eq, ht]
    rfl
  case set_is_empty =>
    let t := __eo_to_smt (eoBinderListCons x xs)
    have ht : __smtx_typeof t = SmtType.None :=
      smtx_typeof_eo_to_smt_binderListCons_none x xs
    change
      __smtx_typeof
          (SmtTerm.eq t (SmtTerm.set_empty (__smtx_typeof t))) =
        SmtType.None
    exact smt_eq_type_none_of_first_arg_none t
      (SmtTerm.set_empty (__smtx_typeof t)) ht
  case set_is_singleton =>
    let t := __eo_to_smt (eoBinderListCons x xs)
    have ht : __smtx_typeof t = SmtType.None :=
      smtx_typeof_eo_to_smt_binderListCons_none x xs
    change
      __smtx_typeof
          (SmtTerm.eq t
            (SmtTerm.set_singleton
              (SmtTerm.map_diff t
                (SmtTerm.set_empty
                  (__eo_to_smt_set_elem_type (__smtx_typeof t)))))) =
        SmtType.None
    exact smt_eq_type_none_of_first_arg_none t
      (SmtTerm.set_singleton
        (SmtTerm.map_diff t
          (SmtTerm.set_empty
            (__eo_to_smt_set_elem_type (__smtx_typeof t))))) ht
  case _at_div_by_zero =>
    change
      __smtx_typeof
          (SmtTerm.qdiv (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.Rational (native_mk_rational 0 1))) =
        SmtType.None
    rw [typeof_qdiv_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case ubv_to_int =>
    change
      __smtx_typeof
          (SmtTerm.ubv_to_int (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [smtx_typeof_ubv_to_int_term_eq,
      smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  case sbv_to_int =>
    change
      __smtx_typeof
          (SmtTerm.sbv_to_int (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [__smtx_typeof.eq_def] <;> simp only
    rw [smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  all_goals
    exact smtx_typeof_eo_to_smt_apply_binderListCons_generic_none
      _ x xs (by rfl)

theorem smtx_typeof_eo_to_smt_apply_apply_forall_binderListCons_none
    (a x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) a)
            (eoBinderListCons x xs))) =
      SmtType.None := by
  by_cases ha : a = Term.__eo_List_nil
  · subst a
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  · cases a
    all_goals
      first
      | exact False.elim (ha rfl)
      | change
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists _
                  (SmtTerm.not (__eo_to_smt (eoBinderListCons x xs))))) =
            SmtType.None
        have hNot :
            __smtx_typeof
                (SmtTerm.not (__eo_to_smt (eoBinderListCons x xs))) =
              SmtType.None := by
          rw [typeof_not_eq, smtx_typeof_eo_to_smt_binderListCons_none]
          rfl
        rw [typeof_not_eq,
          smtx_typeof_eo_to_smt_exists_of_body_none _
            (SmtTerm.not (__eo_to_smt (eoBinderListCons x xs))) hNot]
        rfl

theorem smtx_typeof_eo_to_smt_apply_apply_exists_binderListCons_none
    (a x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.exists) a)
            (eoBinderListCons x xs))) =
      SmtType.None := by
  by_cases ha : a = Term.__eo_List_nil
  · subst a
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  · cases a
    all_goals
      first
      | exact False.elim (ha rfl)
      | change
          __smtx_typeof
              (__eo_to_smt_exists _ (__eo_to_smt (eoBinderListCons x xs))) =
            SmtType.None
        exact smtx_typeof_eo_to_smt_exists_of_body_none _
          (__eo_to_smt (eoBinderListCons x xs))
          (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem eo_to_smt_apply_apply_forall_binderListCons_ne_dt_sel
    (a x xs : Term) :
    ∀ s d i j,
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) a)
            (eoBinderListCons x xs)) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j
  by_cases ha : a = Term.__eo_List_nil
  · subst a
    change SmtTerm.None ≠ SmtTerm.DtSel s d i j
    intro h
    cases h
  · cases a
    all_goals
      first
      | exact False.elim (ha rfl)
      | change
          SmtTerm.not
              (__eo_to_smt_exists _
                (SmtTerm.not (__eo_to_smt (eoBinderListCons x xs)))) ≠
            SmtTerm.DtSel s d i j
        intro h
        cases h

theorem eo_to_smt_apply_apply_forall_binderListCons_ne_dt_tester
    (a x xs : Term) :
    ∀ s d i,
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) a)
            (eoBinderListCons x xs)) ≠
        SmtTerm.DtTester s d i := by
  intro s d i
  by_cases ha : a = Term.__eo_List_nil
  · subst a
    change SmtTerm.None ≠ SmtTerm.DtTester s d i
    intro h
    cases h
  · cases a
    all_goals
      first
      | exact False.elim (ha rfl)
      | change
          SmtTerm.not
              (__eo_to_smt_exists _
                (SmtTerm.not (__eo_to_smt (eoBinderListCons x xs)))) ≠
            SmtTerm.DtTester s d i
        intro h
        cases h

theorem eo_to_smt_apply_apply_exists_binderListCons_ne_dt_sel
    (a x xs : Term) :
    ∀ s d i j,
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.exists) a)
            (eoBinderListCons x xs)) ≠
        SmtTerm.DtSel s d i j := by
  intro s d i j
  by_cases ha : a = Term.__eo_List_nil
  · subst a
    change SmtTerm.None ≠ SmtTerm.DtSel s d i j
    intro h
    cases h
  · cases a
    all_goals
      first
      | exact False.elim (ha rfl)
      | change
          __eo_to_smt_exists _ (__eo_to_smt (eoBinderListCons x xs)) ≠
            SmtTerm.DtSel s d i j
        exact eo_to_smt_exists_binderListCons_ne_dt_sel
          _ x xs s d i j

theorem eo_to_smt_apply_apply_exists_binderListCons_ne_dt_tester
    (a x xs : Term) :
    ∀ s d i,
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.exists) a)
            (eoBinderListCons x xs)) ≠
        SmtTerm.DtTester s d i := by
  intro s d i
  by_cases ha : a = Term.__eo_List_nil
  · subst a
    change SmtTerm.None ≠ SmtTerm.DtTester s d i
    intro h
    cases h
  · cases a
    all_goals
      first
      | exact False.elim (ha rfl)
      | change
          __eo_to_smt_exists _ (__eo_to_smt (eoBinderListCons x xs)) ≠
            SmtTerm.DtTester s d i
        exact eo_to_smt_exists_binderListCons_ne_dt_tester
          _ x xs s d i

theorem smtx_typeof_eo_to_smt_apply_apply_uop_binderListCons_none
    (op : UserOp) (a x xs : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp op) a)
            (eoBinderListCons x xs))) =
      SmtType.None := by
  cases op
  case «forall» =>
    exact smtx_typeof_eo_to_smt_apply_apply_forall_binderListCons_none
      a x xs
  case «exists» =>
    exact smtx_typeof_eo_to_smt_apply_apply_exists_binderListCons_none
      a x xs
  case or =>
    exact smtx_typeof_eo_to_smt_apply_apply_bool_binop_second_none
      (Term.Apply (Term.UOp UserOp.or) a) a x xs SmtTerm.or (by rfl)
      (fun h =>
        (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
          (typeof_or_eq (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs)))
          (by
            unfold term_has_non_none_type
            exact h)).2)
  case and =>
    exact smtx_typeof_eo_to_smt_apply_apply_bool_binop_second_none
      (Term.Apply (Term.UOp UserOp.and) a) a x xs SmtTerm.and (by rfl)
      (fun h =>
        (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs)))
          (by
            unfold term_has_non_none_type
            exact h)).2)
  case imp =>
    exact smtx_typeof_eo_to_smt_apply_apply_bool_binop_second_none
      (Term.Apply (Term.UOp UserOp.imp) a) a x xs SmtTerm.imp (by rfl)
      (fun h =>
        (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
          (typeof_imp_eq (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs)))
          (by
            unfold term_has_non_none_type
            exact h)).2)
  case xor =>
    exact smtx_typeof_eo_to_smt_apply_apply_bool_binop_second_none
      (Term.Apply (Term.UOp UserOp.xor) a) a x xs SmtTerm.xor (by rfl)
      (fun h =>
        (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
          (typeof_xor_eq (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs)))
          (by
            unfold term_has_non_none_type
            exact h)).2)
  case eq =>
    change
      __smtx_typeof
          (SmtTerm.eq (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    exact smt_eq_type_none_of_second_arg_none
      (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case plus =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_binop_second_none
      (Term.Apply (Term.UOp UserOp.plus) a) a x xs SmtTerm.plus
      (by rfl) (fun a b => typeof_plus_eq a b)
  case neg =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_binop_second_none
      (Term.Apply (Term.UOp UserOp.neg) a) a x xs SmtTerm.neg
      (by rfl) (fun a b => typeof_neg_eq a b)
  case mult =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_binop_second_none
      (Term.Apply (Term.UOp UserOp.mult) a) a x xs SmtTerm.mult
      (by rfl) (fun a b => typeof_mult_eq a b)
  case lt =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.lt) a) a x xs SmtTerm.lt
      SmtType.Bool (by rfl) (fun a b => typeof_lt_eq a b)
  case leq =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.leq) a) a x xs SmtTerm.leq
      SmtType.Bool (by rfl) (fun a b => typeof_leq_eq a b)
  case gt =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.gt) a) a x xs SmtTerm.gt
      SmtType.Bool (by rfl) (fun a b => typeof_gt_eq a b)
  case geq =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.geq) a) a x xs SmtTerm.geq
      SmtType.Bool (by rfl) (fun a b => typeof_geq_eq a b)
  case div =>
    exact smtx_typeof_eo_to_smt_apply_apply_int_binop_second_none
      (Term.Apply (Term.UOp UserOp.div) a) a x xs SmtTerm.div
      SmtType.Int (by rfl) (fun a b => typeof_div_eq a b)
  case mod =>
    exact smtx_typeof_eo_to_smt_apply_apply_int_binop_second_none
      (Term.Apply (Term.UOp UserOp.mod) a) a x xs SmtTerm.mod
      SmtType.Int (by rfl) (fun a b => typeof_mod_eq a b)
  case multmult =>
    exact smtx_typeof_eo_to_smt_apply_apply_int_binop_second_none
      (Term.Apply (Term.UOp UserOp.multmult) a) a x xs
      SmtTerm.multmult SmtType.Int (by rfl)
      (fun a b => typeof_multmult_eq a b)
  case divisible =>
    exact smtx_typeof_eo_to_smt_apply_apply_int_binop_second_none
      (Term.Apply (Term.UOp UserOp.divisible) a) a x xs
      SmtTerm.divisible SmtType.Bool (by rfl)
      (fun a b => typeof_divisible_eq a b)
  case div_total =>
    exact smtx_typeof_eo_to_smt_apply_apply_int_binop_second_none
      (Term.Apply (Term.UOp UserOp.div_total) a) a x xs
      SmtTerm.div_total SmtType.Int (by rfl)
      (fun a b => typeof_div_total_eq a b)
  case mod_total =>
    exact smtx_typeof_eo_to_smt_apply_apply_int_binop_second_none
      (Term.Apply (Term.UOp UserOp.mod_total) a) a x xs
      SmtTerm.mod_total SmtType.Int (by rfl)
      (fun a b => typeof_mod_total_eq a b)
  case multmult_total =>
    exact smtx_typeof_eo_to_smt_apply_apply_int_binop_second_none
      (Term.Apply (Term.UOp UserOp.multmult_total) a) a x xs
      SmtTerm.multmult_total SmtType.Int (by rfl)
      (fun a b => typeof_multmult_total_eq a b)
  case select =>
    change
      __smtx_typeof
          (SmtTerm.select (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    exact smt_select_type_none_of_second_arg_none
      (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case _at_array_deq_diff =>
    change
      __smtx_typeof
          (__eo_to_smt_array_deq_diff (__eo_to_smt a)
            (__smtx_typeof (__eo_to_smt a))
            (__eo_to_smt (eoBinderListCons x xs))
            (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs)))) =
        SmtType.None
    exact smt_array_deq_diff_type_none_of_second_arg_none
      (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case concat =>
    change
      __smtx_typeof
          (SmtTerm.concat (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    exact smt_concat_type_none_of_second_arg_none
      (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case bvand =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvand) a) a x xs SmtTerm.bvand
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_39])
  case bvor =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvor) a) a x xs SmtTerm.bvor
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_40])
  case bvnand =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvnand) a) a x xs SmtTerm.bvnand
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_41])
  case bvnor =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvnor) a) a x xs SmtTerm.bvnor
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_42])
  case bvxor =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvxor) a) a x xs SmtTerm.bvxor
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_43])
  case bvxnor =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvxnor) a) a x xs SmtTerm.bvxnor
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_44])
  case bvcomp =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvcomp) a) a x xs SmtTerm.bvcomp
      (SmtType.BitVec 1) (by rfl) (fun a b => by rw [__smtx_typeof.eq_45])
  case bvadd =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvadd) a) a x xs SmtTerm.bvadd
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_47])
  case bvmul =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvmul) a) a x xs SmtTerm.bvmul
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_48])
  case bvudiv =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvudiv) a) a x xs SmtTerm.bvudiv
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_49])
  case bvurem =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvurem) a) a x xs SmtTerm.bvurem
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_50])
  case bvsub =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsub) a) a x xs SmtTerm.bvsub
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_51])
  case bvsdiv =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsdiv) a) a x xs SmtTerm.bvsdiv
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_52])
  case bvsrem =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsrem) a) a x xs SmtTerm.bvsrem
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_53])
  case bvsmod =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsmod) a) a x xs SmtTerm.bvsmod
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_54])
  case bvult =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvult) a) a x xs SmtTerm.bvult
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_55])
  case bvule =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvule) a) a x xs SmtTerm.bvule
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_56])
  case bvugt =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvugt) a) a x xs SmtTerm.bvugt
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_57])
  case bvuge =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvuge) a) a x xs SmtTerm.bvuge
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_58])
  case bvslt =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvslt) a) a x xs SmtTerm.bvslt
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_59])
  case bvsle =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsle) a) a x xs SmtTerm.bvsle
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_60])
  case bvsgt =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsgt) a) a x xs SmtTerm.bvsgt
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_61])
  case bvsge =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsge) a) a x xs SmtTerm.bvsge
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_62])
  case bvshl =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvshl) a) a x xs SmtTerm.bvshl
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_63])
  case bvlshr =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvlshr) a) a x xs SmtTerm.bvlshr
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_64])
  case bvashr =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvashr) a) a x xs SmtTerm.bvashr
      (by rfl) (fun a b => by rw [__smtx_typeof.eq_65])
  case bvuaddo =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvuaddo) a) a x xs SmtTerm.bvuaddo
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_70])
  case bvsaddo =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsaddo) a) a x xs SmtTerm.bvsaddo
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_72])
  case bvumulo =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvumulo) a) a x xs SmtTerm.bvumulo
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_73])
  case bvsmulo =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsmulo) a) a x xs SmtTerm.bvsmulo
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_74])
  case bvusubo =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvusubo) a) a x xs SmtTerm.bvusubo
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_75])
  case bvssubo =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvssubo) a) a x xs SmtTerm.bvssubo
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_76])
  case bvsdivo =>
    exact smtx_typeof_eo_to_smt_apply_apply_bv_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.bvsdivo) a) a x xs SmtTerm.bvsdivo
      SmtType.Bool (by rfl) (fun a b => by rw [__smtx_typeof.eq_77])
  case bvultbv =>
    change
      __smtx_typeof
          (SmtTerm.ite
            (SmtTerm.bvult (__eo_to_smt a)
              (__eo_to_smt (eoBinderListCons x xs)))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
        SmtType.None
    have hCond :
        __smtx_typeof
            (SmtTerm.bvult (__eo_to_smt a)
              (__eo_to_smt (eoBinderListCons x xs))) =
          SmtType.None :=
      smt_bv_binop_ret_type_none_of_second_arg_none SmtTerm.bvult
        SmtType.Bool (__eo_to_smt a)
        (__eo_to_smt (eoBinderListCons x xs))
        (fun a b => by rw [__smtx_typeof.eq_55])
        (smtx_typeof_eo_to_smt_binderListCons_none x xs)
    exact smt_ite_type_none_of_cond_arg_none
      (SmtTerm.bvult (__eo_to_smt a)
        (__eo_to_smt (eoBinderListCons x xs)))
      (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0) hCond
  case bvsltbv =>
    change
      __smtx_typeof
          (SmtTerm.ite
            (SmtTerm.bvslt (__eo_to_smt a)
              (__eo_to_smt (eoBinderListCons x xs)))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
        SmtType.None
    have hCond :
        __smtx_typeof
            (SmtTerm.bvslt (__eo_to_smt a)
              (__eo_to_smt (eoBinderListCons x xs))) =
          SmtType.None :=
      smt_bv_binop_ret_type_none_of_second_arg_none SmtTerm.bvslt
        SmtType.Bool (__eo_to_smt a)
        (__eo_to_smt (eoBinderListCons x xs))
        (fun a b => by rw [__smtx_typeof.eq_59])
        (smtx_typeof_eo_to_smt_binderListCons_none x xs)
    exact smt_ite_type_none_of_cond_arg_none
      (SmtTerm.bvslt (__eo_to_smt a)
        (__eo_to_smt (eoBinderListCons x xs)))
      (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0) hCond
  case _at_from_bools =>
    change
      __smtx_typeof
          (SmtTerm.concat
            (SmtTerm.ite (__eo_to_smt a)
              (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    exact smt_concat_type_none_of_second_arg_none
      (SmtTerm.ite (__eo_to_smt a)
        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
      (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case str_concat =>
    exact smtx_typeof_eo_to_smt_apply_apply_seq_binop_second_none
      (Term.Apply (Term.UOp UserOp.str_concat) a) a x xs
      SmtTerm.str_concat (by rfl) (fun a b => typeof_str_concat_eq a b)
  case _at_strings_deq_diff =>
    change
      __smtx_typeof
          (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
            (SmtTerm.not
              (SmtTerm.eq
                (SmtTerm.str_substr (__eo_to_smt a)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))
                (SmtTerm.str_substr (__eo_to_smt (eoBinderListCons x xs))
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))))
            native_nat_zero) =
        SmtType.None
    have hRightSub :
        __smtx_typeof
            (SmtTerm.str_substr (__eo_to_smt (eoBinderListCons x xs))
              (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
              (SmtTerm.Numeral 1)) =
          SmtType.None := by
      rw [typeof_str_substr_eq,
        smtx_typeof_eo_to_smt_binderListCons_none]
      cases __smtx_typeof
          (SmtTerm.Var (native_string_lit "@x") SmtType.Int) <;>
        rfl
    have hBody :
        __smtx_typeof
            (SmtTerm.not
              (SmtTerm.eq
                (SmtTerm.str_substr (__eo_to_smt a)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))
                (SmtTerm.str_substr (__eo_to_smt (eoBinderListCons x xs))
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1)))) =
          SmtType.None := by
      rw [typeof_not_eq, typeof_eq_eq, hRightSub]
      cases __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt a)
            (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
            (SmtTerm.Numeral 1)) <;>
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
          native_Teq]
    rw [smtx_typeof_choice_nth_term_eq]
    simp [__smtx_typeof_choice_nth, hBody, native_ite, native_Teq]
  case str_contains =>
    exact smtx_typeof_eo_to_smt_apply_apply_seq_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.str_contains) a) a x xs
      SmtTerm.str_contains SmtType.Bool (by rfl)
      (fun a b => typeof_str_contains_eq a b)
  case str_at =>
    change
      __smtx_typeof
          (SmtTerm.str_at (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_str_at_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    cases __smtx_typeof (__eo_to_smt a) <;> rfl
  case str_prefixof =>
    exact smtx_typeof_eo_to_smt_apply_apply_seq_char_binop_second_none
      (Term.Apply (Term.UOp UserOp.str_prefixof) a) a x xs
      SmtTerm.str_prefixof SmtType.Bool (by rfl)
      (fun a b => typeof_str_prefixof_eq a b)
  case str_suffixof =>
    exact smtx_typeof_eo_to_smt_apply_apply_seq_char_binop_second_none
      (Term.Apply (Term.UOp UserOp.str_suffixof) a) a x xs
      SmtTerm.str_suffixof SmtType.Bool (by rfl)
      (fun a b => typeof_str_suffixof_eq a b)
  case str_lt =>
    exact smtx_typeof_eo_to_smt_apply_apply_seq_char_binop_second_none
      (Term.Apply (Term.UOp UserOp.str_lt) a) a x xs
      SmtTerm.str_lt SmtType.Bool (by rfl)
      (fun a b => typeof_str_lt_eq a b)
  case str_leq =>
    exact smtx_typeof_eo_to_smt_apply_apply_seq_char_binop_second_none
      (Term.Apply (Term.UOp UserOp.str_leq) a) a x xs
      SmtTerm.str_leq SmtType.Bool (by rfl)
      (fun a b => typeof_str_leq_eq a b)
  case seq_nth =>
    change
      __smtx_typeof
          (SmtTerm.seq_nth (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    rw [typeof_seq_nth_eq, smtx_typeof_eo_to_smt_binderListCons_none]
    cases __smtx_typeof (__eo_to_smt a) <;> rfl
  case _at_strings_stoi_result =>
    change
      __smtx_typeof
          (SmtTerm.str_to_int
            (SmtTerm.str_substr (__eo_to_smt a)
              (SmtTerm.Numeral 0)
              (__eo_to_smt (eoBinderListCons x xs)))) =
        SmtType.None
    have hSub :
        __smtx_typeof
            (SmtTerm.str_substr (__eo_to_smt a)
              (SmtTerm.Numeral 0)
              (__eo_to_smt (eoBinderListCons x xs))) =
          SmtType.None := by
      exact smt_str_substr_type_none_of_third_arg_none
        (__eo_to_smt a) (SmtTerm.Numeral 0)
        (__eo_to_smt (eoBinderListCons x xs))
        (smtx_typeof_eo_to_smt_binderListCons_none x xs)
    rw [typeof_str_to_int_eq, hSub]
    rfl
  case _at_strings_itos_result =>
    change
      __smtx_typeof
          (SmtTerm.mod (__eo_to_smt a)
            (SmtTerm.multmult (SmtTerm.Numeral 10)
              (__eo_to_smt (eoBinderListCons x xs)))) =
        SmtType.None
    have hDen :
        __smtx_typeof
            (SmtTerm.multmult (SmtTerm.Numeral 10)
              (__eo_to_smt (eoBinderListCons x xs))) =
          SmtType.None :=
      smt_int_binop_type_none_of_second_arg_none SmtTerm.multmult
        SmtType.Int (SmtTerm.Numeral 10)
        (__eo_to_smt (eoBinderListCons x xs))
        (fun a b => typeof_multmult_eq a b)
        (smtx_typeof_eo_to_smt_binderListCons_none x xs)
    exact smt_int_binop_type_none_of_second_arg_none SmtTerm.mod
      SmtType.Int (__eo_to_smt a)
      (SmtTerm.multmult (SmtTerm.Numeral 10)
        (__eo_to_smt (eoBinderListCons x xs)))
      (fun a b => typeof_mod_eq a b) hDen
  case _at_strings_num_occur =>
    change
      __smtx_typeof
          (SmtTerm.div
            (SmtTerm.neg
              (SmtTerm.str_len (__eo_to_smt a))
              (SmtTerm.str_len
                (SmtTerm.str_replace_all (__eo_to_smt a)
                  (__eo_to_smt (eoBinderListCons x xs))
                  (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
            (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs)))) =
        SmtType.None
    have hDen :
        __smtx_typeof
            (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs))) =
          SmtType.None := by
      rw [typeof_str_len_eq,
        smtx_typeof_eo_to_smt_binderListCons_none]
      rfl
    exact smt_int_binop_type_none_of_second_arg_none SmtTerm.div
      SmtType.Int
      (SmtTerm.neg
        (SmtTerm.str_len (__eo_to_smt a))
        (SmtTerm.str_len
          (SmtTerm.str_replace_all (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
      (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs)))
      (fun a b => typeof_div_eq a b) hDen
  case re_range =>
    exact smtx_typeof_eo_to_smt_apply_apply_seq_char_binop_second_none
      (Term.Apply (Term.UOp UserOp.re_range) a) a x xs
      SmtTerm.re_range SmtType.RegLan (by rfl)
      (fun a b => typeof_re_range_eq a b)
  case re_concat =>
    exact smtx_typeof_eo_to_smt_apply_apply_reglan_binop_second_none
      (Term.Apply (Term.UOp UserOp.re_concat) a) a x xs
      SmtTerm.re_concat (by rfl) (fun a b => typeof_re_concat_eq a b)
  case re_inter =>
    exact smtx_typeof_eo_to_smt_apply_apply_reglan_binop_second_none
      (Term.Apply (Term.UOp UserOp.re_inter) a) a x xs
      SmtTerm.re_inter (by rfl) (fun a b => typeof_re_inter_eq a b)
  case re_union =>
    exact smtx_typeof_eo_to_smt_apply_apply_reglan_binop_second_none
      (Term.Apply (Term.UOp UserOp.re_union) a) a x xs
      SmtTerm.re_union (by rfl) (fun a b => typeof_re_union_eq a b)
  case re_diff =>
    exact smtx_typeof_eo_to_smt_apply_apply_reglan_binop_second_none
      (Term.Apply (Term.UOp UserOp.re_diff) a) a x xs
      SmtTerm.re_diff (by rfl) (fun a b => typeof_re_diff_eq a b)
  case str_in_re =>
    exact smtx_typeof_eo_to_smt_apply_apply_seq_char_reglan_binop_second_none
      (Term.Apply (Term.UOp UserOp.str_in_re) a) a x xs
      SmtTerm.str_in_re (by rfl) (fun a b => typeof_str_in_re_eq a b)
  case tuple =>
    change
      __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt a)
            (__smtx_typeof (__eo_to_smt a))
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    exact smt_tuple_prepend_type_none_of_tail_none
      (__eo_to_smt a) (__smtx_typeof (__eo_to_smt a))
      (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case set_union =>
    exact smtx_typeof_eo_to_smt_apply_apply_set_binop_second_none
      (Term.Apply (Term.UOp UserOp.set_union) a) a x xs
      SmtTerm.set_union (by rfl) (fun a b => typeof_set_union_eq a b)
  case set_inter =>
    exact smtx_typeof_eo_to_smt_apply_apply_set_binop_second_none
      (Term.Apply (Term.UOp UserOp.set_inter) a) a x xs
      SmtTerm.set_inter (by rfl) (fun a b => typeof_set_inter_eq a b)
  case set_minus =>
    exact smtx_typeof_eo_to_smt_apply_apply_set_binop_second_none
      (Term.Apply (Term.UOp UserOp.set_minus) a) a x xs
      SmtTerm.set_minus (by rfl) (fun a b => typeof_set_minus_eq a b)
  case set_member =>
    change
      __smtx_typeof
          (SmtTerm.set_member (__eo_to_smt a)
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    exact smt_set_member_type_none_of_second_arg_none
      (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case set_subset =>
    exact smtx_typeof_eo_to_smt_apply_apply_set_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.set_subset) a) a x xs
      SmtTerm.set_subset SmtType.Bool (by rfl)
      (fun a b => typeof_set_subset_eq a b)
  case set_insert =>
    change
      __smtx_typeof
          (__eo_to_smt_set_insert a
            (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None
    exact eo_to_smt_set_insert_type_none_of_base_none
      a (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case _at_sets_deq_diff =>
    change
      __smtx_typeof
          (__eo_to_smt_sets_deq_diff (__eo_to_smt a)
            (__smtx_typeof (__eo_to_smt a))
            (__eo_to_smt (eoBinderListCons x xs))
            (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs)))) =
        SmtType.None
    exact smt_sets_deq_diff_type_none_of_second_arg_none
      (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  case qdiv =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.qdiv) a) a x xs SmtTerm.qdiv
      SmtType.Real (by rfl) (fun a b => typeof_qdiv_eq a b)
  case qdiv_total =>
    exact smtx_typeof_eo_to_smt_apply_apply_arith_ret_binop_second_none
      (Term.Apply (Term.UOp UserOp.qdiv_total) a) a x xs
      SmtTerm.qdiv_total SmtType.Real (by rfl)
      (fun a b => typeof_qdiv_total_eq a b)
  all_goals
    exact smtx_typeof_eo_to_smt_apply_binderListCons_generic_none
      _ x xs (by rfl)

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

theorem smtx_typeof_eo_to_smt_binderShape_plus_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.plus) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_binop_first_none
    (Term.UOp UserOp.plus) x xs body SmtTerm.plus (by rfl)
    (fun a b => typeof_plus_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_neg_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.neg) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_binop_first_none
    (Term.UOp UserOp.neg) x xs body SmtTerm.neg (by rfl)
    (fun a b => typeof_neg_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_mult_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.mult) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_binop_first_none
    (Term.UOp UserOp.mult) x xs body SmtTerm.mult (by rfl)
    (fun a b => typeof_mult_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_lt_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.lt) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_ret_binop_first_none
    (Term.UOp UserOp.lt) x xs body SmtTerm.lt SmtType.Bool
    (by rfl) (fun a b => typeof_lt_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_leq_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.leq) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_ret_binop_first_none
    (Term.UOp UserOp.leq) x xs body SmtTerm.leq SmtType.Bool
    (by rfl) (fun a b => typeof_leq_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_gt_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.gt) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_ret_binop_first_none
    (Term.UOp UserOp.gt) x xs body SmtTerm.gt SmtType.Bool
    (by rfl) (fun a b => typeof_gt_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_geq_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.geq) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_ret_binop_first_none
    (Term.UOp UserOp.geq) x xs body SmtTerm.geq SmtType.Bool
    (by rfl) (fun a b => typeof_geq_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_div_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.div) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_int_binop_first_none
    (Term.UOp UserOp.div) x xs body SmtTerm.div SmtType.Int
    (by rfl) (fun a b => typeof_div_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_mod_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.mod) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_int_binop_first_none
    (Term.UOp UserOp.mod) x xs body SmtTerm.mod SmtType.Int
    (by rfl) (fun a b => typeof_mod_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_multmult_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.multmult) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_int_binop_first_none
    (Term.UOp UserOp.multmult) x xs body SmtTerm.multmult SmtType.Int
    (by rfl) (fun a b => typeof_multmult_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_divisible_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.divisible) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_int_binop_first_none
    (Term.UOp UserOp.divisible) x xs body SmtTerm.divisible SmtType.Bool
    (by rfl) (fun a b => typeof_divisible_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_div_total_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.div_total) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_int_binop_first_none
    (Term.UOp UserOp.div_total) x xs body SmtTerm.div_total SmtType.Int
    (by rfl) (fun a b => typeof_div_total_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_mod_total_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.mod_total) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_int_binop_first_none
    (Term.UOp UserOp.mod_total) x xs body SmtTerm.mod_total SmtType.Int
    (by rfl) (fun a b => typeof_mod_total_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_multmult_total_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.multmult_total) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_int_binop_first_none
    (Term.UOp UserOp.multmult_total) x xs body SmtTerm.multmult_total
    SmtType.Int (by rfl) (fun a b => typeof_multmult_total_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_qdiv_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.qdiv) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_ret_binop_first_none
    (Term.UOp UserOp.qdiv) x xs body SmtTerm.qdiv SmtType.Real
    (by rfl) (fun a b => typeof_qdiv_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_qdiv_total_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.qdiv_total) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_arith_ret_binop_first_none
    (Term.UOp UserOp.qdiv_total) x xs body SmtTerm.qdiv_total SmtType.Real
    (by rfl) (fun a b => typeof_qdiv_total_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_select_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.select) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.select (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  exact smt_select_type_none_of_first_arg_none
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_array_deq_diff_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp._at_array_deq_diff) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (__eo_to_smt_array_deq_diff
          (__eo_to_smt (eoBinderListCons x xs))
          (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs)))
          (__eo_to_smt body) (__smtx_typeof (__eo_to_smt body))) =
      SmtType.None
  exact smt_array_deq_diff_type_none_of_first_arg_none
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_concat_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.concat) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.concat (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  exact smt_concat_type_none_of_first_arg_none
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_bvand_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvand) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvand) x xs body SmtTerm.bvand
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_39])

theorem smtx_typeof_eo_to_smt_binderShape_bvor_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvor) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvor) x xs body SmtTerm.bvor
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_40])

theorem smtx_typeof_eo_to_smt_binderShape_bvnand_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvnand) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvnand) x xs body SmtTerm.bvnand
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_41])

theorem smtx_typeof_eo_to_smt_binderShape_bvnor_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvnor) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvnor) x xs body SmtTerm.bvnor
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_42])

theorem smtx_typeof_eo_to_smt_binderShape_bvxor_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvxor) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvxor) x xs body SmtTerm.bvxor
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_43])

theorem smtx_typeof_eo_to_smt_binderShape_bvxnor_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvxnor) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvxnor) x xs body SmtTerm.bvxnor
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_44])

theorem smtx_typeof_eo_to_smt_binderShape_bvcomp_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvcomp) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvcomp) x xs body SmtTerm.bvcomp (SmtType.BitVec 1)
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_45])

theorem smtx_typeof_eo_to_smt_binderShape_bvadd_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvadd) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvadd) x xs body SmtTerm.bvadd
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_47])

theorem smtx_typeof_eo_to_smt_binderShape_bvmul_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvmul) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvmul) x xs body SmtTerm.bvmul
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_48])

theorem smtx_typeof_eo_to_smt_binderShape_bvudiv_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvudiv) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvudiv) x xs body SmtTerm.bvudiv
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_49])

theorem smtx_typeof_eo_to_smt_binderShape_bvurem_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvurem) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvurem) x xs body SmtTerm.bvurem
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_50])

theorem smtx_typeof_eo_to_smt_binderShape_bvsub_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsub) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvsub) x xs body SmtTerm.bvsub
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_51])

theorem smtx_typeof_eo_to_smt_binderShape_bvsdiv_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsdiv) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvsdiv) x xs body SmtTerm.bvsdiv
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_52])

theorem smtx_typeof_eo_to_smt_binderShape_bvsrem_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsrem) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvsrem) x xs body SmtTerm.bvsrem
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_53])

theorem smtx_typeof_eo_to_smt_binderShape_bvsmod_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsmod) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvsmod) x xs body SmtTerm.bvsmod
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_54])

theorem smtx_typeof_eo_to_smt_binderShape_bvult_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvult) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvult) x xs body SmtTerm.bvult SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_55])

theorem smtx_typeof_eo_to_smt_binderShape_bvule_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvule) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvule) x xs body SmtTerm.bvule SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_56])

theorem smtx_typeof_eo_to_smt_binderShape_bvugt_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvugt) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvugt) x xs body SmtTerm.bvugt SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_57])

theorem smtx_typeof_eo_to_smt_binderShape_bvuge_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvuge) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvuge) x xs body SmtTerm.bvuge SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_58])

theorem smtx_typeof_eo_to_smt_binderShape_bvslt_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvslt) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvslt) x xs body SmtTerm.bvslt SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_59])

theorem smtx_typeof_eo_to_smt_binderShape_bvsle_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsle) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvsle) x xs body SmtTerm.bvsle SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_60])

theorem smtx_typeof_eo_to_smt_binderShape_bvsgt_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsgt) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvsgt) x xs body SmtTerm.bvsgt SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_61])

theorem smtx_typeof_eo_to_smt_binderShape_bvsge_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsge) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvsge) x xs body SmtTerm.bvsge SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_62])

theorem smtx_typeof_eo_to_smt_binderShape_bvshl_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvshl) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvshl) x xs body SmtTerm.bvshl
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_63])

theorem smtx_typeof_eo_to_smt_binderShape_bvlshr_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvlshr) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvlshr) x xs body SmtTerm.bvlshr
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_64])

theorem smtx_typeof_eo_to_smt_binderShape_bvashr_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvashr) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_binop_first_none
    (Term.UOp UserOp.bvashr) x xs body SmtTerm.bvashr
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_65])

theorem smtx_typeof_eo_to_smt_binderShape_bvuaddo_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvuaddo) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvuaddo) x xs body SmtTerm.bvuaddo SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_70])

theorem smtx_typeof_eo_to_smt_binderShape_bvsaddo_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsaddo) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvsaddo) x xs body SmtTerm.bvsaddo SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_72])

theorem smtx_typeof_eo_to_smt_binderShape_bvumulo_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvumulo) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvumulo) x xs body SmtTerm.bvumulo SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_73])

theorem smtx_typeof_eo_to_smt_binderShape_bvsmulo_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsmulo) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvsmulo) x xs body SmtTerm.bvsmulo SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_74])

theorem smtx_typeof_eo_to_smt_binderShape_bvusubo_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvusubo) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvusubo) x xs body SmtTerm.bvusubo SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_75])

theorem smtx_typeof_eo_to_smt_binderShape_bvssubo_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvssubo) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvssubo) x xs body SmtTerm.bvssubo SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_76])

theorem smtx_typeof_eo_to_smt_binderShape_bvsdivo_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.bvsdivo) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_bv_ret_binop_first_none
    (Term.UOp UserOp.bvsdivo) x xs body SmtTerm.bvsdivo SmtType.Bool
    (by rfl) (fun a b => by rw [__smtx_typeof.eq_77])

theorem smtx_typeof_eo_to_smt_binderShape_bvultbv_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.bvultbv) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.ite
          (SmtTerm.bvult (__eo_to_smt (eoBinderListCons x xs))
            (__eo_to_smt body))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
      SmtType.None
  have hCond :
      __smtx_typeof
          (SmtTerm.bvult (__eo_to_smt (eoBinderListCons x xs))
            (__eo_to_smt body)) =
        SmtType.None :=
    smt_bv_binop_ret_type_none_of_first_arg_none SmtTerm.bvult
      SmtType.Bool (__eo_to_smt (eoBinderListCons x xs))
      (__eo_to_smt body) (fun a b => by rw [__smtx_typeof.eq_55])
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  exact smt_ite_type_none_of_cond_arg_none
    (SmtTerm.bvult (__eo_to_smt (eoBinderListCons x xs))
      (__eo_to_smt body))
    (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0) hCond

theorem smtx_typeof_eo_to_smt_binderShape_bvsltbv_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.bvsltbv) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.ite
          (SmtTerm.bvslt (__eo_to_smt (eoBinderListCons x xs))
            (__eo_to_smt body))
          (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
      SmtType.None
  have hCond :
      __smtx_typeof
          (SmtTerm.bvslt (__eo_to_smt (eoBinderListCons x xs))
            (__eo_to_smt body)) =
        SmtType.None :=
    smt_bv_binop_ret_type_none_of_first_arg_none SmtTerm.bvslt
      SmtType.Bool (__eo_to_smt (eoBinderListCons x xs))
      (__eo_to_smt body) (fun a b => by rw [__smtx_typeof.eq_59])
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  exact smt_ite_type_none_of_cond_arg_none
    (SmtTerm.bvslt (__eo_to_smt (eoBinderListCons x xs))
      (__eo_to_smt body))
    (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0) hCond

theorem smtx_typeof_eo_to_smt_binderShape_at_from_bools_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp._at_from_bools) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.concat
          (SmtTerm.ite (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
          (__eo_to_smt body)) =
      SmtType.None
  have hHead :
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
        SmtType.None :=
    smt_ite_type_none_of_cond_arg_none
      (__eo_to_smt (eoBinderListCons x xs))
      (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)
      (smtx_typeof_eo_to_smt_binderListCons_none x xs)
  exact smt_concat_type_none_of_first_arg_none
    (SmtTerm.ite (__eo_to_smt (eoBinderListCons x xs))
      (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
    (__eo_to_smt body) hHead

theorem smtx_typeof_eo_to_smt_binderShape_str_concat_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.str_concat) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_seq_binop_first_none
    (Term.UOp UserOp.str_concat) x xs body SmtTerm.str_concat
    (by rfl) (fun a b => typeof_str_concat_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_strings_deq_diff_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp._at_strings_deq_diff)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
          (SmtTerm.not
            (SmtTerm.eq
              (SmtTerm.str_substr (__eo_to_smt (eoBinderListCons x xs))
                (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                (SmtTerm.Numeral 1))
              (SmtTerm.str_substr (__eo_to_smt body)
                (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                (SmtTerm.Numeral 1))))
          native_nat_zero) =
      SmtType.None
  have hLeftSub :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
            (SmtTerm.Numeral 1)) =
        SmtType.None := by
    rw [typeof_str_substr_eq,
      smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  have hBody :
      __smtx_typeof
          (SmtTerm.not
            (SmtTerm.eq
              (SmtTerm.str_substr (__eo_to_smt (eoBinderListCons x xs))
                (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                (SmtTerm.Numeral 1))
              (SmtTerm.str_substr (__eo_to_smt body)
                (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                (SmtTerm.Numeral 1)))) =
        SmtType.None := by
    rw [typeof_not_eq, typeof_eq_eq, hLeftSub]
    cases __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt body)
          (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
          (SmtTerm.Numeral 1)) <;>
      simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
        native_Teq]
  rw [smtx_typeof_choice_nth_term_eq]
  simp [__smtx_typeof_choice_nth, hBody, native_ite, native_Teq]

theorem smtx_typeof_eo_to_smt_binderShape_str_contains_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.str_contains) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_seq_ret_binop_first_none
    (Term.UOp UserOp.str_contains) x xs body SmtTerm.str_contains
    SmtType.Bool (by rfl) (fun a b => typeof_str_contains_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_str_at_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.str_at) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_at (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  rw [typeof_str_at_eq, smtx_typeof_eo_to_smt_binderListCons_none]
  rfl

theorem smtx_typeof_eo_to_smt_binderShape_str_prefixof_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.str_prefixof) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_seq_char_binop_first_none'
    (Term.UOp UserOp.str_prefixof) x xs body SmtTerm.str_prefixof
    SmtType.Bool (by rfl) (fun a b => typeof_str_prefixof_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_str_suffixof_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.str_suffixof) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_seq_char_binop_first_none'
    (Term.UOp UserOp.str_suffixof) x xs body SmtTerm.str_suffixof
    SmtType.Bool (by rfl) (fun a b => typeof_str_suffixof_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_str_lt_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.str_lt) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_seq_char_binop_first_none'
    (Term.UOp UserOp.str_lt) x xs body SmtTerm.str_lt
    SmtType.Bool (by rfl) (fun a b => typeof_str_lt_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_str_leq_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.str_leq) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_seq_char_binop_first_none'
    (Term.UOp UserOp.str_leq) x xs body SmtTerm.str_leq
    SmtType.Bool (by rfl) (fun a b => typeof_str_leq_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_seq_nth_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.seq_nth) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.seq_nth (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  rw [typeof_seq_nth_eq, smtx_typeof_eo_to_smt_binderListCons_none]
  rfl

theorem smtx_typeof_eo_to_smt_binderShape_strings_stoi_result_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp._at_strings_stoi_result)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_to_int
          (SmtTerm.str_substr (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.Numeral 0) (__eo_to_smt body))) =
      SmtType.None
  have hSub :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt (eoBinderListCons x xs))
            (SmtTerm.Numeral 0) (__eo_to_smt body)) =
        SmtType.None := by
    rw [typeof_str_substr_eq,
      smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  rw [typeof_str_to_int_eq, hSub]
  rfl

theorem smtx_typeof_eo_to_smt_binderShape_strings_itos_result_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp._at_strings_itos_result)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.mod (__eo_to_smt (eoBinderListCons x xs))
          (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt body))) =
      SmtType.None
  exact smt_int_binop_type_none_of_first_arg_none SmtTerm.mod
    SmtType.Int (__eo_to_smt (eoBinderListCons x xs))
    (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt body))
    (fun a b => typeof_mod_eq a b)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_strings_num_occur_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp._at_strings_num_occur)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.div
          (SmtTerm.neg
            (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs)))
            (SmtTerm.str_len
              (SmtTerm.str_replace_all
                (__eo_to_smt (eoBinderListCons x xs))
                (__eo_to_smt body)
                (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
          (SmtTerm.str_len (__eo_to_smt body))) =
      SmtType.None
  have hLen :
      __smtx_typeof
          (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs))) =
        SmtType.None := by
    rw [typeof_str_len_eq,
      smtx_typeof_eo_to_smt_binderListCons_none]
    rfl
  have hNum :
      __smtx_typeof
          (SmtTerm.neg
            (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs)))
            (SmtTerm.str_len
              (SmtTerm.str_replace_all
                (__eo_to_smt (eoBinderListCons x xs))
                (__eo_to_smt body)
                (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))))) =
        SmtType.None :=
    smt_arith_overload_binop_type_none_of_first_arg_none SmtTerm.neg
      (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs)))
      (SmtTerm.str_len
        (SmtTerm.str_replace_all
          (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)
          (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))))
      (fun a b => typeof_neg_eq a b) hLen
  exact smt_int_binop_type_none_of_first_arg_none SmtTerm.div SmtType.Int
    (SmtTerm.neg
      (SmtTerm.str_len (__eo_to_smt (eoBinderListCons x xs)))
      (SmtTerm.str_len
        (SmtTerm.str_replace_all
          (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)
          (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
    (SmtTerm.str_len (__eo_to_smt body))
    (fun a b => typeof_div_eq a b) hNum

theorem smtx_typeof_eo_to_smt_binderShape_re_range_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.re_range) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_seq_char_binop_first_none'
    (Term.UOp UserOp.re_range) x xs body SmtTerm.re_range
    SmtType.RegLan (by rfl) (fun a b => typeof_re_range_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_re_concat_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.re_concat) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_reglan_binop_first_none
    (Term.UOp UserOp.re_concat) x xs body SmtTerm.re_concat
    (by rfl) (fun a b => typeof_re_concat_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_re_inter_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.re_inter) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_reglan_binop_first_none
    (Term.UOp UserOp.re_inter) x xs body SmtTerm.re_inter
    (by rfl) (fun a b => typeof_re_inter_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_re_union_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.re_union) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_reglan_binop_first_none
    (Term.UOp UserOp.re_union) x xs body SmtTerm.re_union
    (by rfl) (fun a b => typeof_re_union_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_re_diff_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.re_diff) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_reglan_binop_first_none
    (Term.UOp UserOp.re_diff) x xs body SmtTerm.re_diff
    (by rfl) (fun a b => typeof_re_diff_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_str_in_re_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp UserOp.str_in_re) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_seq_char_reglan_binop_first_none
    (Term.UOp UserOp.str_in_re) x xs body SmtTerm.str_in_re
    (by rfl) (fun a b => typeof_str_in_re_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_set_union_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.set_union) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_set_binop_first_none
    (Term.UOp UserOp.set_union) x xs body SmtTerm.set_union
    (by rfl) (fun a b => typeof_set_union_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_set_inter_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.set_inter) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_set_binop_first_none
    (Term.UOp UserOp.set_inter) x xs body SmtTerm.set_inter
    (by rfl) (fun a b => typeof_set_inter_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_set_minus_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.set_minus) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_set_binop_first_none
    (Term.UOp UserOp.set_minus) x xs body SmtTerm.set_minus
    (by rfl) (fun a b => typeof_set_minus_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_set_subset_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.set_subset) x xs body)) =
      SmtType.None :=
  smtx_typeof_eo_to_smt_binderShape_set_ret_binop_first_none
    (Term.UOp UserOp.set_subset) x xs body SmtTerm.set_subset SmtType.Bool
    (by rfl) (fun a b => typeof_set_subset_eq a b)

theorem smtx_typeof_eo_to_smt_binderShape_set_member_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.set_member) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.set_member (__eo_to_smt (eoBinderListCons x xs))
          (__eo_to_smt body)) =
      SmtType.None
  exact smt_set_member_type_none_of_first_arg_none_of_second_not_set_none
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)
    (smtx_typeof_eo_to_smt_ne_set_none body)

theorem smtx_typeof_eo_to_smt_binderShape_set_insert_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.set_insert) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (__eo_to_smt_set_insert (eoBinderListCons x xs)
          (__eo_to_smt body)) =
      SmtType.None
  exact eo_to_smt_set_insert_type_none_of_eo_list_cons
    x xs (__eo_to_smt body)

theorem smtx_typeof_eo_to_smt_binderShape_sets_deq_diff_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp._at_sets_deq_diff) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (__eo_to_smt_sets_deq_diff
          (__eo_to_smt (eoBinderListCons x xs))
          (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs)))
          (__eo_to_smt body) (__smtx_typeof (__eo_to_smt body))) =
      SmtType.None
  exact smt_sets_deq_diff_type_none_of_first_arg_none
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_tuple_none
    (x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.UOp UserOp.tuple) x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend
          (__eo_to_smt (eoBinderListCons x xs))
          (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs)))
          (__eo_to_smt body)) =
      SmtType.None
  exact smt_tuple_prepend_type_none_of_head_none
    (__eo_to_smt (eoBinderListCons x xs))
    (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs)))
    (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_uop_none_of_not_quant
    (op : UserOp) (x xs body : Term)
    (hForall : op ≠ UserOp.forall)
    (hExists : op ≠ UserOp.exists) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp op) x xs body)) =
      SmtType.None := by
  cases op
  case not =>
    exact smtx_typeof_eo_to_smt_binderShape_not_none x xs body
  case distinct =>
    exact smtx_typeof_eo_to_smt_binderShape_distinct_none x xs body
  case or =>
    exact smtx_typeof_eo_to_smt_binderShape_or_none x xs body
  case and =>
    exact smtx_typeof_eo_to_smt_binderShape_and_none x xs body
  case imp =>
    exact smtx_typeof_eo_to_smt_binderShape_imp_none x xs body
  case xor =>
    exact smtx_typeof_eo_to_smt_binderShape_xor_none x xs body
  case eq =>
    exact smtx_typeof_eo_to_smt_binderShape_eq_none x xs body
  case plus =>
    exact smtx_typeof_eo_to_smt_binderShape_plus_none x xs body
  case neg =>
    exact smtx_typeof_eo_to_smt_binderShape_neg_none x xs body
  case mult =>
    exact smtx_typeof_eo_to_smt_binderShape_mult_none x xs body
  case lt =>
    exact smtx_typeof_eo_to_smt_binderShape_lt_none x xs body
  case leq =>
    exact smtx_typeof_eo_to_smt_binderShape_leq_none x xs body
  case gt =>
    exact smtx_typeof_eo_to_smt_binderShape_gt_none x xs body
  case geq =>
    exact smtx_typeof_eo_to_smt_binderShape_geq_none x xs body
  case div =>
    exact smtx_typeof_eo_to_smt_binderShape_div_none x xs body
  case mod =>
    exact smtx_typeof_eo_to_smt_binderShape_mod_none x xs body
  case multmult =>
    exact smtx_typeof_eo_to_smt_binderShape_multmult_none x xs body
  case divisible =>
    exact smtx_typeof_eo_to_smt_binderShape_divisible_none x xs body
  case div_total =>
    exact smtx_typeof_eo_to_smt_binderShape_div_total_none x xs body
  case mod_total =>
    exact smtx_typeof_eo_to_smt_binderShape_mod_total_none x xs body
  case multmult_total =>
    exact smtx_typeof_eo_to_smt_binderShape_multmult_total_none x xs body
  case select =>
    exact smtx_typeof_eo_to_smt_binderShape_select_none x xs body
  case _at_array_deq_diff =>
    exact smtx_typeof_eo_to_smt_binderShape_array_deq_diff_none x xs body
  case concat =>
    exact smtx_typeof_eo_to_smt_binderShape_concat_none x xs body
  case bvand =>
    exact smtx_typeof_eo_to_smt_binderShape_bvand_none x xs body
  case bvor =>
    exact smtx_typeof_eo_to_smt_binderShape_bvor_none x xs body
  case bvnand =>
    exact smtx_typeof_eo_to_smt_binderShape_bvnand_none x xs body
  case bvnor =>
    exact smtx_typeof_eo_to_smt_binderShape_bvnor_none x xs body
  case bvxor =>
    exact smtx_typeof_eo_to_smt_binderShape_bvxor_none x xs body
  case bvxnor =>
    exact smtx_typeof_eo_to_smt_binderShape_bvxnor_none x xs body
  case bvcomp =>
    exact smtx_typeof_eo_to_smt_binderShape_bvcomp_none x xs body
  case bvadd =>
    exact smtx_typeof_eo_to_smt_binderShape_bvadd_none x xs body
  case bvmul =>
    exact smtx_typeof_eo_to_smt_binderShape_bvmul_none x xs body
  case bvudiv =>
    exact smtx_typeof_eo_to_smt_binderShape_bvudiv_none x xs body
  case bvurem =>
    exact smtx_typeof_eo_to_smt_binderShape_bvurem_none x xs body
  case bvsub =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsub_none x xs body
  case bvsdiv =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsdiv_none x xs body
  case bvsrem =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsrem_none x xs body
  case bvsmod =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsmod_none x xs body
  case bvult =>
    exact smtx_typeof_eo_to_smt_binderShape_bvult_none x xs body
  case bvule =>
    exact smtx_typeof_eo_to_smt_binderShape_bvule_none x xs body
  case bvugt =>
    exact smtx_typeof_eo_to_smt_binderShape_bvugt_none x xs body
  case bvuge =>
    exact smtx_typeof_eo_to_smt_binderShape_bvuge_none x xs body
  case bvslt =>
    exact smtx_typeof_eo_to_smt_binderShape_bvslt_none x xs body
  case bvsle =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsle_none x xs body
  case bvsgt =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsgt_none x xs body
  case bvsge =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsge_none x xs body
  case bvshl =>
    exact smtx_typeof_eo_to_smt_binderShape_bvshl_none x xs body
  case bvlshr =>
    exact smtx_typeof_eo_to_smt_binderShape_bvlshr_none x xs body
  case bvashr =>
    exact smtx_typeof_eo_to_smt_binderShape_bvashr_none x xs body
  case bvuaddo =>
    exact smtx_typeof_eo_to_smt_binderShape_bvuaddo_none x xs body
  case bvsaddo =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsaddo_none x xs body
  case bvumulo =>
    exact smtx_typeof_eo_to_smt_binderShape_bvumulo_none x xs body
  case bvsmulo =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsmulo_none x xs body
  case bvusubo =>
    exact smtx_typeof_eo_to_smt_binderShape_bvusubo_none x xs body
  case bvssubo =>
    exact smtx_typeof_eo_to_smt_binderShape_bvssubo_none x xs body
  case bvsdivo =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsdivo_none x xs body
  case bvultbv =>
    exact smtx_typeof_eo_to_smt_binderShape_bvultbv_none x xs body
  case bvsltbv =>
    exact smtx_typeof_eo_to_smt_binderShape_bvsltbv_none x xs body
  case _at_from_bools =>
    exact smtx_typeof_eo_to_smt_binderShape_at_from_bools_none x xs body
  case str_concat =>
    exact smtx_typeof_eo_to_smt_binderShape_str_concat_none x xs body
  case _at_strings_deq_diff =>
    exact smtx_typeof_eo_to_smt_binderShape_strings_deq_diff_none x xs body
  case str_contains =>
    exact smtx_typeof_eo_to_smt_binderShape_str_contains_none x xs body
  case str_at =>
    exact smtx_typeof_eo_to_smt_binderShape_str_at_none x xs body
  case str_prefixof =>
    exact smtx_typeof_eo_to_smt_binderShape_str_prefixof_none x xs body
  case str_suffixof =>
    exact smtx_typeof_eo_to_smt_binderShape_str_suffixof_none x xs body
  case str_lt =>
    exact smtx_typeof_eo_to_smt_binderShape_str_lt_none x xs body
  case str_leq =>
    exact smtx_typeof_eo_to_smt_binderShape_str_leq_none x xs body
  case seq_nth =>
    exact smtx_typeof_eo_to_smt_binderShape_seq_nth_none x xs body
  case _at_strings_stoi_result =>
    exact smtx_typeof_eo_to_smt_binderShape_strings_stoi_result_none x xs body
  case _at_strings_itos_result =>
    exact smtx_typeof_eo_to_smt_binderShape_strings_itos_result_none x xs body
  case _at_strings_num_occur =>
    exact smtx_typeof_eo_to_smt_binderShape_strings_num_occur_none x xs body
  case re_range =>
    exact smtx_typeof_eo_to_smt_binderShape_re_range_none x xs body
  case re_concat =>
    exact smtx_typeof_eo_to_smt_binderShape_re_concat_none x xs body
  case re_inter =>
    exact smtx_typeof_eo_to_smt_binderShape_re_inter_none x xs body
  case re_union =>
    exact smtx_typeof_eo_to_smt_binderShape_re_union_none x xs body
  case re_diff =>
    exact smtx_typeof_eo_to_smt_binderShape_re_diff_none x xs body
  case str_in_re =>
    exact smtx_typeof_eo_to_smt_binderShape_str_in_re_none x xs body
  case set_union =>
    exact smtx_typeof_eo_to_smt_binderShape_set_union_none x xs body
  case set_inter =>
    exact smtx_typeof_eo_to_smt_binderShape_set_inter_none x xs body
  case set_minus =>
    exact smtx_typeof_eo_to_smt_binderShape_set_minus_none x xs body
  case set_member =>
    exact smtx_typeof_eo_to_smt_binderShape_set_member_none x xs body
  case set_subset =>
    exact smtx_typeof_eo_to_smt_binderShape_set_subset_none x xs body
  case set_insert =>
    exact smtx_typeof_eo_to_smt_binderShape_set_insert_none x xs body
  case _at_sets_deq_diff =>
    exact smtx_typeof_eo_to_smt_binderShape_sets_deq_diff_none x xs body
  case tuple =>
    exact smtx_typeof_eo_to_smt_binderShape_tuple_none x xs body
  case qdiv =>
    exact smtx_typeof_eo_to_smt_binderShape_qdiv_none x xs body
  case qdiv_total =>
    exact smtx_typeof_eo_to_smt_binderShape_qdiv_total_none x xs body
  case «forall» =>
    exact False.elim (hForall rfl)
  case «exists» =>
    exact False.elim (hExists rfl)
  all_goals
    first
    | exact smtx_typeof_eo_to_smt_binderShape_generic_none
        (Term.UOp _) x xs body (by rfl)
    | change
        __smtx_typeof
            (SmtTerm.Apply _ (__eo_to_smt body)) =
          SmtType.None
      apply smtx_typeof_apply_of_head_none_of_non_datatype_head
      · intro s d i j hEq
        dsimp [__eo_to_smt, eoBinderListCons] at hEq
        first
        | solve | cases hEq
        | have hBinder :
              __smtx_typeof
                  ((SmtTerm.Apply SmtTerm.None (__eo_to_smt x)).Apply
                    (__eo_to_smt xs)) =
                SmtType.None := by
            simpa [eo_to_smt_binderListCons_eq] using
              smtx_typeof_eo_to_smt_binderListCons_none x xs
          have hLe :
              native_zleq 0 (__smtx_bv_sizeof_type SmtType.None) =
                false := by
            rfl
          simp [hBinder, hLe, native_ite] at hEq
      · intro s d i hEq
        dsimp [__eo_to_smt, eoBinderListCons] at hEq
        first
        | solve | cases hEq
        | have hBinder :
              __smtx_typeof
                  ((SmtTerm.Apply SmtTerm.None (__eo_to_smt x)).Apply
                    (__eo_to_smt xs)) =
                SmtType.None := by
            simpa [eo_to_smt_binderListCons_eq] using
              smtx_typeof_eo_to_smt_binderListCons_none x xs
          have hLe :
              native_zleq 0 (__smtx_bv_sizeof_type SmtType.None) =
                false := by
            rfl
          simp [hBinder, hLe, native_ite] at hEq
      · exact smtx_typeof_eo_to_smt_apply_uop_binderListCons_none _ x xs

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

theorem smtx_typeof_eo_to_smt_binderShape_store_none
    (a x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.store) a)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.store (__eo_to_smt a)
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_store_type_none_of_second_arg_none
    (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
    (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_bvite_none
    (c x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.bvite) c)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt c) (SmtTerm.Binary 1 1))
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_ite_type_none_of_then_arg_none
    (SmtTerm.eq (__eo_to_smt c) (SmtTerm.Binary 1 1))
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_str_substr_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.str_substr) s)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s)
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_str_substr_type_none_of_second_arg_none
    (__eo_to_smt s) (__eo_to_smt (eoBinderListCons x xs))
    (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_str_replace_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.str_replace) s)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt s)
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_seq_triop_type_none_of_second_arg_none
    SmtTerm.str_replace (__eo_to_smt s)
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (fun a b c => typeof_str_replace_eq a b c)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_str_indexof_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.str_indexof) s)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_indexof (__eo_to_smt s)
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_str_indexof_type_none_of_second_arg_none
    (__eo_to_smt s) (__eo_to_smt (eoBinderListCons x xs))
    (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_str_update_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.str_update) s)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_update (__eo_to_smt s)
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_str_update_type_none_of_second_arg_none
    (__eo_to_smt s) (__eo_to_smt (eoBinderListCons x xs))
    (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_str_replace_all_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.str_replace_all) s)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_replace_all (__eo_to_smt s)
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_seq_triop_type_none_of_second_arg_none
    SmtTerm.str_replace_all (__eo_to_smt s)
    (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)
    (fun a b c => typeof_str_replace_all_eq a b c)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_str_replace_re_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.str_replace_re) s)
            x xs body)) =
      SmtType.None := by
  exact smtx_typeof_eo_to_smt_binderShape_str_replace_re_second_none
    (Term.Apply (Term.UOp UserOp.str_replace_re) s) x xs body
    SmtTerm.str_replace_re (__eo_to_smt s) (by rfl)
    (fun a b c => typeof_str_replace_re_eq a b c)

theorem smtx_typeof_eo_to_smt_binderShape_str_replace_re_all_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.str_replace_re_all) s)
            x xs body)) =
      SmtType.None := by
  exact smtx_typeof_eo_to_smt_binderShape_str_replace_re_second_none
    (Term.Apply (Term.UOp UserOp.str_replace_re_all) s) x xs body
    SmtTerm.str_replace_re_all (__eo_to_smt s) (by rfl)
    (fun a b c => typeof_str_replace_re_all_eq a b c)

theorem smtx_typeof_eo_to_smt_binderShape_str_indexof_re_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp UserOp.str_indexof_re) s)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_indexof_re (__eo_to_smt s)
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_str_indexof_re_type_none_of_second_arg_none
    (__eo_to_smt s) (__eo_to_smt (eoBinderListCons x xs))
    (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_str_indexof_re_split_none
    (s x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape
            (Term.Apply (Term.UOp UserOp.str_indexof_re_split) s)
            x xs body)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.str_indexof_re_split (__eo_to_smt s)
          (__eo_to_smt (eoBinderListCons x xs)) (__eo_to_smt body)) =
      SmtType.None
  exact smt_str_indexof_re_split_type_none_of_second_arg_none
    (__eo_to_smt s) (__eo_to_smt (eoBinderListCons x xs))
    (__eo_to_smt body)
    (smtx_typeof_eo_to_smt_binderListCons_none x xs)

theorem smtx_typeof_eo_to_smt_binderShape_apply_uop_none
    (op : UserOp) (a x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp op) a) x xs body)) =
      SmtType.None := by
  cases op
  case ite =>
    exact smtx_typeof_eo_to_smt_binderShape_ite_none a x xs body
  case store =>
    exact smtx_typeof_eo_to_smt_binderShape_store_none a x xs body
  case bvite =>
    exact smtx_typeof_eo_to_smt_binderShape_bvite_none a x xs body
  case str_substr =>
    exact smtx_typeof_eo_to_smt_binderShape_str_substr_none a x xs body
  case str_replace =>
    exact smtx_typeof_eo_to_smt_binderShape_str_replace_none a x xs body
  case str_indexof =>
    exact smtx_typeof_eo_to_smt_binderShape_str_indexof_none a x xs body
  case str_update =>
    exact smtx_typeof_eo_to_smt_binderShape_str_update_none a x xs body
  case str_replace_all =>
    exact smtx_typeof_eo_to_smt_binderShape_str_replace_all_none a x xs body
  case str_replace_re =>
    exact smtx_typeof_eo_to_smt_binderShape_str_replace_re_none a x xs body
  case str_replace_re_all =>
    exact smtx_typeof_eo_to_smt_binderShape_str_replace_re_all_none
      a x xs body
  case str_indexof_re =>
    exact smtx_typeof_eo_to_smt_binderShape_str_indexof_re_none
      a x xs body
  case str_indexof_re_split =>
    exact smtx_typeof_eo_to_smt_binderShape_str_indexof_re_split_none
      a x xs body
  case _at_array_deq_diff =>
    exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
      (Term.Apply (Term.UOp UserOp._at_array_deq_diff) a) x xs body
      (by rfl)
      (by
        intro s d i j
        change
          __eo_to_smt_array_deq_diff (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt a))
              (__eo_to_smt (eoBinderListCons x xs))
              (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs))) ≠
            SmtTerm.DtSel s d i j
        exact smt_array_deq_diff_ne_dt_sel
          (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
          s d i j)
      (by
        intro s d i
        change
          __eo_to_smt_array_deq_diff (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt a))
              (__eo_to_smt (eoBinderListCons x xs))
              (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs))) ≠
            SmtTerm.DtTester s d i
        exact smt_array_deq_diff_ne_dt_tester
          (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
          s d i)
      (smtx_typeof_eo_to_smt_apply_apply_uop_binderListCons_none
        UserOp._at_array_deq_diff a x xs)
  case tuple =>
    exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
      (Term.Apply (Term.UOp UserOp.tuple) a) x xs body
      (by rfl)
      (by
        intro s d i j
        change
          __eo_to_smt_tuple_prepend (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt a))
              (__eo_to_smt (eoBinderListCons x xs)) ≠
            SmtTerm.DtSel s d i j
        exact TranslationProofs.eo_to_smt_tuple_prepend_ne_dt_sel
          (__eo_to_smt a) (__smtx_typeof (__eo_to_smt a))
          (__eo_to_smt (eoBinderListCons x xs)) s d i j)
      (by
        intro s d i
        change
          __eo_to_smt_tuple_prepend (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt a))
              (__eo_to_smt (eoBinderListCons x xs)) ≠
            SmtTerm.DtTester s d i
        exact TranslationProofs.eo_to_smt_tuple_prepend_ne_dt_tester
          (__eo_to_smt a) (__smtx_typeof (__eo_to_smt a))
          (__eo_to_smt (eoBinderListCons x xs)) s d i)
      (smtx_typeof_eo_to_smt_apply_apply_uop_binderListCons_none
        UserOp.tuple a x xs)
  case set_insert =>
    exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
      (Term.Apply (Term.UOp UserOp.set_insert) a) x xs body
      (by rfl)
      (by
        intro s d i j
        change
          __eo_to_smt_set_insert a
              (__eo_to_smt (eoBinderListCons x xs)) ≠
            SmtTerm.DtSel s d i j
        exact eo_to_smt_set_insert_base_none_ne_dt_sel
          a (__eo_to_smt (eoBinderListCons x xs))
          (smtx_typeof_eo_to_smt_binderListCons_none x xs) s d i j)
      (by
        intro s d i
        change
          __eo_to_smt_set_insert a
              (__eo_to_smt (eoBinderListCons x xs)) ≠
            SmtTerm.DtTester s d i
        exact eo_to_smt_set_insert_base_none_ne_dt_tester
          a (__eo_to_smt (eoBinderListCons x xs))
          (smtx_typeof_eo_to_smt_binderListCons_none x xs) s d i)
      (smtx_typeof_eo_to_smt_apply_apply_uop_binderListCons_none
        UserOp.set_insert a x xs)
  case _at_sets_deq_diff =>
    exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
      (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) a) x xs body
      (by rfl)
      (by
        intro s d i j
        change
          __eo_to_smt_sets_deq_diff (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt a))
              (__eo_to_smt (eoBinderListCons x xs))
              (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs))) ≠
            SmtTerm.DtSel s d i j
        exact smt_sets_deq_diff_ne_dt_sel
          (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
          s d i j)
      (by
        intro s d i
        change
          __eo_to_smt_sets_deq_diff (__eo_to_smt a)
              (__smtx_typeof (__eo_to_smt a))
              (__eo_to_smt (eoBinderListCons x xs))
              (__smtx_typeof (__eo_to_smt (eoBinderListCons x xs))) ≠
            SmtTerm.DtTester s d i
        exact smt_sets_deq_diff_ne_dt_tester
          (__eo_to_smt a) (__eo_to_smt (eoBinderListCons x xs))
          s d i)
      (smtx_typeof_eo_to_smt_apply_apply_uop_binderListCons_none
        UserOp._at_sets_deq_diff a x xs)
  case «forall» =>
    exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
      (Term.Apply (Term.UOp UserOp.forall) a) x xs body
      (by rfl)
      (eo_to_smt_apply_apply_forall_binderListCons_ne_dt_sel a x xs)
      (eo_to_smt_apply_apply_forall_binderListCons_ne_dt_tester a x xs)
      (smtx_typeof_eo_to_smt_apply_apply_uop_binderListCons_none
        UserOp.forall a x xs)
  case «exists» =>
    exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
      (Term.Apply (Term.UOp UserOp.exists) a) x xs body
      (by rfl)
      (eo_to_smt_apply_apply_exists_binderListCons_ne_dt_sel a x xs)
      (eo_to_smt_apply_apply_exists_binderListCons_ne_dt_tester a x xs)
      (smtx_typeof_eo_to_smt_apply_apply_uop_binderListCons_none
        UserOp.exists a x xs)
  all_goals
    exact smtx_typeof_eo_to_smt_binderShape_outer_apply_none
      (Term.Apply (Term.UOp _) a) x xs body
      (by rfl)
      (by
        intro s d i j hEq
        dsimp [__eo_to_smt, eoBinderListCons] at hEq
        cases hEq)
      (by
        intro s d i hEq
        dsimp [__eo_to_smt, eoBinderListCons] at hEq
        cases hEq)
      (smtx_typeof_eo_to_smt_apply_apply_uop_binderListCons_none
        _ a x xs)

theorem smtx_typeof_eo_to_smt_binderShape_apply_uop_ne_bool
    (op : UserOp) (a x xs body : Term) :
    __smtx_typeof
        (__eo_to_smt
          (eoBinderShape (Term.Apply (Term.UOp op) a) x xs body)) ≠
      SmtType.Bool := by
  intro hBool
  have hNone :=
    smtx_typeof_eo_to_smt_binderShape_apply_uop_none op a x xs body
  rw [hNone] at hBool
  cases hBool

theorem isQuantifierHead_of_uop_binderShape_non_none
    (op : UserOp) (x xs body : Term)
    (hNN :
      __smtx_typeof
          (__eo_to_smt (eoBinderShape (Term.UOp op) x xs body)) ≠
        SmtType.None) :
    IsQuantifierHead (Term.UOp op) := by
  by_cases hForall : op = UserOp.forall
  · subst op
    exact isQuantifierHead_forall
  · by_cases hExists : op = UserOp.exists
    · subst op
      exact isQuantifierHead_exists
    · have hNone :=
        smtx_typeof_eo_to_smt_binderShape_uop_none_of_not_quant
          op x xs body hForall hExists
      exact False.elim (hNN hNone)

theorem isQuantifierHead_of_uop_binderShape_bool
    (op : UserOp) (x xs body : Term)
    (hBool :
      __smtx_typeof
          (__eo_to_smt (eoBinderShape (Term.UOp op) x xs body)) =
        SmtType.Bool) :
    IsQuantifierHead (Term.UOp op) :=
  isQuantifierHead_of_uop_binderShape_non_none op x xs body
    (by
      intro hNone
      rw [hNone] at hBool
      cases hBool)

theorem smtx_typeof_eo_to_smt_binderShape_uop_ne_bool_of_not_quant
    (op : UserOp) (x xs body : Term)
    (hForall : op ≠ UserOp.forall)
    (hExists : op ≠ UserOp.exists) :
    __smtx_typeof
        (__eo_to_smt (eoBinderShape (Term.UOp op) x xs body)) ≠
      SmtType.Bool := by
  intro hBool
  have hNone :=
    smtx_typeof_eo_to_smt_binderShape_uop_none_of_not_quant
      op x xs body hForall hExists
  rw [hNone] at hBool
  cases hBool
